#!/usr/bin/env python3
"""
VERSE EFFECTS (`<computes>`..`<transacts>`) & COALGEBRAIC OPTIMISATION RECEIPTS (`bsar.verse_effects`)
License: GNU AGPLv3
Attestation: probabilistic_structural
Dependencies: 0 (Python >= 3.10 Standard Library Only)

Implements Items #4, #5, and #6 of `build-sheet.md` (Simon Peyton Jones's Verse semantics,
adapted to zero-GC 1990 SNES arenas + coalgebraic bisimulation witnesses):

  1. Failure as Control Flow (`guard(cond)` / `<decides>`) + Zero-GC `<transacts>`:
     - Bare guard expressions (`guard(x <= limit, "reason")`) fail cleanly rather than corrupting RAM.
     - Inside `verse_transact(arena, state, fn)`:
         * Snapshots the 16-bit bump cursor (`arena._checkpoint_cursor()`) and clones a shadow copy
           of mutable state.
         * If ANY guard fails, rolls back the arena cursor in `O(1)` (`LDA !saved : STA !cursor`,
           zero heap GC!) and discards every staged state write ("a transition posts whole or never occurred").

  2. Compiler-Checked Effect Specifiers (`EffectSet`):
     - `<computes>`  : Pure calculation; may NOT read/write mutable state, arenas, or fail guards.
     - `<reads>`     : May inspect declared state/arenas; may NOT mutate or allocate.
     - `<writes>`    : May mutate declared state/arenas.
     - `<decides>`   : May fail via `guard(...)`.
     - `<transacts>` : Implies `<reads> + <writes> + <decides>` with automatic atomic rollback!

  3. Coalgebraic Equivalence for Optimisation Receipts (`prove_bisimulation_receipt`):
     - Verifies via breadth-first relational bisimulation (`R subseteq S_spec x S_fast`) that a
       fast hand-tuned hardware routine (e.g., SA-1 `$2307` middle-word Q8.8 multiply or stream-fused
       machine) is 100% observationally equivalent to its reference specification across all inputs,
       emitting a `STAR` RATS + `ModalBox` SHA-256 **Optimisation Receipt**!
"""

from __future__ import annotations

from collections import deque
import copy
from dataclasses import dataclass, field
import hashlib
import json
from typing import Any, Callable, Dict, FrozenSet, Hashable, Iterable, List, Mapping, Optional, Sequence, Set, Tuple, TypeVar

from .arenas import ArenaScope, RegionPtr
from .asar_zd_microbench import pack_asar_rats_block, verify_asar_rats_block
from .fp_coalgebra import ModalBox

T = TypeVar("T")

VALID_EFFECT_TAGS = frozenset({"computes", "reads", "writes", "decides", "transacts"})


class IxEffectViolationError(TypeError):
    """Raised when a verb performs an operation forbidden by its declared Verse effect specifiers."""


class IxBisimulationError(AssertionError):
    """Raised when a fast routine diverges observationally from its specification coalgebra."""


class _VerseGuardFailure(Exception):
    """Internal control-flow signal used by Verse `<decides>` / `<transacts>` refusal-at-posting."""

    def __init__(self, reason: str) -> None:
        super().__init__(reason)
        self.reason = reason


@dataclass(frozen=True)
class EffectSpec:
    """
    Declared Verse effect specifiers for a Bsar machine transition or verb.
    """

    tags: FrozenSet[str]

    def __post_init__(self) -> None:
        unknown = self.tags - VALID_EFFECT_TAGS
        if unknown:
            raise ValueError(f"Unknown Verse effect specifier(s): {sorted(unknown)}")
        if "computes" in self.tags and len(self.tags) > 1 and self.tags != frozenset({"computes", "decides"}):
            raise ValueError(
                "`<computes>` marks side-effect-free code and cannot be combined with `<reads>`, `<writes>`, or `<transacts>`!"
            )

    @classmethod
    def parse(cls, *effects: str) -> "EffectSpec":
        cleaned = frozenset(e.strip("<> ").lower() for e in effects) or frozenset({"computes"})
        return cls(cleaned)

    @property
    def can_read(self) -> bool:
        return bool(self.tags & {"reads", "writes", "transacts"})

    @property
    def can_write(self) -> bool:
        return bool(self.tags & {"writes", "transacts"})

    @property
    def can_decide(self) -> bool:
        return bool(self.tags & {"decides", "transacts"})

    @property
    def is_transactional(self) -> bool:
        return "transacts" in self.tags


class VerseExecContext:
    """
    Checked execution handle passed into `@verse_verb` / `verse_transact` bodies.
    """

    def __init__(
        self,
        verb_name: str,
        effect_spec: EffectSpec,
        state: Optional[Dict[str, Any]] = None,
        arena: Optional[ArenaScope] = None,
    ) -> None:
        self.verb_name = verb_name
        self.effects = effect_spec
        self._state = state if state is not None else {}
        self._arena = arena

    def read(self, key: str) -> Any:
        if not self.effects.can_read:
            raise IxEffectViolationError(
                f"Effect Violation in `{self.verb_name}` ({sorted(self.effects.tags)}): "
                f"Attempted to read state key `'{key}'` without `<reads>`, `<writes>`, or `<transacts>`!"
            )
        return self._state[key]

    def write(self, key: str, value: Any) -> None:
        if not self.effects.can_write:
            raise IxEffectViolationError(
                f"Effect Violation in `{self.verb_name}` ({sorted(self.effects.tags)}): "
                f"Attempted to mutate state key `'{key}'` without `<writes>` or `<transacts>`!"
            )
        self._state[key] = value

    def alloc_in_arena(self, size: int, align: int = 2, label: str = "tx_buf") -> RegionPtr:
        if not self.effects.can_write:
            raise IxEffectViolationError(
                f"Effect Violation in `{self.verb_name}` ({sorted(self.effects.tags)}): "
                f"Arena bump allocation requires `<writes>` or `<transacts>`!"
            )
        if self._arena is None:
            raise IxEffectViolationError(f"No `ArenaScope` bound to `{self.verb_name}`!")
        return self._arena.alloc(size=size, align=align, label=label)

    def guard(self, condition: bool, reason: str = "guard_failed") -> None:
        """
        Verse bare assertion / guard idiom (`x <= limit`):
          - Requires `<decides>` or `<transacts>` effect specifier!
          - If `condition` is False, aborts the speculative computation cleanly ("refusal-at-posting").
        """
        if not self.effects.can_decide:
            raise IxEffectViolationError(
                f"Effect Violation in `{self.verb_name}` ({sorted(self.effects.tags)}): "
                f"`guard(...)` requires `<decides>` or `<transacts>` effect specifier!"
            )
        if not condition:
            raise _VerseGuardFailure(reason)


@dataclass(frozen=True)
class TransactOutcome:
    committed: bool
    value: Any
    failure_reason: Optional[str]
    arena_cursor_before: int
    arena_cursor_after: int
    asar_asm: str


def verse_transact(
    verb_name: str,
    state: Dict[str, Any],
    body: Callable[[VerseExecContext], T],
    arena: Optional[ArenaScope] = None,
) -> TransactOutcome:
    """
    Execute `body(ctx)` under Verse `<transacts>` semantics with ZERO garbage collection:
      - Snapshots `arena` bump cursor (`O(1)`) and creates a shadow copy of `state`.
      - If `body` completes with all `ctx.guard(...)` assertions holding:
          * Atomically commits the shadow state into `state` and keeps the arena allocations!
      - If ANY `ctx.guard(...)` fails:
          * Rolls back `arena` cursor in `O(1)` (`LDA !saved : STA !cursor`) and discards all
            shadow state writes — the transition never occurred!
    """
    cursor_before = arena.cursor if arena is not None else 0
    snap = arena._checkpoint_cursor() if arena is not None else None
    shadow_state = copy.deepcopy(state)
    ctx = VerseExecContext(
        verb_name=verb_name,
        effect_spec=EffectSpec.parse("<transacts>"),
        state=shadow_state,
        arena=arena,
    )

    asm_lines = [
        f"; [<transacts> `{verb_name}`] O(1) cursor checkpoint = {cursor_before}B",
        f"    LDA !ArenaCursor : STA !TxSavedCursor",
    ]
    try:
        out_val = body(ctx)
    except _VerseGuardFailure as fail:
        if arena is not None and snap is not None:
            arena._rollback_cursor(snap)
        cursor_after = arena.cursor if arena is not None else 0
        asm_lines.append(
            f"    ; Guard failed (`{fail.reason}`) -> refusal-at-posting rollback!"
        )
        asm_lines.append(
            f"    LDA !TxSavedCursor : STA !ArenaCursor        ; Restored cursor = {cursor_after}B"
        )
        return TransactOutcome(
            committed=False,
            value=None,
            failure_reason=fail.reason,
            arena_cursor_before=cursor_before,
            arena_cursor_after=cursor_after,
            asar_asm="\n".join(asm_lines),
        )

    # Commit shadow state atomically into `state`
    state.clear()
    state.update(shadow_state)
    cursor_after = arena.cursor if arena is not None else 0
    asm_lines.append(
        f"    ; All guards passed -> atomic commit (cursor = {cursor_after}B)"
    )
    return TransactOutcome(
        committed=True,
        value=out_val,
        failure_reason=None,
        arena_cursor_before=cursor_before,
        arena_cursor_after=cursor_after,
        asar_asm="\n".join(asm_lines),
    )


def run_verse_verb(
    verb_name: str,
    effects: Sequence[str],
    body: Callable[[VerseExecContext], T],
    state: Optional[Dict[str, Any]] = None,
    arena: Optional[ArenaScope] = None,
) -> Tuple[bool, Optional[T], Optional[str]]:
    """
    Execute a non-transactional verb under explicit Verse effect specifiers
    (`<computes>`, `<reads>`, `<writes>`, `<decides>`).
    Returns `(succeeded, value, failure_reason)`.
    """
    spec = EffectSpec.parse(*effects)
    if spec.is_transactional:
        if state is None:
            state = {}
        tx = verse_transact(verb_name, state, body, arena=arena)
        return (tx.committed, tx.value, tx.failure_reason)

    ctx = VerseExecContext(verb_name=verb_name, effect_spec=spec, state=state, arena=arena)
    try:
        val = body(ctx)
        return (True, val, None)
    except _VerseGuardFailure as fail:
        return (False, None, fail.reason)


# ==============================================================================
# 2. COALGEBRAIC EQUIVALENCE FOR OPTIMISATION RECEIPTS (`OptimisationReceipt`)
# ==============================================================================


@dataclass(frozen=True)
class OptimisationReceipt:
    """
    Checkable Coalgebraic Bisimulation Witness justifying replacing `spec_name`
    with `fast_name` (sealed in an authentic SNES `STAR` RATS block + `ModalBox`).
    """

    spec_name: str
    fast_name: str
    bisimulation_relation_size: int
    alphabet_size: int
    transitions_checked: int
    rats_header_hex: str
    rats_valid: bool
    receipt_sha256: str
    sample_witness_pairs: Tuple[Tuple[str, str], ...]


def prove_bisimulation_receipt(
    *,
    spec_name: str,
    fast_name: str,
    spec_init: Hashable,
    fast_init: Hashable,
    alphabet: Sequence[Any],
    spec_step: Callable[[Any, Any], Hashable],
    fast_step: Callable[[Any, Any], Hashable],
    spec_obs: Callable[[Any], Any],
    fast_obs: Callable[[Any], Any],
    max_pairs: int = 10000,
) -> ModalBox[OptimisationReceipt]:
    """
    Constructively prove that two deterministic coalgebras `(S_spec, spec_obs, spec_step)`
    and `(S_fast, fast_obs, fast_step)` are **behaviourally equivalent (bisimilar)** from
    `(spec_init, fast_init)` across `alphabet`:
      - Every reachable state pair `(s1, s2)` in relation `R` MUST satisfy `spec_obs(s1) == fast_obs(s2)`.
      - For every input `a in alphabet`, `(spec_step(s1, a), fast_step(s2, a))` is also in `R`.
      - If ANY discrepancy exists, reconstructs the **exact shortest counterexample trace** and
        raises `IxBisimulationError`!
      - Otherwise seals the verified relation `R` into a `STAR` RATS + `ModalBox` Optimisation Receipt.
    """
    queue: deque[Tuple[Hashable, Hashable, Tuple[Any, ...]]] = deque(
        [(spec_init, fast_init, ())]
    )
    visited: Set[Tuple[Hashable, Hashable]] = {(spec_init, fast_init)}
    transitions_checked = 0

    while queue:
        if len(visited) > max_pairs:
            raise RuntimeError(f"Bisimulation state space exceeded max_pairs={max_pairs}")
        s1, s2, trace = queue.popleft()
        o1 = spec_obs(s1)
        o2 = fast_obs(s2)
        if o1 != o2:
            raise IxBisimulationError(
                f"Optimisation Receipt REJECTED (`{spec_name}` !~ `{fast_name}`): "
                f"Observational divergence after input trace {list(trace)}!\n"
                f"  Spec state `{s1!r}` observed -> {o1!r}\n"
                f"  Fast state `{s2!r}` observed -> {o2!r}"
            )
        for sym in alphabet:
            n1 = spec_step(s1, sym)
            n2 = fast_step(s2, sym)
            transitions_checked += 1
            pair = (n1, n2)
            if pair not in visited:
                visited.add(pair)
                queue.append((n1, n2, trace + (sym,)))

    canonical_pairs = sorted((repr(a), repr(b)) for a, b in visited)
    witness_json = json.dumps(
        {
            "spec": spec_name,
            "fast": fast_name,
            "relation_size": len(canonical_pairs),
            "transitions_checked": transitions_checked,
            "pairs_digest": hashlib.sha256(
                json.dumps(canonical_pairs).encode("utf-8")
            ).hexdigest(),
        },
        sort_keys=True,
    ).encode("utf-8")

    rats_blob = pack_asar_rats_block(witness_json)
    rats_info = verify_asar_rats_block(rats_blob)
    receipt = OptimisationReceipt(
        spec_name=spec_name,
        fast_name=fast_name,
        bisimulation_relation_size=len(canonical_pairs),
        alphabet_size=len(alphabet),
        transitions_checked=transitions_checked,
        rats_header_hex=rats_info["header_hex"],
        rats_valid=rats_info["valid"],
        receipt_sha256=hashlib.sha256(rats_blob).hexdigest(),
        sample_witness_pairs=tuple(canonical_pairs[:6]),
    )
    return ModalBox.pure(receipt, label=f"OptReceipt[{spec_name}~{fast_name}]")
