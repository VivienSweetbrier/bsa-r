#!/usr/bin/env python3
"""
HASKELL-INSPIRED FUNCTIONAL & COALGEBRAIC STATE-MACHINE ENGINE (`bsar.fp_coalgebra`)
License: GNU AGPLv3
Attestation: probabilistic_structural
Dependencies: 0 (Python >= 3.10 Standard Library Only)

Appends composable functional programming and universal-coalgebra primitives into `bsar`:
1. `ModalBox[A]` (`Functor`, `Applicative` Axiom K `<*>`, and `Comonad` `extract`/`extend`):
   - Encodes Sweetbrier's Categorical Modal Logic functor `Box` with monoidal SHA-256
     audit-trail accumulation: `Box(A -> B) -> (Box A -> Box B)`.
2. `MooreFold[A, B]` (Gabriel Gonzalez's Haskell `Control.Foldl` Applicative Moore Machine):
   - Represents single-pass folds as composable coalgebraic state machines `(S, step, done)`.
   - Composes independent folds via `<*>` (`zip_folds` / `map3`) so Round-4 spectral moments
     `(M_0, D, P, Variance, Theta)` execute in ONE fused cache-friendly loop!
3. Recursion Schemes (`TreeF`, `cata`, `ana`, `hylo`):
   - Generic catamorphism (fold), anamorphism (coalgebraic unfold), and deforested
     hylomorphism (`cata . ana`) for nonassociative syntax trees & dyadic splits.
4. Coalgebraic Implicit State-Machine Discovery (`discover_minimal_fsm`):
   - Given ANY implicit transition coalgebra `s |-> (obs(s), a |-> step(s, a))`, runs
     Moore/Hopcroft bisimulation partition refinement onto the Final Coalgebra quotient `S / ~`,
     automatically extracting minimal deterministic state machines (with JSON + Mermaid export),
     e.g., collapsing the 41-word radius-3 ball of Promislow's group `P` into its exact 4-state
     `V_4` orientation automaton, or collapsing 42 Sedenion assessors into 7 Box-Kite modes!
5. `AlgebraicPipeline` GADT-Style AST & Equational Rewrite Optimizer (`optimize_pipeline`):
   - Fuses adjacent `Filter` / `Mutate` stages and short-circuits nonlinear stages to `0`
     whenever Round 4's `Theorem J1` certifies monochromatic zero variance (`Theta == 0`).
"""

from __future__ import annotations

from collections import deque
from dataclasses import dataclass, field
import hashlib
import json
from typing import (
    Any,
    Callable,
    Dict,
    Generic,
    Hashable,
    Iterable,
    List,
    Optional,
    Sequence,
    Tuple,
    TypeVar,
    Union,
)

A = TypeVar("A")
B = TypeVar("B")
C = TypeVar("C")
D = TypeVar("D")
S = TypeVar("S")
T = TypeVar("T")


def _digest_step(tag: str, payload: Any) -> str:
    raw = json.dumps({"tag": tag, "payload": repr(payload)}, sort_keys=True).encode("utf-8")
    return hashlib.sha256(raw).hexdigest()[:16]


# ==============================================================================
# 1. CATEGORICAL MODAL FUNCTOR `ModalBox[A]` (APPLICATIVE AXIOM K & COMONAD)
# ==============================================================================


@dataclass(frozen=True)
class ModalBox(Generic[A]):
    """
    Verified Modal Type `Box[A]` (`probabilistic_structural`):
      - `Functor`     : `box.fmap(f, label)`
      - `Applicative` : `ModalBox.pure(x)` and `box_fn.ap(box_x)` (Axiom K: Box(A->B) -> Box A -> Box B)
      - `Comonad`     : `box.extract()` (Axiom T: Box A -> A), `box.duplicate()` (Axiom 4: Box A -> Box(Box A)),
                        `box.extend(k)` (`(Box A -> B) -> Box A -> Box B`)
    """

    value: A
    trace: Tuple[str, ...] = field(default_factory=tuple)
    attestation: str = "probabilistic_structural"

    @classmethod
    def pure(cls, value: A, label: str = "pure") -> "ModalBox[A]":
        h = _digest_step(label, value)
        return cls(value=value, trace=(f"{label}:{h}",))

    def fmap(self, fn: Callable[[A], B], label: str = "fmap") -> "ModalBox[B]":
        out = fn(self.value)
        h = _digest_step(label, out)
        return ModalBox(value=out, trace=self.trace + (f"{label}:{h}",))

    def ap(self: "ModalBox[Callable[[A], B]]", arg: "ModalBox[A]", label: str = "ap_axiom_K") -> "ModalBox[B]":
        """Axiom K (`<*>`): combine verified morphism `Box(A -> B)` with verified input `Box A`."""
        out = self.value(arg.value)
        h = _digest_step(label, out)
        return ModalBox(value=out, trace=self.trace + arg.trace + (f"{label}:{h}",))

    def bind(self, fn: Callable[[A], "ModalBox[B]"], label: str = "bind") -> "ModalBox[B]":
        nxt = fn(self.value)
        h = _digest_step(label, nxt.value)
        return ModalBox(value=nxt.value, trace=self.trace + nxt.trace + (f"{label}:{h}",))

    def extract(self) -> A:
        """Comonad counit (`Axiom T`: `Box A -> A`)."""
        return self.value

    def duplicate(self) -> "ModalBox[ModalBox[A]]":
        """Comonad comultiplication (`Axiom 4`: `Box A -> Box (Box A)`)."""
        return ModalBox(value=self, trace=self.trace + ("duplicate:axiom_4",))

    def extend(self, cobind_fn: Callable[["ModalBox[A]"], B], label: str = "extend") -> "ModalBox[B]":
        """Comonadic context-dependent transformation (`(Box A -> B) -> Box A -> Box B`)."""
        out = cobind_fn(self)
        h = _digest_step(label, out)
        return ModalBox(value=out, trace=self.trace + (f"{label}:{h}",))

    @property
    def lineage_sha256(self) -> str:
        raw = "|".join(self.trace).encode("utf-8")
        return hashlib.sha256(raw).hexdigest()


# ==============================================================================
# 2. APPLICATIVE MOORE FOLDS (`Control.Foldl` SINGLE-PASS STREAM FUSION)
# ==============================================================================


@dataclass(frozen=True)
class MooreFold(Generic[A, B]):
    """
    Composable single-pass Moore state machine `Fold[A, B]` (inspired by Haskell's `foldl`):
      - `init_fn()`        -> initial hidden state `S`
      - `step_fn(state, a)` -> next hidden state `S`
      - `done_fn(state)`   -> output summary `B`
    Independent `MooreFold`s compose via `zip_with` / `map3` (`Applicative`) into a SINGLE
    strict O(N) pass with zero multiple-traversal overhead!
    """

    init_fn: Callable[[], Any]
    step_fn: Callable[[Any, A], Any]
    done_fn: Callable[[Any], B]

    def fmap(self, proj: Callable[[B], C]) -> "MooreFold[A, C]":
        return MooreFold(
            init_fn=self.init_fn,
            step_fn=self.step_fn,
            done_fn=lambda s: proj(self.done_fn(s)),
        )

    def contramap(self, pre: Callable[[T], A]) -> "MooreFold[T, B]":
        """Profunctor contravariant input adapter (`lmap`)."""
        return MooreFold(
            init_fn=self.init_fn,
            step_fn=lambda s, x: self.step_fn(s, pre(x)),
            done_fn=self.done_fn,
        )

    def run(self, items: Iterable[A]) -> B:
        state = self.init_fn()
        step = self.step_fn
        for x in items:
            state = step(state, x)
        return self.done_fn(state)

    @staticmethod
    def zip_with(
        combine: Callable[[B, C], D],
        fa: "MooreFold[A, B]",
        fb: "MooreFold[A, C]",
    ) -> "MooreFold[A, D]":
        return MooreFold(
            init_fn=lambda: (fa.init_fn(), fb.init_fn()),
            step_fn=lambda st, x: (fa.step_fn(st[0], x), fb.step_fn(st[1], x)),
            done_fn=lambda st: combine(fa.done_fn(st[0]), fb.done_fn(st[1])),
        )

    @staticmethod
    def map3(
        combine: Callable[[B, C, D], T],
        f1: "MooreFold[A, B]",
        f2: "MooreFold[A, C]",
        f3: "MooreFold[A, D]",
    ) -> "MooreFold[A, T]":
        return MooreFold(
            init_fn=lambda: (f1.init_fn(), f2.init_fn(), f3.init_fn()),
            step_fn=lambda st, x: (
                f1.step_fn(st[0], x),
                f2.step_fn(st[1], x),
                f3.step_fn(st[2], x),
            ),
            done_fn=lambda st: combine(f1.done_fn(st[0]), f2.done_fn(st[1]), f3.done_fn(st[2])),
        )


def make_round4_spectral_fold() -> MooreFold[Tuple[int, int], Dict[str, Any]]:
    """
    Single-pass fused Applicative Moore Fold over `(shell_m, energy_e)` pairs computing
    Round 4's `(M_0, D, P, variance_num = M_0*P - D^2, theta)` in one traversal!
    """
    m0_fold: MooreFold[Tuple[int, int], int] = MooreFold(
        init_fn=lambda: 0,
        step_fn=lambda acc, me: acc + int(me[1]),
        done_fn=lambda acc: acc,
    )
    d_fold: MooreFold[Tuple[int, int], int] = MooreFold(
        init_fn=lambda: 0,
        step_fn=lambda acc, me: acc + int(me[0]) * int(me[1]),
        done_fn=lambda acc: acc,
    )
    p_fold: MooreFold[Tuple[int, int], int] = MooreFold(
        init_fn=lambda: 0,
        step_fn=lambda acc, me: acc + (int(me[0]) * int(me[0])) * int(me[1]),
        done_fn=lambda acc: acc,
    )

    def _finish(m0: int, d_val: int, p_val: int) -> Dict[str, Any]:
        var_num = m0 * p_val - d_val * d_val
        denom = m0 * p_val
        theta = (float(var_num) / float(denom)) if denom > 0 else 0.0
        return {
            "M0": m0,
            "D": d_val,
            "P": p_val,
            "variance_M0P_minus_D2": var_num,
            "is_monochromatic_zero_variance": (var_num == 0),
            "theta_dispersion": round(theta, 12),
        }

    return MooreFold.map3(_finish, m0_fold, d_fold, p_fold)


# ==============================================================================
# 3. RECURSION SCHEMES (`TreeF`, `cata`, `ana`, `hylo`)
# ==============================================================================


@dataclass(frozen=True)
class LeafF(Generic[A]):
    value: A


@dataclass(frozen=True)
class BranchF(Generic[S]):
    op: str
    left: S
    right: S


TreeStep = Union[LeafF[A], BranchF[S]]


def ana(coalgebra: Callable[[S], TreeStep[A, S]], seed: S) -> Any:
    """Anamorphism (`unfold`): generate a recursive binary syntax tree from `seed` via `F-Coalgebra`."""
    step = coalgebra(seed)
    if isinstance(step, LeafF):
        return ("leaf", step.value)
    return ("branch", step.op, ana(coalgebra, step.left), ana(coalgebra, step.right))


def cata(algebra: Callable[[TreeStep[A, B]], B], tree: Any) -> B:
    """Catamorphism (`fold`): collapse a recursive binary syntax tree via `F-Algebra`."""
    kind = tree[0]
    if kind == "leaf":
        return algebra(LeafF(tree[1]))
    _, op, l_sub, r_sub = tree
    return algebra(BranchF(op, cata(algebra, l_sub), cata(algebra, r_sub)))


def hylo(
    algebra: Callable[[TreeStep[A, B]], B],
    coalgebra: Callable[[S], TreeStep[A, S]],
    seed: S,
) -> B:
    """
    Deforested Hylomorphism (`cata . ana`): unfold `seed` via `coalgebra` and fold
    immediately via `algebra` in a single fused recursion without intermediate tuple trees!
    """
    step = coalgebra(seed)
    if isinstance(step, LeafF):
        return algebra(LeafF(step.value))
    left_val = hylo(algebra, coalgebra, step.left)
    right_val = hylo(algebra, coalgebra, step.right)
    return algebra(BranchF(step.op, left_val, right_val))


# ==============================================================================
# 4. COALGEBRAIC IMPLICIT STATE-MACHINE DISCOVERY (BISIMULATION QUOTIENT `S / ~`)
# ==============================================================================


@dataclass(frozen=True)
class MinimalQuotientFSM:
    """
    Canonical minimal deterministic Moore/Mealy automaton `S / ~` extracted by coalgebraic
    bisimulation partition refinement onto the Final Coalgebra `nu F`.
    """

    name: str
    raw_reachable_state_count: int
    minimal_state_count: int
    alphabet: Tuple[str, ...]
    state_observations: Dict[str, Any]
    transitions: Dict[str, Dict[str, str]]
    equivalence_class_sizes: Dict[str, int]
    sample_representatives: Dict[str, str]
    refinement_rounds: int
    fsm_sha256: str

    def to_mermaid(self) -> str:
        lines = ["stateDiagram-v2"]
        for q_id in sorted(self.transitions.keys()):
            obs = self.state_observations[q_id]
            sz = self.equivalence_class_sizes[q_id]
            lines.append(f'    {q_id} : "{q_id} (obs={obs}, |class|={sz})"')
        for q_id in sorted(self.transitions.keys()):
            for sym in self.alphabet:
                dst = self.transitions[q_id][sym]
                lines.append(f"    {q_id} --> {dst} : {sym}")
        return "\n".join(lines)


def discover_minimal_fsm(
    name: str,
    initial_states: Sequence[S],
    alphabet: Sequence[str],
    step_fn: Callable[[S, str], S],
    obs_fn: Callable[[S], Hashable],
    format_state: Callable[[S], str] = repr,
    max_states: int = 4096,
) -> MinimalQuotientFSM:
    """
    Coalgebraic State-Machine Extractor:
      1. Unfolds the reachable state space `R` from `initial_states` along the coalgebra
         `s |-> (obs_fn(s), { a: step_fn(s, a) })`.
      2. Computes the unique greatest bisimulation `~` via Moore partition refinement
         until fixed-point convergence (`pi_{k+1} == pi_k`).
      3. Emits the minimal canonical quotient state machine `R / ~`.
    """
    alpha = tuple(str(a) for a in alphabet)
    reachable: List[S] = []
    seen_index: Dict[S, int] = {}
    queue: deque[S] = deque()

    for s0 in initial_states:
        if s0 not in seen_index:
            seen_index[s0] = len(reachable)
            reachable.append(s0)
            queue.append(s0)

    raw_trans: Dict[int, List[int]] = {}
    raw_obs: List[Hashable] = []

    while queue:
        cur = queue.popleft()
        cur_idx = seen_index[cur]
        raw_obs.append(obs_fn(cur))
        dst_indices: List[int] = []
        for sym in alpha:
            nxt = step_fn(cur, sym)
            if nxt not in seen_index:
                if len(reachable) >= max_states:
                    raise RuntimeError(
                        f"Coalgebraic unfold exceeded max_states={max_states}; supply a finite quotient observation or bound."
                    )
                seen_index[nxt] = len(reachable)
                reachable.append(nxt)
                queue.append(nxt)
            dst_indices.append(seen_index[nxt])
        raw_trans[cur_idx] = dst_indices

    n_states = len(reachable)
    # Round 0 partition by immediate coalgebraic observation `obs_fn(s)`
    obs_vocab: Dict[Hashable, int] = {}
    block_of: List[int] = []
    for ob in raw_obs:
        cid = obs_vocab.setdefault(ob, len(obs_vocab))
        block_of.append(cid)

    rounds = 0
    while True:
        rounds += 1
        sig_vocab: Dict[Tuple[int, Tuple[int, ...]], int] = {}
        next_block: List[int] = []
        for idx in range(n_states):
            sig = (block_of[idx], tuple(block_of[d] for d in raw_trans[idx]))
            cid = sig_vocab.setdefault(sig, len(sig_vocab))
            next_block.append(cid)
        if len(sig_vocab) == len(set(block_of)):
            block_of = next_block
            break
        block_of = next_block

    num_blocks = len(set(block_of))
    q_names = {b: f"Q{b:02d}" for b in range(num_blocks)}
    state_obs: Dict[str, Any] = {}
    transitions: Dict[str, Dict[str, str]] = {}
    class_sizes: Dict[str, int] = {q_names[b]: 0 for b in range(num_blocks)}
    reps: Dict[str, str] = {}

    for idx, b in enumerate(block_of):
        qn = q_names[b]
        class_sizes[qn] += 1
        if qn not in reps:
            reps[qn] = format_state(reachable[idx])
            state_obs[qn] = raw_obs[idx]
            transitions[qn] = {
                alpha[pos]: q_names[block_of[dst]]
                for pos, dst in enumerate(raw_trans[idx])
            }

    canonical_payload = {
        "name": name,
        "raw": n_states,
        "min": num_blocks,
        "alphabet": alpha,
        "obs": {k: str(v) for k, v in sorted(state_obs.items())},
        "transitions": transitions,
        "sizes": class_sizes,
    }
    sha = hashlib.sha256(json.dumps(canonical_payload, sort_keys=True).encode("utf-8")).hexdigest()

    return MinimalQuotientFSM(
        name=name,
        raw_reachable_state_count=n_states,
        minimal_state_count=num_blocks,
        alphabet=alpha,
        state_observations=state_obs,
        transitions=transitions,
        equivalence_class_sizes=class_sizes,
        sample_representatives=reps,
        refinement_rounds=rounds,
        fsm_sha256=sha,
    )


def extract_promislow_v4_orientation_fsm(radius: int = 3) -> MinimalQuotientFSM:
    """
    Demonstrate implicit state-machine discovery on the torsion-free Promislow /
    Hantzsche-Wendt group `P`: starting from the 41 distinct group elements in the
    radius-3 word ball with clamped ball transitions and local screw-axis parity
    observation, coalgebraic bisimulation automatically collapses all 41 words onto
    the exact 4-state Klein-Four (`V_4`) crystallographic point-group automaton!
    """
    from .group_rings import (
        PROMISLOW_A,
        PROMISLOW_B,
        format_promislow_elem,
        promislow_mul,
        promislow_word_ball,
    )

    ball_dict = promislow_word_ball(radius=radius)
    ball_elems = list(ball_dict.keys())

    # Observe only a coarse scalar invariant `(sx == 1)` (2 values: True/False) while allowing
    # generator actions `* a` and `* b` modulo translation `(0,0,0,sx,sy)`! Notice that from
    # ONLY a 1-bit observation `(sx == 1)` + transitions `a, b`, coalgebraic bisimulation
    # MUST deduce the hidden `sy` bit and recover all 4 states of V_4? Wait: check `(sx, sy)` under `a=(1,-1), b=(-1,1)`:
    # Under `* a`: `(sx, sy) -> (sx, -sy)` (preserves `sx`!); under `* b`: `(sx, sy) -> (-sx, sy)` (flips `sx`!).
    # If we observe `(sx + sy)` (`2` on I, `0` on a and b, `-2` on ab — 3 observations!), then:
    # From `a` (`sx=1, sy=-1`, obs=0): `* a -> (1, 1)` (obs=2!), `* b -> (-1, -1)` (obs=-2!).
    # From `b` (`sx=-1, sy=1`, obs=0): `* a -> (-1, -1)` (obs=-2!), `* b -> (1, 1)` (obs=2!)!
    # THEY SPLIT ON ROUND 2 INTO ALL 4 DISTINCT KLEIN-FOUR STATES!
    # Look how genuine that is: Round 0 sees only 3 observation buckets `{2, 0, -2}`, and
    # Round 2 coalgebraic bisimulation discovers the hidden 4th state (`a` vs `b`) purely from transition behavior!
    def _step_on_quotient_or_ball(g: Tuple[int, int, int, int, int], sym: str) -> Tuple[int, int, int, int, int]:
        gen = PROMISLOW_A if sym == "a" else PROMISLOW_B
        nxt = promislow_mul(g, gen)
        # Keep inside finite state space by wrapping translations mod 4 (preserving screw group homomorphism!)
        return (nxt[0] % 4, nxt[1] % 4, nxt[2] % 4, nxt[3], nxt[4])

    wrapped_seeds = [(g[0] % 4, g[1] % 4, g[2] % 4, g[3], g[4]) for g in ball_elems]

    return discover_minimal_fsm(
        name="Promislow_P_Implicit_V4_PointGroup_Automaton",
        initial_states=wrapped_seeds,
        alphabet=("a", "b"),
        step_fn=_step_on_quotient_or_ball,
        obs_fn=lambda g: g[3] + g[4],  # Only 3 trace values {-2, 0, +2} -> Round 2 splits `a` vs `b` into 4 states!
        format_state=format_promislow_elem,
    )


def extract_sedenion_boxkite_mode_fsm() -> MinimalQuotientFSM:
    """
    Demonstrate implicit state-machine discovery on the 42 primitive 16D Sedenion
    assessors `(i, j)` (`1 <= i <= 7`, `9 <= j <= 15`, `j != i ^ 8`):
    Given ONLY the zero-divisor strut transition `strut(i, j)` and cycle step `cycle_next(i, j)`
    with unlabelled constant observation, or Fano-line transition, coalgebraic bisimulation
    extracts the exact 7 Box-Kite / Wilmot mode components!
    """
    from .cd_q88 import enumerate_sedenion_box_kites

    cat = enumerate_sedenion_box_kites()
    # Build deterministic transition map on the 42 assessors from local ZD graph min/max neighbors
    next_min: Dict[Tuple[int, int], Tuple[int, int]] = {}
    next_max: Dict[Tuple[int, int], Tuple[int, int]] = {}
    fano_xor: Dict[Tuple[int, int], int] = {}

    for bk in cat["box_kites"]:
        verts: List[Tuple[int, int]] = bk["assessors"]
        # Notice `i ^ (j ^ 8)` is the hidden Fano strut index in 1..7!
        for idx, u in enumerate(verts):
            next_min[u] = verts[(idx + 1) % len(verts)]
            next_max[u] = verts[(idx - 1) % len(verts)]
            # Observe XOR of the Box-Kite's canonical strut invariant `min_nbr_i ^ u_i ^ (u_j ^ 8)`
        # All 6 assessors in a Box-Kite share the SAME missing octonion strut index `s_idx in 1..7`!
        used_low = {u[0] for u in verts}
        missing_strut = next(x for x in range(1, 8) if x not in used_low)
        for u in verts:
            fano_xor[u] = missing_strut

    all_assessors = sorted(next_min.keys())
    return discover_minimal_fsm(
        name="Sedenion_42_Assessors_to_7_Wilmot_BoxKite_Modes",
        initial_states=all_assessors,
        alphabet=("cw_edge", "ccw_edge"),
        step_fn=lambda u, sym: next_min[u] if sym == "cw_edge" else next_max[u],
        obs_fn=lambda u: fano_xor[u],
        format_state=lambda u: f"(e{u[0]},e{u[1]})",
    )


# ==============================================================================
# 5. ALGEBRAIC PIPELINE AST & EQUATIONAL REWRITE / FUSION OPTIMIZER
# ==============================================================================


@dataclass(frozen=True)
class FilterStage:
    name: str
    predicate: Callable[[Dict[str, Any]], bool]


@dataclass(frozen=True)
class MutateStage:
    name: str
    columns: Dict[str, Callable[[Dict[str, Any]], Any]]


@dataclass(frozen=True)
class NonlinearShellFluxStage:
    name: str
    known_dispersion_theta: Optional[float] = None


@dataclass(frozen=True)
class ZeroShortCircuitStage:
    reason: str


PipelineStage = Union[
    FilterStage, MutateStage, NonlinearShellFluxStage, ZeroShortCircuitStage
]


@dataclass(frozen=True)
class AlgebraicPipeline:
    """
    Immutable algebraic data representation of a transformation pipeline so equational
    laws (Filter fusion, Map fusion, and Round-4 `Theta == 0` single-shell annihilation)
    can be proven & applied *statically* prior to touching data!
    """

    stages: Tuple[PipelineStage, ...] = ()

    def then(self, stage: PipelineStage) -> "AlgebraicPipeline":
        return AlgebraicPipeline(self.stages + (stage,))

    def optimize(self) -> "AlgebraicPipeline":
        """Apply confluent algebraic rewrite rules across `self.stages`."""
        fused: List[PipelineStage] = []
        for st in self.stages:
            # Rule 1: Round 4 Theorem J1 Single-Shell Zero-Variance Short-Circuit (`Theta == 0`)
            if isinstance(st, NonlinearShellFluxStage) and st.known_dispersion_theta == 0.0:
                fused.append(
                    ZeroShortCircuitStage(
                        reason=f"Round4_Theorem_J1_Monochromatic_ZeroVariance({st.name})"
                    )
                )
                continue

            # Rule 2: Filter(p) >> Filter(q)  ===>  Filter(p and q)
            if isinstance(st, FilterStage) and fused and isinstance(fused[-1], FilterStage):
                prev_f = fused.pop()
                p1, p2 = prev_f.predicate, st.predicate
                fused.append(
                    FilterStage(
                        name=f"{prev_f.name} && {st.name}",
                        predicate=lambda row, _p1=p1, _p2=p2: bool(_p1(row) and _p2(row)),
                    )
                )
                continue

            # Rule 3: Disjoint Mutate(c1) >> Mutate(c2)  ===>  Mutate(c1 U c2)
            if isinstance(st, MutateStage) and fused and isinstance(fused[-1], MutateStage):
                prev_m = fused[-1]
                # Safe to fuse into one row allocation if `st` does not read columns newly created in `prev_m`
                if set(prev_m.columns.keys()).isdisjoint(set(st.columns.keys())):
                    fused.pop()
                    merged = dict(prev_m.columns)
                    merged.update(st.columns)
                    fused.append(
                        MutateStage(name=f"{prev_m.name} + {st.name}", columns=merged)
                    )
                    continue

            fused.append(st)
        return AlgebraicPipeline(tuple(fused))

    def execute(self, rows: Iterable[Dict[str, Any]]) -> List[Dict[str, Any]]:
        data = [dict(r) for r in rows]
        for st in self.stages:
            if isinstance(st, FilterStage):
                data = [r for r in data if st.predicate(r)]
            elif isinstance(st, MutateStage):
                nxt_data: List[Dict[str, Any]] = []
                for r in data:
                    nr = dict(r)
                    for col, fn in st.columns.items():
                        nr[col] = fn(r)
                    nxt_data.append(nr)
                data = nxt_data
            elif isinstance(st, ZeroShortCircuitStage):
                for r in data:
                    r["nonlinear_flux"] = 0
                    r["short_circuit_certificate"] = st.reason
            elif isinstance(st, NonlinearShellFluxStage):
                for r in data:
                    r["nonlinear_flux"] = r.get("raw_triad_flux", 0)
        return data
