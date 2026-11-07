#!/usr/bin/env python3
"""
REGION-TYPED BUMP ARENAS & RANK-2 ESCAPE VERIFIER (`bsar.arenas`)
License: GNU AGPLv3
Attestation: probabilistic_structural
Dependencies: 0 (Python >= 3.10 Standard Library Only)

Implements `arena-design-note.md` ("Memory is the second implicit machine"):
  1. Bump Allocation Only (`O(1)` alloc, `O(1)` scope-exit cursor bulldoze, zero `free()`).
  2. Rank-2 (`runST`-style) Escape Rule:
     - Every `with_arena(...)` mints a fresh unforgeable `RegionToken` at lexical nesting `depth >= 1`.
     - Returning a `RegionPtr` from `with_arena`, storing an inner-arena pointer into an outer
       arena (`dst.depth < src.depth`) or `PersistentStorage` (`depth == 0`), or leaving a
       register (`X`, `Y`, `DP`) tainted with the dying region's token raises `IxArenaEscapeError`!
  3. SNES `65c816` & `SA-1` Hardware Geography (`smw_sa1_brutal_vivian.md`):
     - `WRAM_7E_FRAME` (`$7E:2000`, bulldozed at VBlank; S-CPU only — Open Bus on SA-1!),
     - `WRAM_7F_ROOM` (`$7F:0000`, bulldozed on room/level exit; S-CPU only!),
     - `SA1_IRAM_3000` (`$00:3000`, `2 KB` NMI-immune SA-1 scratch),
     - `SA1_BWRAM_40` (`$40:C000` / `$40:0000`, SA-1 & S-CPU shared BW-RAM),
     - `INTERRUPT_MINI` (`$7E:0100`, isolated NMI/IRQ scratch — cannot touch foreground arenas!),
     - `PERSISTENT_SRAM_41C000` (`$41:C000`, quarantined Save RAM — never arena-allocated!).
  4. DMA Alignment & Bank-Boundary Proofs:
     - Tracks exact modular alignment (`1, 2, 4, 16, 256`) and verifies zero `64 KB` bank straddling
       at compile time, minting `RegionPtr` witnesses directly consumable by `bsar.dma_sessions`.
"""

from __future__ import annotations

from dataclasses import dataclass, field
from enum import Enum
import itertools
from typing import Any, Callable, Dict, List, Mapping, Optional, Set, Tuple, TypeVar

T = TypeVar("T")


class IxArenaError(TypeError):
    """Base static verification error for Region-Typed Arenas."""


class IxArenaEscapeError(IxArenaError):
    """Raised when a `RegionPtr` escapes its region via return value, outer store, SRAM, or live register."""


class IxArenaExhaustionError(IxArenaError):
    """Raised when static bump allocations exceed the arena's byte capacity or cross a 64KB bank."""


class IxBusIsolationError(IxArenaError):
    """Raised when SA-1 attempts to touch S-CPU WRAM ($7E/$7F Open Bus) or NMI touches foreground arenas."""


@dataclass(frozen=True)
class AddressSpaceSpec:
    name: str
    bank: int
    base_offset: int
    max_capacity: int
    allowed_cpus: Tuple[str, ...]        # ("SCPU",) | ("SA1",) | ("SCPU", "SA1") | ("NMI",)
    is_arena_eligible: bool = True
    is_interrupt_reserved: bool = False
    description: str = ""


class AddressSpace(Enum):
    WRAM_7E_FRAME = AddressSpaceSpec(
        name="WRAM_7E_FRAME",
        bank=0x7E,
        base_offset=0x2000,
        max_capacity=0x6000,  # 24 KB frame scratch in Bank $7E
        allowed_cpus=("SCPU",),
        description="Per-frame WRAM arena bulldozed at VBlank (S-CPU only; Open Bus on SA-1)",
    )
    WRAM_7F_ROOM = AddressSpaceSpec(
        name="WRAM_7F_ROOM",
        bank=0x7F,
        base_offset=0x0000,
        max_capacity=0x10000,  # 64 KB room/level arena in Bank $7F
        allowed_cpus=("SCPU",),
        description="Per-room/level WRAM arena bulldozed on level exit (S-CPU only)",
    )
    SA1_IRAM_3000 = AddressSpaceSpec(
        name="SA1_IRAM_3000",
        bank=0x00,
        base_offset=0x3000,
        max_capacity=0x0800,  # 2 KB SA-1 internal I-RAM
        allowed_cpus=("SA1", "SCPU"),
        description="SA-1 10.74 MHz I-RAM arena (100% immune to S-CPU NMI DP clobbers)",
    )
    SA1_BWRAM_40 = AddressSpaceSpec(
        name="SA1_BWRAM_40",
        bank=0x40,
        base_offset=0xC000,
        max_capacity=0x0800,  # $40:C000-$40:C7FF safe BW-RAM scratch
        allowed_cpus=("SA1", "SCPU"),
        description="SA-1 Virtual BW-RAM safe region ($40:C000-$40:C7FF)",
    )
    INTERRUPT_MINI = AddressSpaceSpec(
        name="INTERRUPT_MINI",
        bank=0x7E,
        base_offset=0x0100,
        max_capacity=0x0080,  # 128-byte dedicated NMI/IRQ mini-arena
        allowed_cpus=("NMI",),
        is_interrupt_reserved=True,
        description="Dedicated NMI/IRQ mini-arena isolated from foreground scopes",
    )
    PERSISTENT_SRAM_41C000 = AddressSpaceSpec(
        name="PERSISTENT_SRAM_41C000",
        bank=0x41,
        base_offset=0xC000,
        max_capacity=0x0800,  # $41:C000-$41:C7FF Save RAM
        allowed_cpus=("SCPU", "SA1"),
        is_arena_eligible=False,
        description="Quarantined Save RAM ($41:C000-$41:C7FF) — persistent data ONLY, never an arena",
    )


_REGION_COUNTER = itertools.count(1)


@dataclass(frozen=True)
class RegionToken:
    """
    Unforgeable Rank-2 (`runST`-style) region identity minted inside `with_arena`.
    `depth == 0` is reserved exclusively for static/persistent non-arena memory.
    """

    uid: int
    label: str
    depth: int
    space: AddressSpace


@dataclass(frozen=True)
class RegionPtr:
    """
    Typed pointer bound to a specific `RegionToken` (`ρ`), carrying compile-time
    alignment (`align`) and non-bank-crossing (`bank_safe=True`) witnesses.
    """

    region: RegionToken
    bank: int
    offset: int
    size: int
    align: int
    label: str
    bank_safe: bool = True

    @property
    def long_addr(self) -> int:
        return ((self.bank & 0xFF) << 16) | (self.offset & 0xFFFF)

    def format_snes_addr(self) -> str:
        return f"${self.bank:02X}:{self.offset:04X}"


@dataclass
class PersistentSlot:
    """
    Quarantined persistent/global storage slot (`depth == 0`, e.g. SRAM `$41:C000`).
    Enforces the Escape Rule: storing ANY `RegionPtr` (`depth >= 1`) here is a static error!
    """

    label: str
    space: AddressSpace = AddressSpace.PERSISTENT_SRAM_41C000
    stored_value: Any = None

    def store(self, value: Any) -> None:
        escaped = _find_any_region_ptrs(value, min_depth=1)
        if escaped:
            ptr = escaped[0]
            raise IxArenaEscapeError(
                f"Arena Escape Prevented (`{self.label}` in `{self.space.value.name}`): "
                f"Cannot store pointer `{ptr.label}` ({ptr.format_snes_addr()}) from scoped arena "
                f"`{ptr.region.label}` (depth={ptr.region.depth}) into persistent storage (depth=0)!"
            )
        self.stored_value = value


def _find_any_region_ptrs(obj: Any, min_depth: int = 1, SpecificUid: Optional[int] = None) -> List[RegionPtr]:
    """Recursively scan return values or stored payloads for escaping `RegionPtr`s."""
    found: List[RegionPtr] = []
    visited: Set[int] = set()

    def _walk(x: Any) -> None:
        oid = id(x)
        if oid in visited:
            return
        visited.add(oid)
        if isinstance(x, RegionPtr):
            if x.region.depth >= min_depth and (SpecificUid is None or x.region.uid == SpecificUid):
                found.append(x)
            return
        if isinstance(x, Mapping):
            for k, v in x.items():
                _walk(k)
                _walk(v)
        elif isinstance(x, (list, tuple, set, frozenset)):
            for item in x:
                _walk(item)
        elif hasattr(x, "__dict__"):
            for v in vars(x).values():
                _walk(v)

    _walk(obj)
    return found


class ArenaScope:
    """
    Live scoped bump-allocator (`arena r in <space, capacity>`).
    Supports:
      - Bump-only static & checked dynamic allocations,
      - Compile-time alignment padding (`1, 2, 4, 16, 256` bytes) for DMA safety,
      - Directional nested arena reference rules (`inner` may read `outer`; `outer` may NOT store `inner`),
      - Linear/tainted register handshake (`bind_register` / `clear_register`),
      - Zero-GC cursor checkpoint/restore for Verse `<transacts>`,
      - Asar `65c816` assembly emission for `O(1)` bump and `O(1)` VBlank/exit bulldoze.
    """

    def __init__(
        self,
        token: RegionToken,
        capacity: int,
        cpu_context: str,
        active_stack: Tuple[RegionToken, ...],
    ) -> None:
        spec = token.space.value
        if not spec.is_arena_eligible:
            raise IxArenaError(
                f"Space `{spec.name}` (`${spec.bank:02X}:{spec.base_offset:04X}`) is persistent/quarantined "
                f"and may NEVER be used as a bump arena!"
            )
        if cpu_context not in spec.allowed_cpus:
            raise IxBusIsolationError(
                f"Hardware Bus Isolation Error: CPU context `{cpu_context}` cannot access `{spec.name}` "
                f"(allowed={spec.allowed_cpus}). Prevents SA-1 WRAM Open-Bus `$FF` & NMI DP corruption!"
            )
        if capacity <= 0 or capacity > spec.max_capacity:
            raise IxArenaExhaustionError(
                f"Arena `{token.label}` requested capacity `{capacity}B` exceeds `{spec.name}` maximum `{spec.max_capacity}B`."
            )
        if spec.base_offset + capacity > 0x10000:
            raise IxArenaExhaustionError(
                f"Bank-Boundary Error: Arena `{token.label}` at `${spec.bank:02X}:{spec.base_offset:04X}` "
                f"+ `{capacity}B` crosses 64KB bank boundary (`$10000`)!"
            )

        self.token = token
        self.capacity = capacity
        self.cpu_context = cpu_context
        self._active_stack = active_stack
        self._cursor = 0
        self._peak_watermark = 0
        self._is_alive = True
        self._alloc_log: List[RegionPtr] = []
        self._stored_refs: List[Tuple[str, RegionPtr]] = []
        self._register_taints: Dict[str, RegionToken] = {}
        self._asm_lines: List[str] = [
            f"; --- Enter Arena `{token.label}` ({spec.name} ${spec.bank:02X}:{spec.base_offset:04X}, cap={capacity}B, depth={token.depth}) ---"
        ]

    @property
    def cursor(self) -> int:
        return self._cursor

    @property
    def peak_watermark(self) -> int:
        return self._peak_watermark

    @property
    def remaining_bytes(self) -> int:
        return self.capacity - self._cursor

    def _assert_live(self, action: str) -> None:
        if not self._is_alive:
            raise IxArenaEscapeError(
                f"Use-After-Scope-Exit Prevented: Attempted `{action}` on dead arena `{self.token.label}`!"
            )

    def alloc(self, size: int, align: int = 2, label: str = "buf") -> RegionPtr:
        """
        Bump-allocate `size` bytes with compile-time alignment `align` (`1, 2, 4, 16, 256`).
        Zero `free()` exists; static exhaustion or bank-crossing fails immediately!
        """
        self._assert_live(f"alloc({label})")
        if size <= 0:
            raise ValueError(f"Allocation size must be > 0, got {size}")
        if align not in (1, 2, 4, 8, 16, 32, 64, 128, 256):
            raise ValueError(f"Unsupported alignment `{align}`; expected power of 2 in 1..256")

        spec = self.token.space.value
        abs_cur = spec.base_offset + self._cursor
        rem = abs_cur % align
        pad = 0 if rem == 0 else (align - rem)
        new_cursor = self._cursor + pad + size

        if new_cursor > self.capacity:
            raise IxArenaExhaustionError(
                f"Static Arena Exhaustion in `{self.token.label}` (`{spec.name}`): "
                f"allocating `{label}` ({size}B + {pad}B align pad) advances cursor to `{new_cursor}B`, "
                f"exceeding capacity `{self.capacity}B`!"
            )

        alloc_offset = spec.base_offset + self._cursor + pad
        if alloc_offset + size > 0x10000:
            raise IxArenaExhaustionError(
                f"65c816 Bank-Straddle Prevented: `{label}` at `${spec.bank:02X}:{alloc_offset:04X}` "
                f"({size}B) straddles bank `${spec.bank:02X}` boundary!"
            )

        self._cursor = new_cursor
        if self._cursor > self._peak_watermark:
            self._peak_watermark = self._cursor

        ptr = RegionPtr(
            region=self.token,
            bank=spec.bank,
            offset=alloc_offset,
            size=size,
            align=align,
            label=label,
            bank_safe=True,
        )
        self._alloc_log.append(ptr)
        self._asm_lines.append(
            f"    ; bump `{label}` -> {ptr.format_snes_addr()} ({size}B, align={align}B, cursor={self._cursor}/{self.capacity}B)"
        )
        return ptr

    def alloc_checked_dynamic(self, count_reg_expr: str, elem_size: int, trap_label: str) -> str:
        """
        Emit checked runtime trap (`arena-design-note` Q1 v1 fallback for dynamic counts):
        transitions to explicit sum-type exhaustion handler `trap_label` instead of corrupting RAM!
        """
        self._assert_live("alloc_checked_dynamic")
        rem = self.remaining_bytes
        asm = (
            f"    ; Checked dynamic bump guard (remaining={rem}B, elem={elem_size}B)\n"
            f"    LDA {count_reg_expr}\n"
            f"    CMP #${rem // max(1, elem_size):04X}\n"
            f"    BCS {trap_label}          ; Refusal-at-posting -> sum-type Exhausted variant"
        )
        self._asm_lines.append(asm)
        return asm

    def deref_check(self, ptr: RegionPtr) -> None:
        """
        Regions are machine states: a `RegionPtr` is ONLY usable while its `RegionToken`
        is in the active live region stack AND matches legal CPU/Interrupt rules!
        """
        self._assert_live("deref_check")
        if self.cpu_context == "NMI" and not ptr.region.space.value.is_interrupt_reserved:
            raise IxBusIsolationError(
                f"Interrupt Arena Violation: NMI handler in `{self.token.label}` attempted to access "
                f"foreground pointer `{ptr.label}` in `{ptr.region.label}`!"
            )
        if ptr.region not in self._active_stack:
            raise IxArenaEscapeError(
                f"Stale / Dead Region Dereference Prevented: Pointer `{ptr.label}` belongs to region "
                f"`{ptr.region.label}` which is NOT live in current scope {[t.label for t in self._active_stack]}!"
            )

    def store_ref(self, slot_name: str, target_ptr: RegionPtr) -> None:
        """
        Store a reference `target_ptr` inside THIS arena (`self`).
        Directional Nesting Rule:
          - An inner arena (`self.depth == 2`) MAY store a pointer to an outer arena (`target.depth == 1`).
          - An outer arena (`self.depth == 1`) MAY NOT store a pointer to an inner arena (`target.depth == 2`),
            because `self` outlives `target_ptr`!
        """
        self._assert_live(f"store_ref({slot_name})")
        self.deref_check(target_ptr)
        if target_ptr.region.depth > self.token.depth:
            raise IxArenaEscapeError(
                f"Directional Nesting Escape Prevented: Longer-lived outer arena `{self.token.label}` "
                f"(depth={self.token.depth}) cannot store reference `{slot_name}` pointing into "
                f"shorter-lived inner arena `{target_ptr.region.label}` (depth={target_ptr.region.depth})!"
            )
        self._stored_refs.append((slot_name, target_ptr))

    def bind_register(self, reg_name: str, ptr: RegionPtr) -> None:
        """
        Linear Register Handshake (`arena-design-note` Q3):
        Loading a `RegionPtr` into `X`, `Y`, or `DP` taints that register with `ptr.region`.
        Must be cleared/consumed before `ptr.region` exits!
        """
        self._assert_live(f"bind_register({reg_name})")
        self.deref_check(ptr)
        self._register_taints[reg_name] = ptr.region
        self._asm_lines.append(f"    LDX #${ptr.offset:04X}          ; {reg_name} tainted by region `{ptr.region.label}`")

    def clear_register(self, reg_name: str) -> None:
        """Consume / clear a region-tainted hardware register prior to scope exit."""
        self._register_taints.pop(reg_name, None)
        self._asm_lines.append(f"    LDX #$0000               ; {reg_name} region taint cleared")

    # --- Hooks used by Phase 4 Zero-GC Verse `<transacts>` ---
    def _checkpoint_cursor(self) -> Tuple[int, int]:
        self._assert_live("_checkpoint_cursor")
        return (self._cursor, len(self._alloc_log))

    def _rollback_cursor(self, snap: Tuple[int, int]) -> None:
        saved_cursor, saved_len = snap
        self._cursor = saved_cursor
        del self._alloc_log[saved_len:]
        self._asm_lines.append(
            f"    ; <transacts> guard failed -> O(1) rollback cursor to {saved_cursor}B"
        )

    def _close_and_bulldoze(self) -> str:
        """Reclaim entire region in `O(1)` (`LDA #$0000 : STA !arena_cursor`) and check register taints."""
        for reg, tok in self._register_taints.items():
            if tok.uid == self.token.uid:
                raise IxArenaEscapeError(
                    f"Register Escape Prevented at Scope Exit of `{self.token.label}`: "
                    f"Hardware register `{reg}` still holds a live pointer into dying region `{self.token.label}`! "
                    f"Call `arena.clear_register('{reg}')` or consume it before scope exit."
                )
        spec = self.token.space.value
        self._cursor = 0
        self._is_alive = False
        self._asm_lines.append(
            f"    LDA #$0000 : STA !ArenaCursor_{self.token.label} ; O(1) VBlank/Exit bulldoze ({spec.name})"
        )
        return "\n".join(self._asm_lines)


_ACTIVE_ARENA_STACK: List[ArenaScope] = []


def with_arena(
    label: str,
    space: AddressSpace,
    capacity: int,
    body: Callable[[ArenaScope], T],
    cpu_context: str = "SCPU",
) -> Tuple[T, Dict[str, Any]]:
    """
    Rank-2 Scoped Region Construct (`arena r in <space, capacity>: ...`):
      1. Mints a fresh `RegionToken` at `depth = len(_ACTIVE_ARENA_STACK) + 1` (or `depth = 1` for NMI).
      2. Enforces interrupt isolation (foreground arenas are invisible inside `cpu_context == 'NMI'`).
      3. Runs `body(arena_scope)`.
      4. Verifies that NO `RegionPtr` tied to `token` escapes in the return value `result` or in
         any outer arena's register taint map, then bulldozes the cursor in `O(1)`!
    """
    if cpu_context == "NMI":
        visible_tokens: Tuple[RegionToken, ...] = ()
        depth = 1
    else:
        visible_tokens = tuple(s.token for s in _ACTIVE_ARENA_STACK)
        depth = len(_ACTIVE_ARENA_STACK) + 1

    tok = RegionToken(uid=next(_REGION_COUNTER), label=label, depth=depth, space=space)
    scope = ArenaScope(
        token=tok,
        capacity=capacity,
        cpu_context=cpu_context,
        active_stack=visible_tokens + (tok,),
    )
    _ACTIVE_ARENA_STACK.append(scope)
    try:
        result = body(scope)
        # Check return-value escape (`runST` rank-2 check)
        escaped_ret = _find_any_region_ptrs(result, SpecificUid=tok.uid)
        if escaped_ret:
            bad = escaped_ret[0]
            raise IxArenaEscapeError(
                f"Rank-2 `runST` Escape Prevented: Pointer `{bad.label}` ({bad.format_snes_addr()}) "
                f"attempted to escape dying arena `{label}` via scope return value!"
            )
        asm_listing = scope._close_and_bulldoze()
    finally:
        _ACTIVE_ARENA_STACK.pop()
        scope._is_alive = False

    receipt = {
        "arena_label": label,
        "space": space.value.name,
        "cpu_context": cpu_context,
        "capacity_bytes": capacity,
        "peak_watermark_bytes": scope.peak_watermark,
        "final_cursor_after_bulldoze": scope.cursor,
        "asar_asm": asm_listing,
    }
    return result, receipt
