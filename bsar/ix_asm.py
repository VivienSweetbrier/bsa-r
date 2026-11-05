#!/usr/bin/env python3
"""
ATKEY INDEXED MONAD (`IxAsm[I, J, A]`) PROCESSOR-FLAG & Q8.8 KERNEL VERIFIER (`bsar.ix_asm`)
License: GNU AGPLv3
Attestation: probabilistic_structural
Dependencies: 0 (Python >= 3.10 Standard Library Only)

Eliminates implicit processor-flag bugs in assembly and fixed-point hardware kernels
via Robert Atkey's Parameterized / Indexed Monad (`IxMonad m i j a`) paired with
GADT-style precondition/postcondition indices and Sweetbrier Modal Box (`Box_{i -> j}`):

  1. SNES `65c816` / `SA-1` / `Asar` Processor Status Register (`P`) & Stack Tracking:
     - `m_width`     : `"W8"` (`SEP #$20`) | `"W16"` (`REP #$20`) | `"UNKNOWN"`
     - `x_width`     : `"W8"` (`SEP #$10`) | `"W16"` (`REP #$10`) | `"UNKNOWN"`
     - `carry`       : `"CLEAR"` (`CLC`)   | `"SET"` (`SEC`)      | `"DIRTY"` (clobbered)
     - `stack_bytes` : Tuple of pushed item byte-widths (`1` or `2`) so `PHA` in `W16`
                       followed by `PLA` in `W8` (or `RTS` with non-empty stack) is
                       caught as a static type error BEFORE emitting a single byte!

  2. `BSA-R` `32D Q8.8 Pathion` Fixed-Point Accumulator Flag Tracking:
     - `q_scale`     : `"Q8_8"` (normalized 16-bit signed fixed-point) |
                       `"Q16_16"` (raw 32-bit product after `Q8.8 * Q8.8` before `>> 8`)
     - `zd_flag`     : `"UNCHECKED"` | `"ANNIHILATED"` | `"NONZERO"`

  3. Branch Join Unification (`ix_branch_eq` / `ix_branch_ne`):
     - Enforces `then_prog.post_state == else_prog.post_state` at every conditional
       join point (`BEQ` / `BNE`), making branch-induced flag desynchronization
       mathematically impossible (mirroring `lean/IxMonadProcessorFlags.lean`).
"""

from __future__ import annotations

from dataclasses import dataclass, field
import hashlib
import json
from typing import Any, Callable, Dict, Generic, List, Optional, Sequence, Tuple, TypeVar

from .asar_zd_microbench import pack_asar_rats_block, verify_asar_rats_block
from .fp_coalgebra import ModalBox

I = TypeVar("I", bound="ProcFlagState")
J = TypeVar("J", bound="ProcFlagState")
K = TypeVar("K", bound="ProcFlagState")
A = TypeVar("A")
B = TypeVar("B")


class IxFlagTypeError(TypeError):
    """
    Raised statically at Indexed Monad composition time (`ibind` / `>>` / `branch_eq`)
    whenever an assembly instruction or fixed-point kernel op violates its required
    pre-state processor flags or leaves divergent post-state flags across branches.
    """


@dataclass(frozen=True)
class ProcFlagState:
    """
    Phantom Type-State Index `i` / `j` for `IxAsm[i, j, a]`.
    Tracks both 65c816 Processor Status (`M`, `X`, `C`, stack byte widths) and
    BSA-R Q8.8 Fixed-Point Accumulator scale (`Q8_8` vs `Q16_16`).
    """

    m_width: str = "W8"                      # "W8" | "W16" | "UNKNOWN"
    x_width: str = "W8"                      # "W8" | "W16" | "UNKNOWN"
    carry: str = "DIRTY"                     # "CLEAR" | "SET" | "DIRTY"
    q_scale: str = "Q8_8"                    # "Q8_8" | "Q16_16"
    zd_flag: str = "UNCHECKED"               # "UNCHECKED" | "ANNIHILATED" | "NONZERO"
    stack_bytes: Tuple[int, ...] = ()        # Pushed byte widths on hardware stack

    @property
    def stack_depth(self) -> int:
        return sum(self.stack_bytes)

    def short_sig(self) -> str:
        return (
            f"Flags(M={self.m_width}, X={self.x_width}, C={self.carry}, "
            f"Q={self.q_scale}, ZD={self.zd_flag}, SP={self.stack_depth}B)"
        )


# Standard canonical entry states
BOOT_65816_EMULATION = ProcFlagState(
    m_width="W8", x_width="W8", carry="DIRTY", q_scale="Q8_8", zd_flag="UNCHECKED", stack_bytes=()
)
ENTRY_16BIT_CLEAN = ProcFlagState(
    m_width="W16", x_width="W16", carry="CLEAR", q_scale="Q8_8", zd_flag="UNCHECKED", stack_bytes=()
)


@dataclass(frozen=True)
class AsmOpRecord:
    """Single verified state-transition morphism `pre_state -> post_state`."""

    mnemonic: str
    asar_line: str
    machine_bytes: bytes
    pre_state: ProcFlagState
    post_state: ProcFlagState
    comment: str = ""
    sim_effect: Optional[Callable[[Dict[str, int]], None]] = field(
        default=None, compare=False, repr=False
    )


@dataclass(frozen=True)
class IxAsm(Generic[I, J, A]):
    """
    Atkey's Parameterized / Indexed Monad `IxAsm[I, J, A]`:
      - `pre_state`  : Required input `ProcFlagState` (`I`)
      - `post_state` : Guaranteed output `ProcFlagState` (`J`)
      - `value`      : Pure return payload (`A`)
      - `ops`        : Verified instruction morphisms composing `I -> ... -> J`
    """

    pre_state: ProcFlagState
    post_state: ProcFlagState
    value: A
    ops: Tuple[AsmOpRecord, ...] = ()

    @classmethod
    def ireturn(cls, state: ProcFlagState, value: A) -> "IxAsm[ProcFlagState, ProcFlagState, A]":
        """Indexed Monad unit (`ireturn : a -> m i i a`)."""
        return cls(pre_state=state, post_state=state, value=value, ops=())

    def ibind(
        self, fn: Callable[[A, ProcFlagState], "IxAsm[ProcFlagState, ProcFlagState, B]"]
    ) -> "IxAsm[ProcFlagState, ProcFlagState, B]":
        """
        Indexed Monad Kleisli bind (`(>>>=) : m i j a -> (a -> m j k b) -> m i k b`).
        Enforces `self.post_state == next_prog.pre_state`!
        """
        nxt = fn(self.value, self.post_state)
        if self.post_state != nxt.pre_state:
            raise IxFlagTypeError(
                f"Indexed Monad state mismatch across ibind:\n"
                f"  Left post-state : {self.post_state.short_sig()}\n"
                f"  Right pre-state : {nxt.pre_state.short_sig()}"
            )
        return IxAsm(
            pre_state=self.pre_state,
            post_state=nxt.post_state,
            value=nxt.value,
            ops=self.ops + nxt.ops,
        )

    def then(
        self, step_builder: Callable[[ProcFlagState], "IxAsm[ProcFlagState, ProcFlagState, B]"]
    ) -> "IxAsm[ProcFlagState, ProcFlagState, B]":
        """Indexed sequence (`(>>>) : m i j a -> m j k b -> m i k b`)."""
        return self.ibind(lambda _val, st: step_builder(st))

    def __rshift__(
        self, step_builder: Callable[[ProcFlagState], "IxAsm[ProcFlagState, ProcFlagState, B]"]
    ) -> "IxAsm[ProcFlagState, ProcFlagState, B]":
        """Syntactic sugar `prog >> step` for Indexed Monad Kleisli composition."""
        return self.then(step_builder)

    def assemble_bytes(self) -> bytes:
        return b"".join(op.machine_bytes for op in self.ops)

    def assemble_asar_source(self, routine_label: str = "SweetbrierIxKernel") -> str:
        lines = [
            f"; ==============================================================================",
            f"; Asar 65c816 + BSA-R Q8.8 Verified Indexed-Monad Routine: {routine_label}",
            f"; Entry Type-State : {self.pre_state.short_sig()}",
            f"; Exit  Type-State : {self.post_state.short_sig()}",
            f"; Total Machine Bytes: {len(self.assemble_bytes())} bytes",
            f"; ==============================================================================",
            f"{routine_label}:",
        ]
        for op in self.ops:
            hex_str = op.machine_bytes.hex().upper()
            pad_asm = f"    {op.asar_line:<24}"
            lines.append(
                f"{pad_asm} ; [{hex_str:<8}] {op.pre_state.short_sig()} -> {op.post_state.short_sig()}"
            )
        return "\n".join(lines)

    def seal_rats_modal_box(self, routine_label: str = "SweetbrierIxKernel") -> ModalBox[Dict[str, Any]]:
        """
        Lift the verified Indexed Monad program `IxAsm[I, J, A]` into the
        Sweetbrier Modal Functor `Box(I -> J)` with an authentic SNES `STAR` RATS seal.
        """
        raw_code = self.assemble_bytes()
        rats_blob = pack_asar_rats_block(raw_code if raw_code else b"\x60")
        rats_audit = verify_asar_rats_block(rats_blob)
        payload = {
            "routine_label": routine_label,
            "pre_state": self.pre_state.short_sig(),
            "post_state": self.post_state.short_sig(),
            "instruction_count": len(self.ops),
            "machine_bytes_len": len(raw_code),
            "machine_bytes_hex": raw_code.hex(),
            "rats_header_hex": rats_audit["header_hex"],
            "rats_valid": rats_audit["valid"],
            "asar_source": self.assemble_asar_source(routine_label),
            "sha256": hashlib.sha256(rats_blob).hexdigest(),
        }
        return ModalBox.pure(payload, label=f"IxAsm_Box[{routine_label}]")

    def simulate(self, initial_regs: Optional[Dict[str, int]] = None) -> Dict[str, Any]:
        """Run deterministic register/stack simulation across the verified morphism chain."""
        regs: Dict[str, int] = {
            "A": 0,
            "X": 0,
            "Y": 0,
            "C": 0 if self.pre_state.carry == "CLEAR" else (1 if self.pre_state.carry == "SET" else 0),
            "Q_ACC": 0,
            "Q_SLAB_0": 0,
            "SP_DEPTH": self.pre_state.stack_depth,
        }
        if initial_regs:
            regs.update(initial_regs)
        for op in self.ops:
            if op.sim_effect is not None:
                op.sim_effect(regs)
        return regs

    def to_mermaid(self) -> str:
        lines = ["flowchart TD"]
        lines.append(f'    S0["Entry: {self.pre_state.short_sig()}"]')
        for idx, op in enumerate(self.ops):
            nxt_id = f"S{idx + 1}"
            prev_id = f"S{idx}"
            lbl = op.asar_line.replace('"', "'")
            lines.append(f'    {nxt_id}["{ op.post_state.short_sig() }"]')
            lines.append(f'    {prev_id} -->|"{lbl}"| {nxt_id}')
        return "\n".join(lines)


# ==============================================================================
# 2. GADT-TYPED 65c816 / ASAR & BSA-R Q8.8 INSTRUCTION COMBINATORS
# ==============================================================================


def ix_start(initial_state: ProcFlagState = BOOT_65816_EMULATION) -> IxAsm[ProcFlagState, ProcFlagState, None]:
    """Initialize an Indexed Monad assembly block at a known `ProcFlagState`."""
    return IxAsm.ireturn(initial_state, None)


def rep_m16() -> Callable[[ProcFlagState], IxAsm[ProcFlagState, ProcFlagState, None]]:
    """`REP #$20` (`C2 20`): Clear `M` bit -> 16-bit Accumulator (`m_width = 'W16'`)."""

    def _step(st: ProcFlagState) -> IxAsm[ProcFlagState, ProcFlagState, None]:
        post = ProcFlagState(
            m_width="W16",
            x_width=st.x_width,
            carry=st.carry,
            q_scale=st.q_scale,
            zd_flag=st.zd_flag,
            stack_bytes=st.stack_bytes,
        )
        op = AsmOpRecord(
            mnemonic="REP",
            asar_line="REP #$20",
            machine_bytes=bytes([0xC2, 0x20]),
            pre_state=st,
            post_state=post,
            comment="16-bit Accumulator (M=0)",
        )
        return IxAsm(st, post, None, (op,))

    return _step


def sep_m8() -> Callable[[ProcFlagState], IxAsm[ProcFlagState, ProcFlagState, None]]:
    """`SEP #$20` (`E2 20`): Set `M` bit -> 8-bit Accumulator (`m_width = 'W8'`)."""

    def _step(st: ProcFlagState) -> IxAsm[ProcFlagState, ProcFlagState, None]:
        post = ProcFlagState(
            m_width="W8",
            x_width=st.x_width,
            carry=st.carry,
            q_scale=st.q_scale,
            zd_flag=st.zd_flag,
            stack_bytes=st.stack_bytes,
        )
        op = AsmOpRecord(
            mnemonic="SEP",
            asar_line="SEP #$20",
            machine_bytes=bytes([0xE2, 0x20]),
            pre_state=st,
            post_state=post,
            comment="8-bit Accumulator (M=1)",
            sim_effect=lambda r: r.__setitem__("A", r["A"] & 0xFF),
        )
        return IxAsm(st, post, None, (op,))

    return _step


def rep_x16() -> Callable[[ProcFlagState], IxAsm[ProcFlagState, ProcFlagState, None]]:
    """`REP #$10` (`C2 10`): Clear `X` bit -> 16-bit Index X/Y (`x_width = 'W16'`)."""

    def _step(st: ProcFlagState) -> IxAsm[ProcFlagState, ProcFlagState, None]:
        post = ProcFlagState(
            m_width=st.m_width,
            x_width="W16",
            carry=st.carry,
            q_scale=st.q_scale,
            zd_flag=st.zd_flag,
            stack_bytes=st.stack_bytes,
        )
        op = AsmOpRecord(
            mnemonic="REP",
            asar_line="REP #$10",
            machine_bytes=bytes([0xC2, 0x10]),
            pre_state=st,
            post_state=post,
            comment="16-bit Index X/Y (X=0)",
        )
        return IxAsm(st, post, None, (op,))

    return _step


def sep_x8() -> Callable[[ProcFlagState], IxAsm[ProcFlagState, ProcFlagState, None]]:
    """`SEP #$10` (`E2 10`): Set `X` bit -> 8-bit Index X/Y (`x_width = 'W8'`)."""

    def _step(st: ProcFlagState) -> IxAsm[ProcFlagState, ProcFlagState, None]:
        post = ProcFlagState(
            m_width=st.m_width,
            x_width="W8",
            carry=st.carry,
            q_scale=st.q_scale,
            zd_flag=st.zd_flag,
            stack_bytes=st.stack_bytes,
        )
        op = AsmOpRecord(
            mnemonic="SEP",
            asar_line="SEP #$10",
            machine_bytes=bytes([0xE2, 0x10]),
            pre_state=st,
            post_state=post,
            comment="8-bit Index X/Y (X=1)",
            sim_effect=lambda r: (
                r.__setitem__("X", r["X"] & 0xFF),
                r.__setitem__("Y", r["Y"] & 0xFF),
            ),
        )
        return IxAsm(st, post, None, (op,))

    return _step


def rep_mx16() -> Callable[[ProcFlagState], IxAsm[ProcFlagState, ProcFlagState, None]]:
    """`REP #$30` (`C2 30`): 16-bit Accumulator AND 16-bit Index (`m_width='W16', x_width='W16'`)."""

    def _step(st: ProcFlagState) -> IxAsm[ProcFlagState, ProcFlagState, None]:
        post = ProcFlagState(
            m_width="W16",
            x_width="W16",
            carry=st.carry,
            q_scale=st.q_scale,
            zd_flag=st.zd_flag,
            stack_bytes=st.stack_bytes,
        )
        op = AsmOpRecord(
            mnemonic="REP",
            asar_line="REP #$30",
            machine_bytes=bytes([0xC2, 0x30]),
            pre_state=st,
            post_state=post,
            comment="16-bit A & X/Y (M=0, X=0)",
        )
        return IxAsm(st, post, None, (op,))

    return _step


def clc() -> Callable[[ProcFlagState], IxAsm[ProcFlagState, ProcFlagState, None]]:
    """`CLC` (`18`): Clear Carry flag (`carry = 'CLEAR'`)."""

    def _step(st: ProcFlagState) -> IxAsm[ProcFlagState, ProcFlagState, None]:
        post = ProcFlagState(
            m_width=st.m_width,
            x_width=st.x_width,
            carry="CLEAR",
            q_scale=st.q_scale,
            zd_flag=st.zd_flag,
            stack_bytes=st.stack_bytes,
        )
        op = AsmOpRecord(
            mnemonic="CLC",
            asar_line="CLC",
            machine_bytes=bytes([0x18]),
            pre_state=st,
            post_state=post,
            comment="Clear Carry (C=0)",
            sim_effect=lambda r: r.__setitem__("C", 0),
        )
        return IxAsm(st, post, None, (op,))

    return _step


def sec() -> Callable[[ProcFlagState], IxAsm[ProcFlagState, ProcFlagState, None]]:
    """`SEC` (`38`): Set Carry flag (`carry = 'SET'`)."""

    def _step(st: ProcFlagState) -> IxAsm[ProcFlagState, ProcFlagState, None]:
        post = ProcFlagState(
            m_width=st.m_width,
            x_width=st.x_width,
            carry="SET",
            q_scale=st.q_scale,
            zd_flag=st.zd_flag,
            stack_bytes=st.stack_bytes,
        )
        op = AsmOpRecord(
            mnemonic="SEC",
            asar_line="SEC",
            machine_bytes=bytes([0x38]),
            pre_state=st,
            post_state=post,
            comment="Set Carry (C=1)",
            sim_effect=lambda r: r.__setitem__("C", 1),
        )
        return IxAsm(st, post, None, (op,))

    return _step


def lda_imm8(val: int) -> Callable[[ProcFlagState], IxAsm[ProcFlagState, ProcFlagState, None]]:
    """
    `LDA #$xx` (`A9 xx`): Load 8-bit immediate into Accumulator.
    STATIC PRECONDITION: `m_width == 'W8'`.
    Raises `IxFlagTypeError` if `M` is `W16` (preventing 65c816 instruction stream misalignment!).
    """
    if not (0 <= val <= 0xFF):
        raise ValueError(f"lda_imm8 value must be 0..0xFF, got {val:#x}")

    def _step(st: ProcFlagState) -> IxAsm[ProcFlagState, ProcFlagState, None]:
        if st.m_width != "W8":
            raise IxFlagTypeError(
                f"65c816 Flag Bug Prevented: `LDA #${val:02X}` (8-bit immediate) called while "
                f"Accumulator width is `{st.m_width}`! Execute `SEP #$20` (`sep_m8()`) first."
            )
        op = AsmOpRecord(
            mnemonic="LDA",
            asar_line=f"LDA #${val:02X}",
            machine_bytes=bytes([0xA9, val & 0xFF]),
            pre_state=st,
            post_state=st,
            comment="8-bit immediate load",
            sim_effect=lambda r: r.__setitem__("A", val & 0xFF),
        )
        return IxAsm(st, st, None, (op,))

    return _step


def lda_imm16(val: int) -> Callable[[ProcFlagState], IxAsm[ProcFlagState, ProcFlagState, None]]:
    """
    `LDA #$xxxx` (`A9 lo hi`): Load 16-bit immediate into Accumulator.
    STATIC PRECONDITION: `m_width == 'W16'`.
    Raises `IxFlagTypeError` if `M` is `W8` (preventing 65c816 PC desync crash!).
    """
    if not (0 <= val <= 0xFFFF):
        raise ValueError(f"lda_imm16 value must be 0..0xFFFF, got {val:#x}")

    def _step(st: ProcFlagState) -> IxAsm[ProcFlagState, ProcFlagState, None]:
        if st.m_width != "W16":
            raise IxFlagTypeError(
                f"65c816 Flag Bug Prevented: `LDA #${val:04X}` (16-bit immediate) called while "
                f"Accumulator width is `{st.m_width}`! Execute `REP #$20` (`rep_m16()`) first."
            )
        op = AsmOpRecord(
            mnemonic="LDA",
            asar_line=f"LDA #${val:04X}",
            machine_bytes=bytes([0xA9, val & 0xFF, (val >> 8) & 0xFF]),
            pre_state=st,
            post_state=st,
            comment="16-bit immediate load",
            sim_effect=lambda r: r.__setitem__("A", val & 0xFFFF),
        )
        return IxAsm(st, st, None, (op,))

    return _step


def ldx_imm16(val: int) -> Callable[[ProcFlagState], IxAsm[ProcFlagState, ProcFlagState, None]]:
    """
    `LDX #$xxxx` (`A2 lo hi`): Load 16-bit immediate into Index X.
    STATIC PRECONDITION: `x_width == 'W16'`.
    """
    if not (0 <= val <= 0xFFFF):
        raise ValueError(f"ldx_imm16 value must be 0..0xFFFF, got {val:#x}")

    def _step(st: ProcFlagState) -> IxAsm[ProcFlagState, ProcFlagState, None]:
        if st.x_width != "W16":
            raise IxFlagTypeError(
                f"65c816 Flag Bug Prevented: `LDX #${val:04X}` (16-bit immediate) called while "
                f"Index width X is `{st.x_width}`! Execute `REP #$10` (`rep_x16()`) first."
            )
        op = AsmOpRecord(
            mnemonic="LDX",
            asar_line=f"LDX #${val:04X}",
            machine_bytes=bytes([0xA2, val & 0xFF, (val >> 8) & 0xFF]),
            pre_state=st,
            post_state=st,
            comment="16-bit X index load",
            sim_effect=lambda r: r.__setitem__("X", val & 0xFFFF),
        )
        return IxAsm(st, st, None, (op,))

    return _step


def adc_imm16(val: int) -> Callable[[ProcFlagState], IxAsm[ProcFlagState, ProcFlagState, None]]:
    """
    `ADC #$xxxx` (`69 lo hi`): Add with Carry (16-bit immediate).
    STATIC PRECONDITIONS:
      1. `m_width == 'W16'`
      2. `carry in ('CLEAR', 'SET')` — Rejects `carry == 'DIRTY'`!
    POSTCONDITION:
      Transitions `carry -> 'DIRTY'` so a subsequent `ADC` without `CLC`/`SEC`
      (or explicit `adc_chain16`) is caught at compile time!
    """
    if not (0 <= val <= 0xFFFF):
        raise ValueError(f"adc_imm16 value must be 0..0xFFFF, got {val:#x}")

    def _step(st: ProcFlagState) -> IxAsm[ProcFlagState, ProcFlagState, None]:
        if st.m_width != "W16":
            raise IxFlagTypeError(
                f"65c816 Flag Bug Prevented: `ADC #${val:04X}` requires `M=W16`, got `{st.m_width}`."
            )
        if st.carry not in ("CLEAR", "SET"):
            raise IxFlagTypeError(
                f"65c816 Carry Bug Prevented: `ADC #${val:04X}` called with uninitialized/dirty "
                f"Carry flag (`carry={st.carry}`)! Execute `CLC` (`clc()`) or `SEC` (`sec()`) first."
            )
        post = ProcFlagState(
            m_width=st.m_width,
            x_width=st.x_width,
            carry="DIRTY",
            q_scale=st.q_scale,
            zd_flag=st.zd_flag,
            stack_bytes=st.stack_bytes,
        )

        def _sim(r: Dict[str, int]) -> None:
            total = (r["A"] & 0xFFFF) + (val & 0xFFFF) + (1 if st.carry == "SET" else 0)
            r["C"] = 1 if total > 0xFFFF else 0
            r["A"] = total & 0xFFFF

        op = AsmOpRecord(
            mnemonic="ADC",
            asar_line=f"ADC #${val:04X}",
            machine_bytes=bytes([0x69, val & 0xFF, (val >> 8) & 0xFF]),
            pre_state=st,
            post_state=post,
            comment="16-bit add with certified Carry; clobbers Carry -> DIRTY",
            sim_effect=_sim,
        )
        return IxAsm(st, post, None, (op,))

    return _step


def pha() -> Callable[[ProcFlagState], IxAsm[ProcFlagState, ProcFlagState, None]]:
    """
    `PHA` (`48`): Push Accumulator onto hardware stack.
    Pushes 2 bytes if `M == 'W16'` or 1 byte if `M == 'W8'`, recording exact byte width
    in the type-state `stack_bytes` tuple!
    """

    def _step(st: ProcFlagState) -> IxAsm[ProcFlagState, ProcFlagState, None]:
        if st.m_width not in ("W8", "W16"):
            raise IxFlagTypeError("Cannot execute `PHA` when Accumulator width `M` is UNKNOWN.")
        pushed_w = 2 if st.m_width == "W16" else 1
        post = ProcFlagState(
            m_width=st.m_width,
            x_width=st.x_width,
            carry=st.carry,
            q_scale=st.q_scale,
            zd_flag=st.zd_flag,
            stack_bytes=st.stack_bytes + (pushed_w,),
        )
        op = AsmOpRecord(
            mnemonic="PHA",
            asar_line="PHA",
            machine_bytes=bytes([0x48]),
            pre_state=st,
            post_state=post,
            comment=f"Push {pushed_w}B Accumulator to stack",
            sim_effect=lambda r: r.__setitem__("SP_DEPTH", post.stack_depth),
        )
        return IxAsm(st, post, None, (op,))

    return _step


def pla() -> Callable[[ProcFlagState], IxAsm[ProcFlagState, ProcFlagState, None]]:
    """
    `PLA` (`68`): Pull Accumulator from hardware stack.
    STATIC PRECONDITIONS:
      1. `stack_bytes` is non-empty (no stack underflow!).
      2. Current `m_width` pull size (`1B` or `2B`) matches the top pushed byte width!
         (Prevents the classic 65c816 bug of `PHA` in 16-bit mode followed by `PLA` in 8-bit mode!)
    """

    def _step(st: ProcFlagState) -> IxAsm[ProcFlagState, ProcFlagState, None]:
        if not st.stack_bytes:
            raise IxFlagTypeError(
                "65c816 Stack Underflow Bug Prevented: `PLA` called with empty local stack (`SP=0B`)!"
            )
        pull_w = 2 if st.m_width == "W16" else 1
        top_w = st.stack_bytes[-1]
        if pull_w != top_w:
            raise IxFlagTypeError(
                f"65c816 Stack Width Desync Bug Prevented: Top of stack was pushed as `{top_w}B`, "
                f"but `PLA` is executing in `{st.m_width}` (`{pull_w}B`) mode! "
                f"1 byte would leak on the hardware stack and corrupt `RTS`!"
            )
        post = ProcFlagState(
            m_width=st.m_width,
            x_width=st.x_width,
            carry=st.carry,
            q_scale=st.q_scale,
            zd_flag=st.zd_flag,
            stack_bytes=st.stack_bytes[:-1],
        )
        op = AsmOpRecord(
            mnemonic="PLA",
            asar_line="PLA",
            machine_bytes=bytes([0x68]),
            pre_state=st,
            post_state=post,
            comment=f"Pull {pull_w}B Accumulator from stack",
            sim_effect=lambda r: r.__setitem__("SP_DEPTH", post.stack_depth),
        )
        return IxAsm(st, post, None, (op,))

    return _step


def rts() -> Callable[[ProcFlagState], IxAsm[ProcFlagState, ProcFlagState, None]]:
    """
    `RTS` (`60`): Return from Subroutine.
    STATIC PRECONDITIONS:
      1. `stack_depth == 0` (every `PHA` was balanced by a matching `PLA`!).
      2. `q_scale == 'Q8_8'` (no unnormalized `Q16_16` fixed-point intermediate left dangling!).
    """

    def _step(st: ProcFlagState) -> IxAsm[ProcFlagState, ProcFlagState, None]:
        if st.stack_bytes:
            raise IxFlagTypeError(
                f"65c816 Subroutine Stack Leak Prevented: `RTS` called with `{st.stack_depth}B` "
                f"still pushed on the stack (`stack_bytes={st.stack_bytes}`)! "
                f"CPU would pop data as return address and crash!"
            )
        if st.q_scale != "Q8_8":
            raise IxFlagTypeError(
                f"BSA-R Fixed-Point Scale Bug Prevented: `RTS` called while accumulator scale "
                f"is unnormalized `{st.q_scale}`!"
            )
        op = AsmOpRecord(
            mnemonic="RTS",
            asar_line="RTS",
            machine_bytes=bytes([0x60]),
            pre_state=st,
            post_state=st,
            comment="Verified subroutine return (SP=0B, Q=Q8_8)",
        )
        return IxAsm(st, st, None, (op,))

    return _step


# ==============================================================================
# 3. BSA-R 32D Q8.8 FIXED-POINT & ZERO-DIVISOR KERNEL COMBINATORS
# ==============================================================================


def q88_mul_raw(
    lhs_q88: int, rhs_q88: int
) -> Callable[[ProcFlagState], IxAsm[ProcFlagState, ProcFlagState, None]]:
    """
    Multiply two signed 16-bit `Q8.8` fixed-point numbers (`lhs_q88 * rhs_q88`).
    STATIC PRECONDITION: `q_scale == 'Q8_8'`.
    POSTCONDITION: Transitions `q_scale -> 'Q16_16'` and `carry -> 'DIRTY'`.
    Cannot store or multiply again until `q16_shift8_normalize()` is called!
    """

    def _step(st: ProcFlagState) -> IxAsm[ProcFlagState, ProcFlagState, None]:
        if st.q_scale != "Q8_8":
            raise IxFlagTypeError(
                f"BSA-R Fixed-Point Bug Prevented: `q88_mul_raw` called while accumulator "
                f"is already in `{st.q_scale}`! Normalize via `q16_shift8_normalize()` (`>> 8`) first."
            )
        post = ProcFlagState(
            m_width=st.m_width,
            x_width=st.x_width,
            carry="DIRTY",
            q_scale="Q16_16",
            zd_flag="UNCHECKED",
            stack_bytes=st.stack_bytes,
        )
        raw_prod = int(lhs_q88) * int(rhs_q88)
        op = AsmOpRecord(
            mnemonic="Q88_MUL_RAW",
            asar_line=f"JSL BSAR_Q88_MulRaw      ; {lhs_q88} * {rhs_q88} -> Q16.16",
            machine_bytes=bytes([0x22, 0x00, 0x80, 0x01]),
            pre_state=st,
            post_state=post,
            comment="Raw Q8.8 * Q8.8 -> Q16.16 product",
            sim_effect=lambda r: r.__setitem__("Q_ACC", raw_prod),
        )
        return IxAsm(st, post, None, (op,))

    return _step


def q16_shift8_normalize() -> Callable[[ProcFlagState], IxAsm[ProcFlagState, ProcFlagState, None]]:
    """
    Arithmetic right shift `>> 8` (`Q16.16 -> Q8.8`) with 16-bit signed saturation.
    STATIC PRECONDITION: `q_scale == 'Q16_16'`.
    POSTCONDITION: Transitions `q_scale -> 'Q8_8'`.
    """

    def _step(st: ProcFlagState) -> IxAsm[ProcFlagState, ProcFlagState, None]:
        if st.q_scale != "Q16_16":
            raise IxFlagTypeError(
                f"BSA-R Fixed-Point Bug Prevented: `q16_shift8_normalize` (`>> 8`) called on "
                f"already-normalized `{st.q_scale}` register (would divide value by 256 in error!)."
            )
        post = ProcFlagState(
            m_width=st.m_width,
            x_width=st.x_width,
            carry="DIRTY",
            q_scale="Q8_8",
            zd_flag=st.zd_flag,
            stack_bytes=st.stack_bytes,
        )

        def _sim(r: Dict[str, int]) -> None:
            shifted = r["Q_ACC"] >> 8
            clamped = max(-32768, min(32767, shifted))
            r["Q_ACC"] = clamped
            r["A"] = clamped & 0xFFFF

        op = AsmOpRecord(
            mnemonic="Q16_SHIFT8",
            asar_line="XBA : ASR #$08           ; Q16.16 >> 8 -> Q8.8",
            machine_bytes=bytes([0xEB, 0x4A]),
            pre_state=st,
            post_state=post,
            comment="Normalize Q16.16 -> Q8.8",
            sim_effect=_sim,
        )
        return IxAsm(st, post, None, (op,))

    return _step


def q88_store_slab() -> Callable[[ProcFlagState], IxAsm[ProcFlagState, ProcFlagState, None]]:
    """
    Store normalized `Q8.8` blade into the `64-byte` L1 cache slab (`$7E:2000,X`).
    STATIC PRECONDITION: `q_scale == 'Q8_8'` AND `m_width == 'W16'`.
    """

    def _step(st: ProcFlagState) -> IxAsm[ProcFlagState, ProcFlagState, None]:
        if st.q_scale != "Q8_8":
            raise IxFlagTypeError(
                f"BSA-R Fixed-Point Bug Prevented: Cannot store unnormalized `{st.q_scale}` "
                f"product into 64B `Q8.8` Pathion slab! Call `q16_shift8_normalize()` first."
            )
        if st.m_width != "W16":
            raise IxFlagTypeError(
                f"65c816 Flag Bug Prevented: 16-bit `Q8.8` slab store `STA $7E2000,X` requires "
                f"`M=W16`, got `{st.m_width}`!"
            )
        op = AsmOpRecord(
            mnemonic="STA_Q88",
            asar_line="STA $7E2000,X",
            machine_bytes=bytes([0x9F, 0x00, 0x20, 0x7E]),
            pre_state=st,
            post_state=st,
            comment="Store verified Q8.8 blade to 64B slab",
            sim_effect=lambda r: r.__setitem__("Q_SLAB_0", r["Q_ACC"]),
        )
        return IxAsm(st, st, None, (op,))

    return _step


# ==============================================================================
# 4. CONDITIONAL BRANCH JOIN GATE (`ix_branch_eq` — ENFORCES J_THEN == J_ELSE)
# ==============================================================================


def ix_branch_eq(
    then_builder: Callable[[IxAsm[ProcFlagState, ProcFlagState, None]], IxAsm[ProcFlagState, ProcFlagState, Any]],
    else_builder: Callable[[IxAsm[ProcFlagState, ProcFlagState, None]], IxAsm[ProcFlagState, ProcFlagState, Any]],
    branch_label: str = " branch_join",
) -> Callable[[ProcFlagState], IxAsm[ProcFlagState, ProcFlagState, None]]:
    """
    Indexed Monad Conditional Branch Combinator (`BEQ` / `BRA` join).
    Evaluates both `then_builder` and `else_builder` starting from `pre_state` `i`
    and STATICALLY ENFORCES:
        `then_prog.post_state == else_prog.post_state`!
    If one branch changes `REP #$20` (`M=W16`), leaves `Carry=DIRTY`, pushes to stack,
    or forgets `q16_shift8_normalize()` while the other branch does not, raises
    `IxFlagTypeError` at compile time!
    """

    def _step(st: ProcFlagState) -> IxAsm[ProcFlagState, ProcFlagState, None]:
        seed = ix_start(st)
        t_prog = then_builder(seed)
        e_prog = else_builder(seed)
        if t_prog.post_state != e_prog.post_state:
            raise IxFlagTypeError(
                f"Branch Join Processor-Flag Divergence Prevented at `{branch_label}`!\n"
                f"   Entry State : {st.short_sig()}\n"
                f"  `then` Exit : {t_prog.post_state.short_sig()}\n"
                f"  `else` Exit : {e_prog.post_state.short_sig()}\n"
                f"Both branch arms MUST unify on the exact same post-state `ProcFlagState`!"
            )
        t_bytes = t_prog.assemble_bytes()
        e_bytes = e_prog.assemble_bytes()
        # Emit BEQ + then_ops + BRA + else_ops
        beq_op = AsmOpRecord(
            mnemonic="BEQ",
            asar_line=f"BEQ .then_{branch_label.strip()}",
            machine_bytes=bytes([0xF0, len(e_bytes) + 2]),
            pre_state=st,
            post_state=st,
            comment="Branch to then-arm if Z=1",
        )
        bra_op = AsmOpRecord(
            mnemonic="BRA",
            asar_line=f"BRA .join_{branch_label.strip()}",
            machine_bytes=bytes([0x80, len(t_bytes)]),
            pre_state=e_prog.post_state,
            post_state=e_prog.post_state,
            comment="Jump to unified branch join",
        )
        combined_ops = (beq_op,) + e_prog.ops + (bra_op,) + t_prog.ops
        return IxAsm(
            pre_state=st,
            post_state=t_prog.post_state,
            value=None,
            ops=combined_ops,
        )

    return _step


# ==============================================================================
# 5. SELF-CONTAINED BENCHMARK & AUDIT SUITE (`run_ix_asm_verification_suite`)
# ==============================================================================


def run_ix_asm_verification_suite() -> Dict[str, Any]:
    """
    Runs the complete Unified Indexed Monad (`IxAsm`) verification suite:
      1. Compiles a valid hybrid 65c816 + BSA-R Q8.8 Pathion routine (`SweetbrierPathionBladeKernel`)
         with branch joins, stack save/restore, Carry-certified 16-bit addition, and
         `Q8.8 -> Q16.16 -> Q8.8` fixed-point normalization, sealing it in a `STAR` RATS `ModalBox`.
      2. Exercises all 5 classic assembly processor-flag bugs and verifies that every single
         one is caught statically as an `IxFlagTypeError` at composition time (`0` runtime leaks).
    """
    # 1. Valid unified kernel: 8-bit boot -> 16-bit M/X -> PHA -> branch_eq -> PLA -> Q8.8 Mul/Norm/Store -> RTS
    valid_prog = (
        ix_start(BOOT_65816_EMULATION)
        >> lda_imm8(0x7F)
        >> rep_mx16()
        >> ldx_imm16(0x0040)
        >> pha()
        >> ix_branch_eq(
            then_builder=lambda p: p >> clc() >> lda_imm16(0x0100) >> adc_imm16(0x0080),
            else_builder=lambda p: p >> sec() >> lda_imm16(0x00FF) >> adc_imm16(0x0080),
            branch_label="pathion_gate",
        )
        >> pla()
        >> q88_mul_raw(256, 384)       # 1.0 * 1.5 in Q8.8 -> 98304 in Q16.16
        >> q16_shift8_normalize()      # 98304 >> 8 -> 384 (1.5 in Q8.8)
        >> q88_store_slab()
        >> rts()
    )

    modal_cert = valid_prog.seal_rats_modal_box("SweetbrierPathionBladeKernel")
    sim_state = valid_prog.simulate()

    # 2. Adversarially test all 5 processor-flag bug classes to prove static rejection
    bug_trials = [
        (
            "BUG_1_M_WIDTH_DESYNC_16BIT_IMM_IN_8BIT_MODE",
            lambda: ix_start(BOOT_65816_EMULATION) >> lda_imm16(0x1234),
        ),
        (
            "BUG_2_DIRTY_CARRY_BEFORE_ADC16",
            lambda: ix_start(BOOT_65816_EMULATION) >> rep_m16() >> adc_imm16(0x0010),
        ),
        (
            "BUG_3_BRANCH_JOIN_FLAG_DIVERGENCE",
            lambda: ix_start(BOOT_65816_EMULATION)
            >> ix_branch_eq(
                then_builder=lambda p: p >> rep_m16() >> lda_imm16(0x1000),
                else_builder=lambda p: p >> lda_imm8(0x10),  # Left M=W8 in else arm!
                branch_label="divergent_flags",
            ),
        ),
        (
            "BUG_4_STACK_WIDTH_OR_RTS_LEAK",
            lambda: ix_start(BOOT_65816_EMULATION) >> rep_m16() >> pha() >> sep_m8() >> pla(),
        ),
        (
            "BUG_5_UNSHIFTED_Q16_16_STORE_INTO_Q8_8_SLAB",
            lambda: ix_start(BOOT_65816_EMULATION)
            >> rep_m16()
            >> q88_mul_raw(256, 256)
            >> q88_store_slab(),  # Forgot q16_shift8_normalize()!
        ),
    ]

    caught_bugs: List[Dict[str, Any]] = []
    for bug_name, trigger_fn in bug_trials:
        try:
            trigger_fn()
            caught_bugs.append({"bug": bug_name, "caught_statically": False, "error": None})
        except IxFlagTypeError as exc:
            caught_bugs.append(
                {"bug": bug_name, "caught_statically": True, "error": str(exc).splitlines()[0]}
            )

    all_caught = all(item["caught_statically"] for item in caught_bugs)
    return {
        "attestation": "probabilistic_structural",
        "valid_kernel": modal_cert.extract(),
        "modal_trace": list(modal_cert.trace),
        "simulation_registers": sim_state,
        "mermaid_flowchart": valid_prog.to_mermaid(),
        "static_bug_rejections": caught_bugs,
        "all_5_flag_bugs_rejected_statically": all_caught,
    }
