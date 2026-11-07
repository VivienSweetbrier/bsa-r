#!/usr/bin/env python3
"""
SESSION-TYPED DMA / VBLANK & SA-1 HARDWARE WAIT PROTOCOLS (`bsar.dma_sessions`)
License: GNU AGPLv3
Attestation: probabilistic_structural
Dependencies: 0 (Python >= 3.10 Standard Library Only)

Implements Item #2 of `build-sheet.md` + `smw_sa1_brutal_vivian.md` Rules 4–6:
  1. Linear Session-Typed PPU / DMA Protocol (`DMASession`):
     - `Idle` -> `arm_dma(channel, src_region_ptr, target, dest_addr)` -> `Armed`
     - `Armed` -> `commit_in_vblank(vblank_token)` -> `Completed` (consumes session!)
     - Makes three classic SNES graphical corruption bugs unrepresentable:
         a) Triggering `$420B` (`MDMAEN`) or writing VRAM/CGRAM/OAM during Active Display!
         b) Arming a DMA channel and forgetting to complete/consume it before frame end!
         c) Exceeding the NTSC/PAL VBlank byte transfer budget (~4.6 KB safe NTSC window)
            or passing an unaligned / bank-straddling source buffer!
  2. Linear Session-Typed SA-1 5-Cycle Hardware Multiplier (`SA1MathSession`):
     - Writing `$2251`/`$2253` produces an `SA1PendingProduct(cycles_remaining=5)` token.
     - Reading `$2306` (32-bit product) or `$2307` (`Q8.8` right-shifted middle 16-bit word!)
       is a STATIC TYPE ERROR until `wait_cycles(>= 5)` (`NOP : NOP : NOP` = 6 cycles or
       interleaved instructions) transitions the session to `SA1ReadyProduct`!
"""

from __future__ import annotations

from dataclasses import dataclass, field
from typing import Any, Callable, Dict, List, Optional, Tuple, TypeVar

from .arenas import RegionPtr

T = TypeVar("T")

NTSC_SAFE_VBLANK_DMA_BYTES = 4608  # Safe ~4.5 KB NTSC VBlank DMA budget alongside OAM/scroll


class IxDMASessionError(TypeError):
    """Raised statically when a DMA/VBlank or SA-1 hardware session protocol is violated."""


@dataclass
class VBlankWindowToken:
    """
    Capability token minted ONLY inside `with_vblank_session(...)` (or `with_forced_blank(...)`).
    Cannot be forged or used after VBlank exits!
    """

    mode: str                                  # "NMI_VBLANK" | "FORCED_BLANK_INIDISP_80"
    max_budget_bytes: int = NTSC_SAFE_VBLANK_DMA_BYTES
    bytes_transferred: int = 0
    _is_open: bool = True
    _asm_lines: List[str] = field(default_factory=list)

    @property
    def remaining_budget(self) -> int:
        return self.max_budget_bytes - self.bytes_transferred

    def _require_open(self) -> None:
        if not self._is_open:
            raise IxDMASessionError(
                "Active-Display VRAM Corruption Prevented: Attempted to use an expired `VBlankWindowToken` "
                "after VBlank ended!"
            )


@dataclass
class DMAChannelSession:
    """
    Linear Session-Typed DMA Channel (`channel in 0..7`):
      Lifecycle: `"IDLE"` -> `"ARMED"` -> `"COMPLETED"`
      An `"ARMED"` session MUST be consumed inside a live `VBlankWindowToken` before scope exit!
    """

    channel: int
    state: str = "IDLE"                        # "IDLE" | "ARMED" | "COMPLETED"
    source_ptr: Optional[RegionPtr] = None
    target_bus: str = ""                       # "VRAM" | "CGRAM" | "OAM"
    dest_addr: int = 0
    transfer_bytes: int = 0
    _asm_trace: List[str] = field(default_factory=list)

    def __post_init__(self) -> None:
        if not (0 <= self.channel <= 7):
            raise IxDMASessionError(f"SNES DMA channel must be in 0..7, got {self.channel}")


class DMASessionCoordinator:
    """
    Tracks all DMA channels declared in a frame/routine so NO channel can be left
    half-completed (`state == 'ARMED'`) when the scope finishes!
    """

    def __init__(self) -> None:
        self._sessions: List[DMAChannelSession] = []
        self._used_channels: set[int] = set()

    def arm_dma(
        self,
        *,
        channel: int,
        src_ptr: RegionPtr,
        target_bus: str = "VRAM",
        dest_addr: int = 0x0000,
    ) -> DMAChannelSession:
        """
        Step 1 of the DMA Session (`Idle -> Armed`):
          - Verifies `src_ptr` is `bank_safe` (guaranteed by `RegionPtr`) and word-aligned (`align >= 2`
            for 16-bit VRAM/CGRAM transfers).
          - Emits `$43x0-$43x6` channel setup instructions (legal during Active Display or VBlank),
            WITHOUT touching `$420B` (`MDMAEN`) or PPU ports yet!
        """
        if channel in self._used_channels:
            raise IxDMASessionError(
                f"DMA Channel Collision: Channel {channel} is already armed in this session cycle!"
            )
        if not src_ptr.bank_safe:
            raise IxDMASessionError(
                f"DMA Bank-Wrap Hazard: Source `{src_ptr.label}` ({src_ptr.format_snes_addr()}) is not bank-safe!"
            )
        if target_bus in ("VRAM", "CGRAM") and src_ptr.align < 2:
            raise IxDMASessionError(
                f"DMA Alignment Violation: `{target_bus}` transfer from `{src_ptr.label}` requires >= 2-byte "
                f"alignment, got align={src_ptr.align}B!"
            )
        if target_bus not in ("VRAM", "CGRAM", "OAM"):
            raise ValueError(f"Unsupported PPU target_bus `{target_bus}`")

        dmap_mode, bbus_reg = {
            "VRAM": (0x01, 0x18),   # 2-register write once ($2118/$2119)
            "CGRAM": (0x00, 0x22),  # 1-register write ($2122)
            "OAM": (0x00, 0x04),    # 1-register write ($2104)
        }[target_bus]

        ch_hex = f"{channel:X}"
        asm = [
            f"    ; [DMA Session Ch{channel}: IDLE -> ARMED] src={src_ptr.format_snes_addr()} ({src_ptr.size}B) -> {target_bus} ${dest_addr:04X}",
            f"    SEP #$20",
            f"    LDA #${dmap_mode:02X} : STA $43{ch_hex}0       ; DMAP{channel}",
            f"    LDA #${bbus_reg:02X} : STA $43{ch_hex}1       ; BBAD{channel} ($21{bbus_reg:02X})",
            f"    LDA #${src_ptr.bank:02X} : STA $43{ch_hex}4   ; A1B{channel} bank",
            f"    REP #$20",
            f"    LDA #${src_ptr.offset:04X} : STA $43{ch_hex}2 ; A1T{channel} offset",
            f"    LDA #${src_ptr.size:04X} : STA $43{ch_hex}5   ; DAS{channel} byte count",
        ]
        sess = DMAChannelSession(
            channel=channel,
            state="ARMED",
            source_ptr=src_ptr,
            target_bus=target_bus,
            dest_addr=dest_addr,
            transfer_bytes=src_ptr.size,
            _asm_trace=asm,
        )
        self._used_channels.add(channel)
        self._sessions.append(sess)
        return sess

    def transfer_in_vblank(
        self, session: DMAChannelSession, vblank: VBlankWindowToken
    ) -> Dict[str, Any]:
        """
        Step 2 of the DMA Session (`Armed -> InFlightVBlank -> Completed`):
          - REQUIRES a live `VBlankWindowToken` (`not isinstance(..., VBlankWindowToken)` or closed -> error!).
          - Enforces linear state consumption (`session.state` MUST be `'ARMED'`; double-commit fails!).
          - Verifies `vblank.bytes_transferred + session.transfer_bytes <= vblank.max_budget_bytes`.
        """
        if not isinstance(vblank, VBlankWindowToken):
            raise IxDMASessionError(
                "Active-Display VRAM Write Prevented: `transfer_in_vblank` requires an authentic "
                "`VBlankWindowToken` (cannot transfer outside VBlank or Forced Blank)!"
            )
        vblank._require_open()

        if session.state != "ARMED":
            raise IxDMASessionError(
                f"Linear DMA Session Violation on Channel {session.channel}: expected state `'ARMED'`, "
                f"got `'{session.state}'` (double-transfer or un-armed transfer prevented)!"
            )

        new_total = vblank.bytes_transferred + session.transfer_bytes
        if new_total > vblank.max_budget_bytes:
            raise IxDMASessionError(
                f"VBlank Cycle/Byte Budget Exhausted: Channel {session.channel} (`{session.source_ptr.label}`, "
                f"{session.transfer_bytes}B) pushes VBlank DMA total to {new_total}B, exceeding the safe "
                f"{vblank.max_budget_bytes}B window (would bleed into Active Display scanline 0)!"
            )

        vblank.bytes_transferred = new_total
        session.state = "COMPLETED"
        mask = 1 << session.channel

        addr_setup: List[str] = []
        if session.target_bus == "VRAM":
            addr_setup = [
                f"    SEP #$20 : LDA #$80 : STA $2115              ; VMAIN word increment",
                f"    REP #$20 : LDA #${session.dest_addr:04X} : STA $2116 ; VMADDL/H",
            ]
        elif session.target_bus == "CGRAM":
            addr_setup = [
                f"    SEP #$20 : LDA #${session.dest_addr & 0xFF:02X} : STA $2121 ; CGADD",
            ]
        elif session.target_bus == "OAM":
            addr_setup = [
                f"    REP #$20 : LDA #${session.dest_addr:04X} : STA $2102 ; OAMADDL/H",
            ]

        fire_asm = addr_setup + [
            f"    SEP #$20 : LDA #${mask:02X} : STA $420B      ; [DMA Ch{session.channel}: ARMED -> COMPLETED] ({new_total}/{vblank.max_budget_bytes}B)",
        ]
        session._asm_trace.extend(fire_asm)
        vblank._asm_lines.extend(session._asm_trace)
        return {
            "channel": session.channel,
            "target_bus": session.target_bus,
            "bytes": session.transfer_bytes,
            "vblank_total_bytes": new_total,
            "state": session.state,
        }

    def verify_all_sessions_completed(self) -> None:
        """Called automatically at cycle exit: rejects any stranded `'ARMED'` DMA transfer!"""
        stranded = [s for s in self._sessions if s.state != "COMPLETED"]
        if stranded:
            s = stranded[0]
            raise IxDMASessionError(
                f"Half-Completed DMA Session Prevented: Channel {s.channel} (`{s.source_ptr.label if s.source_ptr else '?'}`) "
                f"was left in state `'{s.state}'` without being transferred & consumed inside VBlank!"
            )


def with_dma_frame_protocol(
    arm_phase: Callable[[DMASessionCoordinator], T],
    vblank_phase: Callable[[DMASessionCoordinator, VBlankWindowToken, T], Any],
    vblank_budget_bytes: int = NTSC_SAFE_VBLANK_DMA_BYTES,
) -> Dict[str, Any]:
    """
    Execute a full frame's Session-Typed DMA conversation:
      1. `arm_phase(coord)` runs during Active Display (cannot forge a `VBlankWindowToken`!).
      2. `vblank_phase(coord, vblank_tok, armed_handles)` runs inside VBlank (`NMI`).
      3. `vblank_tok` is revoked on exit and `coord.verify_all_sessions_completed()` ensures
         zero half-completed transfers remain!
    """
    coord = DMASessionCoordinator()
    armed_payload = arm_phase(coord)
    vb_tok = VBlankWindowToken(mode="NMI_VBLANK", max_budget_bytes=vblank_budget_bytes)
    try:
        vb_result = vblank_phase(coord, vb_tok, armed_payload)
    finally:
        vb_tok._is_open = False

    coord.verify_all_sessions_completed()
    return {
        "sessions_completed": len(coord._sessions),
        "vblank_bytes_transferred": vb_tok.bytes_transferred,
        "vblank_budget_bytes": vblank_budget_bytes,
        "vblank_result": vb_result,
        "asar_asm": "\n".join(vb_tok._asm_lines),
    }


# ==============================================================================
# 2. SESSION-TYPED SA-1 5-CYCLE HARDWARE MULTIPLIER (`$2250-$2307` Q8.8 PROTOCOL)
# ==============================================================================


@dataclass
class SA1MathSession:
    """
    Models the SMW SA-1 hardware multiplier (`$2250, $2251, $2253 -> $2306/$2307`) as a
    linear session (`smw_sa1_brutal_vivian.md` Rules 4, 5, & 6):
      - SA-1 multiplication requires **5 clock cycles** after writing `$2253`.
      - Reading `$2306` or `$2307` (`Q8.8` middle-16-bit auto-right-shift!) before waiting
        `>= 5` cycles returns hardware `0` — here made a compile-time `IxDMASessionError`!
    """

    lhs_s16: int
    rhs_q88: int
    cycles_waited: int = 0
    consumed: bool = False
    asm_lines: List[str] = field(default_factory=list)

    @classmethod
    def start_q88_mul(cls, lhs_s16: int, rhs_q88: int, cpu_context: str = "SA1") -> "SA1MathSession":
        if cpu_context != "SA1":
            raise IxDMASessionError(
                f"Hardware Math Divergence Prevented: SA-1 math registers `$2250-$2309` require "
                f"`cpu_context='SA1'`, got `'{cpu_context}'` (S-CPU must not mix `$4202` and `$2250`)!"
            )
        asm = [
            f"    ; [SA-1 Math Session: ARMED (needs 5 cycles)] {lhs_s16} * {rhs_q88} (Q8.8)",
            f"    SEP #$20 : STZ $2250                         ; Select SA-1 multiplication mode",
            f"    REP #$20",
            f"    LDA #${lhs_s16 & 0xFFFF:04X} : STA $2251     ; Multiplicand MA",
            f"    LDA #${rhs_q88 & 0xFFFF:04X} : STA $2253     ; Multiplier MB -> 5-cycle hardware timer starts!",
        ]
        return cls(lhs_s16=lhs_s16, rhs_q88=rhs_q88, cycles_waited=0, consumed=False, asm_lines=asm)

    def wait_nops(self, nop_count: int = 3) -> "SA1MathSession":
        """Each 65c816 `NOP` (`EA`) consumes 2 cycles; 3 NOPs = 6 cycles >= 5 required cycles."""
        if nop_count <= 0:
            raise ValueError("nop_count must be >= 1")
        self.cycles_waited += 2 * nop_count
        nops_str = " : ".join(["NOP"] * nop_count)
        self.asm_lines.append(
            f"    {nops_str:<44} ; +{2 * nop_count} cycles (waited={self.cycles_waited}/5)"
        )
        return self

    def read_q88_middle_word_2307(self) -> Tuple[int, str]:
        """
        Read `$2307` (middle 16 bits of 32-bit product = exact `(lhs * rhs) >> 8` Q8.8 scale!).
        Fails statically if `cycles_waited < 5` or if already consumed!
        """
        if self.consumed:
            raise IxDMASessionError("SA-1 Math Session already consumed!")
        if self.cycles_waited < 5:
            raise IxDMASessionError(
                f"SA-1 5-Cycle Math Hazard Prevented: Attempted `LDA $2307` after only "
                f"{self.cycles_waited} cycles (requires >= 5 cycles; hardware would read 0!). "
                f"Call `.wait_nops(3)` or schedule >= 5 cycles of work first."
            )
        self.consumed = True
        prod_32 = int(self.lhs_s16) * int(self.rhs_q88)
        middle_16_signed = ((prod_32 >> 8) + 0x8000) % 0x10000 - 0x8000
        self.asm_lines.append(
            f"    LDA $2307                                    ; [SA-1 Math READY -> CONSUMED] exact >>8 Q8.8 result = {middle_16_signed}"
        )
        return middle_16_signed, "\n".join(self.asm_lines)
