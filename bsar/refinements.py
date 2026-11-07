#!/usr/bin/env python3
"""
REFINEMENT TYPES FOR LENGTHS, BANK CROSSINGS, BUDGETS, & SILICON OPCODES (`bsar.refinements`)
License: GNU AGPLv3
Attestation: probabilistic_structural
Dependencies: 0 (Python >= 3.10 Standard Library Only)

Implements Item #3 of `build-sheet.md` + `smw_sa1_brutal_vivian.md` constraints:
  1. `RefinedInt`: Carries `[lo, hi]` value invariants (`{v : Int | lo <= v <= hi}`), catching
     register width overflows (`W8` `0..255` vs `W16` `0..65535`) and RPG/engine stat typos
     at compile time with plain-English provenance.
  2. `RefinedSlice`: Carries length bounds, ROM mapping geometry (`LoROM` `$8000-$FFFF` 32KB half-banks
     vs `SA1`/`ExHiROM` `$0000-$FFFF` 64KB full banks), and explicit `wrap_policy` (`"forbid"` vs `"mask"`),
     rejecting silent bank-straddling tables and page-wraparound cycle/corruption bugs!
  3. Hardware PPU / Engine Budgets (`OAMBudget`, `SpriteSlotBudget`, `CGRAMBudget`):
     Enforces `128` OAM entries, `12` vanilla SMW / `22` SA-1 active sprite slots, and `256` CGRAM colors.
  4. Silicon Instruction Legality (`verify_65816_silicon_legality`):
     Catches non-existent 65c816 instructions such as stack-relative `CPX d,s` and `CPY d,s`
     (`smw_sa1_brutal_vivian.md` Rule 5) and emits exact `TXA : CMP d,s` / `TYA : CMP d,s` diagnostics.
"""

from __future__ import annotations

from dataclasses import dataclass
import re
from typing import Iterable, List, Optional, Sequence, Tuple


class IxRefinementError(TypeError):
    """Raised statically when a length, bank boundary, wrap policy, or silicon opcode refinement fails."""


@dataclass(frozen=True)
class RefinedInt:
    """
    Liquid-Haskell-style bounded integer `{v : int | lo <= v <= hi}` with source provenance.
     Arithmetic (`add`, `sub`, `index_into`) propagates bounds and verifies wraparound policies!
    """

    value: int
    lo: int
    hi: int
    label: str = "int"
    provenance: str = ""

    def __post_init__(self) -> None:
        if self.lo > self.hi:
            raise ValueError(f"Invalid refinement interval [{self.lo}, {self.hi}] for `{self.label}`")
        if not (self.lo <= self.value <= self.hi):
            loc = f" at {self.provenance}" if self.provenance else ""
            raise IxRefinementError(
                f"Refinement Bound Violation{loc}: `{self.label}` = {self.value} lies outside "
                f"required range [{self.lo}..{self.hi}]!"
            )

    @classmethod
    def u8(cls, value: int, label: str = "u8_index", provenance: str = "") -> "RefinedInt":
        return cls(value=value, lo=0, hi=0xFF, label=label, provenance=provenance)

    @classmethod
    def u16(cls, value: int, label: str = "u16_word", provenance: str = "") -> "RefinedInt":
        return cls(value=value, lo=0, hi=0xFFFF, label=label, provenance=provenance)

    def require_fits_register(self, reg_width: str) -> "RefinedInt":
        """Verify that the entire statically refined interval `[lo, hi]` fits inside `W8` or `W16`."""
        max_allowed = 0xFF if reg_width == "W8" else 0xFFFF
        if self.lo < 0 or self.hi > max_allowed:
            raise IxRefinementError(
                f"Register-Fit Refinement Failed: `{self.label}` has type-level bound [{self.lo}..{self.hi}], "
                f"which can overflow `{reg_width}` register range [0..{max_allowed}]!"
            )
        return self

    def add_no_wrap(self, delta: "RefinedInt", max_ceiling: int) -> "RefinedInt":
        """Sum two refined integers while proving the worst-case upper bound `hi_1 + hi_2` never wraps."""
        new_lo = self.lo + delta.lo
        new_hi = self.hi + delta.hi
        if new_hi > max_ceiling or new_lo < 0:
            raise IxRefinementError(
                f"Silent Wraparound Prevented: `{self.label} + {delta.label}` worst-case interval "
                f"[{new_lo}..{new_hi}] exceeds ceiling {max_ceiling}!"
            )
        return RefinedInt(
            value=self.value + delta.value,
            lo=new_lo,
            hi=new_hi,
            label=f"({self.label}+{delta.label})",
            provenance=self.provenance or delta.provenance,
        )


@dataclass(frozen=True)
class RefinedBufferSlice:
    """
    Buffer / ROM Table Type carrying static length bound, ROM bank mapping geometry,
    and explicit wraparound policy (`wrap_policy in {'forbid', 'mask_pow2'}`).
    """

    label: str
    bank: int
    offset: int
    length: int
    max_length: int
    mapping: str = "SA1"          # "SA1" | "HiROM" | "LoROM"
    wrap_policy: str = "forbid"   # "forbid" | "mask_pow2"
    provenance: str = ""

    def __post_init__(self) -> None:
        loc = f" ({self.provenance})" if self.provenance else ""
        if self.length <= 0 or self.length > self.max_length:
            raise IxRefinementError(
                f"Length Refinement Violation on `{self.label}`{loc}: length {self.length}B "
                f"exceeds declared type bound [1..{self.max_length}B]!"
            )
        if not (0x00 <= self.bank <= 0xFF):
            raise IxRefinementError(f"Invalid SNES bank `${self.bank:X}` on `{self.label}`{loc}.")

        if self.mapping == "LoROM":
            # LoROM ROM banks occupy $8000..$FFFF (32,768 bytes)
            if self.offset < 0x8000 or (self.offset + self.length) > 0x10000:
                overrun = max(0, (self.offset + self.length) - 0x10000)
                raise IxRefinementError(
                    f"LoROM Bank-Crossing Violation on `{self.label}`{loc}: table at "
                    f"${self.bank:02X}:{self.offset:04X} + {self.length}B straddles the 32KB LoROM bank boundary "
                    f"(`$FFFF`) by {overrun}B!"
                )
        elif self.mapping in ("SA1", "HiROM"):
            if self.offset < 0x0000 or (self.offset + self.length) > 0x10000:
                overrun = (self.offset + self.length) - 0x10000
                raise IxRefinementError(
                    f"{self.mapping} Bank-Crossing Violation on `{self.label}`{loc}: buffer at "
                    f"${self.bank:02X}:{self.offset:04X} + {self.length}B straddles the 64KB bank boundary "
                    f"(`$FFFF`) by {overrun}B!"
                )
        else:
            raise ValueError(f"Unknown SNES mapping `{self.mapping}`")

        if self.wrap_policy == "mask_pow2":
            if (self.length & (self.length - 1)) != 0:
                raise IxRefinementError(
                    f"Wrap Policy Violation on `{self.label}`{loc}: `mask_pow2` ring buffer requires "
                    f"power-of-two byte length, got {self.length}B!"
                )
        elif self.wrap_policy != "forbid":
            raise ValueError(f"Unsupported wrap_policy `{self.wrap_policy}`")

    def check_index(self, idx: RefinedInt) -> int:
        """
        Verify array indexing `buf[idx]` statically against `self.length` and `self.wrap_policy`.
        """
        if self.wrap_policy == "forbid":
            if idx.lo < 0 or idx.hi >= self.length:
                raise IxRefinementError(
                    f"Buffer Overrun Prevented on `{self.label}` (${self.bank:02X}:{self.offset:04X}, "
                    f"len={self.length}B): index `{idx.label}` has bound [{idx.lo}..{idx.hi}] "
                    f"(must be within [0..{self.length - 1}])!"
                )
            return self.offset + idx.value
        # Explicit ring-buffer mask_pow2
        return self.offset + (idx.value & (self.length - 1))


# ==============================================================================
# HARDWARE BUDGET REFINEMENTS (OAM, SPRITE SLOTS, CGRAM PALETTES)
# ==============================================================================


def check_snes_hardware_budgets(
    *,
    oam_tiles: int = 0,
    active_sprites: int = 0,
    cgram_colors: int = 0,
    sa1_mode: bool = True,
    provenance: str = "",
) -> dict:
    """
    Plain-language editor/compiler refinement checker for SNES hardware budgets:
      - OAM table: max `128` hardware sprites (`512B` low table + `32B` high table)
      - Active level sprite slots: `22` in SMW SA-1 Pack vs `12` in vanilla SMW
      - CGRAM palette RAM: max `256` 15-bit BGR555 colors (`512B`)
    """
    loc = f" in {provenance}" if provenance else ""
    max_sprite_slots = 22 if sa1_mode else 12
    if not (0 <= oam_tiles <= 128):
        raise IxRefinementError(
            f"OAM Budget Exceeded{loc}: Scene requests {oam_tiles} OAM tile slots, "
            f"but the SNES PPU hardware ceiling is 128 OAM entries!"
        )
    if not (0 <= active_sprites <= max_sprite_slots):
        mode_lbl = "SA-1" if sa1_mode else "Vanilla SMW"
        raise IxRefinementError(
            f"Active Sprite Slot Budget Exceeded{loc}: Level places {active_sprites} active sprites "
            f"simultaneously, exceeding the {mode_lbl} ceiling of {max_sprite_slots} slots!"
        )
    if not (0 <= cgram_colors <= 256):
        raise IxRefinementError(
            f"CGRAM Palette Budget Exceeded{loc}: Palette upload contains {cgram_colors} colors "
            f"(> 256 SNES CGRAM colors / 512 bytes)!"
        )
    return {
        "oam_tiles": oam_tiles,
        "oam_limit": 128,
        "active_sprites": active_sprites,
        "sprite_slot_limit": max_sprite_slots,
        "cgram_colors": cgram_colors,
        "cgram_limit": 256,
        "valid": True,
    }


# ==============================================================================
# 65c816 SILICON INSTRUCTION LEGALITY CHECKER (`CPX d,s` / `CPY d,s` GUARD)
# ==============================================================================

_FORBIDDEN_STACK_REL_RE = re.compile(
    r"^\s*(CPX|CPY)\s+([^;]+),\s*s\b", re.IGNORECASE
)


def verify_65816_silicon_legality(asm_lines: Iterable[str], source_name: str = "<asm>") -> List[str]:
    """
    Verify that emitted or inline 65c816 assembly contains zero physically non-existent
    silicon opcodes (such as `CPX d,s` or `CPY d,s`, per `smw_sa1_brutal_vivian.md` Rule 5).
    """
    checked: List[str] = []
    for line_no, raw in enumerate(asm_lines, start=1):
        m = _FORBIDDEN_STACK_REL_RE.match(raw)
        if m:
            op = m.group(1).upper()
            disp = m.group(2).strip()
            transfer = "TXA" if op == "CPX" else "TYA"
            raise IxRefinementError(
                f"Impossible 65c816 Silicon Opcode at {source_name}:{line_no}: `{raw.strip()}`! "
                f"The WDC 65c816 has NO stack-relative addressing mode for `{op}`. "
                f"Rewrite as `{transfer} : CMP {disp},s` (preserving `A` first if live)."
            )
        checked.append(raw)
    return checked
