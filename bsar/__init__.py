"""
🅱💲🅰-R: Hypercubic Compiler (`bsar`)
License: GNU AGPLv3
Attestation: probabilistic_structural

Unites:
  🅱 — Binary 2^k Cayley-Dickson (16D Sedenions & 32D Pathions) + Lua Dynamic Frames
  💲 — Sedenion Zero-Divisor Expense Slasher (64-byte L1-cache-line Q8.8 registers)
  🅰 — Asar 3-Pass Deterministic Hilbert CSR/CSC Slab Assembler + RATS SHA-256 Seal
  -R — Copy-on-Modify Tidyverse Pipe Verbs + Carrollian Middle-Term Projection (∃m)
"""

from .asar_zd_microbench import (
    pack_asar_rats_block,
    run_asar_q88_zero_divisor_microbench,
    verify_asar_rats_block,
)
from .cd_q88 import (
    BOX_KITE_COUNT_16D,
    L1_CACHE_LINE_BYTES,
    LUT_32D_BYTES,
    PathionQ88,
    PorchZeroDivisorGate,
    S32BitPackedLUT,
    associator_q88,
    cd_mult_q88,
    enumerate_sedenion_box_kites,
    float_to_q88,
    fold_ast_q88,
    q88_to_float,
)
from .hardware_pin import pin_host_hardware
from .hypercube import (
    BsaRHypercubeCompiler,
    EpistemicCellState,
    LuaDynamicRecord,
    RPipe,
    canonical_sha256,
    hilbert_nd_to_d,
)

__version__ = "0.2.0"
BANNER = "🅱💲🅰-R: Hypercubic Compiler v0.2.0"

__all__ = [
    "BANNER",
    "__version__",
    "BOX_KITE_COUNT_16D",
    "L1_CACHE_LINE_BYTES",
    "LUT_32D_BYTES",
    "PathionQ88",
    "PorchZeroDivisorGate",
    "S32BitPackedLUT",
    "associator_q88",
    "cd_mult_q88",
    "enumerate_sedenion_box_kites",
    "float_to_q88",
    "fold_ast_q88",
    "q88_to_float",
    "BsaRHypercubeCompiler",
    "EpistemicCellState",
    "LuaDynamicRecord",
    "RPipe",
    "canonical_sha256",
    "hilbert_nd_to_d",
    "pin_host_hardware",
    "pack_asar_rats_block",
    "verify_asar_rats_block",
    "run_asar_q88_zero_divisor_microbench",
]
