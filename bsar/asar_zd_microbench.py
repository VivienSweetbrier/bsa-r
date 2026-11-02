#!/usr/bin/env python3
"""
ASAR-STYLE 3-PASS BIT-EXACT Q8.8 ZERO-DIVISOR MICROBENCH (`bsar.asar_zd_microbench`)
License: GNU AGPLv3
Attestation: probabilistic_structural

Honors the SNES `Asar` 3-pass deterministic assembler invariant (Alcaro / RPGHacker /
KungFuFurby) directly over `64-byte` `Q8.8` `16D` Sedenion & `32D` Pathion zero divisors:

  - Pass 0 (Symbol & Blade Ordinal Discovery):
      Enumerates all 7 Sedenion Box-Kites (42 primitive assessors, 168 |PSL(2,7)|
      directed zero-divisor edges), 1 native 32D Pathion Sand Mandala zero divisor
      `(e_1 + e_18) * (e_4 - e_23)`, and 8 Q8.8 distributive Porch signal+bloat probes,
      assigning deterministic byte offsets (`0..176 * 64`) with zero forward-reference ambiguity.
  - Pass 1 (Binary Q8.8 Slab Assembly + SNES `RATS` Tag):
      Evaluates every 64-byte Q8.8 product and seals the slab behind an authentic 8-byte
      SNES `RATS` header: `b"STAR" + uint16_le(len - 1) + uint16_le(~(len - 1) & 0xFFFF)`.
  - Pass 2 (Independent Re-Assembly & Zero Label/Byte Drift Verification):
      Re-executes the entire assembly from a fresh `S32BitPackedLUT` instance and asserts:
        1. `pass1_rats_slab == pass2_rats_slab` (`pass_to_pass_byte_drift == 0`),
        2. `168 / 168` Sedenion annihilation edges == literal `b"\\x00" * 64`,
        3. Native `32D` Sand Mandala == literal `b"\\x00" * 64`,
        4. `8 / 8` Porch probes satisfy `G_porch * (sig + bloat) == G_porch * sig` across all 64 bytes,
        5. Valid `STAR` RATS bitwise complement (`size_m1 ^ inv_size_m1 == 0xFFFF`).
"""

from __future__ import annotations

import hashlib
import struct
import time
from typing import Any, Dict, List, Tuple

from .cd_q88 import (
    L1_CACHE_LINE_BYTES,
    LUT_32D_BYTES,
    PathionQ88,
    PorchZeroDivisorGate,
    Q88_ONE,
    S32BitPackedLUT,
    cd_mult_q88,
    enumerate_sedenion_box_kites,
)

RATS_MAGIC = b"STAR"


def pack_asar_rats_block(payload: bytes) -> bytes:
    """
    Pack binary payload behind an authentic 8-byte SNES `Asar` RATS protection tag:
      offset 0..3: ASCII "STAR"
      offset 4..5: uint16 little-endian `(len(payload) - 1)`
      offset 6..7: uint16 little-endian bitwise inverse `~(len(payload) - 1) & 0xFFFF`
    """
    if not (1 <= len(payload) <= 65536):
        raise ValueError(f"RATS payload must be 1..65536 bytes, got {len(payload)}")
    size_m1 = len(payload) - 1
    inv_size_m1 = (~size_m1) & 0xFFFF
    return RATS_MAGIC + struct.pack("<HH", size_m1, inv_size_m1) + payload


def verify_asar_rats_block(blob: bytes) -> Dict[str, Any]:
    if len(blob) < 8 or blob[:4] != RATS_MAGIC:
        return {"valid": False, "reason": "missing_STAR_magic"}
    size_m1, inv_size_m1 = struct.unpack("<HH", blob[4:8])
    complement_ok = (size_m1 ^ inv_size_m1) == 0xFFFF
    expected_len = size_m1 + 1
    actual_len = len(blob) - 8
    return {
        "valid": bool(complement_ok and expected_len == actual_len),
        "header_hex": blob[:8].hex(),
        "size_m1": size_m1,
        "inv_size_m1": inv_size_m1,
        "xor_check_hex": f"0x{size_m1 ^ inv_size_m1:04x}",
        "payload_bytes": actual_len,
    }


def _discover_pass0_symbols(lut: S32BitPackedLUT) -> List[Dict[str, Any]]:
    """
    Pass 0: Enumerate all 168 directed 16D Sedenion zero-divisor pairs in canonical order,
    followed by 1 native 32D Sand Mandala pair and 8 Q8.8 distributive Porch probes.
    """
    symbols: List[Dict[str, Any]] = []

    for i in range(1, 8):
        for j in range(8, 16):
            for k in range(1, 8):
                if i == k:
                    continue
                for l in range(8, 16):
                    if (i ^ k) == (j ^ l):
                        s_ik = lut.sign(i, k)
                        s_jl = lut.sign(j, l)
                        s_il = lut.sign(i, l)
                        s_jk = lut.sign(j, k)
                        for sgn in (-1, 1):
                            if (s_ik + sgn * s_jl == 0) and (sgn * s_il + s_jk == 0):
                                symbols.append(
                                    {
                                        "kind": "SEDENION_16D_ZD",
                                        "label": f"ZD16_e{i}_p_e{j}__x__e{k}_{'p' if sgn > 0 else 'm'}_e{l}",
                                        "offset": len(symbols) * L1_CACHE_LINE_BYTES,
                                        "params": (i, j, 1, k, l, sgn),
                                    }
                                )

    # Native 32D Pathion Sand Mandala zero divisor: (e_1 + e_18) * (e_4 - e_23) == 0
    symbols.append(
        {
            "kind": "PATHION_32D_SAND_MANDALA",
            "label": "ZD32_e1_p_e18__x__e4_m_e23",
            "offset": len(symbols) * L1_CACHE_LINE_BYTES,
            "params": (1, 18, 1, 4, 23, -1),
        }
    )

    # 8 deterministic fractional Q8.8 Porch signal+bloat residual probes (residual == 0x00 * 64)
    probe_specs = [
        (0, 1.25, 9.50),
        (1, -3.75, 14.25),
        (2, 6.125, -8.875),
        (3, -0.50, -19.00),
        (4, 11.00, 4.375),
        (5, -7.25, 12.625),
        (6, 2.875, -15.50),
        (7, 8.50, 11.125),
    ]
    for p_idx, sig_f, bloat_f in probe_specs:
        symbols.append(
            {
                "kind": "PORCH_DISTRIBUTIVE_RESIDUAL",
                "label": f"PORCH_BK{(p_idx % 7) + 1}_RESIDUAL_{p_idx}",
                "offset": len(symbols) * L1_CACHE_LINE_BYTES,
                "params": (p_idx % 7, sig_f, bloat_f),
            }
        )

    return symbols


def _assemble_slab_pass(
    symbols: List[Dict[str, Any]], lut: S32BitPackedLUT
) -> Tuple[bytes, Dict[str, int]]:
    """
    Assemble the exact binary slab of 64-byte Q8.8 results from Pass-0 symbol descriptors.
    Every single record in this slab MUST evaluate to literal `0x00 * 64` if exact Q8.8
    zero-divisor annihilation and distributivity hold with zero rounding drift!
    """
    chunks: List[bytes] = []
    stats = {
        "sedenion_16d_exact_zero": 0,
        "pathion_32d_exact_zero": 0,
        "porch_residual_exact_zero": 0,
    }
    zero_64b = b"\x00" * L1_CACHE_LINE_BYTES

    for sym in symbols:
        kind = sym["kind"]
        if kind in ("SEDENION_16D_ZD", "PATHION_32D_SAND_MANDALA"):
            li, lj, lsgn, rk, rl, rsgn = sym["params"]
            u = PathionQ88.basis(li, Q88_ONE) + PathionQ88.basis(lj, lsgn * Q88_ONE)
            v = PathionQ88.basis(rk, Q88_ONE) + PathionQ88.basis(rl, rsgn * Q88_ONE)
            out_64b = cd_mult_q88(u, v, lut=lut).to_bytes()
            if out_64b == zero_64b:
                if kind == "SEDENION_16D_ZD":
                    stats["sedenion_16d_exact_zero"] += 1
                else:
                    stats["pathion_32d_exact_zero"] += 1
            chunks.append(out_64b)
        elif kind == "PORCH_DISTRIBUTIVE_RESIDUAL":
            bk_idx, sig_f, bloat_f = sym["params"]
            gate = PorchZeroDivisorGate(box_kite_index=bk_idx)
            mixed = gate.encode_signal_and_bloat(sig_f, bloat_f)
            clean = gate.encode_signal_and_bloat(sig_f, 0.0)
            r_mixed = cd_mult_q88(gate.gate_blade, mixed, lut=lut)
            r_clean = cd_mult_q88(gate.gate_blade, clean, lut=lut)
            residual_64b = (r_mixed - r_clean).to_bytes()
            if residual_64b == zero_64b:
                stats["porch_residual_exact_zero"] += 1
            chunks.append(residual_64b)

    raw_payload = b"".join(chunks)
    return pack_asar_rats_block(raw_payload), stats


def run_asar_q88_zero_divisor_microbench(
    timing_iterations: int = 2000,
) -> Dict[str, Any]:
    """
    Execute the full 3-Pass Asar-deterministic Q8.8 Zero-Divisor verification & latency microbench.
    """
    t_lut0 = time.perf_counter()
    lut_pass1 = S32BitPackedLUT()
    lut_pass2 = S32BitPackedLUT()
    lut_bootstrap_ms = (time.perf_counter() - t_lut0) * 1000.0
    assert lut_pass1.packed_bytes == lut_pass2.packed_bytes

    t_asm0 = time.perf_counter()
    # Pass 0: Symbol & ordinal discovery
    symbols_p0 = _discover_pass0_symbols(lut_pass1)

    # Pass 1: Initial binary Q8.8 RATS slab emission
    rats_pass1, stats_p1 = _assemble_slab_pass(symbols_p0, lut_pass1)

    # Pass 2: Independent symbol re-discovery + binary re-assembly + zero byte-drift assert
    symbols_p2 = _discover_pass0_symbols(lut_pass2)
    rats_pass2, stats_p2 = _assemble_slab_pass(symbols_p2, lut_pass2)
    three_pass_asm_ms = (time.perf_counter() - t_asm0) * 1000.0

    symbol_offset_drift = sum(
        abs(a["offset"] - b["offset"]) for a, b in zip(symbols_p0, symbols_p2)
    )
    byte_drift = sum(1 for a, b in zip(rats_pass1, rats_pass2) if a != b) + abs(
        len(rats_pass1) - len(rats_pass2)
    )
    lut_sha256 = hashlib.sha256(lut_pass1.packed_bytes).hexdigest()
    rats_sha256 = hashlib.sha256(rats_pass2).hexdigest()
    rats_info = verify_asar_rats_block(rats_pass2)

    # Microbenchmark hot-L1-cache 64-byte Q8.8 zero-divisor product latency (p50 / p95 / mean µs)
    u32 = PathionQ88.basis(1, Q88_ONE) + PathionQ88.basis(18, Q88_ONE)
    v32 = PathionQ88.basis(4, Q88_ONE) - PathionQ88.basis(23, Q88_ONE)

    # Warm L1 cache
    for _ in range(32):
        cd_mult_q88(u32, v32, lut=lut_pass2)

    samples_us: List[float] = []
    batch = 20
    batches = max(10, timing_iterations // batch)
    for _ in range(batches):
        t0 = time.perf_counter_ns()
        for _ in range(batch):
            cd_mult_q88(u32, v32, lut=lut_pass2)
        dt_us = (time.perf_counter_ns() - t0) / 1000.0 / batch
        samples_us.append(dt_us)

    samples_us.sort()
    p50_us = samples_us[len(samples_us) // 2]
    p95_us = samples_us[min(len(samples_us) - 1, int(len(samples_us) * 0.95))]
    mean_us = sum(samples_us) / len(samples_us)

    bk_meta = enumerate_sedenion_box_kites(lut_pass2)

    return {
        "microbench_id": "ASAR_3PASS_Q88_ZD_MICROBENCH",
        "asar_three_pass_deterministic": bool(
            symbol_offset_drift == 0
            and byte_drift == 0
            and rats_info["valid"]
            and stats_p2["sedenion_16d_exact_zero"] == 168
            and stats_p2["pathion_32d_exact_zero"] == 1
            and stats_p2["porch_residual_exact_zero"] == 8
        ),
        "pass0_symbol_count": len(symbols_p0),
        "pass1_to_pass2_symbol_offset_drift": symbol_offset_drift,
        "pass1_to_pass2_byte_drift": byte_drift,
        "rats_header": rats_info,
        "rats_slab_total_bytes": len(rats_pass2),
        "rats_slab_sha256": rats_sha256,
        "s32_lut_128b_sha256": lut_sha256,
        "state_vector_bytes": L1_CACHE_LINE_BYTES,
        "s32_lut_bytes": LUT_32D_BYTES,
        "box_kite_count": bk_meta["box_kite_count"],
        "sedenion_16d_annihilation_verified": f"{stats_p2['sedenion_16d_exact_zero']}/168",
        "pathion_32d_sand_mandala_verified": f"{stats_p2['pathion_32d_exact_zero']}/1",
        "porch_distributive_probes_verified": f"{stats_p2['porch_residual_exact_zero']}/8",
        "latency_single_64b_zd_mult_p50_us": round(p50_us, 3),
        "latency_single_64b_zd_mult_p95_us": round(p95_us, 3),
        "latency_single_64b_zd_mult_mean_us": round(mean_us, 3),
        "three_pass_full_assembly_ms": round(three_pass_asm_ms, 2),
        "first_principles_lut_dual_bootstrap_ms": round(lut_bootstrap_ms, 2),
    }
