#!/usr/bin/env python3
"""
HOSTILE & DETERMINISTIC TEST SUITE FOR `bsar` (🅱💲🅰-R: Hypercubic Compiler v0.2.0)
License: GNU AGPLv3
Attestation: probabilistic_structural
"""

from __future__ import annotations

import copy
from pathlib import Path
import sys
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))

from bsar import (
    BOX_KITE_COUNT_16D,
    BsaRHypercubeCompiler,
    EpistemicCellState,
    L1_CACHE_LINE_BYTES,
    LUT_32D_BYTES,
    LuaDynamicRecord,
    PathionQ88,
    PorchZeroDivisorGate,
    S32BitPackedLUT,
    associator_q88,
    cd_mult_q88,
    enumerate_sedenion_box_kites,
    fold_ast_q88,
    pack_asar_rats_block,
    pin_host_hardware,
    run_asar_q88_zero_divisor_microbench,
    verify_asar_rats_block,
)
from bsar.chore_bench import (
    benchmark_chore5_public_multiagent_traces,
    pin_tokenizer_metadata,
    run_all_benchmarks_and_export,
)


class TestBsaRHypercubicCompiler(unittest.TestCase):
    def test_l1_cache_line_footprints_and_binary_roundtrip(self) -> None:
        lut = S32BitPackedLUT()
        self.assertEqual(len(lut.packed_bytes), LUT_32D_BYTES)  # 128 bytes == 2 L1 cache lines
        p = PathionQ88.from_floats([float(i - 16) * 0.25 for i in range(32)])
        raw = p.to_bytes()
        self.assertEqual(len(raw), L1_CACHE_LINE_BYTES)  # 64 bytes == 1 L1 cache line
        self.assertEqual(PathionQ88.from_bytes(raw), p)

    def test_pinned_hardware_telemetry_and_l1d_ratio(self) -> None:
        hw = pin_host_hardware()
        self.assertTrue(bool(hw["cpu_model"]))
        self.assertGreaterEqual(hw["l1d_per_core_bytes"], 16384)
        self.assertEqual(hw["bsar_kernel_total_bytes"], 192)
        self.assertFalse(hw["gpu_required"])
        self.assertLess(hw["bsar_pct_of_single_core_l1d"], 2.0)

    def test_asar_three_pass_q88_zero_divisor_microbench_and_rats_seal(self) -> None:
        rats_blob = pack_asar_rats_block(b"\x00" * 64)
        info = verify_asar_rats_block(rats_blob)
        self.assertTrue(info["valid"])
        self.assertEqual(info["xor_check_hex"], "0xffff")
        self.assertEqual(info["payload_bytes"], 64)

        zd = run_asar_q88_zero_divisor_microbench(timing_iterations=200)
        self.assertTrue(zd["asar_three_pass_deterministic"])
        self.assertEqual(zd["pass0_symbol_count"], 177)
        self.assertEqual(zd["pass1_to_pass2_symbol_offset_drift"], 0)
        self.assertEqual(zd["pass1_to_pass2_byte_drift"], 0)
        self.assertEqual(zd["sedenion_16d_annihilation_verified"], "168/168")
        self.assertEqual(zd["pathion_32d_sand_mandala_verified"], "1/1")
        self.assertEqual(zd["porch_distributive_probes_verified"], "8/8")

    def test_sedenion_box_kites_and_native_32d_sand_mandala_exact_zero(self) -> None:
        cat = enumerate_sedenion_box_kites()
        self.assertEqual(cat["box_kite_count"], BOX_KITE_COUNT_16D)  # 7
        self.assertEqual(cat["active_assessor_count"], 42)
        self.assertEqual(cat["directed_annihilation_edges"], 168)

        u16 = PathionQ88.basis(1) + PathionQ88.basis(10)
        v16 = PathionQ88.basis(4) - PathionQ88.basis(15)
        self.assertEqual(cd_mult_q88(u16, v16).to_bytes(), b"\x00" * 64)

        u32 = PathionQ88.basis(1) + PathionQ88.basis(18)
        v32 = PathionQ88.basis(4) - PathionQ88.basis(23)
        self.assertEqual(cd_mult_q88(u32, v32).to_bytes(), b"\x00" * 64)

    def test_porch_zero_divisor_distributive_signal_lock_and_clutch(self) -> None:
        gate = PorchZeroDivisorGate(box_kite_index=2)
        noisy = gate.encode_signal_and_bloat(signal_scalar=4.5, bloat_amplitude=-11.25)
        clean = gate.encode_signal_and_bloat(signal_scalar=4.5, bloat_amplitude=0.0)

        res_noisy = gate.filter_with_clutch(noisy)
        res_clean = gate.filter_with_clutch(clean)

        self.assertEqual(res_noisy["filtered_64b"], res_clean["filtered_64b"])
        self.assertEqual(PathionQ88.from_bytes(res_noisy["clutch_rollback_64b"]), noisy)

        escapes = gate.seven_box_kite_escapes()
        self.assertEqual(len(escapes), 7)
        self.assertTrue(all(e["residual_is_exact_zero"] for e in escapes))

    def test_non_associativity_and_broken_alternativity_on_ast_folds(self) -> None:
        assoc = associator_q88(PathionQ88.basis(1), PathionQ88.basis(2), PathionQ88.basis(4))
        self.assertFalse(assoc.is_exact_zero())

        h_ab_c = fold_ast_q88((("grep", "filter"), "summarize")).to_bytes()
        h_a_bc = fold_ast_q88(("grep", ("filter", "summarize"))).to_bytes()
        h_ba_c = fold_ast_q88((("filter", "grep"), "summarize")).to_bytes()
        self.assertNotEqual(h_ab_c, h_a_bc)
        self.assertNotEqual(h_ab_c, h_ba_c)

        h_aa_b = fold_ast_q88((("retry", "retry"), "commit")).to_bytes()
        h_a_ab = fold_ast_q88(("retry", ("retry", "commit"))).to_bytes()
        self.assertNotEqual(h_aa_b, h_a_ab)

    def test_three_pass_hypercube_determinism_o1_index_and_rpipe_immutability(self) -> None:
        comp = BsaRHypercubeCompiler(axes=("pillar", "tool", "mediator"), name="unit_cube")
        r1 = LuaDynamicRecord("N1", attrs={"owner": "hermes"})
        r1.add_cell({"pillar": "ALPHA", "tool": "grep", "mediator": "M1"}, weight=2.5, cluster_id="C1")
        r1.add_cell({"pillar": "ALPHA", "tool": "grep", "mediator": "M2"}, weight=1.5, cluster_id="C1")
        r2 = LuaDynamicRecord("N2", attrs={"owner": "sock"})
        r2.add_cell({"pillar": "BETA", "tool": "sql", "mediator": "M1"}, weight=3.0, cluster_id="C2")
        comp.register(r1)
        comp.register(r2)

        slab1 = comp.compile_three_pass()
        slab2 = comp.compile_three_pass()
        self.assertEqual(slab1["rats_sha256"], slab2["rats_sha256"])

        base_pipe = BsaRHypercubeCompiler.pipe(slab1)
        snap = copy.deepcopy(base_pipe.rows)

        idx_slice = base_pipe.filter_eq(pillar="ALPHA", tool="grep")
        lin_slice = base_pipe.filter(lambda r: r["pillar"] == "ALPHA" and r["tool"] == "grep")
        self.assertEqual(idx_slice.rows, lin_slice.rows)

        proj = idx_slice.eliminate_axis("mediator", key_axes=("record_id", "pillar", "tool"))
        self.assertEqual(len(proj), 1)
        self.assertEqual(proj.rows[0]["mediator"], EpistemicCellState.PROJECTED_STAR.value)
        self.assertEqual(sorted(proj.rows[0]["expanded_mediator"]), ["M1", "M2"])
        self.assertEqual(base_pipe.rows, snap)

    def test_public_multiagent_traces_sha256_and_compression(self) -> None:
        count_fn, tok_meta = pin_tokenizer_metadata(prefer_o200k=True)
        self.assertTrue(bool(tok_meta["bpe_canary_sha256"]))
        c5 = benchmark_chore5_public_multiagent_traces(count_fn)
        self.assertTrue(c5["manifest_all_sha256_verified"])
        self.assertEqual(set(c5["frameworks"].keys()), {"langchain", "crewai", "autogen"})
        self.assertGreater(c5["compression_ratio_x"], 400.0)
        sum_naive = sum(c5["frameworks"][k]["naive_input_tokens"] for k in ("langchain", "crewai", "autogen"))
        sum_standalone_bsar = sum(c5["frameworks"][k]["bsar_input_tokens"] for k in ("langchain", "crewai", "autogen"))
        self.assertEqual(sum_naive, c5["naive_input_tokens"])
        # Unified 4D hypercube rollup eliminates duplicate table headers across the 3 frameworks
        self.assertLessEqual(c5["bsar_input_tokens"], sum_standalone_bsar)

    def test_end_to_end_benchmark_and_hud_export_fast_mode(self) -> None:
        out_dir = Path(__file__).resolve().parent.parent / "dist_test_tmp"
        report = run_all_benchmarks_and_export(out_dir, prefer_o200k=False)
        self.assertGreater(report["headline_summary"]["overall_token_reduction_pct"], 80.0)
        self.assertTrue((out_dir / "index.html").exists())
        self.assertTrue((out_dir / "bsar_benchmark_metrics.csv").exists())
        self.assertTrue((out_dir / "cerebral_valley_metrics.csv").exists())
        for f in out_dir.iterdir():
            f.unlink()
        out_dir.rmdir()


if __name__ == "__main__":
    unittest.main(verbosity=2)
