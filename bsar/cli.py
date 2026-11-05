#!/usr/bin/env python3
"""
CLEAN `bsar` CLI ENTRYPOINT (`python -m bsar ...` / `bsar ...`)
Official Banner: 🅱💲🅰-R: Hypercubic Compiler & Algebraic Workbench
License: GNU AGPLv3
"""

from __future__ import annotations

import argparse
import json
from pathlib import Path
import shutil
import sys

from . import BANNER
from .asar_zd_microbench import run_asar_q88_zero_divisor_microbench
from .cd_q88 import (
    GLOBAL_S32_LUT,
    L1_CACHE_LINE_BYTES,
    LUT_32D_BYTES,
    enumerate_sedenion_box_kites,
    fold_ast_q88,
)
from .hardware_pin import pin_host_hardware


def _configure_utf8_stdout() -> None:
    if hasattr(sys.stdout, "reconfigure"):
        try:
            sys.stdout.reconfigure(encoding="utf-8")
        except Exception:
            pass


def _parse_gamma(gamma_str: str | None, level: int) -> tuple[int, ...]:
    if not gamma_str:
        return (-1,) * level
    parts = [int(tok.strip()) for tok in gamma_str.split(",") if tok.strip()]
    if len(parts) != level or any(p not in (-1, 1) for p in parts):
        raise ValueError(f"--gamma must supply {level} comma-separated values in {{-1, +1}}")
    return tuple(parts)


def main(argv: list[str] | None = None) -> int:
    _configure_utf8_stdout()
    parser = argparse.ArgumentParser(
        prog="bsar",
        description=(
            f"{BANNER} — Zero-Dependency 3-Pass Hilbert Hypercubes, Exact Z/Q/F_p + 64B Q8.8 "
            "Cayley-Dickson Algebras, Relation Graphs, Nonassociative AST Probes, & Group Rings"
        ),
    )
    sub = parser.add_subparsers(dest="cmd")

    sub.add_parser("info", help="Display pinned CPU/L1D hardware layout and Box-Kite invariants")
    sub.add_parser("boxkites", help="Dump all 7 16D Sedenion Box-Kites (42 assessors, 168 annihilation edges)")
    sub.add_parser("zd-bench", help="Run Asar-style 3-pass bit-exact Q8.8 zero-divisor microbench + STAR RATS check")

    p_bench = sub.add_parser("bench", help="Run real-world + public multi-agent trace benchmarks & build HUD + CSV")
    p_bench.add_argument(
        "--out-dir",
        default=str(Path(__file__).resolve().parent.parent / "dist"),
        help="Output directory for JSON, CSV, and interactive HTML HUD",
    )
    p_bench.add_argument(
        "--sync-docs",
        action="store_true",
        help="Also copy exported CSV, JSON, and HUD HTML into docs/compiler-hud/",
    )

    p_math = sub.add_parser(
        "math",
        help="Run exact mathematical probes (Cayley-Dickson structure, manifolds, relation graphs, identities, group rings)",
    )
    math_sub = p_math.add_subparsers(dest="math_cmd")

    math_sub.add_parser(
        "calibrate",
        help="Run regression calibration suite against published results (Wilmot, Moreno/Reggiani/Koebisu, Guterman-Zhilina, Promislow/Gardam)",
    )

    p_rel = math_sub.add_parser(
        "relations",
        help="Compile 3-pass Hilbert sparse relation-graph hypercube (zero-divisor, commutativity, mutual alternativity)",
    )
    p_rel.add_argument("--level", type=int, default=4, help="Cayley-Dickson level n (dim = 2^n, default 4 = 16D)")
    p_rel.add_argument("--gamma", type=str, default=None, help="Comma-separated doubling signs in {-1,+1}, e.g. '-1,-1,-1,1'")

    p_id = math_sub.add_parser(
        "identities",
        help="Probe nonassociative identities across 2^n-ions (or a specific signature / prime characteristic)",
    )
    p_id.add_argument("--max-level", type=int, default=5, help="Sweep levels 0..max_level (default 5 = up to 32D Pathions)")
    p_id.add_argument("--identity", type=str, default=None, help="Named identity to test on a single algebra (e.g. left_alternativity, flexibility)")
    p_id.add_argument("--level", type=int, default=4, help="Single algebra level when --identity is specified")
    p_id.add_argument("--gamma", type=str, default=None, help="Optional split signature when --identity is specified")
    p_id.add_argument("--mod", type=int, default=None, help="Optional prime modulus p for F_p probe")

    p_ker = math_sub.add_parser(
        "annihilator",
        help="Compute exact right/left annihilator ker(L_x) or ker(R_x) over Q or F_p for sparse basis coordinates",
    )
    p_ker.add_argument("--level", type=int, default=5, help="Cayley-Dickson level n (dim = 2^n, default 5 = 32D Pathions)")
    p_ker.add_argument("--gamma", type=str, default=None, help="Optional comma-separated signature in {-1,+1}^n")
    p_ker.add_argument("--mod", type=int, default=None, help="Optional prime modulus p")
    p_ker.add_argument(
        "--coords",
        type=str,
        default="1:1,18:1",
        help="Sparse index:coeff pairs, e.g. '1:1,18:1' for e_1 + e_18",
    )
    p_ker.add_argument("--side", choices=("right", "left"), default="right", help="Annihilator side")

    p_gr = math_sub.add_parser(
        "groupring",
        help="Compile support-product multiplicity hypercube & char-0 vs char-p annihilator check in torsion-free Promislow group P",
    )
    p_gr.add_argument(
        "--words",
        type=str,
        default=None,
        help="Comma-separated words in a,b,A,B (defaults to Promislow's 14-element non-UP set)",
    )

    p_r4 = math_sub.add_parser(
        "round4",
        help="Run Navier-Stokes Round-4 shell dispersion Theta, OutwardInterval Stiefel V_2(R^7) certification, T^3 Bloch-Floquet char-0 proofs, & optional Z3/SymPy checks",
    )
    p_r4.add_argument(
        "--angle",
        type=float,
        default=0.73,
        help="Continuous geodesic rotation angle (radians) on Stiefel V_2(R^7) for OutwardInterval certification",
    )
    p_r4.add_argument(
        "--words",
        type=str,
        default=None,
        help="Optional comma-separated Promislow group words for unbounded-support T^3 Bloch-Floquet audit",
    )

    p_fsm = math_sub.add_parser(
        "fsm",
        help="Extract minimal implicit deterministic state machines via coalgebraic bisimulation (Promislow P -> V_4 & Sedenion 42 -> 7 Box-Kite modes)",
    )
    p_fsm.add_argument(
        "--mermaid",
        action="store_true",
        help="Include Mermaid stateDiagram-v2 blueprints in the JSON output",
    )

    math_sub.add_parser(
        "ixasm",
        help="Run Atkey Indexed Monad (IxAsm) 65c816 + BSA-R Q8.8 Processor-Flag Type-State Verifier & RATS Assembler",
    )

    args = parser.parse_args(argv)
    if args.cmd in (None, "info"):
        bk = enumerate_sedenion_box_kites()
        hw = pin_host_hardware()
        info = {
            "compiler": BANNER,
            "pinned_hardware": hw,
            "pathion_32d_q88_bytes": L1_CACHE_LINE_BYTES,
            "s32_xor_sign_lut_bytes": LUT_32D_BYTES,
            "total_kernel_l1_cache_lines": (L1_CACHE_LINE_BYTES + LUT_32D_BYTES) // 64,
            "sedenion_16d_box_kites": bk["box_kite_count"],
            "sedenion_16d_assessors": bk["active_assessor_count"],
            "sedenion_16d_annihilation_edges": bk["directed_annihilation_edges"],
            "sample_ast_separation": {
                "(grep * filter) * summarize": fold_ast_q88((("grep", "filter"), "summarize")).hex_fingerprint(),
                "grep * (filter * summarize)": fold_ast_q88(("grep", ("filter", "summarize"))).hex_fingerprint(),
            },
        }
        print(json.dumps(info, indent=2, ensure_ascii=False))
        return 0

    if args.cmd == "boxkites":
        print(json.dumps(enumerate_sedenion_box_kites(GLOBAL_S32_LUT), indent=2))
        return 0

    if args.cmd == "zd-bench":
        payload = {
            "compiler": BANNER,
            "pinned_hardware": pin_host_hardware(),
            "asar_q88_zd_microbench": run_asar_q88_zero_divisor_microbench(),
        }
        print(json.dumps(payload, indent=2, ensure_ascii=False))
        return 0

    if args.cmd == "bench":
        from .chore_bench import run_all_benchmarks_and_export

        out_path = Path(args.out_dir)
        report = run_all_benchmarks_and_export(out_path)
        if args.sync_docs:
            docs_hud = Path(__file__).resolve().parent.parent / "docs" / "compiler-hud"
            docs_hud.mkdir(parents=True, exist_ok=True)
            for fname in (
                "index.html",
                "bsar_benchmark_metrics.csv",
                "cerebral_valley_metrics.csv",
                "cerebral_valley_benchmark.json",
            ):
                src = out_path / fname
                if src.exists() and src.resolve() != (docs_hud / fname).resolve():
                    shutil.copy2(src, docs_hud / fname)
        print(json.dumps(report["headline_summary"], indent=2, ensure_ascii=False))
        return 0

    if args.cmd == "math":
        from .group_rings import (
            PROMISLOW_14_NON_UP_WORDS,
            compile_support_product_hypercube,
            construct_gardam_f2_unit_and_char0_lift,
            make_promislow_group_ring,
            parse_promislow_word,
            solve_support_zero_divisor_kernel,
            verify_promislow_14_non_up_set,
        )
        from .math_algebras import (
            CayleyDicksonAlgebra,
            compile_guterman_zhilina_relation_hypercube,
            exact_annihilator_profile,
            identity_ladder_matrix,
            moreno_pathion_kernel_spectrum_probe,
            probe_nonassociative_identity,
            sample_reggiani_stiefel_v2_q7,
            wilmot_structure_and_reduction_report,
        )

        mcmd = args.math_cmd or "calibrate"
        if mcmd == "calibrate":
            rel = compile_guterman_zhilina_relation_hypercube(level=4)
            rel.pop("slab", None)
            out = {
                "workbench": BANNER,
                "purpose": "Exact Z/Q/F_p + 64B Q8.8 calibration suite verifying baseline invariants for open collaborative probes",
                "wilmot_structure_summary": wilmot_structure_and_reduction_report(),
                "moreno_pathion_32d_spectrum": moreno_pathion_kernel_spectrum_probe(),
                "reggiani_koebisu_stiefel_frames": sample_reggiani_stiefel_v2_q7(),
                "guterman_zhilina_s16_relations": rel,
                "identity_ladder_R_to_P32": identity_ladder_matrix(max_level=5),
                "promislow_14_non_up_hypercube": verify_promislow_14_non_up_set(),
                "gardam_f2_unit_and_char0_lift": construct_gardam_f2_unit_and_char0_lift(),
            }
            print(json.dumps(out, indent=2, ensure_ascii=False))
            return 0

        if mcmd == "relations":
            gam = _parse_gamma(args.gamma, args.level)
            rep = compile_guterman_zhilina_relation_hypercube(level=args.level, gamma=gam)
            rep.pop("slab", None)
            print(json.dumps(rep, indent=2, ensure_ascii=False))
            return 0

        if mcmd == "identities":
            if args.identity:
                gam = _parse_gamma(args.gamma, args.level)
                res = probe_nonassociative_identity(
                    args.identity, level=args.level, gamma=gam, modulus=args.mod
                )
                print(json.dumps(res, indent=2, ensure_ascii=False))
            else:
                print(json.dumps(identity_ladder_matrix(max_level=args.max_level), indent=2))
            return 0

        if mcmd == "annihilator":
            gam = _parse_gamma(args.gamma, args.level)
            alg = CayleyDicksonAlgebra(level=args.level, gamma=gam, modulus=args.mod)
            sparse: dict[int, int] = {}
            for item in args.coords.split(","):
                item = item.strip()
                if not item:
                    continue
                k_s, v_s = item.split(":")
                sparse[int(k_s.strip())] = int(v_s.strip())
            el = alg.elem(sparse)
            prof = exact_annihilator_profile(el, side=args.side)
            print(json.dumps(prof, indent=2, ensure_ascii=False))
            return 0

        if mcmd == "groupring":
            words = (
                [w.strip() for w in args.words.split(",") if w.strip()]
                if args.words
                else list(PROMISLOW_14_NON_UP_WORDS)
            )
            elems = [parse_promislow_word(w) for w in words]
            spec = make_promislow_group_ring(modulus=None)
            cube_res = compile_support_product_hypercube(
                spec, elems, elems, left_labels=words, right_labels=words
            )
            cube_res.pop("slab", None)
            alpha_ones = spec.elem({g: 1 for g in elems})
            ker_res = solve_support_zero_divisor_kernel(alpha_ones, elems, primes=(2, 3, 5))
            print(
                json.dumps(
                    {
                        "words": words,
                        "support_product_hypercube": cube_res,
                        "ones_sum_annihilator_probe": ker_res,
                    },
                    indent=2,
                    ensure_ascii=False,
                )
            )
            return 0

        if mcmd == "round4":
            from .round4_bridge import (
                cayley_dickson_shell_dispersion,
                certify_continuous_stiefel_rotation_interval,
                promislow_bloch_floquet_t3_audit,
                verify_round4_algebraic_bridge_z3,
            )

            s16 = CayleyDicksonAlgebra(level=4)
            zd_pair_elem = s16.elem({1: 1, 10: 1})
            single_shell_elem = s16.elem({1: 2, 3: -1})
            words = (
                [w.strip() for w in args.words.split(",") if w.strip()]
                if args.words
                else list(PROMISLOW_14_NON_UP_WORDS)
            )
            spec = make_promislow_group_ring(modulus=None)
            alpha_p = spec.elem({parse_promislow_word(w): 1 for w in words})
            bf_box = promislow_bloch_floquet_t3_audit(alpha_p)

            out_r4 = {
                "workbench": BANNER,
                "sedenion_zd_bimodal_dispersion": cayley_dickson_shell_dispersion(zd_pair_elem).extract(),
                "sedenion_single_shell_dispersion": cayley_dickson_shell_dispersion(single_shell_elem).extract(),
                "stiefel_v2_r7_outward_interval": certify_continuous_stiefel_rotation_interval(args.angle),
                "promislow_t3_bloch_floquet_audit": bf_box.extract(),
                "modal_box_lineage_sha256": bf_box.lineage_sha256,
                "z3_sympy_universal_certifier": verify_round4_algebraic_bridge_z3(),
            }
            print(json.dumps(out_r4, indent=2, ensure_ascii=False))
            return 0

        if mcmd == "fsm":
            from .fp_coalgebra import (
                extract_promislow_v4_orientation_fsm,
                extract_sedenion_boxkite_mode_fsm,
            )

            fsm_p = extract_promislow_v4_orientation_fsm()
            fsm_s = extract_sedenion_boxkite_mode_fsm()
            out_fsm: dict[str, object] = {
                "workbench": BANNER,
                "promislow_v4_fsm": {
                    "name": fsm_p.name,
                    "raw_reachable_state_count": fsm_p.raw_reachable_state_count,
                    "minimal_state_count": fsm_p.minimal_state_count,
                    "refinement_rounds": fsm_p.refinement_rounds,
                    "state_observations": fsm_p.state_observations,
                    "transitions": fsm_p.transitions,
                    "equivalence_class_sizes": fsm_p.equivalence_class_sizes,
                    "sample_representatives": fsm_p.sample_representatives,
                    "fsm_sha256": fsm_p.fsm_sha256,
                },
                "sedenion_7_mode_fsm": {
                    "name": fsm_s.name,
                    "raw_reachable_state_count": fsm_s.raw_reachable_state_count,
                    "minimal_state_count": fsm_s.minimal_state_count,
                    "refinement_rounds": fsm_s.refinement_rounds,
                    "state_observations": fsm_s.state_observations,
                    "transitions": fsm_s.transitions,
                    "equivalence_class_sizes": fsm_s.equivalence_class_sizes,
                    "sample_representatives": fsm_s.sample_representatives,
                    "fsm_sha256": fsm_s.fsm_sha256,
                },
            }
            if args.mermaid:
                out_fsm["promislow_v4_mermaid"] = fsm_p.to_mermaid()
                out_fsm["sedenion_7_mode_mermaid"] = fsm_s.to_mermaid()
            print(json.dumps(out_fsm, indent=2, ensure_ascii=False))
            return 0

        if mcmd == "ixasm":
            from .ix_asm import run_ix_asm_verification_suite

            out_ix = {
                "workbench": BANNER,
                "ix_asm_verification": run_ix_asm_verification_suite(),
            }
            print(json.dumps(out_ix, indent=2, ensure_ascii=False))
            return 0

    return 0


if __name__ == "__main__":
    raise SystemExit(main())
