#!/usr/bin/env python3
"""
CLEAN `bsar` CLI ENTRYPOINT (`python -m bsar ...` / `bsar ...`)
Official Banner: 🅱💲🅰-R: Hypercubic Compiler
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


def main(argv: list[str] | None = None) -> int:
    _configure_utf8_stdout()
    parser = argparse.ArgumentParser(
        prog="bsar",
        description=f"{BANNER} — Slash AI Token & Compute Expenses via 3-Pass Hilbert Hypercubes + 64-Byte Q8.8 Cayley-Dickson Algebra",
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

    return 0


if __name__ == "__main__":
    raise SystemExit(main())
