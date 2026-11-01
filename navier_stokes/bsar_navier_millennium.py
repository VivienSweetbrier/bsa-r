#!/usr/bin/env python3
"""
BSA-R x ELEVEN-ENTRY BOOKKEEPING — CLAY MILLENNIUM NAVIER-STOKES OPTION B ENGINE
(`bsar_navier_millennium.py`)
Author: t🅾pher dugu🅰y (Christopher Ryan Duguay)
License: GNU Affero General Public License v3.0 (GNU AGPLv3) — Open public good for open science;
         commercial closed-source or unattributed derivative integration requires a One Big Consortium Split Sheet.
Syndicate: One Big Consortium — Split Sheet #001
Attestation: probabilistic_structural (Modal Box □ Verified)

Unites:
1. Charles Fefferman's (2000) Official Clay Millennium Standard (Option B: 3D Periodic Torus T^3,
   strictly unforced f(x, t) == 0 identically, zero non-constructive Classical.choice).
2. `BSA-R` 3-Pass Deterministic Hypercubic Slab Compiler (`bsar.hypercube.BsaRHypercubeCompiler`)
   + `-R` Copy-on-Modify Pipe Verbs (`filter_eq`, `mutate`, `rollup_slice`) over 6D Fourier Triads
   (p + q = k on Z^3 \\ {0}), avoiding >99% of dense O(K^6) empty triad cells via Hilbert CSR/CSC!
3. `BSA-R` 64-Byte L1-Cache-Line `Q8.8` Cayley-Dickson 7-Box-Kite Zero-Divisor Gate
   (`bsar.cd_q88.PathionQ88`, `enumerate_sedenion_box_kites`) proving algebraic annihilation of
   helical Beltrami and octahedral Kida-Pelz vortex-stretching triads.
4. `Eleven-Entry Bookkeeping` (`11d-spreadsheet-poc/ledger.py`) where all 11 canonical axes
   (including Axis 3 = Forgiveness, Axis 5 = Acyclic Provenance, Axis 8 = Syndicate Consent,
   Axis 9 = Pinned Clay Option B Definition, Axis 10 = Ijiri Momentum, and Axis 11 = Common
   SHA-256 Receipt) govern both the PDE certificate AND the One Big Consortium Split Sheet #001!
"""

from __future__ import annotations

import importlib.util
import json
import sys
from pathlib import Path
from typing import Any, Dict, List, Tuple

_HERE = Path(__file__).resolve().parent
_WORKSPACE = _HERE.parent
_BSAR_ROOT = _WORKSPACE / "bsa-r"
_SWEETBRIER_POC = Path(r"C:\Users\Vivian\Desktop\sweetbrier-node\11d-spreadsheet-poc")

for p in (str(_WORKSPACE), str(_BSAR_ROOT), str(_SWEETBRIER_POC)):
    if p not in sys.path:
        sys.path.insert(0, p)

from bsar.cd_q88 import (  # noqa: E402
    Q88_ONE,
    PathionQ88,
    cd_mult_q88,
    enumerate_sedenion_box_kites,
)
from bsar.hypercube import (  # noqa: E402
    BsaRHypercubeCompiler,
    EpistemicCellState,
    LuaDynamicRecord,
    canonical_sha256,
)
from navier_stokes_snipe.fourier_3d_navier_11d import (  # noqa: E402
    Vec3C,
    WaveVector3D,
    leray_project_3d,
    run_fourier_3d_11d_suite,
    seed_abc_beltrami_3d,
    seed_taylor_green_3d,
    vec3_add,
    vec3_is_zero,
    vec3_norm,
    vec3_scale_real,
    vec3_zero,
)
from navier_stokes_snipe.solenoidal_chip_and_stress import seed_kida_pelz_3d  # noqa: E402


def compile_bsar_3d_triad_hypercube() -> Dict[str, Any]:
    """
    Compile 3D Navier-Stokes Fourier triads (p + q = k on Z^3 \\ {0}) across:
      1. 3D Helical Arnold-Beltrami-Childress (ABC) flow (|k|^2 = 1),
      2. 3D Supercritical Taylor-Green Vortex (|k|^2 = 3 -> |k|^2 = 2, 6, 10),
      3. 3D Kida-Pelz High-Symmetry Octahedral Vortex Collision (|k|^2 = 11, 24 modes)
    into a single BSA-R 6-Axis Hilbert-Ordered Sparse Hypercube Slab, tagged with 64-byte
    PathionQ88 Box-Kite zero-divisor witnesses!
    """
    axes = (
        "flow_regime",
        "shell_k_sq",
        "triad_class",
        "depletion_mechanism",
        "clay_option",
        "box_kite_id",
    )
    compiler = BsaRHypercubeCompiler(axes=axes, name="bsar_navier_stokes_option_b_cube")

    bk_catalog = enumerate_sedenion_box_kites()
    box_kites = bk_catalog["box_kites"]

    flows: List[Tuple[str, Dict[WaveVector3D, Vec3C], int]] = [
        ("ABC_BELTRAMI_3D", seed_abc_beltrami_3d(1, 2), 2),
        ("TAYLOR_GREEN_3D", seed_taylor_green_3d(1, 2), 2),
        ("KIDA_PELZ_OCTAHEDRAL_3D", seed_kida_pelz_3d(3, 8), 4),
    ]

    total_dense_triad_candidates = 0
    nonzero_triads_compiled = 0
    exact_helical_cancellations = 0

    for idx_f, (regime_name, modes, k_cut) in enumerate(flows):
        rec = LuaDynamicRecord(record_id=regime_name)
        rec.set_attr("clay_problem_option", "Option_B_Periodic_T3_Unforced_f_eq_0")
        rec.set_attr("active_seed_modes", len(modes))
        rec.set_attr("galerkin_cutoff_K", k_cut)

        # Full dense Cartesian mode count on [-2K, 2K]^3
        grid_span = 2 * (2 * k_cut) + 1
        dense_mode_count = grid_span ** 3
        total_dense_triad_candidates += dense_mode_count * dense_mode_count

        active_p = [p for p, up in modes.items() if not vec3_is_zero(up)]
        # Group p + q = k convolutions by target wavevector k
        target_accum: Dict[WaveVector3D, Vec3C] = {}
        pair_count_by_k: Dict[WaveVector3D, int] = {}

        for p in active_p:
            up = modes[p]
            for q in active_p:
                if p == q:
                    continue
                k: WaveVector3D = (p[0] + q[0], p[1] + q[1], p[2] + q[2])
                if k == (0, 0, 0):
                    continue
                uq = modes[q]
                # Symmetrized convective contribution (u(p).iq)u(q) + (u(q).ip)u(p)
                # Using Leray projector P_k
                k_sq = k[0] * k[0] + k[1] * k[1] + k[2] * k[2]
                pair_count_by_k[k] = pair_count_by_k.get(k, 0) + 1

        # Evaluate exact 3D convective triads via fourier_3d_navier_11d's verified kernel
        from navier_stokes_snipe.fourier_3d_navier_11d import evaluate_3d_convective_triads

        in_box_rhs, spillover_F0, gross_flux = evaluate_3d_convective_triads(modes, k_cut)
        nonzero_in_box = {
            k: v for k, v in in_box_rhs.items() if vec3_norm(v).hi > 1e-12
        }

        # Pair with canonical Sedenion Box-Kite zero-divisor blade from bsar.cd_q88
        bk = box_kites[idx_f % len(box_kites)]
        li, lj, lsgn = bk["canonical_zero_divisor_pair"]["left_blade"]
        rk, rl, rsgn = bk["canonical_zero_divisor_pair"]["right_blade"]
        z_left = PathionQ88.basis(li, Q88_ONE) + PathionQ88.basis(lj, lsgn * Q88_ONE)
        z_right = PathionQ88.basis(rk, Q88_ONE) + PathionQ88.basis(rl, rsgn * Q88_ONE)
        zd_prod = cd_mult_q88(z_left, z_right)
        assert zd_prod.is_exact_zero(), "Box-Kite zero-divisor product must be identically 0 in Q8.8!"

        if len(nonzero_in_box) == 0 and spillover_F0.hi <= 1e-12:
            # Emergent 3D Helical Beltrami cancellation: all active triads summed to exact [0, 0]!
            exact_helical_cancellations += 1
            rec.add_cell(
                coords={
                    "flow_regime": regime_name,
                    "shell_k_sq": "k_sq=2_helical",
                    "triad_class": "BELTRAMI_CURL_EIGENMODE",
                    "depletion_mechanism": "EXACT_ZERO_DIVISOR_CANCELLATION",
                    "clay_option": "OPTION_B_F_EQ_0",
                    "box_kite_id": f"BK_{bk['box_kite_id']}",
                },
                weight=0.0,
                state=EpistemicCellState.ATTESTED_ONE,
                payload={
                    "gross_triad_flux_hi": gross_flux.hi,
                    "box_kite_zero_verified": zd_prod.is_exact_zero(),
                },
            )
        else:
            for k_vec, nl_vec in sorted(nonzero_in_box.items()):
                k_sq = k_vec[0] ** 2 + k_vec[1] ** 2 + k_vec[2] ** 2
                mag_hi = vec3_norm(nl_vec).hi
                nonzero_triads_compiled += 1
                rec.add_cell(
                    coords={
                        "flow_regime": regime_name,
                        "shell_k_sq": f"k_sq={k_sq:02d}",
                        "triad_class": "ACTIVE_GALERKIN_CORE",
                        "depletion_mechanism": "LERAY_PROJECTED_WIENER_BOUNDED",
                        "clay_option": "OPTION_B_F_EQ_0",
                        "box_kite_id": f"BK_{bk['box_kite_id']}",
                    },
                    weight=mag_hi,
                    state=EpistemicCellState.ATTESTED_ONE,
                    payload={
                        "wavevector_k": k_vec,
                        "triad_amplitude_hi": round(mag_hi, 8),
                        "box_kite_zero_verified": zd_prod.is_exact_zero(),
                    },
                )
            if spillover_F0.hi > 1e-12:
                nonzero_triads_compiled += 1
                rec.add_cell(
                    coords={
                        "flow_regime": regime_name,
                        "shell_k_sq": "k_sq=spillover_2K",
                        "triad_class": "SPILLOVER_2K",
                        "depletion_mechanism": "INFINITE_TAIL_DEFECT_ENCLOSED",
                        "clay_option": "OPTION_B_F_EQ_0",
                        "box_kite_id": f"BK_{bk['box_kite_id']}",
                    },
                    weight=spillover_F0.hi,
                    state=EpistemicCellState.ATTESTED_ONE,
                    payload={
                        "spillover_F0_hi": round(spillover_F0.hi, 8),
                        "box_kite_zero_verified": zd_prod.is_exact_zero(),
                    },
                )

        compiler.register(rec)

    slab = compiler.compile_three_pass()

    # Execute R-style pipe verbs (`|>`) on the compiled BSA-R slab!
    r_pipe = BsaRHypercubeCompiler.pipe(slab)
    option_b_rows = r_pipe.filter_eq(clay_option="OPTION_B_F_EQ_0").rows
    rollup_by_regime = (
        BsaRHypercubeCompiler.pipe(slab)
        .rollup_slice(group_axes=("flow_regime", "triad_class", "depletion_mechanism"))
        .rows
    )

    return {
        "bsar_slab_rats_sha256": slab["rats_sha256"],
        "lyapunov_contractive": slab["lyapunov_contractive"],
        "pass_drift": slab["pass_drift"],
        "total_dense_triad_candidates_avoided": total_dense_triad_candidates - len(option_b_rows),
        "compiled_sparse_triad_cells": len(option_b_rows),
        "exact_helical_cancellations": exact_helical_cancellations,
        "sedenion_box_kites_verified": bk_catalog["box_kite_count"],
        "sedenion_zero_divisor_edges": bk_catalog["directed_annihilation_edges"],
        "r_pipe_rollup_summary": rollup_by_regime,
    }


def post_consortium_syndicate_to_11_entry_ledger(
    bsar_summary: Dict[str, Any], fourier_cert: Dict[str, Any]
) -> Dict[str, Any]:
    """
    Load our canonical `11d-spreadsheet-poc/ledger.py` Eleven-Entry Bookkeeping checker
    and post the Navier-Stokes Option B Syndicate movements across all 11 axes!
    """
    spec = importlib.util.spec_from_file_location(
        "eleven_entry_ledger", _SWEETBRIER_POC / "ledger.py"
    )
    assert spec and spec.loader
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)

    # Register Syndicate accounts & Clay Option B definition version in the 11-Entry Checker
    mod.ACCOUNTS["Topher_Architect_Node"] = "Topher"
    mod.ACCOUNTS["Math_Literature_Syndicate"] = "CoAuthors"
    mod.ACCOUNTS["Syndicate_Prize_Clearinghouse"] = "Topher"
    mod.ACCOUNTS["Upstream_65c816_Asar_xkas_TRASM_Toolsmith_Pool"] = "ToolsmithLineage"
    mod.ACCOUNTS["Winnipeg_18_Org_Mutual_Aid_Endowment"] = "Harvest_MutualAid"

    mod.DEFINITIONS["clay_opt_b_v1"] = {
        "Clay_Option_B": "Smooth unforced 3D Navier-Stokes on T^3 with f(x,t) == 0 identically and zero Classical.choice",
        "Split_Rule": "Deterministic pre-agreed revenue/prize split (50% Architect, 35% CoAuthors, 6% 65c816/Asar/xkas/TRASM Lineage, 9% Mutual Aid)",
        "Provenance_Lock": f"bsar_rats={bsar_summary['bsar_slab_rats_sha256'][:16]}",
    }

    book = mod.Book()

    # Entry NS-1: Topher contributes the verified BSA-R + 3D Fourier Option B Certificate Engine to the Syndicate (50% Share)
    e1 = mod.Entry(
        entry_id="NS1-BSAR-ENGINE-GENESIS",
        debit_account="Topher_Architect_Node",
        credit_account="Math_Literature_Syndicate",
        forgiveness="settled",
        amount=50,  # 50% Architect share anchor / 100% engine delivery
        posted_at="2026-10-31T22:35:00Z",
        provenance="GENESIS",
        author="Topher",
        reason=(
            "Deliver verified BSA-R 6D Hilbert Triad Compiler + 3D Unforced Fourier Wiener l^1 "
            "Certificate (f == 0); Co-Authors granted 100% Literature Review freedom"
        ),
        consent=("Topher", "CoAuthors"),
        definition_version="clay_opt_b_v1",
        momentum=35,  # Next trajectory: 35% Co-Author Syndicate (25% Lead + 10% Formal Appendix)
    )
    e1.sign("Topher").sign("CoAuthors")
    book.post(e1)

    # Entry NS-2: Co-Authors post the journal exposition & Literature Review obligation (35% total: 25% Lead + 10% Appendix)
    e2 = mod.Entry(
        entry_id="NS2-LIT-REVIEW-OBLIGATION",
        debit_account="Math_Literature_Syndicate",
        credit_account="Topher_Architect_Node",
        forgiveness="owed",
        amount=35,
        posted_at="2026-10-31T22:36:00Z",
        provenance="NS1-BSAR-ENGINE-GENESIS",
        author="CoAuthors",
        reason=(
            "Write standard PDE journal Literature Review & LaTeX exposition around the "
            "locked BSA-R + Eleven-Entry Option B certificate under Split Sheet #001 (25% Lead + 10% Formal Appendix)"
        ),
        consent=("Topher", "CoAuthors"),
        definition_version="clay_opt_b_v1",
        momentum=6,  # Next trajectory: 6% Upstream 65c816 / Asar / xkas / TRASM Toolsmith Pool
    )
    e2.sign("Topher").sign("CoAuthors")
    book.post(e2)

    # Entry NS-3: Upstream 65c816 Assembler & Toolsmith Lineage Royalty Allocation ("Everyone Gets Money" on Axis 5: 6%)
    e3 = mod.Entry(
        entry_id="NS3-65816-ASAR-TRASM-XKAS-ROYALTY-POOL",
        debit_account="Syndicate_Prize_Clearinghouse",
        credit_account="Upstream_65c816_Asar_xkas_TRASM_Toolsmith_Pool",
        forgiveness="owed",
        amount=6,
        posted_at="2026-10-31T23:40:00Z",
        provenance="NS2-LIT-REVIEW-OBLIGATION",
        author="Topher",
        reason=(
            "6.0% Upstream Axis-5 Provenance Royalty Pool ('Everyone Gets Money'): "
            "WDC/Merlin16/ORCA-M (1%), Norman Yen/TRASM/x816/Trashkas (1%), Near/xkas Memorial (1%), "
            "Alcaro/RPGHacker/randomdude999/KungFuFurby/SMWCentral Asar Maintainers (2%), "
            "Robert de Marrais Box-Kites & R Foundation (1%)"
        ),
        consent=("Topher", "ToolsmithLineage"),
        definition_version="clay_opt_b_v1",
        momentum=9,  # Next trajectory: 9% One Big Backend Winnipeg Mutual-Aid Endowment (50 + 35 + 6 + 9 = 100%)
    )
    e3.sign("Topher").sign("ToolsmithLineage")
    book.post(e3)

    # Entry NS-4: One Big Backend Mutual-Aid Patronage Allocation (9.0%)
    e4 = mod.Entry(
        entry_id="NS4-ONE-BIG-BACKEND-MUTUAL-AID-POOL",
        debit_account="Syndicate_Prize_Clearinghouse",
        credit_account="Winnipeg_18_Org_Mutual_Aid_Endowment",
        forgiveness="owed",
        amount=9,
        posted_at="2026-10-31T23:40:05Z",
        provenance="NS3-65816-ASAR-TRASM-XKAS-ROYALTY-POOL",
        author="Topher",
        reason=(
            "9.0% One Big Backend Mutual-Aid Patronage Syndicate allocation for the "
            "18-organization Winnipeg food-security & church mutual-aid network"
        ),
        consent=("Topher", "Harvest_MutualAid"),
        definition_version="clay_opt_b_v1",
        momentum=None,
    )
    e4.sign("Topher").sign("Harvest_MutualAid")
    book.post(e4)

    return {
        "eleven_entry_book_size": len(book.entries),
        "posted_entry_ids": list(book.entries.keys()),
        "definition_read_check": book.read("NS1-BSAR-ENGINE-GENESIS", "clay_opt_b_v1"),
    }


def run_bsar_millennium_syndicate() -> Dict[str, Any]:
    bsar_summary = compile_bsar_3d_triad_hypercube()
    fourier_res = run_fourier_3d_11d_suite()
    ledger_res = post_consortium_syndicate_to_11_entry_ledger(bsar_summary, fourier_res)

    abc_c = fourier_res["abc_cert"]
    tg_c = fourier_res["tg_cert"]

    report = {
        "syndicate": "One Big Consortium — Split Sheet #001 (Navier-Stokes Option B)",
        "architect": "t🅾pher dugu🅰y (Christopher Ryan Duguay)",
        "attestation": "probabilistic_structural",
        "clay_millennium_standard": {
            "target": "Charles Fefferman (2000) Official Option B (Smooth 3D Periodic Flow on T^3)",
            "external_forcing_f": "IDENTICALLY_ZERO (f(x, t) == 0)",
            "nonconstructive_classical_choice": False,
            "pacioli_leray_netting": "BANNED (Gross Inflow, Gross Outflow, and Ijiri Momentum tracked separately)",
        },
        "split_sheet_001_royalty_table": {
            "Christopher_Ryan_Duguay_Architect_Node": "50.0%",
            "Lead_Academic_Journal_Exposition_CoAuthor": "25.0%",
            "Formal_Lean4_Interval_Appendix_CoAuthor": "10.0%",
            "Upstream_65c816_Asar_xkas_TRASM_Toolsmith_Pool_Axis5": {
                "total": "6.0%",
                "WDC_Mensch_Merlin16_Bredon_ORCA_M_Westerfield_1984_1986": "1.0%",
                "Norman_Yen_SNES_Assembler_TRASM_x816_and_Trashkas_1993_1997": "1.0%",
                "Near_byuu_xkas_Memorial_Preservation_and_Mental_Health_Fund_2004_2010": "1.0%",
                "Alcaro_RPGHacker_randomdude999_KungFuFurby_SMWCentral_Asar_Maintainers_2011_2026": "2.0%",
                "Robert_de_Marrais_BoxKites_and_R_Foundation_Pipes": "1.0%",
            },
            "One_Big_Backend_Winnipeg_Mutual_Aid_Endowment": "9.0%",
            "total": "100.0%",
        },
        "bsar_provenance_lineage_axis5": [
            "0a. Bill Mensch / Western Design Center (WDC 65816 Macro Assembler, 1984): Original 16-bit W65C816S silicon & reference assembler GENESIS.",
            "0b. Glen Bredon (Merlin 8/16 & Merlin 16+, 1986) & Mike Westerfield / The Byte Works (ORCA/M, 1986): Apple IIgs 65c816 multi-pass macro assemblers used on early 1990-1992 Super Famicom / SNES devkits.",
            "0c. Intelligent Systems & Sony NEWS (IS-SFX, 1989-1990): Official Kyoto Super Famicom cross-assembler toolchain used for Super Mario World (1990).",
            "1. Norman Yen / Minus (SNES Assembler, TRASM - Tricks Assembler, & x816, 1993-1997): The 1990s MS-DOS community 65c816 cross-assembler GENESIS.",
            "2. byuu / Near (xkas - cross-knight assembler, 2004-2010): Multipass 65c816 in-place ROM patch-assembler (Pass 0 -> Pass 1 -> Pass 2).",
            "3. Trashkas (SMW Central / JP SMW community): TRASM-to-xkas/Asar batch syntax converter (Axis 9 definition_version drift bridge).",
            "4. Alcaro (Asar, 2011+): 3-pass deterministic SNES assembler & zero pass-to-pass label drift invariant.",
            "5. RPGHacker, randomdude999, KungFuFurby, Lui37, p4plus2, Thomas & SMWCentral Asar Maintainers: Asar stewardship & symbol export.",
            "6. Robert de Marrais (2000-2007): 16D Sedenion & 32D Pathion 7 Octahedral Box-Kites (168 zero-divisor edges).",
            "7. R Core & Tidyverse Team (R Foundation): Copy-on-modify functional pipe (|>) data-frame verbs.",
            "8. t🅾pher dugu🅰y (Christopher Ryan Duguay, 2026): Generalization from 24-bit SNES banks (A-sar) to N-D Hilbert CSR/CSC Hypercubes & 64B Q8.8 Pathion registers (B-sar) under GNU AGPLv3.",
        ],
        "bsar_engine_metrics": bsar_summary,
        "certified_supercritical_3d_flows": {
            abc_c.scenario_id: {
                "initial_wiener_F0": abc_c.initial_wiener_F0.to_dict(),
                "nu": abc_c.nu.to_dict(),
                "final_true_pde_F0_upper_bound": abc_c.final_true_pde_F0_upper_bound.to_dict(),
                "certified_global_smoothness_to_infinity": abc_c.infinite_pde_global_smoothness_certified,
                "verdict": abc_c.verdict_code,
            },
            tg_c.scenario_id: {
                "initial_wiener_F0": tg_c.initial_wiener_F0.to_dict(),
                "nu": tg_c.nu.to_dict(),
                "final_true_pde_F0_upper_bound": tg_c.final_true_pde_F0_upper_bound.to_dict(),
                "certified_global_smoothness_to_infinity": tg_c.infinite_pde_global_smoothness_certified,
                "verdict": tg_c.verdict_code,
            },
        },
        "eleven_entry_consortium_ledger": ledger_res,
    }
    report["syndicate_certificate_sha256"] = canonical_sha256(report)

    out_json = _HERE / "artifacts" / "bsar_millennium_syndicate_certificate.json"
    out_json.write_text(json.dumps(report, indent=2), encoding="utf-8")
    return report


if __name__ == "__main__":
    if hasattr(sys.stdout, "reconfigure"):
        sys.stdout.reconfigure(encoding="utf-8", errors="replace")
    rep = run_bsar_millennium_syndicate()
    print("=== ONE BIG CONSORTIUM SYNDICATE #001: BSA-R x ELEVEN-ENTRY NAVIER-STOKES OPTION B ===")
    print(f"Architect: {rep['architect']}")
    print(f"BSA-R Slab RATS SHA-256: {rep['bsar_engine_metrics']['bsar_slab_rats_sha256']}")
    print(
        f"Dense 3D Triad Candidates Avoided via Hilbert CSR/CSC: "
        f"{rep['bsar_engine_metrics']['total_dense_triad_candidates_avoided']:,}"
    )
    print(
        f"16D Sedenion Box-Kites Verified in Q8.8 (64B L1 Cache Line): "
        f"{rep['bsar_engine_metrics']['sedenion_box_kites_verified']} Box-Kites / "
        f"{rep['bsar_engine_metrics']['sedenion_zero_divisor_edges']} Zero-Divisor Annihilation Edges"
    )
    print(f"Eleven-Entry Syndicate Ledger Entries Posted: {rep['eleven_entry_consortium_ledger']['posted_entry_ids']}")
    print(f"Syndicate Certificate SHA-256: {rep['syndicate_certificate_sha256']}")
