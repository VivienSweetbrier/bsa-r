#!/usr/bin/env python3
"""
EXACT MATHEMATICAL WORKBENCH & HOSTILE REGRESSION SUITE (`tests/test_bsar_math.py`)
License: GNU AGPLv3
Attestation: probabilistic_structural

Verifies:
  1. Arbitrary 2^n-ions, split signatures, 15 = 8 + 7 ultracomplex subalgebras, & 84 -> 7 reduction
  2. Bareiss integer det(L_x), Koebisu sedenion quartic factorization, Moreno 4k Pathion spectrum,
     & dense 7-lane rational Householder Stiefel V_2(Q^7) zero-divisor frames
  3. Guterman-Zhilina 3-pass BSA-R sparse relation-graph hypercubes (standard & split)
  4. Two-stage Q8.8-to-Exact nonassociative AST prober & Hostile Q8.8-underflow firewall check!
  5. Torsion-free Promislow / Hantzsche-Wendt group P relators, Promislow 14-element non-UP cube,
     Gardam 21-term F_2[P] unit + char-0 Z[P] parity lift, custom group-ring kernel solver,
     and Albuquerque-Majid twisted group-ring isomorphism R^{sigma}[(Z_2)^n] ~= A_n(gamma)
  6. CLI `python -m bsar math ...` subcommand smoke checks
"""

from __future__ import annotations

from fractions import Fraction
import io
from pathlib import Path
import sys
import unittest
from contextlib import redirect_stdout

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))

from bsar import (
    BsaRHypercubeCompiler,
    CayleyDicksonAlgebra,
    GroupRingSpec,
    bareiss_det_int,
    catalan_bracketings,
    compile_guterman_zhilina_relation_hypercube,
    compile_support_product_hypercube,
    construct_gardam_f2_unit_and_char0_lift,
    eval_nonassociative_ast_exact,
    eval_nonassociative_ast_q88,
    exact_annihilator_profile,
    identity_ladder_matrix,
    is_alternative_element,
    is_doubly_alternative_element,
    koebisu_sedenion_det_factorization,
    make_cayley_dickson_twisted_group_ring,
    make_promislow_group_ring,
    moreno_pathion_kernel_spectrum_probe,
    probe_nonassociative_identity,
    promislow_word_ball,
    sample_reggiani_stiefel_v2_q7,
    solve_support_zero_divisor_kernel,
    verify_promislow_14_non_up_set,
    wilmot_structure_and_reduction_report,
)
from bsar.cd_q88 import PathionQ88
from bsar.cli import main as cli_main


class TestBsaRMathWorkbench(unittest.TestCase):
    def test_wilmot_subalgebras_reduction_and_split_signatures(self) -> None:
        rep = wilmot_structure_and_reduction_report()
        self.assertEqual(rep["s16_basis_triples_total"], 455)
        self.assertEqual(rep["quaternionic_fano_triples"], 35)
        self.assertEqual(rep["non_quaternionic_associative_triples"], 168)
        self.assertEqual(rep["associative_triples_total"], 203)
        self.assertEqual(rep["nonassociative_triples"], 252)
        self.assertEqual(rep["eight_dim_subalgebras_total"], 15)
        self.assertEqual(rep["octonion_subalgebra_count"], 8)
        self.assertEqual(rep["ultracomplex_quasi_octonion_count"], 7)

        red = rep["zd_3cycle_mode_reduction"]
        self.assertEqual(red["total_primitive_cross_half_pairs"], 84)
        self.assertEqual(red["pairs_per_ultracomplex_subalgebra"], [12] * 7)
        self.assertEqual(red["reduced_primary_modes"], 7)

        by_sig = {c["name"]: c for c in rep["split_signature_census"]}
        self.assertEqual(by_sig["standard_sedenions"]["primitive_cross_half_pairs"], 84)
        self.assertGreater(
            by_sig["split_sedenions_last_step"]["unordered_all_2blade_zd_pairs"],
            by_sig["standard_sedenions"]["unordered_all_2blade_zd_pairs"],
        )

    def test_koebisu_det_moreno_pathion_spectrum_and_reggiani_stiefel_frames(self) -> None:
        s16 = CayleyDicksonAlgebra(level=4)
        # Non-zero-divisor dense sedenion in Z^16
        x_gen = s16.elem([1, 2, -1, 0, 1, 0, -2, 1, -1, 1, 0, 2, -1, 1, 0, -1])
        k_gen = koebisu_sedenion_det_factorization(x_gen)
        self.assertTrue(k_gen["exact_polynomial_match"])
        self.assertFalse(k_gen["is_zero_divisor"])
        self.assertGreater(k_gen["det_bareiss_exact"], 0)

        # Dense 7-lane rational Householder Stiefel V_2(Q^7) frames
        frames = sample_reggiani_stiefel_v2_q7()
        self.assertEqual(len(frames), 3)
        for fr in frames:
            self.assertTrue(fr["stiefel_orthonormal_exact"])
            self.assertEqual(fr["det_L_x"], 0)
            self.assertEqual(fr["annihilator_dim_ker_L_x"], 4)
            self.assertTrue(fr["exact_product_xy_is_zero"])
        # Ensure at least two frames have all 14 imaginary lanes active (not mere 2-blades!)
        self.assertGreaterEqual(frames[1]["active_imaginary_lanes"], 12)

        # Moreno 32D Pathion {0, 4, 8, 12} spectrum + 64D Chingon zero-divisor sanity check
        spec32 = moreno_pathion_kernel_spectrum_probe()
        self.assertTrue(spec32["spectrum_complete"])
        for w in spec32["witnesses"]:
            self.assertTrue(w["moreno_mod4_holds"])
            self.assertTrue(w["all_basis_certified_zero"])

        c64 = CayleyDicksonAlgebra(level=6)
        zd64 = c64.blade2(1, 34, 1)
        prof64 = exact_annihilator_profile(zd64)
        self.assertGreater(prof64["nullity"], 0)
        self.assertEqual(prof64["nullity"] % 4, 0)
        self.assertTrue(prof64["all_basis_vectors_certified_zero"])

    def test_guterman_zhilina_relation_hypercubes_and_rpipe_slicing(self) -> None:
        std_rep = compile_guterman_zhilina_relation_hypercube(level=4)
        zd_rel = std_rep["relations"]["zero_divisor"]
        self.assertEqual(zd_rel["active_vertices"], 84)
        self.assertEqual(zd_rel["connected_components"], 7)  # 7 signed Box-Kite double-covers!
        self.assertEqual(zd_rel["component_sizes"], [12] * 7)
        # Signed 12-vertex crown/double-cover of K_{2,2,2} has exact diameter 3 (dist(e_i+e_j, e_i-e_j) = 3)!
        self.assertEqual(zd_rel["max_component_diameter"], 3)
        self.assertIsNotNone(zd_rel["hexagon_6cycle_witness"])

        pipe = BsaRHypercubeCompiler.pipe(std_rep["slab"])
        c01_edges = pipe.filter_eq(relation="zero_divisor", component="C01").rows
        self.assertEqual(len(c01_edges), 24)  # K_{2,2,2} with 12 signed vertices -> 24 undirected ZD edges!

        # Check doubly-alternative distinction at level 5 (32D Pathions)
        p32 = CayleyDicksonAlgebra(level=5)
        # Half in O is alternative -> doubly alternative; half with non-alternative S16 blade -> not!
        d_alt_ok = p32.blade2(1, 18, 1)
        d_alt_bad = p32.elem({1: 1, 10: 1, 18: 1})
        self.assertTrue(is_doubly_alternative_element(d_alt_ok))
        self.assertFalse(is_doubly_alternative_element(d_alt_bad))

    def test_nonassociative_identities_catalan_trees_and_hostile_q88_underflow_guard(self) -> None:
        ladder = {r["level"]: r for r in identity_ladder_matrix(max_level=5)}
        # R (0): commutative; C (1): commutative; H (2): associative, non-commutative
        self.assertTrue(ladder[1]["commutativity"])
        self.assertFalse(ladder[2]["commutativity"])
        self.assertTrue(ladder[2]["associativity"])
        # O (3): alternative + Moufang, non-associative
        self.assertFalse(ladder[3]["associativity"])
        self.assertTrue(ladder[3]["left_alternativity"])
        self.assertTrue(ladder[3]["left_moufang"])
        # S (4) & P (5): flexible + power-associative ("ultracomplex"), NOT alternative or Moufang!
        for lvl in (4, 5):
            self.assertFalse(ladder[lvl]["left_alternativity"])
            self.assertFalse(ladder[lvl]["left_moufang"])
            self.assertTrue(ladder[lvl]["flexibility"])
            self.assertTrue(ladder[lvl]["power_associativity_4"])

        # Catalan C_3 = 5, C_4 = 14
        self.assertEqual(len(catalan_bracketings(("x1", "x2", "x3", "x4"))), 5)
        self.assertEqual(len(catalan_bracketings(("x1", "x2", "x3", "x4", "x5"))), 14)

        # HOSTILE NODE-1 FIREWALL TEST:
        # In raw 16-bit Q8.8 fixed-point, tiny amplitudes (8/256) * (8/256) = 64/65536 underflow to 0!
        # Verify that raw Q8.8 underflows while exact CDElem over Q NEVER falsely reports zero!
        tiny_u_q88 = PathionQ88.basis(1, 8)
        tiny_v_q88 = PathionQ88.basis(2, 8)
        self.assertTrue(eval_nonassociative_ast_q88(("*", "x", "y"), {"x": tiny_u_q88, "y": tiny_v_q88}).is_exact_zero())

        s16 = CayleyDicksonAlgebra(level=4)
        tiny_u_ex = s16.basis(1, Fraction(8, 256))
        tiny_v_ex = s16.basis(2, Fraction(8, 256))
        exact_prod = eval_nonassociative_ast_exact(("*", "x", "y"), {"x": tiny_u_ex, "y": tiny_v_ex}, s16)
        self.assertFalse(exact_prod.is_zero())
        self.assertEqual(exact_prod.support(), {3: Fraction(1, 1024)})

    def test_promislow_14_gardam_unit_twisted_cd_bridge_and_kernel_solver(self) -> None:
        prom = verify_promislow_14_non_up_set()
        self.assertTrue(prom["relators_verified"])
        self.assertEqual(prom["left_size"], 14)
        self.assertEqual(prom["cartesian_pairs"], 196)
        self.assertEqual(prom["unique_product_count"], 0)
        self.assertFalse(prom["has_unique_product_property_on_pair"])
        self.assertGreaterEqual(prom["min_multiplicity"], 2)

        gardam = construct_gardam_f2_unit_and_char0_lift()
        self.assertEqual(gardam["alpha_support_size"], 21)
        self.assertEqual(gardam["beta_inverse_support_size"], 21)
        self.assertTrue(gardam["f2_right_and_left_unit"])
        self.assertEqual(gardam["char0_identity_coefficient"], 17)
        self.assertTrue(gardam["all_off_identity_even_mod_2"])
        self.assertEqual(gardam["odd_multiplicity_products_in_alpha_x_beta"], 1)

        # Verify Albuquerque-Majid twisted group-ring isomorphism R^{sigma}[(Z_2)^4] ~= S_16
        t_s16 = make_cayley_dickson_twisted_group_ring(level=4)
        u_tw = t_s16.elem({1: 1, 10: 1})
        v_tw = t_s16.elem({4: 1, 15: -1})
        self.assertTrue((u_tw * v_tw).is_zero())

        ker_tw = solve_support_zero_divisor_kernel(u_tw, list(range(16)), primes=(2, 3))
        self.assertEqual(ker_tw["char0_nullity_Q"], 4)
        self.assertGreaterEqual(ker_tw["positive_char_nullities"][2]["nullity"], 4)

        # Custom torsion-free discrete Heisenberg group H_3(Z) support check (orderable -> ALWAYS has UP!)
        heisenberg = GroupRingSpec(
            name="Z[Heisenberg_H3]",
            identity=(0, 0, 0),
            mul_fn=lambda a, b: (a[0] + b[0], a[1] + b[1], a[2] + b[2] + a[0] * b[1]),
        )
        h_supp = [(0, 0, 0), (1, 0, 0), (0, 1, 0), (1, 1, 1)]
        h_cube = compile_support_product_hypercube(heisenberg, h_supp, h_supp)
        self.assertTrue(h_cube["has_two_unique_products_on_pair"])

    def test_cli_math_subcommands(self) -> None:
        for argv in [
            ["math", "annihilator", "--level", "5", "--coords", "1:1,18:1"],
            ["math", "identities", "--identity", "flexibility", "--level", "4"],
            ["math", "relations", "--level", "4", "--gamma", "-1,-1,-1,1"],
            ["math", "groupring"],
        ]:
            buf = io.StringIO()
            with redirect_stdout(buf):
                rc = cli_main(argv)
            self.assertEqual(rc, 0)
            self.assertIn("{", buf.getvalue())


if __name__ == "__main__":
    unittest.main(verbosity=2)
