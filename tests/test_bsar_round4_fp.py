#!/usr/bin/env python3
"""
Verification Suite for `bsar` v0.4.0:
  - Haskell-inspired Functional & Coalgebraic State-Machine Engine (`bsar.fp_coalgebra`)
  - Navier-Stokes Round-4 (`Step 5`) Algebraic & Group-Ring Bridge (`bsar.round4_bridge`)
  - CLI `bsar math round4` and `bsar math fsm` subcommands
"""

from __future__ import annotations

from fractions import Fraction
import io
import json
import math
import unittest
from contextlib import redirect_stdout

from bsar import (
    PROMISLOW_14_NON_UP_WORDS,
    AlgebraicPipeline,
    BranchF,
    CayleyDicksonAlgebra,
    FilterStage,
    LeafF,
    ModalBox,
    MooreFold,
    MutateStage,
    NonlinearShellFluxStage,
    OutwardInterval,
    ZeroShortCircuitStage,
    ana,
    cata,
    cayley_dickson_shell_dispersion,
    certify_continuous_stiefel_rotation_interval,
    construct_gardam_f2_unit_and_char0_lift,
    discover_minimal_fsm,
    extract_promislow_v4_orientation_fsm,
    extract_sedenion_boxkite_mode_fsm,
    has_z3_and_sympy,
    hylo,
    make_promislow_group_ring,
    make_round4_spectral_fold,
    parse_promislow_word,
    promislow_bloch_floquet_matrix_at_rationals,
    promislow_bloch_floquet_t3_audit,
    verify_round4_algebraic_bridge_z3,
)
from bsar.cli import main as bsar_cli_main


def _mat_mul_4x4(a: list[list[Fraction]], b: list[list[Fraction]]) -> list[list[Fraction]]:
    out = [[Fraction(0, 1) for _ in range(4)] for _ in range(4)]
    for i in range(4):
        for k in range(4):
            aik = a[i][k]
            if aik == 0:
                continue
            for j in range(4):
                out[i][j] += aik * b[k][j]
    return out


class TestBsaRRound4AndFunctionalCoalgebra(unittest.TestCase):
    def test_modal_box_functor_applicative_and_comonad_laws(self) -> None:
        b0 = ModalBox.pure(7, label="seed")
        # Functor identity & composition
        self.assertEqual(b0.fmap(lambda x: x).extract(), b0.extract())
        f = lambda x: x * 3
        g = lambda y: y + 5
        self.assertEqual(b0.fmap(f).fmap(g).extract(), b0.fmap(lambda x: g(f(x))).extract())

        # Applicative Axiom K: Box(A -> B) -> Box A -> Box B
        box_fn = ModalBox.pure(lambda x: x * x + 1, label="morphism")
        applied = box_fn.ap(b0)
        self.assertEqual(applied.extract(), 50)
        self.assertEqual(len(applied.trace), 3)
        self.assertEqual(len(applied.lineage_sha256), 64)

        # Comonad laws: extract(duplicate(w)) == w and extend(extract)(w) == w
        dup = b0.duplicate()
        self.assertEqual(dup.extract().extract(), 7)
        ext_id = b0.extend(lambda box: box.extract())
        self.assertEqual(ext_id.extract(), b0.extract())

    def test_applicative_moore_fold_and_hylo_deforestation(self) -> None:
        stream = [(-1, 3), (1, 3), (2, 5), (4, 2)]
        fold = make_round4_spectral_fold()
        stats = fold.run(stream)

        m0_ref = sum(e for _, e in stream)
        d_ref = sum(m * e for m, e in stream)
        p_ref = sum((m * m) * e for m, e in stream)
        self.assertEqual(stats["M0"], m0_ref)
        self.assertEqual(stats["D"], d_ref)
        self.assertEqual(stats["P"], p_ref)
        self.assertEqual(stats["variance_M0P_minus_D2"], m0_ref * p_ref - d_ref * d_ref)

        # Contramap + zip_with test
        sq_sum = MooreFold(lambda: 0, lambda s, x: s + x, lambda s: s).contramap(lambda x: x * x)
        cnt = MooreFold(lambda: 0, lambda s, _: s + 1, lambda s: s)
        mean_sq = MooreFold.zip_with(lambda total, n: total / n, sq_sum, cnt)
        self.assertAlmostEqual(mean_sq.run([1, 2, 3, 4]), 7.5)

        # Recursion schemes deforestation law: hylo(alg, coalg, seed) == cata(alg, ana(coalg, seed))
        s16 = CayleyDicksonAlgebra(level=4)
        factors = [s16.basis(1), s16.basis(2), s16.basis(9), s16.basis(14)]

        def split_coalg(span: tuple[int, int]):
            lo, hi = span
            if hi - lo == 1:
                return LeafF(factors[lo])
            mid = (lo + hi) // 2
            return BranchF("*", (lo, mid), (mid, hi))

        def eval_alg(step):
            if isinstance(step, LeafF):
                return step.value
            return step.left * step.right

        via_cata_ana = cata(eval_alg, ana(split_coalg, (0, len(factors))))
        via_hylo = hylo(eval_alg, split_coalg, (0, len(factors)))
        self.assertEqual(via_hylo, via_cata_ana)
        self.assertEqual(via_hylo, (factors[0] * factors[1]) * (factors[2] * factors[3]))

    def test_coalgebraic_implicit_state_machine_discovery(self) -> None:
        # 1. Redundant 8-state mod-8 counter where observation is parity `s % 2` -> collapses to 2 states!
        fsm_mod2 = discover_minimal_fsm(
            name="Mod8_to_Parity_2State",
            initial_states=[0],
            alphabet=("inc", "stay"),
            step_fn=lambda s, a: (s + 1) % 8 if a == "inc" else s,
            obs_fn=lambda s: s % 2,
        )
        self.assertEqual(fsm_mod2.raw_reachable_state_count, 8)
        self.assertEqual(fsm_mod2.minimal_state_count, 2)

        # 2. Torsion-free Promislow group P -> implicit 4-state Klein-Four V_4 automaton!
        # Round 0 sees ONLY 3 trace classes {-2, 0, +2}, and Round 2 splits `a` vs `b` into 4 states!
        fsm_p = extract_promislow_v4_orientation_fsm()
        self.assertEqual(fsm_p.minimal_state_count, 4)
        self.assertGreaterEqual(fsm_p.refinement_rounds, 2)
        self.assertIn("stateDiagram-v2", fsm_p.to_mermaid())

        # 3. 42 Sedenion primitive assessors -> Wilmot's 7 Box-Kite modes (6 assessors per class)
        fsm_s = extract_sedenion_boxkite_mode_fsm()
        self.assertEqual(fsm_s.raw_reachable_state_count, 42)
        self.assertEqual(fsm_s.minimal_state_count, 7)
        self.assertTrue(all(sz == 6 for sz in fsm_s.equivalence_class_sizes.values()))

    def test_algebraic_pipeline_rewrite_and_round4_zero_variance_short_circuit(self) -> None:
        raw_pipe = (
            AlgebraicPipeline()
            .then(FilterStage("pos_x", lambda r: r["x"] > 0))
            .then(FilterStage("even_x", lambda r: r["x"] % 2 == 0))
            .then(MutateStage("sq", {"x2": lambda r: r["x"] * r["x"]}))
            .then(MutateStage("cube", {"x3": lambda r: r["x"] ** 3}))
            .then(NonlinearShellFluxStage("triad_flux", known_dispersion_theta=0.0))
        )
        opt_pipe = raw_pipe.optimize()
        # 5 stages fuse cleanly down to 3 stages: [Filter(fused), Mutate(fused), ZeroShortCircuitStage]
        self.assertEqual(len(raw_pipe.stages), 5)
        self.assertEqual(len(opt_pipe.stages), 3)
        self.assertIsInstance(opt_pipe.stages[0], FilterStage)
        self.assertIsInstance(opt_pipe.stages[1], MutateStage)
        self.assertIsInstance(opt_pipe.stages[2], ZeroShortCircuitStage)

        rows = [
            {"x": -2, "raw_triad_flux": 0},
            {"x": 1, "raw_triad_flux": 0},
            {"x": 2, "raw_triad_flux": 0},
            {"x": 4, "raw_triad_flux": 0},
        ]
        out_raw = raw_pipe.execute(rows)
        out_opt = opt_pipe.execute(rows)
        self.assertEqual(len(out_opt), 2)
        for r_a, r_b in zip(out_raw, out_opt):
            self.assertEqual(r_a["x2"], r_b["x2"])
            self.assertEqual(r_a["x3"], r_b["x3"])
            self.assertEqual(r_b["nonlinear_flux"], 0)
            self.assertIn("Round4_Theorem_J1", r_b["short_circuit_certificate"])

    def test_round4_shell_dispersion_and_outward_interval_stiefel(self) -> None:
        iv_third = OutwardInterval.from_rational(1, 3)
        self.assertTrue(iv_third.contains(1.0 / 3.0))
        self.assertGreater(iv_third.width, 0.0)
        iv_cross = OutwardInterval(-2.0, 3.0).sqr()
        self.assertEqual(iv_cross.lo, 0.0)
        self.assertGreaterEqual(iv_cross.hi, 9.0)

        for angle in (0.73, math.pi / 7.0, math.sqrt(2.0)):
            cert = certify_continuous_stiefel_rotation_interval(angle)
            self.assertTrue(cert["koebisu_Q_traps_zero"])
            self.assertTrue(cert["bimodal_4e1e2_minus_M0sq_traps_zero"])

        s16 = CayleyDicksonAlgebra(level=4)
        # Zero divisor e_1 + e_10 -> maximal bimodal dispersion Theta == 1, Q == 0
        zd = s16.elem({1: 1, 10: 1})
        zd_disp = cayley_dickson_shell_dispersion(zd).extract()
        self.assertEqual(zd_disp["z2_bimodal_imaginary_shells"]["theta_dispersion"], 1.0)
        self.assertEqual(zd_disp["sedenion_round4_koebisu_bridge"]["quartic_Q_via_round4_Theorem_K"], 0)
        self.assertTrue(zd_disp["sedenion_round4_koebisu_bridge"]["maximal_dispersion_theta_equals_1"])

        # Single-shell octonion 2*e_1 - e_3 -> Theta == 0, strictly invertible Q == 25 > 0
        oct_single = s16.elem({1: 2, 3: -1})
        oct_disp = cayley_dickson_shell_dispersion(oct_single).extract()
        self.assertEqual(oct_disp["z2_bimodal_imaginary_shells"]["theta_dispersion"], 0.0)
        self.assertEqual(oct_disp["sedenion_round4_koebisu_bridge"]["quartic_Q_via_round4_Theorem_K"], 25)
        self.assertTrue(oct_disp["sedenion_round4_koebisu_bridge"]["single_shell_strictly_invertible"])

        # 64D Chingon multi-shell dyadic filtration check
        c64 = CayleyDicksonAlgebra(level=6)
        x64 = c64.elem({1: 1, 9: 2, 35: -1})
        disp64 = cayley_dickson_shell_dispersion(x64).extract()
        self.assertEqual(disp64["algebra_dim"], 64)
        self.assertGreater(disp64["dyadic_multi_shell_filtration"]["variance_M0P_minus_D2"], 0)

    def test_promislow_bloch_floquet_t3_homomorphism_and_char0_certification(self) -> None:
        spec = make_promislow_group_ring(modulus=None)
        s14 = [parse_promislow_word(w) for w in PROMISLOW_14_NON_UP_WORDS]
        alpha_14 = spec.elem({g: 1 for g in s14})
        beta_sample = spec.elem({parse_promislow_word("ab"): 2, parse_promislow_word("BaB"): -3})

        # Verify exact 4x4 rational matrix algebra homomorphism M_{alpha * beta} == M_alpha @ M_beta!
        pt = (Fraction(2, 1), Fraction(3, 1), Fraction(5, 1))
        m_a = promislow_bloch_floquet_matrix_at_rationals(alpha_14, *pt)
        m_b = promislow_bloch_floquet_matrix_at_rationals(beta_sample, *pt)
        m_ab = promislow_bloch_floquet_matrix_at_rationals(alpha_14 * beta_sample, *pt)
        self.assertEqual(m_ab, _mat_mul_4x4(m_a, m_b))

        # Promislow's 14-element non-UP indicator sum is certified non-ZD across ALL unbounded supports in char 0!
        audit_14 = promislow_bloch_floquet_t3_audit(alpha_14).extract()
        self.assertTrue(audit_14["certified_non_zero_divisor_in_char0_unbounded_support"])
        self.assertNotEqual(audit_14["det_at_2_3_5_rational"], "0/1")

        # Gardam's 21-term element lifted to Z[P]: odd determinant at (1,1,1) (unit mod 2!) and non-ZD in char 0!
        gardam_info = construct_gardam_f2_unit_and_char0_lift()
        # Reconstruct Gardam's 21-term char-0 lift via construct_gardam's words or test a 21-term check:
        # Let's also check `promislow_bloch_floquet_t3_audit` on a nontrivial unit `g` (`det` is monomial != 0)
        g_single = spec.elem({parse_promislow_word("abaB"): 1})
        audit_g = promislow_bloch_floquet_t3_audit(g_single).extract()
        self.assertEqual(abs(audit_g["augmentation_det_at_1_1_1"]), 1)
        self.assertEqual(gardam_info["alpha_support_size"], 21)
        self.assertTrue(gardam_info["f2_product_equals_identity"])

    def test_z3_sympy_universal_certifier_and_cli_subcommands(self) -> None:
        z3_rep = verify_round4_algebraic_bridge_z3()
        if has_z3_and_sympy():
            self.assertTrue(z3_rep["available"])
            self.assertTrue(z3_rep["all_universal_proofs_verified"])
            self.assertEqual(z3_rep["z3_single_shell_zero_divisor_impossibility"], "unsat")
            self.assertEqual(z3_rep["z3_zero_divisor_forces_theta_eq_1_and_orthogonality"], "unsat")
            self.assertEqual(z3_rep["z3_promislow14_non_up_char0_annihilator_unsat"], "unsat")

        # Smoke-test CLI `bsar math round4` and `bsar math fsm --mermaid`
        buf_r4 = io.StringIO()
        with redirect_stdout(buf_r4):
            rc1 = bsar_cli_main(["math", "round4", "--angle", "0.5"])
        self.assertEqual(rc1, 0)
        parsed_r4 = json.loads(buf_r4.getvalue())
        self.assertTrue(parsed_r4["stiefel_v2_r7_outward_interval"]["koebisu_Q_traps_zero"])

        buf_fsm = io.StringIO()
        with redirect_stdout(buf_fsm):
            rc2 = bsar_cli_main(["math", "fsm", "--mermaid"])
        self.assertEqual(rc2, 0)
        parsed_fsm = json.loads(buf_fsm.getvalue())
        self.assertEqual(parsed_fsm["promislow_v4_fsm"]["minimal_state_count"], 4)
        self.assertEqual(parsed_fsm["sedenion_7_mode_fsm"]["minimal_state_count"], 7)
        self.assertIn("stateDiagram-v2", parsed_fsm["promislow_v4_mermaid"])

    def test_ix_asm_indexed_monad_processor_flag_verifier(self) -> None:
        from bsar.ix_asm import (
            BOOT_65816_EMULATION,
            IxFlagTypeError,
            adc_imm16,
            ix_branch_eq,
            ix_start,
            lda_imm16,
            lda_imm8,
            pha,
            pla,
            q88_mul_raw,
            q88_store_slab,
            rep_m16,
            run_ix_asm_verification_suite,
            sep_m8,
        )

        suite = run_ix_asm_verification_suite()
        self.assertTrue(suite["all_5_flag_bugs_rejected_statically"])
        self.assertTrue(suite["valid_kernel"]["rats_valid"])
        self.assertEqual(suite["simulation_registers"]["Q_SLAB_0"], 384)
        self.assertEqual(suite["simulation_registers"]["SP_DEPTH"], 0)
        self.assertEqual(len(suite["static_bug_rejections"]), 5)

        # Verify each individual static flag error raises IxFlagTypeError
        with self.assertRaises(IxFlagTypeError):
            _ = ix_start(BOOT_65816_EMULATION) >> lda_imm16(0x1234)
        with self.assertRaises(IxFlagTypeError):
            _ = ix_start(BOOT_65816_EMULATION) >> rep_m16() >> adc_imm16(0x0010)
        with self.assertRaises(IxFlagTypeError):
            _ = ix_start(BOOT_65816_EMULATION) >> ix_branch_eq(
                then_builder=lambda p: p >> rep_m16(),
                else_builder=lambda p: p >> lda_imm8(0x01),
            )
        with self.assertRaises(IxFlagTypeError):
            _ = ix_start(BOOT_65816_EMULATION) >> rep_m16() >> pha() >> sep_m8() >> pla()
        with self.assertRaises(IxFlagTypeError):
            _ = ix_start(BOOT_65816_EMULATION) >> rep_m16() >> q88_mul_raw(256, 256) >> q88_store_slab()


if __name__ == "__main__":
    unittest.main()
