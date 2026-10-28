#!/usr/bin/env python3
"""
HOSTILE & DETERMINISTIC TEST SUITE FOR EPISTEMIC CONCORDANCE
License: GNU AGPLv3
Attestation: probabilistic_structural
"""

from __future__ import annotations

import copy
from pathlib import Path
import unittest

from bsar_xcube import (
    BsarXCubeCompiler,
    EpistemicState,
    LuaAssociativeNode,
    float_db_to_q8_8,
    hilbert_xy_to_d,
    q8_8_to_float_db,
)
from compile_corpus import (
    EXPECTED_TRENT_SHA256,
    build_concordance_bundle,
    write_static_build,
)
from replicability_ledger import (
    CromwellViolationError,
    EpistemicRugPullError,
    ReplicabilityLedger,
    WitnessChannel,
    ZeroPiiSafetyFloor,
    build_resurrection_replicability_audit,
)


class TestEpistemicConcordance(unittest.TestCase):
    def test_zero_pii_safety_floor_blocks_private_fields(self) -> None:
        floor = ZeroPiiSafetyFloor()
        floor.assert_clean({"topic": "CCC § 604", "verse": "JHN.3.16"})
        with self.assertRaises(ValueError):
            floor.assert_clean({"nested": {"phone_number": "204-555-0100"}})

    def test_bsar_three_pass_determinism_and_r_pipe_immutability(self) -> None:
        c1 = BsarXCubeCompiler()
        node = LuaAssociativeNode(604, pillar="I_CREED", topic="John 3:16", summary="Redemptive love.")
        node.add_thread(
            verse_ref="JHN.3.16",
            cluster_id="CL_JHN316",
            warrant_mode="DIRECT_QUOTE",
            canon_scope="ECUMENICAL_66_SHARED",
            mediator="TRENT_ART_IV",
            decibans=10.0,
        )
        node.add_thread(
            verse_ref="JHN.3.16",
            cluster_id="CL_JHN316",
            warrant_mode="DIRECT_QUOTE",
            canon_scope="ECUMENICAL_66_SHARED",
            mediator="DIRECT_SCRIPTURE",
            decibans=10.0,
        )
        c1.register_node(node)
        slab_a = c1.compile_three_pass()
        slab_b = c1.compile_three_pass()
        self.assertEqual(slab_a["rats_sha256"], slab_b["rats_sha256"])
        self.assertTrue(slab_a["lyapunov_contractive"])

        pipe0 = BsarXCubeCompiler.pipe(slab_a)
        snapshot = copy.deepcopy(pipe0.rows)
        projected = pipe0.eliminate_mediator()
        # Copy-on-modify guarantee: upstream pipe0 never mutates
        self.assertEqual(pipe0.rows, snapshot)
        self.assertEqual(len(pipe0), 2)
        self.assertEqual(len(projected), 1)
        self.assertEqual(projected.rows[0]["mediator"], EpistemicState.DONT_CARE_STAR.value)
        self.assertEqual(len(projected.rows[0]["mediators_expanded"]), 2)

    def test_q8_8_and_hilbert_bijection(self) -> None:
        q = float_db_to_q8_8(10.5)
        self.assertEqual(q, 2688)
        self.assertAlmostEqual(q8_8_to_float_db(q), 10.5, places=4)
        coords = [(1, 1), (604, 14), (1374, 19), (2842, 7)]
        hilbert_ids = [hilbert_xy_to_d(65536, x, y) for x, y in coords]
        self.assertEqual(len(hilbert_ids), len(set(hilbert_ids)))

    def test_epistemic_rug_pull_and_cromwell_floor(self) -> None:
        ledger = ReplicabilityLedger()
        ch = WitnessChannel(
            channel_id="C1",
            cluster_id="CL1",
            title="Primary Witness",
            primary_locus="1 Cor 15:3",
            incentive_profile="COSTLY_NEGATIVE_PAYOFF",
            p_given_hypothesis=0.9,
            p_given_alternative=0.09,
            notes="Test channel",
        )
        with self.assertRaises(CromwellViolationError):
            ledger.register_crux("BAD", "Q", "H1", "H2", 0.0, [ch])

        crux = ledger.register_crux("OK", "Q", "H1", "H2", 0.01, [ch])
        with self.assertRaises(EpistemicRugPullError):
            ledger.evaluate_crux(crux, expected_rubric_sha256="0" * 64)

    def test_hume_replicability_audit_blocks_pseudoreplication_and_harking(self) -> None:
        audit = build_resurrection_replicability_audit()
        clean = audit["clean_single_mechanism_skeptic"]
        patched = audit["patchwork_harking_skeptic_3_patches"]

        # 6 raw channels -> 5 independent clusters (Matthew parallel collapsed onto Markan core!)
        self.assertEqual(clean["raw_channel_count"], 6)
        self.assertEqual(clean["independent_cluster_count"], 5)
        self.assertIn("CH2B_MATTHEW_PARALLEL", clean["pseudoreplication_blocked"])
        # Even at harsh 0.001 (-30 dB) Humean prior, 5 independent costly channels cross >99.9% posterior
        self.assertGreater(clean["posterior_probability"], 0.99)
        self.assertGreater(patched["posterior_decibans"], clean["posterior_decibans"])

    def test_full_trent_ccc_bible_nicene_bundle_and_static_export(self) -> None:
        out_dir = Path(__file__).resolve().parent / "dist"
        stats = write_static_build(out_dir)
        self.assertTrue((out_dir / "index.html").exists())
        self.assertTrue((out_dir / "ccc_trent_bible_xcube.json").exists())
        self.assertGreater(stats["html_bytes"], 20000)

        bundle = build_concordance_bundle()
        self.assertEqual(bundle["trent_witness_sha256"], EXPECTED_TRENT_SHA256)
        props = bundle["nicene_cosmology_boundary"]["propositions"]
        states = {p["state"] for p in props}
        self.assertEqual(states, {"1", "?", "0"})


if __name__ == "__main__":
    unittest.main(verbosity=2)
