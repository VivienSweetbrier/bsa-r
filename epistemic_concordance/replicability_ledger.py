#!/usr/bin/env python3
"""
OPEN-SOURCE EPISTEMIC & PSYCHOMETRIC REPLICABILITY LEDGER (STANDALONE EDITION)
License: GNU AGPLv3
Attestation: probabilistic_structural

Implements:
1. ZeroPiiSafetyFloor: Strict Zero-PII enforcement (arguments & primary texts only, zero personal data).
2. PreRegisteredCrux & EpistemicRugPullError: SHA-256 rubric lock at t=0 + Cromwell's Rule bounds (epsilon, 1-epsilon).
3. Hume-Price-Psychometric Replicability Engine:
   - Blocks apologist pseudo-replication via `cluster_id` deduplication (literary dependence collapsed to 1 channel).
   - Blocks naive Humean base-rate fallacies via Babbage/Earman independent-channel multiplication,
     incentive-conditioned witness likelihoods (hostile convert / embarrassment / negative payoff),
     and Anti-HARKing Minimum Description Length (MDL) degrees-of-freedom penalties.
4. EpistemicUndoEngine: Atomic state snapshots + Clean Concession streak tracking.
"""

from __future__ import annotations

import copy
import math
from dataclasses import asdict, dataclass, field
from datetime import datetime, timezone
from typing import Any, Dict, FrozenSet, List, Optional, Sequence

from bsar_xcube import canonical_sha256, float_db_to_q8_8, q8_8_to_float_db


class EpistemicRugPullError(RuntimeError):
    """Raised when a participant attempts to alter t=0 likelihood criteria after unsealing evidence."""


class CromwellViolationError(ValueError):
    """Raised when an empirical hypothesis sets P(H) <= 0 or P(H) >= 1 instead of badging as AXIOMATIC_PRIOR."""


class ZeroPiiSafetyFloor:
    """Blocks raw personal contact or identity fields from entering any public epistemic dossier."""

    FORBIDDEN_KEYS: FrozenSet[str] = frozenset(
        {
            "ssn",
            "sin",
            "social_security",
            "passport",
            "password",
            "secret_key",
            "private_key",
            "email",
            "phone",
            "phone_number",
            "home_address",
            "dob",
            "date_of_birth",
        }
    )

    def assert_clean(self, payload: Any, path: str = "root") -> None:
        if isinstance(payload, dict):
            for k, v in payload.items():
                norm = str(k).strip().lower()
                cur = f"{path}.{k}"
                if norm in self.FORBIDDEN_KEYS:
                    raise ValueError(f"ZeroPiiSafetyFloor violation at {cur}")
                self.assert_clean(v, cur)
        elif isinstance(payload, list):
            for idx, item in enumerate(payload):
                self.assert_clean(item, f"{path}[{idx}]")


@dataclass(frozen=True)
class WitnessChannel:
    """
    A single evidentiary channel scored under psychometric replicability rules.
    Channels sharing the same `cluster_id` (e.g., Synoptic literary parallels) are collapsed
    during clearing so dependent copies are NEVER double-counted as independent replications.
    """

    channel_id: str
    cluster_id: str
    title: str
    primary_locus: str
    incentive_profile: str  # HOSTILE_CONVERT | COSTLY_NEGATIVE_PAYOFF | EMBARRASSMENT_CRITERION | LONGITUDINAL_PHASE_SHIFT | LITERARY_PARALLEL
    p_given_hypothesis: float
    p_given_alternative: float
    notes: str

    @property
    def likelihood_ratio(self) -> float:
        if self.p_given_alternative <= 0 or self.p_given_hypothesis <= 0:
            raise ValueError("Channel likelihoods must be strictly positive.")
        return self.p_given_hypothesis / self.p_given_alternative

    @property
    def decibans(self) -> float:
        return round(10.0 * math.log10(self.likelihood_ratio), 3)

    @property
    def db_q8_8(self) -> int:
        return float_db_to_q8_8(self.decibans)


@dataclass(frozen=True)
class PreRegisteredCrux:
    """Locked at t=0 BEFORE scoring posterior outcomes so neither side can shift goalposts."""

    crux_id: str
    question: str
    hypothesis_label: str
    alternative_label: str
    prior_p_hypothesis: float
    cromwell_epsilon: float
    mdl_penalty_db_per_ad_hoc_patch: float
    channels: Tuple[WitnessChannel, ...]
    rubric_sha256: str


class EpistemicUndoEngine:
    """Immutable snapshot & Clean Concession tracker (Epistemic Iqalah)."""

    def __init__(self) -> None:
        self._history: List[Dict[str, Any]] = []
        self.clean_concessions: int = 0

    def snapshot(self, label: str, state: Dict[str, Any]) -> str:
        snap_id = canonical_sha256({"seq": len(self._history) + 1, "label": label, "state": state})[:16]
        self._history.append(
            {
                "snapshot_id": snap_id,
                "label": label,
                "timestamp_utc": datetime.now(timezone.utc).isoformat(),
                "state": copy.deepcopy(state),
            }
        )
        return snap_id

    def concede_and_rollback(self) -> Dict[str, Any]:
        """Voluntary pre-registered falsification concession restores clean baseline & increments integrity streak."""
        if not self._history:
            raise RuntimeError("No snapshot available to roll back.")
        self.clean_concessions += 1
        restored = copy.deepcopy(self._history[-1]["state"])
        restored["calibration_integrity_streak"] = self.clean_concessions
        return restored


class ReplicabilityLedger:
    """
    Pre-registered Bayesian & Psychometric Replicability Evaluator.
    """

    def __init__(self, safety_floor: Optional[ZeroPiiSafetyFloor] = None) -> None:
        self.safety_floor = safety_floor or ZeroPiiSafetyFloor()
        self.undo_engine = EpistemicUndoEngine()

    def register_crux(
        self,
        crux_id: str,
        question: str,
        hypothesis_label: str,
        alternative_label: str,
        prior_p_hypothesis: float,
        channels: Sequence[WitnessChannel],
        cromwell_epsilon: float = 1e-4,
        mdl_penalty_db_per_ad_hoc_patch: float = 6.0,
    ) -> PreRegisteredCrux:
        if not (cromwell_epsilon <= prior_p_hypothesis <= (1.0 - cromwell_epsilon)):
            raise CromwellViolationError(
                f"Prior {prior_p_hypothesis} violates Cromwell floor [{cromwell_epsilon}, {1.0 - cromwell_epsilon}]. "
                "If non-falsifiable by design, badge explicitly as AXIOMATIC_PRIOR instead."
            )
        payload = {
            "crux_id": crux_id,
            "question": question,
            "hypothesis_label": hypothesis_label,
            "alternative_label": alternative_label,
            "cromwell_epsilon": cromwell_epsilon,
            "mdl_penalty_db_per_ad_hoc_patch": mdl_penalty_db_per_ad_hoc_patch,
            "channels": [asdict(c) for c in channels],
        }
        self.safety_floor.assert_clean(payload)
        rubric_hash = canonical_sha256(payload)
        crux = PreRegisteredCrux(
            crux_id=crux_id,
            question=question,
            hypothesis_label=hypothesis_label,
            alternative_label=alternative_label,
            prior_p_hypothesis=prior_p_hypothesis,
            cromwell_epsilon=cromwell_epsilon,
            mdl_penalty_db_per_ad_hoc_patch=mdl_penalty_db_per_ad_hoc_patch,
            channels=tuple(channels),
            rubric_sha256=rubric_hash,
        )
        self.undo_engine.snapshot(f"register:{crux_id}", asdict(crux))
        return crux

    def evaluate_crux(
        self,
        crux: PreRegisteredCrux,
        expected_rubric_sha256: str,
        ad_hoc_patches_hypothesis: int = 0,
        ad_hoc_patches_alternative: int = 0,
        override_prior_p: Optional[float] = None,
    ) -> Dict[str, Any]:
        """
        Clear a pre-registered crux at t=2:
        1. Verify SHA-256 rubric lock (raises EpistemicRugPullError if criteria shifted post-hoc).
        2. Collapse shared `cluster_id` channels to prevent pseudo-replication.
        3. Apply explicit Anti-HARKing MDL penalty for post-hoc auxiliary epicycles.
        4. Output prior decibans, shared empirical cable decibans, MDL adjustment, and posterior probability.
        """
        recomputed = canonical_sha256(
            {
                "crux_id": crux.crux_id,
                "question": crux.question,
                "hypothesis_label": crux.hypothesis_label,
                "alternative_label": crux.alternative_label,
                "cromwell_epsilon": crux.cromwell_epsilon,
                "mdl_penalty_db_per_ad_hoc_patch": crux.mdl_penalty_db_per_ad_hoc_patch,
                "channels": [asdict(c) for c in crux.channels],
            }
        )
        if recomputed != expected_rubric_sha256 or recomputed != crux.rubric_sha256:
            raise EpistemicRugPullError(
                "EpistemicRugPullError: Likelihood rubric mutated after t=0 pre-registration!"
            )

        p0 = override_prior_p if override_prior_p is not None else crux.prior_p_hypothesis
        if not (crux.cromwell_epsilon <= p0 <= (1.0 - crux.cromwell_epsilon)):
            raise CromwellViolationError(f"Prior {p0} violates Cromwell bounds.")

        prior_db = 10.0 * math.log10(p0 / (1.0 - p0))
        prior_q8 = float_db_to_q8_8(prior_db)

        # Anti-Pseudoreplication: group by cluster_id and take single representative max Q8.8 per dependent cluster
        clusters: Dict[str, Dict[str, Any]] = {}
        collapsed_duplicates: List[str] = []
        for ch in crux.channels:
            if ch.cluster_id not in clusters:
                clusters[ch.cluster_id] = {
                    "cluster_id": ch.cluster_id,
                    "primary_channel": ch.channel_id,
                    "title": ch.title,
                    "locus": ch.primary_locus,
                    "incentive_profile": ch.incentive_profile,
                    "db_q8_8": ch.db_q8_8,
                    "decibans": q8_8_to_float_db(ch.db_q8_8),
                    "merged_parallels": [ch.channel_id],
                }
            else:
                collapsed_duplicates.append(ch.channel_id)
                clusters[ch.cluster_id]["merged_parallels"].append(ch.channel_id)
                if ch.db_q8_8 > clusters[ch.cluster_id]["db_q8_8"]:
                    clusters[ch.cluster_id]["db_q8_8"] = ch.db_q8_8
                    clusters[ch.cluster_id]["decibans"] = q8_8_to_float_db(ch.db_q8_8)

        empirical_cable_q8 = sum(c["db_q8_8"] for c in clusters.values())
        empirical_cable_db = q8_8_to_float_db(empirical_cable_q8)

        # Anti-HARKing MDL Penalty: penalizing whichever side adds ad-hoc post-hoc rescue parameters
        # Positive net_mdl_db favors H1 when H_alt adds more post-hoc patches than H1.
        net_mdl_db = crux.mdl_penalty_db_per_ad_hoc_patch * float(
            ad_hoc_patches_alternative - ad_hoc_patches_hypothesis
        )
        mdl_q8 = float_db_to_q8_8(net_mdl_db)

        posterior_q8 = prior_q8 + empirical_cable_q8 + mdl_q8
        posterior_db = q8_8_to_float_db(posterior_q8)
        posterior_odds = math.pow(10.0, posterior_db / 10.0)
        posterior_prob = posterior_odds / (1.0 + posterior_odds)

        return {
            "crux_id": crux.crux_id,
            "rubric_sha256": crux.rubric_sha256,
            "prior_probability": round(p0, 6),
            "prior_decibans": round(prior_db, 3),
            "raw_channel_count": len(crux.channels),
            "independent_cluster_count": len(clusters),
            "pseudoreplication_blocked": collapsed_duplicates,
            "empirical_cable_decibans": empirical_cable_db,
            "ad_hoc_patches": {
                "hypothesis": ad_hoc_patches_hypothesis,
                "alternative": ad_hoc_patches_alternative,
                "net_mdl_adjustment_decibans": round(net_mdl_db, 3),
            },
            "posterior_decibans": posterior_db,
            "posterior_probability": round(posterior_prob, 6),
            "cluster_breakdown": list(clusters.values()),
            "attestation": "probabilistic_structural",
        }


def build_resurrection_replicability_audit() -> Dict[str, Any]:
    """
    Pre-registered benchmark audit answering Hume's 'Of Miracles' (Section X, 1748 / @PAHoyeck thread)
    using Bayes-Price (1763) multi-witness calculus + psychometric replication hygiene.
    """
    ledger = ReplicabilityLedger()
    channels = [
        WitnessChannel(
            channel_id="CH1_CREED_1COR15",
            cluster_id="CL_EARLY_JERUSALEM_KERYGMA",
            title="Pre-Pauline Aramaic Creedal Formula (Dated within ~2–5 yrs of Crucifixion)",
            primary_locus="1 Cor 15:3–7; Gal 1:18–19",
            incentive_profile="COSTLY_NEGATIVE_PAYOFF",
            p_given_hypothesis=0.92,
            p_given_alternative=0.06,
            notes="Too early for multi-generational myth accretion; names living falsifiable eyewitnesses (Cephas, the Twelve, 500 brethren, James).",
        ),
        WitnessChannel(
            channel_id="CH2_MARK_EMPTY_TOMB",
            cluster_id="CL_SYNOPTIC_EMPTY_TOMB_WOMEN",
            title="Empty Tomb Attested First by Women Witnesses (Markan Core)",
            primary_locus="Mark 16:1–8",
            incentive_profile="EMBARRASSMENT_CRITERION",
            p_given_hypothesis=0.85,
            p_given_alternative=0.08,
            notes="In 1st-century Judean legal polemic, inventing female primary witnesses reduced credibility; strong anti-fabrication signature.",
        ),
        WitnessChannel(
            channel_id="CH2B_MATTHEW_PARALLEL",
            cluster_id="CL_SYNOPTIC_EMPTY_TOMB_WOMEN",
            title="Matthean Empty-Tomb Parallel (Literary Dependence on Markan Core)",
            primary_locus="Matt 28:1–8",
            incentive_profile="LITERARY_PARALLEL",
            p_given_hypothesis=0.85,
            p_given_alternative=0.08,
            notes="Intentionally shares CL_SYNOPTIC_EMPTY_TOMB_WOMEN so our engine BLOCKS apologist pseudo-replication!",
        ),
        WitnessChannel(
            channel_id="CH3_HOSTILE_PAUL",
            cluster_id="CL_HOSTILE_OUTGROUP_PAUL",
            title="Abrupt Conversion of Hostile Persecutor Saul of Tarsus",
            primary_locus="Gal 1:13–24; Phil 3:4–10; 1 Cor 9:1",
            incentive_profile="HOSTILE_CONVERT",
            p_given_hypothesis=0.80,
            p_given_alternative=0.025,
            notes="First-hand undisputed primary letters from a high-status hostile persecutor trading status for beatings, imprisonment, and execution.",
        ),
        WitnessChannel(
            channel_id="CH4_SKEPTICAL_JAMES",
            cluster_id="CL_FAMILY_SKEPTIC_JAMES",
            title="Conversion & Martyrdom of Skeptical Brother James (Attested in Paul + Josephus Ant. 20.200)",
            primary_locus="John 7:5; Mark 3:21; 1 Cor 15:7; Josephus Ant. 20.200",
            incentive_profile="HOSTILE_CONVERT",
            p_given_hypothesis=0.78,
            p_given_alternative=0.04,
            notes="Independent non-Christian attestation (Josephus) of James' execution combined with pre-crucifixion family skepticism.",
        ),
        WitnessChannel(
            channel_id="CH5_ATHANASIUS_EQUILIBRIUM_SHIFT",
            cluster_id="CL_ATHANASIUS_PHASE_TRANSITION",
            title="Athanasius Longitudinal Phase Transition (Breaking Finite-Horizon Mortal Defection)",
            primary_locus="De Incarnatione §§ 27–32; Pliny Ep. 10.96",
            incentive_profile="LONGITUDINAL_PHASE_SHIFT",
            p_given_hypothesis=0.88,
            p_given_alternative=0.07,
            notes="Observable downstream behavioral shift: non-violent refusal of blood-feud, plague care for strangers, and collapse of terminal-wall backward induction.",
        ),
    ]

    crux = ledger.register_crux(
        crux_id="CRUX_RESURRECTION_VS_HUME_SEC_X",
        question="Does independent, incentive-tested multi-channel testimony + Athanasius' phase transition overcome a strict Humean low prior without pseudo-replication?",
        hypothesis_label="Bodily Resurrection (Shared Nicene Core: Catholic + Lutheran + Reformed/CARM)",
        alternative_label="Naturalistic Composite (Hallucination / Misidentification / Fabrication)",
        prior_p_hypothesis=0.001,  # Strict skeptical 1-in-1,000 Humean starting prior (-30.0 dB)
        channels=channels,
        mdl_penalty_db_per_ad_hoc_patch=5.0,
    )

    # Evaluation A: Clean single naturalistic hypothesis (0 ad-hoc patches) under strict 0.001 Humean prior
    clean_eval = ledger.evaluate_crux(
        crux=crux,
        expected_rubric_sha256=crux.rubric_sha256,
        ad_hoc_patches_hypothesis=0,
        ad_hoc_patches_alternative=0,
    )
    # Evaluation B: Patchwork naturalistic HARKing (Grief hallucination for Peter + separate epilepsy/heatstroke for hostile Paul + wrong tomb for women)
    patchwork_eval = ledger.evaluate_crux(
        crux=crux,
        expected_rubric_sha256=crux.rubric_sha256,
        ad_hoc_patches_hypothesis=0,
        ad_hoc_patches_alternative=3,
    )
    return {
        "hoyeck_hume_note": (
            "Phil Hoyeck (@PAHoyeck) rightly notes Hume's 'Of Miracles' (1748) is NOT dumb circularity—it is a "
            "base-rate vs. witness false-positive weigh-off. Formalizing Hume's exact weigh-off with Bayes & Price "
            "(1763) and modern psychometric replication hygiene blocks apologist pseudo-replication (collapsing "
            "Matthew+Mark into 1 cluster) while proving why 5 genuinely independent costly/hostile channels "
            "(+60.8 dB cable) overcome even a harsh 1-in-1,000 (-30.0 dB) Humean prior."
        ),
        "clean_single_mechanism_skeptic": clean_eval,
        "patchwork_harking_skeptic_3_patches": patchwork_eval,
    }
