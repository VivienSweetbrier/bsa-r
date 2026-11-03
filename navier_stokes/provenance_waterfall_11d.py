#!/usr/bin/env python3
"""
STANDALONE PROVENANCE-TO-PAYMENT WATERFALL ENGINE (`provenance_waterfall_11d.py`)
Implements Contingent Claims Register v1.0 (Protocol Rules `4a`–`4f`) in Exact Rational Arithmetic
over `11d-spreadsheet-poc/ledger.py` (`https://sweetbrier.si/11d`).

Governance & Scope Isolation (`Node 0` / `Node 1` / `Node 2` · `probabilistic_structural`):
  - Standalone contingent allocation & provenance-ledger engine. Makes ZERO mathematical prize claims
    and transmits ZERO unsolicited external notifications.
  - Configured in Christopher's `100% Give-It-Away` mode (`architect_retain = Fraction(0, 1)`):
    0% retained by Architect; 100% of any contingent proceeds flow outward across living collaborators,
    direct mathematical dependencies, 65c816/Lean4/Z3/R tool lineage, memorial funds, and the
    Winnipeg 18-Organization Mutual-Aid Endowment.
  - Enforces the Six Frozen Protocol Rules (`4a`–`4f`):
      4a. Frozen bibliography (`bsar_navier_stokes.bib`, all 33 keys + upstream tool nodes) -> finite acyclic DAG.
      4b. Axis 7 (`reason`) separates epistemic credit (`exposition`/`background` -> 0 cash weight) from
          load-bearing entitlement (`theorem_dependency`, `code_dependency`, `tool_lineage`, `data`).
      4c. Pool-first rational partition (`P1_COLLAB`, `P2_MATH_DEP`, `P3_TOOL_LINEAGE`,
          `P4_ESTATES_MEMORIAL`, `P5_ENDOWMENT`) — never pricing Newton or Hilbert ad-hoc.
      4d. Exact `fractions.Fraction` recursive waterfall (`retain 1 - rho`, `pass rho` upstream),
          with sub-threshold dust `< epsilon_dust` swept deterministically to `P5_ENDOWMENT`.
      4e. Axis 8 (`consent`) gate: living citees carry `UNCLAIMED` status with zero obligation until
          affirmative bilateral opt-in; non-living lineage routes strictly to `P4_ESTATES_MEMORIAL` fiduciaries.
      4f. Strict three-way separation:
            (i)   Axis 5 + Axis 7  = Epistemic Lineage Finding (who made the work possible),
            (ii)  Waterfall+Axis 8 = Contingent Payability Finding (what the rules make payable),
            (iii) Axis 11          = Settlement Receipt Finding (countersigned SHA-256 proof of payment).
"""

from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction
import hashlib
import json
import re
import sys
from pathlib import Path
from typing import Any, Dict, FrozenSet, List, Optional, Sequence, Set, Tuple

_HERE = Path(__file__).resolve().parent
_WORKSPACE = _HERE.parent
_BSAR_ROOT = _WORKSPACE / "bsa-r" if (_WORKSPACE / "bsa-r").exists() else _HERE.parent

for p in (str(_WORKSPACE), str(_BSAR_ROOT)):
    if p not in sys.path:
        sys.path.insert(0, p)

from navier_stokes_snipe.bsar_navier_millennium import load_portable_eleven_entry_ledger  # noqa: E402


AXIS7_LOAD_BEARING_REASONS: FrozenSet[str] = frozenset(
    {"theorem_dependency", "code_dependency", "tool_lineage", "data"}
)
AXIS7_ATTRIBUTION_ONLY_REASONS: FrozenSet[str] = frozenset({"exposition", "background"})
AXIS7_ALL_REASONS: FrozenSet[str] = AXIS7_LOAD_BEARING_REASONS | AXIS7_ATTRIBUTION_ONLY_REASONS

FROZEN_POOL_SHARES_GIVE_100_AWAY: Dict[str, Fraction] = {
    "P0_ARCHITECT_RETAIN": Fraction(0, 100),   # 0.0% — Christopher gives 100% away!
    "P1_COLLAB": Fraction(35, 100),            # 35.0% — Living PDE & Formal Lean 4 Co-Authors
    "P2_MATH_DEP": Fraction(15, 100),          # 15.0% — Living theorem_dependency lineage
    "P3_TOOL_LINEAGE": Fraction(15, 100),      # 15.0% — Living 65c816/Asar + Lean 4 + Z3 + R toolsmiths
    "P4_ESTATES_MEMORIAL": Fraction(10, 100),  # 10.0% — Predetermined estates & memorial fellowships
    "P5_ENDOWMENT": Fraction(25, 100),         # 25.0% — Winnipeg 18-Org Mutual-Aid baseline + dust/unclaimed sink
}


@dataclass(frozen=True)
class ProvenanceNode:
    node_id: str
    title: str
    axis7_reason: str
    pool_id: Optional[str]          # None for root or attribution-only (`exposition` / `background`) nodes
    seed_weight_in_pool: Fraction   # Relative rational weight inside `pool_id` (0 for attribution-only)
    beneficiary_account: str        # Account ID on the Eleven-Entry Bookkeeping ledger
    consent_owner: str              # Living party or predetermined memorial trustee required on Axis 8
    is_living_beneficiary: bool     # False => routed via predetermined `P4_ESTATES_MEMORIAL` fiduciary (Rule 4e)
    upstream_edges: Tuple[Tuple[str, Fraction], ...] = ()  # Outgoing citations toward GENESIS (v, weight)


def parse_bibtex_keys(bib_path: Path) -> List[str]:
    """Parse all `@type{key,` citation keys from `bsar_navier_stokes.bib` in file order."""
    raw = bib_path.read_text(encoding="utf-8")
    return re.findall(r"@\w+\{\s*([^,\s]+)\s*,", raw)


def build_frozen_navier_provenance_dag(bib_path: Optional[Path] = None) -> Dict[str, ProvenanceNode]:
    """
    Construct the frozen acyclic Axis-5 provenance graph covering ALL 33 BibTeX entries in
    `bsar_navier_stokes.bib` plus the co-author & 65c816/R software-lineage nodes (`Rule 4a` & `4b`).
    """
    if bib_path is None:
        cand1 = _BSAR_ROOT / "navier_stokes" / "bsar_navier_stokes.bib"
        cand2 = _HERE / "bsar_navier_stokes.bib"
        bib_path = cand1 if cand1.exists() else cand2

    nodes_list: List[ProvenanceNode] = [
        # Root work (`THIS_WORK` = duguay2026zenodo, Architect retains 0/1!)
        ProvenanceNode(
            node_id="duguay2026zenodo",
            title="BSA-R x Eleven-Entry Bookkeeping (Christopher Duguay, 2026 — 0% Architect Retain)",
            axis7_reason="code_dependency",
            pool_id="P0_ARCHITECT_RETAIN",
            seed_weight_in_pool=Fraction(1, 1),
            beneficiary_account="Architect_Zero_Retain_PassThrough",
            consent_owner="Topher",
            is_living_beneficiary=True,
            upstream_edges=(),
        ),
        # P1_COLLAB (35%): Living PDE & Formal Lean 4 Co-Authors (25% Lead PDE + 10% Formal Lean/CAP Appendix)
        ProvenanceNode(
            node_id="collab_lead_pde_coauthor",
            title="Lead Academic PDE Co-Author Slot (Target Lemma BIOT-SAVART-BIMODAL-3D)",
            axis7_reason="theorem_dependency",
            pool_id="P1_COLLAB",
            seed_weight_in_pool=Fraction(5, 7),  # 25/35 of P1 = 25% of total
            beneficiary_account="Lead_PDE_Collaborator_Escrow",
            consent_owner="LeadPDECoAuthor",
            is_living_beneficiary=True,
            upstream_edges=(("tao2016", Fraction(1, 2)), ("fefferman2000", Fraction(1, 2))),
        ),
        ProvenanceNode(
            node_id="collab_lean4_cap_coauthor",
            title="Formal Lean 4 & Interval-CAP Appendix Co-Author Slot",
            axis7_reason="code_dependency",
            pool_id="P1_COLLAB",
            seed_weight_in_pool=Fraction(2, 7),  # 10/35 of P1 = 10% of total
            beneficiary_account="Formal_Lean4_CAP_Collaborator_Escrow",
            consent_owner="Lean4CAPCoAuthor",
            is_living_beneficiary=True,
            upstream_edges=(("lean4_2021", Fraction(1, 2)), ("vdblessard2015", Fraction(1, 2))),
        ),
        # P2_MATH_DEP (15%): Living load-bearing `theorem_dependency` works in `bsar_navier_stokes.bib`
        ProvenanceNode(
            node_id="fefferman2000",
            title="Charles L. Fefferman (2000/2006) Clay Option B Specification",
            axis7_reason="theorem_dependency",
            pool_id="P2_MATH_DEP",
            seed_weight_in_pool=Fraction(2, 15),
            beneficiary_account="Fefferman_OptionB_Lineage_Acct",
            consent_owner="C_Fefferman",
            is_living_beneficiary=True,
            upstream_edges=(("leray1934", Fraction(1, 1)),),
        ),
        ProvenanceNode(
            node_id="leilin2011",
            title="Zhen Lei & Fanghua Lin (2011) Wiener F^0 < nu Global Mild Gate",
            axis7_reason="theorem_dependency",
            pool_id="P2_MATH_DEP",
            seed_weight_in_pool=Fraction(3, 15),
            beneficiary_account="Lei_Lin_Wiener_Gate_Acct",
            consent_owner="Lei_and_Lin",
            is_living_beneficiary=True,
            upstream_edges=(("leray1934", Fraction(1, 2)), ("fujitakato1964", Fraction(1, 2))),
        ),
        ProvenanceNode(
            node_id="tao2016",
            title="Terence Tao (2016) Averaged 3D Navier-Stokes Bimodal Blow-Up Barrier",
            axis7_reason="theorem_dependency",
            pool_id="P2_MATH_DEP",
            seed_weight_in_pool=Fraction(3, 15),
            beneficiary_account="Tao_Bimodal_Barrier_Acct",
            consent_owner="T_Tao",
            is_living_beneficiary=True,
            upstream_edges=(("leray1934", Fraction(1, 1)),),
        ),
        ProvenanceNode(
            node_id="vdblessard2015",
            title="Jan Bouwe van den Berg & Jean-Philippe Lessard (2015) Radii-Polynomial CAP",
            axis7_reason="theorem_dependency",
            pool_id="P2_MATH_DEP",
            seed_weight_in_pool=Fraction(2, 15),
            beneficiary_account="VdBerg_Lessard_CAP_Acct",
            consent_owner="VdBerg_and_Lessard",
            is_living_beneficiary=True,
            upstream_edges=(("ariolikoch2010", Fraction(1, 1)),),
        ),
        ProvenanceNode(
            node_id="ariolikoch2010",
            title="Gianni Arioli & Hans Koch (2010) Dissipative PDE CAP Enclosure",
            axis7_reason="theorem_dependency",
            pool_id="P2_MATH_DEP",
            seed_weight_in_pool=Fraction(1, 15),
            beneficiary_account="Arioli_Koch_Dissipative_CAP_Acct",
            consent_owner="Arioli_and_Koch",
            is_living_beneficiary=True,
            upstream_edges=(),
        ),
        ProvenanceNode(
            node_id="foiastemam1989",
            title="Ciprian Foias & Roger Temam (1989) Gevrey-1 Analyticity Strip",
            axis7_reason="theorem_dependency",
            pool_id="P2_MATH_DEP",
            seed_weight_in_pool=Fraction(1, 15),
            beneficiary_account="Temam_Gevrey_Lineage_Acct",
            consent_owner="R_Temam",
            is_living_beneficiary=True,
            upstream_edges=(("memorial_foias_fellowship", Fraction(1, 2)), ("leray1934", Fraction(1, 2))),
        ),
        ProvenanceNode(
            node_id="doeringtiti1995",
            title="Charles R. Doering & Edriss S. Titi (1995) Exponential Spectrum Decay",
            axis7_reason="theorem_dependency",
            pool_id="P2_MATH_DEP",
            seed_weight_in_pool=Fraction(1, 15),
            beneficiary_account="Titi_Exponential_Spectrum_Acct",
            consent_owner="E_Titi",
            is_living_beneficiary=True,
            upstream_edges=(("memorial_doering_fund", Fraction(1, 1)),),
        ),
        ProvenanceNode(
            node_id="constantinmajda1988",
            title="Peter Constantin & Andrew Majda (1988) Beltrami Curl Spectrum",
            axis7_reason="theorem_dependency",
            pool_id="P2_MATH_DEP",
            seed_weight_in_pool=Fraction(1, 15),
            beneficiary_account="Constantin_Beltrami_Acct",
            consent_owner="P_Constantin",
            is_living_beneficiary=True,
            upstream_edges=(("memorial_majda_fund", Fraction(1, 1)),),
        ),
        ProvenanceNode(
            node_id="waleffe1992",
            title="Fabian Waleffe (1992) Helical Triad Instability & Depletion",
            axis7_reason="theorem_dependency",
            pool_id="P2_MATH_DEP",
            seed_weight_in_pool=Fraction(1, 30),
            beneficiary_account="Waleffe_Helical_Triads_Acct",
            consent_owner="F_Waleffe",
            is_living_beneficiary=True,
            upstream_edges=(),
        ),
        ProvenanceNode(
            node_id="moreno1998",
            title="Guillermo Moreno (1998) Cayley-Dickson Zero-Divisor Decomposition",
            axis7_reason="theorem_dependency",
            pool_id="P2_MATH_DEP",
            seed_weight_in_pool=Fraction(1, 60),
            beneficiary_account="Moreno_CayleyDickson_Acct",
            consent_owner="G_Moreno",
            is_living_beneficiary=True,
            upstream_edges=(),
        ),
        ProvenanceNode(
            node_id="grigg2005",
            title="Ian Grigg (2005) Ricardian Triple-Entry Shared Receipt (Axis 11)",
            axis7_reason="theorem_dependency",
            pool_id="P2_MATH_DEP",
            seed_weight_in_pool=Fraction(1, 60),
            beneficiary_account="Grigg_Ricardian_Receipt_Acct",
            consent_owner="I_Grigg",
            is_living_beneficiary=True,
            upstream_edges=(("ijiri1989", Fraction(1, 1)),),
        ),
        # P3_TOOL_LINEAGE (15%): Provers, SMT solvers, R runtime & 42-year 65c816 assembler chain
        ProvenanceNode(
            node_id="lean4_2021",
            title="Leonardo de Moura & Sebastian Ullrich (2021) Lean 4 Theorem Prover / Lean FRO",
            axis7_reason="tool_lineage",
            pool_id="P3_TOOL_LINEAGE",
            seed_weight_in_pool=Fraction(4, 15),
            beneficiary_account="Lean_FRO_Open_Source_Fund",
            consent_owner="LeanFRO_Trustee",
            is_living_beneficiary=True,
            upstream_edges=(("z3_2008", Fraction(1, 1)),),
        ),
        ProvenanceNode(
            node_id="z3_2008",
            title="Leonardo de Moura & Nikolaj Bjorner (2008) Z3 SMT Solver",
            axis7_reason="tool_lineage",
            pool_id="P3_TOOL_LINEAGE",
            seed_weight_in_pool=Fraction(2, 15),
            beneficiary_account="Z3_Theorem_Prover_Fellowship",
            consent_owner="Z3_Maintainers",
            is_living_beneficiary=True,
            upstream_edges=(),
        ),
        ProvenanceNode(
            node_id="r_foundation_pipes",
            title="R Core Team & R Foundation (Base R `|>` Pipe & Statistical Runtime)",
            axis7_reason="tool_lineage",
            pool_id="P3_TOOL_LINEAGE",
            seed_weight_in_pool=Fraction(3, 15),
            beneficiary_account="R_Foundation_for_Statistical_Computing",
            consent_owner="R_Foundation_Board",
            is_living_beneficiary=True,
            upstream_edges=(),
        ),
        ProvenanceNode(
            node_id="alcaro_smwcentral_asar_2011",
            title="Alcaro, RPGHacker, randomdude999, KungFuFurby & SMWCentral Asar 3-Pass Assembler",
            axis7_reason="tool_lineage",
            pool_id="P3_TOOL_LINEAGE",
            seed_weight_in_pool=Fraction(3, 15),
            beneficiary_account="SMWCentral_Asar_Maintainers_Pool",
            consent_owner="Asar_Maintainers",
            is_living_beneficiary=True,
            upstream_edges=(("near_byuu_xkas_2004", Fraction(1, 1)),),
        ),
        ProvenanceNode(
            node_id="norman_yen_trasm_1993",
            title="Norman Yen / Minus (1993-1997) SNES Assembler, TRASM & x816 + Trashkas",
            axis7_reason="tool_lineage",
            pool_id="P3_TOOL_LINEAGE",
            seed_weight_in_pool=Fraction(1, 15),
            beneficiary_account="Norman_Yen_TRASM_x816_Lineage_Acct",
            consent_owner="Norman_Yen",
            is_living_beneficiary=True,
            upstream_edges=(
                ("wdc_mensch_1984", Fraction(1, 2)),
                ("westerfield_orcam_1986", Fraction(1, 4)),
                ("bredon_merlin_1986", Fraction(1, 4)),
            ),
        ),
        ProvenanceNode(
            node_id="wdc_mensch_1984",
            title="Bill Mensch / Western Design Center (1984) W65C816S Silicon & Macro Assembler",
            axis7_reason="tool_lineage",
            pool_id="P3_TOOL_LINEAGE",
            seed_weight_in_pool=Fraction(1, 15),
            beneficiary_account="WDC_65c816_Engineering_Scholarship",
            consent_owner="WDC_Mensch",
            is_living_beneficiary=True,
            upstream_edges=(),
        ),
        ProvenanceNode(
            node_id="westerfield_orcam_1986",
            title="Mike Westerfield / The Byte Works (1986) Apple IIgs ORCA/M 65c816 Assembler",
            axis7_reason="tool_lineage",
            pool_id="P3_TOOL_LINEAGE",
            seed_weight_in_pool=Fraction(1, 15),
            beneficiary_account="ByteWorks_ORCAM_Lineage_Acct",
            consent_owner="M_Westerfield",
            is_living_beneficiary=True,
            upstream_edges=(),
        ),
        # P4_ESTATES_MEMORIAL (10%): Non-living lineage routed strictly to predetermined fiduciaries (`Rule 4e`)
        ProvenanceNode(
            node_id="ladyzhenskaya1967",
            title="Olga A. Ladyzhenskaya (1967) Non-Newtonian Shear-Thickening Regularity -> Memorial Fellowship",
            axis7_reason="theorem_dependency",
            pool_id="P4_ESTATES_MEMORIAL",
            seed_weight_in_pool=Fraction(2, 10),
            beneficiary_account="Olga_Ladyzhenskaya_Memorial_Fellowship",
            consent_owner="Ladyzhenskaya_Memorial_Trustee",
            is_living_beneficiary=False,
            upstream_edges=(("leray1934", Fraction(1, 1)),),
        ),
        ProvenanceNode(
            node_id="leray1934",
            title="Jean Leray (1934) Solenoidal Projector & Energy Inequality -> Memorial Mathematics Fund",
            axis7_reason="theorem_dependency",
            pool_id="P4_ESTATES_MEMORIAL",
            seed_weight_in_pool=Fraction(2, 10),
            beneficiary_account="Jean_Leray_Memorial_Math_Fund",
            consent_owner="Leray_Memorial_Trustee",
            is_living_beneficiary=False,
            upstream_edges=(),
        ),
        ProvenanceNode(
            node_id="ijiri1989",
            title="Yuji Ijiri (1989) Momentum Accounting (Axis 10) -> CMU Accounting Scholarship",
            axis7_reason="theorem_dependency",
            pool_id="P4_ESTATES_MEMORIAL",
            seed_weight_in_pool=Fraction(1, 10),
            beneficiary_account="Yuji_Ijiri_Memorial_Scholarship",
            consent_owner="Ijiri_Memorial_Trustee",
            is_living_beneficiary=False,
            upstream_edges=(),
        ),
        ProvenanceNode(
            node_id="demarrais2000",
            title="Robert P. C. de Marrais (2000) 42 Sedenion Assessors & 7 Box-Kites -> Preservation Fund",
            axis7_reason="theorem_dependency",
            pool_id="P4_ESTATES_MEMORIAL",
            seed_weight_in_pool=Fraction(1, 10),
            beneficiary_account="DeMarrais_Open_Science_Preservation_Fund",
            consent_owner="OpenScience_Memorial_Trustee",
            is_living_beneficiary=False,
            upstream_edges=(),
        ),
        ProvenanceNode(
            node_id="near_byuu_xkas_2004",
            title="Near / byuu (2004-2010) xkas Multipass 65c816 Assembler -> Preservation & Mental Health Fund",
            axis7_reason="tool_lineage",
            pool_id="P4_ESTATES_MEMORIAL",
            seed_weight_in_pool=Fraction(2, 10),
            beneficiary_account="Near_xkas_Preservation_and_Mental_Health_Fund",
            consent_owner="Preservation_MentalHealth_Trustee",
            is_living_beneficiary=False,
            upstream_edges=(("norman_yen_trasm_1993", Fraction(1, 1)),),
        ),
        ProvenanceNode(
            node_id="bredon_merlin_1986",
            title="Glen Bredon (1986) Merlin 8/16 Apple IIgs Assembler -> Bredon Memorial CS Fund",
            axis7_reason="tool_lineage",
            pool_id="P4_ESTATES_MEMORIAL",
            seed_weight_in_pool=Fraction(1, 20),
            beneficiary_account="Glen_Bredon_Merlin16_Memorial_Fund",
            consent_owner="Bredon_Memorial_Trustee",
            is_living_beneficiary=False,
            upstream_edges=(),
        ),
        ProvenanceNode(
            node_id="memorial_foias_fellowship",
            title="Ciprian Foias Memorial PDE Fellowship",
            axis7_reason="theorem_dependency",
            pool_id="P4_ESTATES_MEMORIAL",
            seed_weight_in_pool=Fraction(1, 20),
            beneficiary_account="Ciprian_Foias_Memorial_PDE_Fellowship",
            consent_owner="Foias_Memorial_Trustee",
            is_living_beneficiary=False,
            upstream_edges=(),
        ),
        ProvenanceNode(
            node_id="memorial_doering_fund",
            title="Charles R. Doering Memorial Applied Mathematics Fund",
            axis7_reason="theorem_dependency",
            pool_id="P4_ESTATES_MEMORIAL",
            seed_weight_in_pool=Fraction(1, 20),
            beneficiary_account="Charles_Doering_Memorial_Math_Fund",
            consent_owner="Doering_Memorial_Trustee",
            is_living_beneficiary=False,
            upstream_edges=(),
        ),
        ProvenanceNode(
            node_id="memorial_majda_fund",
            title="Andrew J. Majda Memorial Turbulence & Climate Fellowship",
            axis7_reason="theorem_dependency",
            pool_id="P4_ESTATES_MEMORIAL",
            seed_weight_in_pool=Fraction(1, 20),
            beneficiary_account="Andrew_Majda_Memorial_Fellowship",
            consent_owner="Majda_Memorial_Trustee",
            is_living_beneficiary=False,
            upstream_edges=(),
        ),
        # P5_ENDOWMENT (25% baseline + 100% deterministic dust & unclaimed Axis-8 sink)
        ProvenanceNode(
            node_id="winnipeg_18_org_endowment",
            title="Winnipeg 18-Organization Food-Security & Church Mutual-Aid Endowment",
            axis7_reason="data",
            pool_id="P5_ENDOWMENT",
            seed_weight_in_pool=Fraction(1, 1),
            beneficiary_account="Winnipeg_18_Org_Mutual_Aid_Endowment",
            consent_owner="Harvest_MutualAid",
            is_living_beneficiary=True,
            upstream_edges=(),
        ),
        # Attribution-Only BibTeX Nodes (`Rule 4b`: `exposition` / `background` -> 100% epistemic lineage, 0 cash weight)
        ProvenanceNode("bkm1984", "Beale-Kato-Majda (1984) Vorticity Criterion", "background", None, Fraction(0, 1), "Attribution_Only_Lineage", "EpistemicRecord", False),
        ProvenanceNode("buckmastervicol2019", "Buckmaster & Vicol (2019) Convex Integration Weak Solutions", "exposition", None, Fraction(0, 1), "Attribution_Only_Lineage", "EpistemicRecord", True),
        ProvenanceNode("ckn1982", "Caffarelli-Kohn-Nirenberg (1982) Partial Regularity", "background", None, Fraction(0, 1), "Attribution_Only_Lineage", "EpistemicRecord", True),
        ProvenanceNode("cheskidov2010", "Cheskidov & Shvydkoy (2010) Besov Ill-Posedness", "exposition", None, Fraction(0, 1), "Attribution_Only_Lineage", "EpistemicRecord", True),
        ProvenanceNode("cf1993", "Constantin & Fefferman (1993) Direction of Vorticity", "exposition", None, Fraction(0, 1), "Attribution_Only_Lineage", "EpistemicRecord", True),
        ProvenanceNode("dickson1919", "Leonard E. Dickson (1919) Cayley-Dickson Doubling", "background", None, Fraction(0, 1), "Attribution_Only_Lineage", "EpistemicRecord", False),
        ProvenanceNode("ess2003", "Escauriaza-Seregin-Sverak (2003) L_{3,inf} Regularity", "background", None, Fraction(0, 1), "Attribution_Only_Lineage", "EpistemicRecord", True),
        ProvenanceNode("fujitakato1964", "Fujita & Kato (1964) Fractional Powers Semigroup", "background", None, Fraction(0, 1), "Attribution_Only_Lineage", "EpistemicRecord", False),
        ProvenanceNode("gomezserrano2019", "Javier Gomez-Serrano (2019) CAP in PDE Survey", "exposition", None, Fraction(0, 1), "Attribution_Only_Lineage", "EpistemicRecord", True),
        ProvenanceNode("hilbert1891", "David Hilbert (1891) Space-Filling Curve", "background", None, Fraction(0, 1), "Attribution_Only_Lineage", "EpistemicRecord", False),
        ProvenanceNode("hopf1951", "Eberhard Hopf (1951) Weak Energy Solutions", "background", None, Fraction(0, 1), "Attribution_Only_Lineage", "EpistemicRecord", False),
        ProvenanceNode("kato1984", "Tosio Kato (1984) Strong L^p Mild Solutions", "background", None, Fraction(0, 1), "Attribution_Only_Lineage", "EpistemicRecord", False),
        ProvenanceNode("kochtataru2001", "Koch & Tataru (2001) BMO^{-1} Well-Posedness", "background", None, Fraction(0, 1), "Attribution_Only_Lineage", "EpistemicRecord", True),
        ProvenanceNode("tucker2002", "Warwick Tucker (2002) Rigorous ODE Solver", "exposition", None, Fraction(0, 1), "Attribution_Only_Lineage", "EpistemicRecord", True),
        ProvenanceNode("biferale2012", "Biferale-Musacchio-Toschi (2012) Helical Inverse Cascade", "exposition", None, Fraction(0, 1), "Attribution_Only_Lineage", "EpistemicRecord", True),
    ]

    dag = {n.node_id: n for n in nodes_list}

    # Verify every key in `bsar_navier_stokes.bib` is present in the frozen DAG (`Rule 4a`)
    if bib_path and bib_path.is_file():
        bib_keys = parse_bibtex_keys(bib_path)
        missing = [k for k in bib_keys if k not in dag]
        if missing:
            raise ValueError(f"Frozen bibliography keys missing from provenance DAG: {missing}")

    return dag


def topological_sort_acyclic(dag: Dict[str, ProvenanceNode]) -> List[str]:
    """
    Verify acyclicity (`Rule 4a` / `Axis 5`) via Kahn's in-degree algorithm and return topological
    order from downstream (`THIS_WORK` / pools) toward upstream (`GENESIS`).
    Raises ValueError on any self-citation or cycle.
    """
    in_deg: Dict[str, int] = {nid: 0 for nid in dag}
    for u, node in dag.items():
        if node.axis7_reason not in AXIS7_ALL_REASONS:
            raise ValueError(f"Invalid Axis 7 reason on {u}: {node.axis7_reason}")
        for v, w in node.upstream_edges:
            if v == u:
                raise ValueError(f"Rule 4a violation: self-citation {u} -> {u}")
            if v not in dag:
                raise ValueError(f"Dangling citation edge {u} -> {v}")
            if w <= 0:
                raise ValueError(f"Edge weight must be strictly positive on {u} -> {v}")
            in_deg[v] += 1

    ready = sorted([nid for nid, deg in in_deg.items() if deg == 0])
    order: List[str] = []
    while ready:
        u = ready.pop(0)
        order.append(u)
        for v, _ in dag[u].upstream_edges:
            in_deg[v] -= 1
            if in_deg[v] == 0:
                ready.append(v)
                ready.sort()

    if len(order) != len(dag):
        cyclic = sorted(set(dag.keys()) - set(order))
        raise ValueError(f"Rule 4a violation: cycle detected in provenance graph among {cyclic}")
    return order


def compute_exact_provenance_waterfall(
    dag: Dict[str, ProvenanceNode],
    pool_shares: Optional[Dict[str, Fraction]] = None,
    rho: Fraction = Fraction(1, 4),
    epsilon_dust: Fraction = Fraction(1, 1000),
    consenting_owners: Optional[Set[str]] = None,
    endowment_node_id: str = "winnipeg_18_org_endowment",
) -> Dict[str, Any]:
    """
    Execute Rules `4a`–`4f` in exact `fractions.Fraction` rational arithmetic:
      - `4a`: Topological acyclicity verification.
      - `4b`: Filter outgoing edges strictly to `load_bearing` target nodes (`exposition`/`background`
              retain 100% epistemic lineage in `lineage_finding_axis5_axis7`, `0` waterfall cash weight).
      - `4c`: Seed nodes from the frozen top-level pool shares (`sum == 1`, `architect_retain == 0`).
      - `4d`: Propagate `rho` upstream in topological order (`sum S(u) == 1`), then sweep sub-threshold
              dust `0 < S(u) < epsilon_dust` into `endowment_node_id`.
      - `4e`: Apply `Axis 8` consent gate: unconsented living shares stay `UNCLAIMED` (and compute both
              pending-escrow and post-expiry endowment-swept distributions); non-living nodes must route
              via predetermined `P4_ESTATES_MEMORIAL` fiduciaries.
      - `4f`: Emit three strictly separated findings (`lineage`, `payability`, `settlement`).
    """
    if pool_shares is None:
        pool_shares = dict(FROZEN_POOL_SHARES_GIVE_100_AWAY)
    if sum(pool_shares.values(), Fraction(0, 1)) != Fraction(1, 1):
        raise ValueError("Top-level pool shares must sum to exactly 1/1")
    if not (Fraction(0, 1) <= rho < Fraction(1, 1)):
        raise ValueError("Pass-through fraction rho must satisfy 0 <= rho < 1")

    topo_order = topological_sort_acyclic(dag)

    # Verify per-pool internal weights sum to 1 for every active pool (`Rule 4c`)
    for pid, p_share in pool_shares.items():
        members = [n for n in dag.values() if n.pool_id == pid]
        w_sum = sum((n.seed_weight_in_pool for n in members), Fraction(0, 1))
        if p_share > 0 and w_sum != Fraction(1, 1):
            raise ValueError(f"Pool {pid} internal weights sum to {w_sum}, expected 1/1")

    # Initial pool seeds I(u) (`Rule 4b` & `4c`)
    seed_I: Dict[str, Fraction] = {}
    for nid, node in dag.items():
        if node.axis7_reason in AXIS7_ATTRIBUTION_ONLY_REASONS or node.pool_id is None:
            seed_I[nid] = Fraction(0, 1)
        else:
            seed_I[nid] = pool_shares[node.pool_id] * node.seed_weight_in_pool

    assert sum(seed_I.values(), Fraction(0, 1)) == Fraction(1, 1)

    # Normalize load-bearing outgoing edges Out_+(u) (`Rule 4b` & `4d`)
    load_bearing_out: Dict[str, List[Tuple[str, Fraction]]] = {}
    for nid, node in dag.items():
        lb_edges = [
            (v, w)
            for (v, w) in node.upstream_edges
            if dag[v].axis7_reason in AXIS7_LOAD_BEARING_REASONS
        ]
        if lb_edges:
            tot_w = sum((w for _, w in lb_edges), Fraction(0, 1))
            load_bearing_out[nid] = [(v, w / tot_w) for (v, w) in lb_edges]
        else:
            load_bearing_out[nid] = []

    # Recursive topological waterfall (`Rule 4d`)
    accum_A: Dict[str, Fraction] = {nid: seed_I[nid] for nid in dag}
    retained_S: Dict[str, Fraction] = {}

    for u in topo_order:
        outs = load_bearing_out[u]
        if outs and accum_A[u] > 0:
            retained_S[u] = (Fraction(1, 1) - rho) * accum_A[u]
            pass_amt = rho * accum_A[u]
            for v, w_norm in outs:
                accum_A[v] += pass_amt * w_norm
        else:
            retained_S[u] = accum_A[u]

    assert sum(retained_S.values(), Fraction(0, 1)) == Fraction(1, 1), (
        "Exact rational conservation violated before dust sweep!"
    )

    # Dust sweep (`0 < S(u) < epsilon_dust` -> `endowment_node_id`)
    post_dust_S: Dict[str, Fraction] = dict(retained_S)
    dust_swept_total = Fraction(0, 1)
    dust_swept_nodes: List[str] = []
    for nid in topo_order:
        if nid == endowment_node_id:
            continue
        if Fraction(0, 1) < post_dust_S[nid] < epsilon_dust:
            dust_swept_total += post_dust_S[nid]
            post_dust_S[nid] = Fraction(0, 1)
            dust_swept_nodes.append(nid)
    post_dust_S[endowment_node_id] += dust_swept_total

    assert sum(post_dust_S.values(), Fraction(0, 1)) == Fraction(1, 1), (
        "Exact rational conservation violated after dust sweep!"
    )

    # Rule 4e: Non-living beneficiary invariant + Axis 8 Consent Gate
    for nid, node in dag.items():
        if not node.is_living_beneficiary and post_dust_S[nid] > 0:
            if node.pool_id != "P4_ESTATES_MEMORIAL":
                raise ValueError(
                    f"Rule 4e violation: non-living node {nid} has positive share without P4_ESTATES_MEMORIAL fiduciary"
                )

    if consenting_owners is None:
        # Default simulation: all predetermined fiduciaries + mutual aid + tool foundations consent;
        # living individual academic citees default to `UNCLAIMED` until they affirmatively opt in!
        consenting_owners = {
            "Topher",
            "LeadPDECoAuthor",
            "Lean4CAPCoAuthor",
            "LeanFRO_Trustee",
            "Z3_Maintainers",
            "R_Foundation_Board",
            "Asar_Maintainers",
            "Ladyzhenskaya_Memorial_Trustee",
            "Leray_Memorial_Trustee",
            "Ijiri_Memorial_Trustee",
            "OpenScience_Memorial_Trustee",
            "Preservation_MentalHealth_Trustee",
            "Bredon_Memorial_Trustee",
            "Foias_Memorial_Trustee",
            "Doering_Memorial_Trustee",
            "Majda_Memorial_Trustee",
            "Harvest_MutualAid",
        }

    payable_now: Dict[str, Fraction] = {}
    unclaimed_pending: Dict[str, Fraction] = {}
    for nid, share in post_dust_S.items():
        if share == 0:
            payable_now[nid] = Fraction(0, 1)
            unclaimed_pending[nid] = Fraction(0, 1)
            continue
        owner = dag[nid].consent_owner
        if owner in consenting_owners:
            payable_now[nid] = share
            unclaimed_pending[nid] = Fraction(0, 1)
        else:
            payable_now[nid] = Fraction(0, 1)
            unclaimed_pending[nid] = share

    # If claim window T_claim expires without opt-in, unclaimed shares sweep 100% to P5_ENDOWMENT (`Rule 4e`)
    post_expiry_payable: Dict[str, Fraction] = dict(payable_now)
    unclaimed_total = sum(unclaimed_pending.values(), Fraction(0, 1))
    post_expiry_payable[endowment_node_id] += unclaimed_total
    assert sum(post_expiry_payable.values(), Fraction(0, 1)) == Fraction(1, 1)

    # Rule 4f View 1: Epistemic Lineage Finding (`Axis 5 + Axis 7`)
    lineage_finding = [
        {
            "node_id": nid,
            "title": dag[nid].title,
            "axis7_reason": dag[nid].axis7_reason,
            "load_bearing_for_waterfall": dag[nid].axis7_reason in AXIS7_LOAD_BEARING_REASONS,
            "upstream_citations": [v for v, _ in dag[nid].upstream_edges],
        }
        for nid in topo_order
    ]

    # Rule 4f View 2: Contingent Payability Finding (`Waterfall + Axis 8`)
    payability_finding = [
        {
            "node_id": nid,
            "beneficiary_account": dag[nid].beneficiary_account,
            "consent_owner": dag[nid].consent_owner,
            "is_living_beneficiary": dag[nid].is_living_beneficiary,
            "seed_share_rational": f"{seed_I[nid].numerator}/{seed_I[nid].denominator}",
            "post_waterfall_share_rational": f"{post_dust_S[nid].numerator}/{post_dust_S[nid].denominator}",
            "post_waterfall_pct": round(float(post_dust_S[nid]) * 100.0, 6),
            "axis8_status": (
                "ZERO_ATTRIBUTION_ONLY"
                if post_dust_S[nid] == 0
                else ("CONSENTED_PAYABLE" if payable_now[nid] > 0 else "UNCLAIMED_NO_OBLIGATION")
            ),
        }
        for nid in topo_order
        if post_dust_S[nid] > 0 or dag[nid].axis7_reason in AXIS7_ATTRIBUTION_ONLY_REASONS
    ]

    return {
        "topological_order": topo_order,
        "architect_retain_share": f"{post_dust_S['duguay2026zenodo'].numerator}/{post_dust_S['duguay2026zenodo'].denominator}",
        "rho_pass_through": f"{rho.numerator}/{rho.denominator}",
        "epsilon_dust": f"{epsilon_dust.numerator}/{epsilon_dust.denominator}",
        "dust_swept_rational": f"{dust_swept_total.numerator}/{dust_swept_total.denominator}",
        "dust_swept_nodes": dust_swept_nodes,
        "unclaimed_pending_rational": f"{unclaimed_total.numerator}/{unclaimed_total.denominator}",
        "exact_total_conservation_equal_one": (
            sum(post_dust_S.values(), Fraction(0, 1)) == Fraction(1, 1)
            and sum(post_expiry_payable.values(), Fraction(0, 1)) == Fraction(1, 1)
        ),
        "post_dust_shares": post_dust_S,
        "payable_now_shares": payable_now,
        "unclaimed_pending_shares": unclaimed_pending,
        "post_expiry_shares": post_expiry_payable,
        "lineage_finding_axis5_axis7": lineage_finding,
        "payability_finding_waterfall_axis8": payability_finding,
    }


def post_waterfall_claims_to_eleven_entry_book(
    dag: Dict[str, ProvenanceNode],
    waterfall_res: Dict[str, Any],
    notional_contingent_cents: int = 100_000_000,  # e.g., $1,000,000.00 in integer cents
) -> Dict[str, Any]:
    """
    Rule 4f View 3 (`Settlement & Ledger Verification`):
    Post every `CONSENTED_PAYABLE` claim onto `11d-spreadsheet-poc/ledger.py`'s `Book` with
    exact Ijiri `momentum` chaining (`Axis 10`), bilateral `Axis 8` consent, pinned `Axis 9`
    definition version, and countersigned `Axis 11` SHA-256 receipts—plus verify `Axis 3`
    (`Book.forgive()`) lawful momentum-breaking grace on a declined claim!
    """
    mod, loader_src = load_portable_eleven_entry_ledger()
    mod.ACCOUNTS["Contingent_Waterfall_Clearinghouse"] = "ClearinghouseTrustee"
    for node in dag.values():
        mod.ACCOUNTS[node.beneficiary_account] = node.consent_owner

    mod.DEFINITIONS["waterfall_contingent_v1"] = {
        "protocol": "Provenance-to-Payment Waterfall v1.0 (Rules 4a-4f)",
        "architect_retain": "0/1 (100% Give-It-Away)",
        "rho_pass_through": waterfall_res["rho_pass_through"],
        "epsilon_dust": waterfall_res["epsilon_dust"],
    }

    book = mod.Book()
    payable_shares: Dict[str, Fraction] = waterfall_res["payable_now_shares"]
    active_items: List[Tuple[str, int]] = [
        (nid, int(round(float(sh * notional_contingent_cents))))
        for nid, sh in payable_shares.items()
        if sh > 0
    ]

    prev_entry_id = "GENESIS"
    receipts: Dict[str, str] = {}
    for idx, (nid, cents) in enumerate(active_items):
        node = dag[nid]
        eid = f"WF-{idx + 1:02d}-{nid.upper()[:24]}"
        next_cents = active_items[idx + 1][1] if idx + 1 < len(active_items) else None
        consent_tuple = tuple(sorted({"ClearinghouseTrustee", node.consent_owner}))
        ent = mod.Entry(
            entry_id=eid,
            debit_account="Contingent_Waterfall_Clearinghouse",
            credit_account=node.beneficiary_account,
            forgiveness="owed",
            amount=cents,
            posted_at=f"2026-11-03T17:10:{idx:02d}Z",
            provenance=prev_entry_id,
            author="ClearinghouseTrustee",
            reason=f"Rule 4a-4f contingent waterfall allocation ({node.axis7_reason}) for {nid}",
            consent=consent_tuple,
            definition_version="waterfall_contingent_v1",
            momentum=next_cents,
        )
        for party in consent_tuple:
            ent.sign(party)
        book.post(ent)
        receipts[eid] = ent.receipt()
        prev_entry_id = eid

    return {
        "ledger_loader": loader_src,
        "entries_posted_count": len(book.entries),
        "total_consented_cents_posted": sum(c for _, c in active_items),
        "settlement_receipts_axis11": receipts,
        "version_pin_check": book.read(next(iter(receipts)), "waterfall_contingent_v1"),
    }


def run_provenance_waterfall_suite() -> Dict[str, Any]:
    dag = build_frozen_navier_provenance_dag()
    wf = compute_exact_provenance_waterfall(dag)
    ledger_settlement = post_waterfall_claims_to_eleven_entry_book(dag, wf)

    cert_payload = {
        "artifact": "Provenance-to-Payment Waterfall Engine (`Contingent Claims Register v1.0`)",
        "attestation": "probabilistic_structural",
        "scope_notice": (
            "Standalone contingent allocation & provenance ledger specification implementing Rules 4a-4f. "
            "Zero external transmissions; zero prize claims; 0.0% retained by Architect (100.0% given away)."
        ),
        "node_count_total": len(dag),
        "attribution_only_zero_cash_nodes": sum(
            1 for n in dag.values() if n.axis7_reason in AXIS7_ATTRIBUTION_ONLY_REASONS
        ),
        "architect_retain_share": wf["architect_retain_share"],
        "rho_pass_through": wf["rho_pass_through"],
        "epsilon_dust": wf["epsilon_dust"],
        "dust_swept_rational": wf["dust_swept_rational"],
        "dust_swept_nodes": wf["dust_swept_nodes"],
        "unclaimed_pending_rational": wf["unclaimed_pending_rational"],
        "exact_total_conservation_equal_one": wf["exact_total_conservation_equal_one"],
        "lineage_finding_axis5_axis7": wf["lineage_finding_axis5_axis7"],
        "payability_finding_waterfall_axis8": wf["payability_finding_waterfall_axis8"],
        "settlement_finding_axis11": ledger_settlement,
    }
    canon = json.dumps(cert_payload, sort_keys=True, separators=(",", ":")).encode("utf-8")
    cert_payload["certificate_sha256"] = hashlib.sha256(canon).hexdigest()

    out_paths = [
        _HERE / "artifacts" / "provenance_waterfall_11d_certificate.json",
        _BSAR_ROOT / "navier_stokes" / "provenance_waterfall_11d_certificate.json",
    ]
    for op in out_paths:
        if op.parent.exists():
            op.write_text(json.dumps(cert_payload, indent=2), encoding="utf-8")

    return cert_payload


if __name__ == "__main__":
    if hasattr(sys.stdout, "reconfigure"):
        sys.stdout.reconfigure(encoding="utf-8", errors="replace")
    rep = run_provenance_waterfall_suite()
    print("=== CONTINGENT CLAIMS REGISTER v1.0: 100% GIVE-IT-AWAY PROVENANCE WATERFALL ===")
    print(f"Total Frozen DAG Nodes: {rep['node_count_total']} (Attribution-Only 0-Cash Nodes: {rep['attribution_only_zero_cash_nodes']})")
    print(f"Architect Retain Share: {rep['architect_retain_share']} (100% Distributed Outward!)")
    print(f"Generational Pass-Through rho={rep['rho_pass_through']} | Dust Swept to Endowment={rep['dust_swept_rational']} ({rep['dust_swept_nodes']})")
    print(f"Unclaimed Living Citee Shares (Zero Obligation Until Axis-8 Opt-In): {rep['unclaimed_pending_rational']}")
    print(f"Exact Rational Conservation (Sum == 1/1): {rep['exact_total_conservation_equal_one']}")
    print(f"Eleven-Entry Consented Ledger Entries Posted & Signed: {rep['settlement_finding_axis11']['entries_posted_count']}")
    print(f"Waterfall Certificate SHA-256: {rep['certificate_sha256']}")
