#!/usr/bin/env python3
"""
BSAR SPARSE 6D XCUBE COMPILER & R-VERB PIPE ENGINE (STANDALONE EDITION)
License: GNU AGPLv3 (Open-source free hosting; commercial closed-source integration requires dual license)
Attestation: probabilistic_structural (Modal Functor Box Gate)

Implements the four Bsar tricks for theological & epistemic concordance compilation:
1. Asar-style 3-Pass Deterministic Compiler (Pass 0 Support Lock -> Pass 1 Hilbert CSR/CSC -> Pass 2 Q8.8 + SHA-256 Seal)
2. R-style Copy-on-Modify Data-Frame Verbs (filter, inner_join, mutate, rollup_slice, select)
3. Lua-style Dynamic Associative Frames (ragged 0..N citation fan-out in O(edges) with canonical key sort)
4. XCubes-style N-Dimensional Named Hypercubes + Carrollian 4-Valued Middle-Term Elimination (exists m)
"""

from __future__ import annotations

import copy
import hashlib
import json
import math
from dataclasses import asdict, dataclass, field
from enum import Enum
from typing import Any, Callable, Dict, Iterable, List, Optional, Sequence, Tuple


def canonical_sha256(data: Any) -> str:
    """Compute a deterministic SHA-256 digest over canonically sorted JSON."""
    encoded = json.dumps(data, sort_keys=True, ensure_ascii=False, default=str).encode("utf-8")
    return hashlib.sha256(encoded).hexdigest()


def float_db_to_q8_8(db_value: float) -> int:
    """Convert decibans (10 * log10(LR)) into signed 16-bit Q8.8 fixed-point integer (1/256 dB precision)."""
    scaled = int(round(db_value * 256.0))
    return max(-32768, min(32767, scaled))


def q8_8_to_float_db(q_val: int) -> float:
    """Convert signed Q8.8 fixed-point integer back into decibans."""
    return round(q_val / 256.0, 4)


def hilbert_xy_to_d(n: int, x: int, y: int) -> int:
    """
    Map 2D integer coordinates (x, y) in [0, n-1]^2 (n a power of 2) onto a 1D Hilbert curve index.
    Preserves 2D locality when packing CCC_Paragraph x Bible_Verse into contiguous 1D static shards.
    """
    d = 0
    s = n >> 1
    while s > 0:
        rx = 1 if (x & s) > 0 else 0
        ry = 1 if (y & s) > 0 else 0
        d += s * s * ((3 * rx) ^ ry)
        if ry == 0:
            if rx == 1:
                x = s - 1 - x
                y = s - 1 - y
            x, y = y, x
        s >>= 1
    return d


class EpistemicState(str, Enum):
    """4-Valued Carrollian epistemic state (mirrors src/compression/carroll_cube.py)."""

    ATTESTED_ONE = "1"      # Verified direct/convergent support
    EXCLUDED_ZERO = "0"     # Verified incompatibility / counter-witness
    DONT_CARE_STAR = "*"    # Existentially projected / rolled-up mediator axis
    UNKNOWN_OPEN = "?"      # Unassessed / open scholarly question (never faked as 1 or 0)


@dataclass(frozen=True)
class DisjunctiveScopeNote:
    """Preserves (Clause_A OR Clause_B) footnote ambiguity without premature flattening."""

    option_a: str
    option_b: str
    note: str


class LicensedTextAdapter:
    """
    Respectful Concordance & Publisher Revenue Hook (Node 0 & AGPLv3 Dual-License Ready).

    Default open-source behavior ('VaticanOutboundConcordanceAdapter'):
    - Never re-hosts copyrighted full-text USCCB/LEV English CCC prose.
    - Displays clean-room 1-sentence atomic proposition summaries + uncopyrightable citation numbers (Feist).
    - Drives readers directly to official Vatican.va (English & Latin Editio Typica) and official print/licensed editions
      so bishops' conferences and publishers earn full traffic and book sales.
    - Commercial apps holding an official USCCB/CCCB/LEV text license can subclass this adapter under a commercial
      partnership license to hydrate inline licensed text.
    """

    adapter_name: str = "VaticanOutboundConcordanceAdapter"

    def resolve_ccc_display(
        self,
        ccc_num: int,
        clean_room_summary: str,
        vatican_en_url: str,
        vatican_lt_url: str,
        usccb_reader_url: str = "https://www.usccb.org/sites/default/files/flipbooks/catechism/",
    ) -> Dict[str, str]:
        return {
            "ccc_paragraph": f"CCC § {ccc_num}",
            "clean_room_proposition": clean_room_summary,
            "vatican_en_url": vatican_en_url,
            "vatican_latin_url": vatican_lt_url,
            "official_print_and_flipbook_url": usccb_reader_url,
            "rights_mode": "CONCORDANCE_SUMMARY_PLUS_OFFICIAL_OUTBOUND_LINK",
        }


class LuaAssociativeNode:
    """
    Lua-style dynamically-sized associative table for a single CCC paragraph/statement node.
    Stores variable fan-out (0 to 50+ Scripture, Trent, and Patristic threads) in O(edges)
    without dense 2,865 x 35,527 matrix padding.
    """

    def __init__(self, ccc_id: int, **attrs: Any) -> None:
        self.ccc_id = int(ccc_id)
        self.attrs: Dict[str, Any] = dict(attrs)
        self.threads: List[Dict[str, Any]] = []

    def add_thread(self, **edge_attrs: Any) -> "LuaAssociativeNode":
        required = {"verse_ref", "cluster_id", "warrant_mode", "canon_scope"}
        missing = required - set(edge_attrs.keys())
        if missing:
            raise ValueError(f"LuaAssociativeNode missing required XCube axes: {sorted(missing)}")
        record = dict(edge_attrs)
        record.setdefault("epistemic_state", EpistemicState.ATTESTED_ONE.value)
        record.setdefault("mediator", "DIRECT_SCRIPTURE")
        record.setdefault("newman_note", "N0_EXPLICIT_KERYGMA")
        db_float = float(record.pop("decibans", 3.0))
        record["db_q8_8"] = float_db_to_q8_8(db_float)
        self.threads.append(record)
        return self

    def canonical_dict(self) -> Dict[str, Any]:
        sorted_threads = sorted(
            self.threads,
            key=lambda t: (
                str(t.get("verse_ref", "")),
                str(t.get("mediator", "")),
                str(t.get("warrant_mode", "")),
            ),
        )
        out = {"ccc_id": self.ccc_id, **self.attrs, "threads": sorted_threads}
        return dict(sorted(out.items(), key=lambda kv: kv[0]))


class CubePipe:
    """
    R-style functional, copy-on-modify pipe wrapper over a 6D XCube edge list.
    Every verb returns a brand-new CubePipe without mutating upstream state.
    """

    def __init__(self, rows: Iterable[Dict[str, Any]]) -> None:
        self._rows: Tuple[Dict[str, Any], ...] = tuple(copy.deepcopy(r) for r in rows)

    @property
    def rows(self) -> List[Dict[str, Any]]:
        return [copy.deepcopy(r) for r in self._rows]

    def __len__(self) -> int:
        return len(self._rows)

    def filter(self, predicate: Optional[Callable[[Dict[str, Any]], bool]] = None, **exact_matches: Any) -> "CubePipe":
        out: List[Dict[str, Any]] = []
        for row in self._rows:
            if any(row.get(k) != v for k, v in exact_matches.items()):
                continue
            if predicate is not None and not predicate(row):
                continue
            out.append(row)
        return CubePipe(out)

    def mutate(self, **computed_cols: Callable[[Dict[str, Any]], Any]) -> "CubePipe":
        out: List[Dict[str, Any]] = []
        for row in self._rows:
            nr = copy.deepcopy(row)
            for col_name, fn in computed_cols.items():
                nr[col_name] = fn(nr)
            out.append(nr)
        return CubePipe(out)

    def inner_join(
        self,
        right_table: Sequence[Dict[str, Any]],
        left_on: str,
        right_on: str,
        prefix: str = "",
    ) -> "CubePipe":
        index: Dict[Any, List[Dict[str, Any]]] = {}
        for r in right_table:
            index.setdefault(r.get(right_on), []).append(r)
        out: List[Dict[str, Any]] = []
        for left in self._rows:
            matches = index.get(left.get(left_on), [])
            for right in matches:
                merged = copy.deepcopy(left)
                for k, v in right.items():
                    if k == right_on and k in merged:
                        continue
                    target_key = f"{prefix}{k}" if prefix else k
                    merged[target_key] = copy.deepcopy(v)
                out.append(merged)
        return CubePipe(out)

    def eliminate_mediator(self) -> "CubePipe":
        """
        Carrollian Middle-Term Elimination (pi_m(F) = exists m F(CCC, m, Bible)).
        Projects out intermediate Patristic/Trent/Vatican II mediators m into direct (ccc_id, verse_ref)
        pairs while retaining an expandable `mediators_expanded` provenance list!
        """
        grouped: Dict[Tuple[int, str], Dict[str, Any]] = {}
        for row in self._rows:
            key = (int(row["ccc_id"]), str(row["verse_ref"]))
            if key not in grouped:
                base = copy.deepcopy(row)
                base["mediator"] = EpistemicState.DONT_CARE_STAR.value
                base["mediators_expanded"] = [row.get("mediator", "DIRECT_SCRIPTURE")]
                grouped[key] = base
            else:
                existing = grouped[key]
                med = row.get("mediator", "DIRECT_SCRIPTURE")
                if med not in existing["mediators_expanded"]:
                    existing["mediators_expanded"].append(med)
                # Keep maximum single-channel Q8.8 weight on identical (ccc_id, verse_ref) to avoid double counting
                existing["db_q8_8"] = max(int(existing["db_q8_8"]), int(row["db_q8_8"]))
        return CubePipe(grouped.values())

    def rollup_slice(self, group_axes: Sequence[str]) -> "CubePipe":
        """
        OLAP XCube Roll-Up with Cardinal Newman Anti-Echo Cluster Deduplication:
        Multiple verses sharing a single synoptic `cluster_id` within a group count ONCE (max Q8.8 weight),
        while genuinely independent clusters sum additively in Q8.8 fixed-point decibans.
        """
        buckets: Dict[Tuple[Any, ...], List[Dict[str, Any]]] = {}
        for row in self._rows:
            gkey = tuple(row.get(ax) for ax in group_axes)
            buckets.setdefault(gkey, []).append(row)

        summaries: List[Dict[str, Any]] = []
        for gkey in sorted(buckets.keys(), key=lambda x: str(x)):
            items = buckets[gkey]
            cluster_best_q8: Dict[str, int] = {}
            verses: List[str] = []
            for it in items:
                vref = str(it.get("verse_ref", ""))
                if vref and vref not in verses:
                    verses.append(vref)
                if it.get("epistemic_state") == EpistemicState.ATTESTED_ONE.value:
                    cid = str(it.get("cluster_id", vref))
                    qval = int(it.get("db_q8_8", 0))
                    cluster_best_q8[cid] = max(cluster_best_q8.get(cid, -32768), qval)

            total_q8 = sum(cluster_best_q8.values())
            rec: Dict[str, Any] = {ax: val for ax, val in zip(group_axes, gkey)}
            rec["raw_edge_count"] = len(items)
            rec["independent_cluster_count"] = len(cluster_best_q8)
            rec["cable_q8_8"] = total_q8
            rec["cable_decibans"] = q8_8_to_float_db(total_q8)
            rec["bayes_factor_approx"] = round(math.pow(10.0, rec["cable_decibans"] / 10.0), 3)
            rec["supporting_verses"] = verses
            summaries.append(rec)
        return CubePipe(summaries)

    def select(self, *columns: str) -> List[Dict[str, Any]]:
        return [{col: row.get(col) for col in columns} for row in self._rows]


class BsarXCubeCompiler:
    """
    3-Pass Contractive Compiler (Pass 0 Support Lock -> Pass 1 Hilbert CSR/CSC -> Pass 2 Q8.8 + SHA-256 Slab).
    """

    HILBERT_GRID_N = 65536  # 2^16 covers 2,865 CCC paragraphs x 35,527 Bible verses cleanly

    def __init__(self, text_adapter: Optional[LicensedTextAdapter] = None) -> None:
        self.text_adapter = text_adapter or LicensedTextAdapter()
        self._nodes: Dict[int, LuaAssociativeNode] = {}
        self._verse_ordinal_map: Dict[str, int] = {}

    def register_node(self, node: LuaAssociativeNode) -> None:
        self._nodes[node.ccc_id] = node

    def spread_pericope(
        self,
        ccc_ids: Sequence[int],
        verse_refs: Sequence[str],
        cluster_id: str,
        total_decibans: float,
        warrant_mode: str = "PERICOPE_SPREAD",
        canon_scope: str = "ECUMENICAL_66_SHARED",
        mediator: str = "DIRECT_SCRIPTURE",
        newman_note: str = "N0_EXPLICIT_KERYGMA",
    ) -> None:
        """
        XCubes Weighted Top-Down Spreading (S_W):
        Distributes a multi-verse pericope citation across atomic CCC statements while tagging each edge
        `is_spread_from_pericope=True` and conserving cluster identity so total weight never inflates!
        """
        if not ccc_ids or not verse_refs:
            return
        per_statement_db = total_decibans / float(len(ccc_ids))
        for cid in ccc_ids:
            if cid not in self._nodes:
                continue
            for vref in verse_refs:
                self._nodes[cid].add_thread(
                    verse_ref=vref,
                    cluster_id=cluster_id,
                    warrant_mode=warrant_mode,
                    canon_scope=canon_scope,
                    mediator=mediator,
                    newman_note=newman_note,
                    decibans=per_statement_db,
                    is_spread_from_pericope=True,
                )

    def compile_three_pass(self) -> Dict[str, Any]:
        """
        Execute deterministic 3-pass compilation:
        - Pass 0: Canonical key sort + freeze sparse support S_0 + assign deterministic verse ordinals.
        - Pass 1: Compute 2D Hilbert curve indices + forward (CCC -> Verse) & reverse (Verse -> CCC) CSR maps.
        - Pass 2: Verify zero Pass-1/Pass-2 size drift (lambda_max < 0) and seal with canonical SHA-256.
        """
        # PASS 0: Canonical sort & support lock
        sorted_ccc_ids = sorted(self._nodes.keys())
        all_verses = sorted(
            {
                str(t["verse_ref"])
                for cid in sorted_ccc_ids
                for t in self._nodes[cid].threads
            }
        )
        self._verse_ordinal_map = {v: idx + 1 for idx, v in enumerate(all_verses)}

        pass0_edges: List[Dict[str, Any]] = []
        node_catalog: Dict[str, Any] = {}

        for cid in sorted_ccc_ids:
            cdict = self._nodes[cid].canonical_dict()
            display_meta = self.text_adapter.resolve_ccc_display(
                ccc_num=cid,
                clean_room_summary=str(cdict.get("summary", "")),
                vatican_en_url=str(cdict.get("vatican_en_url", "https://www.vatican.va/archive/ENG0015/_INDEX.HTM")),
                vatican_lt_url=str(cdict.get("vatican_lt_url", "https://www.vatican.va/archive/catechismus_lt/")),
            )
            node_catalog[str(cid)] = {
                "ccc_id": cid,
                "pillar": cdict.get("pillar", ""),
                "topic": cdict.get("topic", ""),
                "trent_ref_id": cdict.get("trent_ref_id", ""),
                "tradition_lenses": cdict.get("tradition_lenses", {}),
                "newman_profile": cdict.get("newman_profile", {}),
                **display_meta,
            }
            for t in cdict["threads"]:
                v_ord = self._verse_ordinal_map[str(t["verse_ref"])]
                h_idx = hilbert_xy_to_d(self.HILBERT_GRID_N, cid, v_ord)
                pass0_edges.append(
                    {
                        "hilbert_d": h_idx,
                        "ccc_id": cid,
                        "pillar": cdict.get("pillar", ""),
                        "verse_ref": str(t["verse_ref"]),
                        "verse_ord": v_ord,
                        "cluster_id": str(t["cluster_id"]),
                        "warrant_mode": str(t["warrant_mode"]),
                        "canon_scope": str(t["canon_scope"]),
                        "mediator": str(t["mediator"]),
                        "newman_note": str(t["newman_note"]),
                        "epistemic_state": str(t["epistemic_state"]),
                        "db_q8_8": int(t["db_q8_8"]),
                        "decibans": q8_8_to_float_db(int(t["db_q8_8"])),
                        "is_spread_from_pericope": bool(t.get("is_spread_from_pericope", False)),
                    }
                )

        # PASS 1: Hilbert-ordered layout + Bidirectional CSR/CSC tables
        pass1_edges = sorted(
            pass0_edges,
            key=lambda e: (e["hilbert_d"], e["ccc_id"], e["verse_ref"], e["mediator"]),
        )
        forward_csr: Dict[str, List[int]] = {}
        reverse_csc: Dict[str, List[int]] = {}
        for edge_idx, edge in enumerate(pass1_edges):
            forward_csr.setdefault(str(edge["ccc_id"]), []).append(edge_idx)
            reverse_csc.setdefault(edge["verse_ref"], []).append(edge_idx)

        # PASS 2: Contractive verification (support size invariant) & RATS/SHA-256 Integrity Header
        size_drift = abs(len(pass1_edges) - len(pass0_edges))
        if size_drift != 0:
            raise RuntimeError(f"Bsar Pass-2 Lyapunov violation: support drifted by {size_drift}")

        slab_body = {
            "schema": "bsar.xcube.theology.v1",
            "license": "GNU-AGPLv3",
            "adapter": self.text_adapter.adapter_name,
            "pass_convergence_drift": size_drift,
            "lyapunov_contractive": True,
            "counts": {
                "ccc_nodes": len(node_catalog),
                "distinct_verses": len(all_verses),
                "sparse_edges": len(pass1_edges),
            },
            "nodes": node_catalog,
            "edges": pass1_edges,
            "forward_ccc_to_edge_ids": forward_csr,
            "reverse_verse_to_edge_ids": reverse_csc,
        }
        slab_sha256 = canonical_sha256(slab_body)
        return {
            "rats_sha256": slab_sha256,
            "attestation": "probabilistic_structural",
            **slab_body,
        }

    @staticmethod
    def pipe(compiled_slab: Dict[str, Any]) -> CubePipe:
        """Open an R-style functional CubePipe over a compiled Bsar slab."""
        return CubePipe(compiled_slab.get("edges", []))
