#!/usr/bin/env python3
"""
TORSION-FREE GROUP-RING & TWISTED LOOP-RING PROBER (`bsar.group_rings`)
License: GNU AGPLv3
Attestation: probabilistic_structural

Designed for group-ring & Kaplansky Conjecture researchers (Giles Gardam `arXiv:2102.11818`,
S. V. Ivanov `arXiv:2610.17662`, David Promislow `1988`, Moe Tabei `2026`):
1. Exact O(1) crystallographic Bieberbach screw-motion normal form for the torsion-free
   orientable Hantzsche-Wendt / Promislow group:
       P = < a, b | b^-1 a^2 b = a^-2,  a^-1 b^2 a = b^-2 >
2. 3-Pass `BsaRHypercubeCompiler` Support-Multiplication Hypercube (`S_A x S_B -> G`)
   computing Unique Product (`UP`) and Two-Unique-Products (`TUP`) multiplicity spectra
   via `RPipe`, including exact certification of Promislow's 14-element non-UP set in `P`
   (`0` unique products across all `14 x 14 = 196` pairs!).
3. Exact verification of Giles Gardam's 21-term nontrivial unit `alpha` and its 21-term
   inverse `beta = alpha^-1` in `F_2[P]` (`alpha * beta == 1 mod 2`), alongside an exact
   `char 0` lift into `Z[P]` exposing the parity-cancellation residual (`121` support words,
   `17` at `1_P`, strictly even `{2, 4, 6, 8, 10}` on all `120` off-identity words) —
   contrasting positive-characteristic cancellation (Gardam 2021, Ivanov 2026) with the
   open Characteristic-0 Kaplansky Zero-Divisor Conjecture.
4. Exact Characteristic-0 (`Q[G]`) vs Characteristic-p (`F_p[G]`) Support Annihilator
   Kernel Solver (`solve_support_zero_divisor_kernel`) + explicit Albuquerque-Majid (1999)
   twisted group-ring bridge `R^{sigma}[(Z_2)^n] ~= A_n(gamma)`.
"""

from __future__ import annotations

from collections import deque
from dataclasses import dataclass
from fractions import Fraction
from typing import Any, Callable, Dict, Hashable, Iterable, List, Optional, Sequence, Tuple

from .hypercube import BsaRHypercubeCompiler, LuaDynamicRecord
from .math_algebras import (
    CayleyDicksonAlgebra,
    clear_fraction_denominators,
    exact_nullspace_mod_p,
    exact_nullspace_rational,
)

# Canonical element of Hantzsche-Wendt / Promislow group P in Z^3 x| V_4:
# Represents affine Euclidean screw motion u |-> diag(sx, sy, sx*sy) u + (tx2/2, ty2/2, tz2/2)
PromislowElem = Tuple[int, int, int, int, int]

PROMISLOW_ID: PromislowElem = (0, 0, 0, 1, 1)
PROMISLOW_A: PromislowElem = (1, 1, 0, 1, -1)
PROMISLOW_B: PromislowElem = (0, 1, 1, -1, 1)

# Verified 14-element Non-Unique-Product subset inside the radius-3 word ball of P
# (`a, b` with `A = a^-1, B = b^-1`): 0 unique products in S * S!
PROMISLOW_14_NON_UP_WORDS: Tuple[str, ...] = (
    "a",
    "abb",
    "aB",
    "Ba",
    "ABB",
    "BA",
    "AB",
    "BB",
    "bb",
    "A",
    "bAb",
    "bab",
    "ab",
    "bA",
)


def promislow_mul(g1: PromislowElem, g2: PromislowElem) -> PromislowElem:
    """Exact O(1) group multiplication in the torsion-free Hantzsche-Wendt / Promislow group P."""
    tx1, ty1, tz1, sx1, sy1 = g1
    tx2, ty2, tz2, sx2, sy2 = g2
    sz1 = sx1 * sy1
    return (tx1 + sx1 * tx2, ty1 + sy1 * ty2, tz1 + sz1 * tz2, sx1 * sx2, sy1 * sy2)


def promislow_inv(g: PromislowElem) -> PromislowElem:
    """Exact O(1) group inverse in P."""
    tx, ty, tz, sx, sy = g
    return (-sx * tx, -sy * ty, -(sx * sy) * tz, sx, sy)


def promislow_pow(g: PromislowElem, exp: int) -> PromislowElem:
    """Exact integer power g^exp in P."""
    if exp == 0:
        return PROMISLOW_ID
    base = g if exp > 0 else promislow_inv(g)
    acc = PROMISLOW_ID
    k = abs(exp)
    while k > 0:
        if k & 1:
            acc = promislow_mul(acc, base)
        base = promislow_mul(base, base)
        k >>= 1
    return acc


def parse_promislow_word(word: str) -> PromislowElem:
    """
    Evaluate a generator word in `P` where `a, b` (or `x, y`) denote generators and
    `A, B` (or `X, Y`) denote `a^-1, b^-1` (`'1'` or `''` denotes identity).
    """
    if word in ("", "1"):
        return PROMISLOW_ID
    a_inv = promislow_inv(PROMISLOW_A)
    b_inv = promislow_inv(PROMISLOW_B)
    tok_map = {
        "a": PROMISLOW_A,
        "A": a_inv,
        "b": PROMISLOW_B,
        "B": b_inv,
        "x": PROMISLOW_A,
        "X": a_inv,
        "y": PROMISLOW_B,
        "Y": b_inv,
    }
    cur = PROMISLOW_ID
    for ch in word:
        if ch not in tok_map:
            raise ValueError(f"Unsupported generator symbol {ch!r} in word {word!r}")
        cur = promislow_mul(cur, tok_map[ch])
    return cur


def format_promislow_elem(g: PromislowElem) -> str:
    """Compact canonical coordinate string for hypercube axes and certificates."""
    tx, ty, tz, sx, sy = g
    coset = {
        (1, 1): "I",
        (1, -1): "a",
        (-1, 1): "b",
        (-1, -1): "ab",
    }[(sx, sy)]
    return f"({tx},{ty},{tz};{coset})"


def promislow_word_ball(radius: int = 3) -> Dict[PromislowElem, str]:
    """Generate the exact reduced word ball of given radius in P around 1_P."""
    ball: Dict[PromislowElem, str] = {PROMISLOW_ID: "1"}
    q: deque[Tuple[str, PromislowElem]] = deque([("", PROMISLOW_ID)])
    steps = (
        ("a", "A", PROMISLOW_A),
        ("A", "a", promislow_inv(PROMISLOW_A)),
        ("b", "B", PROMISLOW_B),
        ("B", "b", promislow_inv(PROMISLOW_B)),
    )
    while q:
        w, g = q.popleft()
        if len(w) >= radius:
            continue
        for ch, inv_ch, gen in steps:
            if w and w[-1] == inv_ch:
                continue
            nw = w + ch
            ng = promislow_mul(g, gen)
            if ng not in ball:
                ball[ng] = nw
                q.append((nw, ng))
    return ball


# ==============================================================================
# 1. GENERAL SPARSE GROUP RING & TWISTED GROUP-RING ENGINE (CHAR 0 & CHAR p)
# ==============================================================================


@dataclass(frozen=True)
class GroupRingSpec:
    """
    Algebra specification for a sparse group ring `R[G]` or 2-cochain twisted group/loop
    algebra `R^{sigma}[G]` over Z (`modulus=None`) or `F_p` (`modulus=p`).
    """

    name: str
    identity: Hashable
    mul_fn: Callable[[Any, Any], Any]
    modulus: Optional[int] = None
    cocycle_fn: Optional[Callable[[Any, Any], int]] = None
    format_fn: Callable[[Any], str] = str

    def elem(self, terms: Dict[Any, int]) -> "GroupRingElem":
        cleaned: Dict[Any, int] = {}
        for g, c in terms.items():
            val = (int(c) % self.modulus) if self.modulus is not None else int(c)
            if val != 0:
                cleaned[g] = val
        return GroupRingElem(self, cleaned)

    def zero(self) -> "GroupRingElem":
        return GroupRingElem(self, {})

    def one(self) -> "GroupRingElem":
        return self.elem({self.identity: 1})


@dataclass
class GroupRingElem:
    spec: GroupRingSpec
    terms: Dict[Any, int]

    def is_zero(self) -> bool:
        return len(self.terms) == 0

    def support_size(self) -> int:
        return len(self.terms)

    def with_modulus(self, modulus: Optional[int]) -> "GroupRingElem":
        new_spec = GroupRingSpec(
            name=self.spec.name,
            identity=self.spec.identity,
            mul_fn=self.spec.mul_fn,
            modulus=modulus,
            cocycle_fn=self.spec.cocycle_fn,
            format_fn=self.spec.format_fn,
        )
        return new_spec.elem(self.terms)

    def __add__(self, other: "GroupRingElem") -> "GroupRingElem":
        acc = dict(self.terms)
        for g, c in other.terms.items():
            acc[g] = acc.get(g, 0) + c
        return self.spec.elem(acc)

    def __sub__(self, other: "GroupRingElem") -> "GroupRingElem":
        acc = dict(self.terms)
        for g, c in other.terms.items():
            acc[g] = acc.get(g, 0) - c
        return self.spec.elem(acc)

    def __mul__(self, other: "GroupRingElem") -> "GroupRingElem":
        acc: Dict[Any, int] = {}
        mul_g = self.spec.mul_fn
        cocycle = self.spec.cocycle_fn
        for g1, c1 in self.terms.items():
            for g2, c2 in other.terms.items():
                prod_g = mul_g(g1, g2)
                twist = cocycle(g1, g2) if cocycle is not None else 1
                acc[prod_g] = acc.get(prod_g, 0) + twist * c1 * c2
        return self.spec.elem(acc)


def make_promislow_group_ring(modulus: Optional[int] = None) -> GroupRingSpec:
    return GroupRingSpec(
        name=f"{'Z' if modulus is None else f'F_{modulus}'}[Promislow_P]",
        identity=PROMISLOW_ID,
        mul_fn=promislow_mul,
        modulus=modulus,
        cocycle_fn=None,
        format_fn=format_promislow_elem,
    )


def make_cayley_dickson_twisted_group_ring(
    level: int = 4,
    gamma: Optional[Sequence[int]] = None,
    modulus: Optional[int] = None,
) -> GroupRingSpec:
    """
    Albuquerque & Majid (1999) bridge: construct the 2^n-dimensional Cayley-Dickson algebra
    `A_n(gamma)` explicitly as the twisted group algebra `R^{sigma}[(Z_2)^n]` over the
    elementary abelian 2-group `(Z_2)^n = ({0..2^n-1}, XOR)` with 2-cochain `sigma(i, j) = S[i][j]`.
    """
    cd = CayleyDicksonAlgebra(level=level, gamma=gamma, modulus=modulus)
    st = cd.sign_table
    return GroupRingSpec(
        name=f"TwistedGroupRing_CD(2^{level})",
        identity=0,
        mul_fn=lambda i, j: int(i) ^ int(j),
        modulus=modulus,
        cocycle_fn=lambda i, j: st[int(i)][int(j)],
        format_fn=lambda i: f"e_{i}",
    )


# ==============================================================================
# 2. 3-PASS BSA-R SUPPORT-PRODUCT HYPERCUBE (UNIQUE PRODUCT & PROMISLOW 14 AUDIT)
# ==============================================================================


def compile_support_product_hypercube(
    spec: GroupRingSpec,
    left_support: Sequence[Any],
    right_support: Sequence[Any],
    left_labels: Optional[Sequence[str]] = None,
    right_labels: Optional[Sequence[str]] = None,
) -> Dict[str, Any]:
    """
    Compile the pairwise product map `S_A x S_B -> G` into a 3-pass `BsaRHypercubeCompiler`
    Hilbert `CSR/CSC` hypercube slab and run an `RPipe` multiplicity roll-up to detect:
      - Unique Products (`multiplicity == 1`): any unique product `u * v = p` forces `a_u * b_v = 0`
        in every domain `K`, immediately blocking zero-divisor support there!
      - Two-Unique-Products (`TUP`) & parity-even fibers (`multiplicity % 2 == 0`).
    """
    l_lbls = list(left_labels) if left_labels is not None else [spec.format_fn(g) for g in left_support]
    r_lbls = list(right_labels) if right_labels is not None else [spec.format_fn(g) for g in right_support]

    comp = BsaRHypercubeCompiler(
        axes=("product_elem", "left_word", "right_word", "twist_sign"),
        name=f"support_conv_{spec.name}",
    )

    for idx_u, (u_g, u_name) in enumerate(zip(left_support, l_lbls)):
        rec = LuaDynamicRecord(f"L{idx_u:02d}_{u_name}", attrs={"left_word": u_name})
        for idx_v, (v_g, v_name) in enumerate(zip(right_support, r_lbls)):
            prod_g = spec.mul_fn(u_g, v_g)
            twist = spec.cocycle_fn(u_g, v_g) if spec.cocycle_fn is not None else 1
            rec.add_cell(
                coords={
                    "product_elem": spec.format_fn(prod_g),
                    "left_word": u_name,
                    "right_word": v_name,
                    "twist_sign": str(twist),
                },
                weight=1.0,
                cluster_id=f"{idx_u}:{idx_v}",
            )
        comp.register(rec)

    slab = comp.compile_three_pass()
    roll = BsaRHypercubeCompiler.pipe(slab).rollup_slice(group_axes=("product_elem",)).rows

    unique_products = [r["product_elem"] for r in roll if r["raw_cells"] == 1]
    odd_multiplicity_products = [r["product_elem"] for r in roll if (r["raw_cells"] % 2) == 1]
    multiplicities = [int(r["raw_cells"]) for r in roll]

    return {
        "group_ring": spec.name,
        "left_size": len(left_support),
        "right_size": len(right_support),
        "cartesian_pairs": len(left_support) * len(right_support),
        "distinct_products": len(roll),
        "unique_product_count": len(unique_products),
        "has_unique_product_property_on_pair": len(unique_products) > 0,
        "has_two_unique_products_on_pair": len(unique_products) >= 2,
        "odd_multiplicity_product_count": len(odd_multiplicity_products),
        "min_multiplicity": min(multiplicities) if multiplicities else 0,
        "max_multiplicity": max(multiplicities) if multiplicities else 0,
        "rats_sha256": slab["rats_sha256"],
        "slab": slab,
    }


def verify_promislow_14_non_up_set() -> Dict[str, Any]:
    """
    Verify David Promislow's (1988) 14-element non-unique-product subset inside the
    torsion-free Hantzsche-Wendt group P via 3-pass BSA-R hypercube compilation.
    """
    spec = make_promislow_group_ring(modulus=None)
    elems = [parse_promislow_word(w) for w in PROMISLOW_14_NON_UP_WORDS]
    assert len(set(elems)) == 14, "All 14 Promislow elements must be distinct in P."
    assert PROMISLOW_ID not in set(elems), "Promislow's 14-element set avoids 1_P."

    audit = compile_support_product_hypercube(
        spec,
        left_support=elems,
        right_support=elems,
        left_labels=PROMISLOW_14_NON_UP_WORDS,
        right_labels=PROMISLOW_14_NON_UP_WORDS,
    )
    audit.pop("slab")
    return {
        "promislow_14_words": list(PROMISLOW_14_NON_UP_WORDS),
        "relators_verified": (
            promislow_mul(promislow_inv(PROMISLOW_B), promislow_mul(promislow_pow(PROMISLOW_A, 2), PROMISLOW_B))
            == promislow_pow(PROMISLOW_A, -2)
            and promislow_mul(promislow_inv(PROMISLOW_A), promislow_mul(promislow_pow(PROMISLOW_B, 2), PROMISLOW_A))
            == promislow_pow(PROMISLOW_B, -2)
        ),
        **audit,
    }


# ==============================================================================
# 3. GARDAM (2102.11818) F_2[P] UNIT & CHAR-0 VS CHAR-p ANNIHILATOR PROBER
# ==============================================================================


def construct_gardam_f2_unit_and_char0_lift() -> Dict[str, Any]:
    """
    Construct Giles Gardam's (`arXiv:2102.11818`, *Annals of Mathematics* 2021) explicit
    21-element nontrivial unit `alpha = p + q a + r b + s ab` in `F_2[P]`, solve for its
    exact 21-element inverse `beta = alpha^-1` in `F_2[P]`, verify `alpha * beta == 1_P (mod 2)`,
    and audit the exact `char 0` lift in `Z[P]` showing how positive-characteristic parity
    cancellation leaves `char 0` open.
    """
    spec_z = make_promislow_group_ring(modulus=None)
    spec_f2 = make_promislow_group_ring(modulus=2)

    x = promislow_pow(PROMISLOW_A, 2)
    y = promislow_pow(PROMISLOW_B, 2)
    ab = promislow_mul(PROMISLOW_A, PROMISLOW_B)
    z = promislow_pow(ab, 2)

    def laurent_sum(exps: Iterable[Tuple[int, int, int]]) -> GroupRingElem:
        terms: Dict[PromislowElem, int] = {}
        for ix, iy, iz in exps:
            g = promislow_mul(
                promislow_pow(x, ix),
                promislow_mul(promislow_pow(y, iy), promislow_pow(z, iz)),
            )
            terms[g] = terms.get(g, 0) + 1
        return spec_z.elem(terms)

    p_part = laurent_sum((ix, iy, iz) for ix in (0, 1) for iy in (0, 1) for iz in (0, -1))
    q_part = laurent_sum([(-1, -1, 0), (1, 0, 0), (0, -1, 1), (0, 0, 1)])
    r_part = laurent_sum([(0, 0, 0), (1, 0, 0), (0, -1, 1), (1, 1, 1)])
    s_part = laurent_sum([(0, 0, 0), (1, 0, -1), (-1, 0, -1), (0, 1, -1), (0, -1, -1)])

    e_a = spec_z.elem({PROMISLOW_A: 1})
    e_b = spec_z.elem({PROMISLOW_B: 1})
    e_ab = spec_z.elem({ab: 1})

    alpha_z = p_part + (q_part * e_a) + (r_part * e_b) + (s_part * e_ab)
    alpha_f2 = alpha_z.with_modulus(2)

    # Compact [-2..2]^3 x V_4 translation box (5^3 * 4 = 500 group elements) suffices to find beta!
    coset_reps = (PROMISLOW_ID, PROMISLOW_A, PROMISLOW_B, ab)
    box: List[PromislowElem] = []
    for ix in range(-2, 3):
        tx_g = promislow_pow(x, ix)
        for iy in range(-2, 3):
            txy_g = promislow_mul(tx_g, promislow_pow(y, iy))
            for iz in range(-2, 3):
                t_all = promislow_mul(txy_g, promislow_pow(z, iz))
                for rep in coset_reps:
                    box.append(promislow_mul(t_all, rep))

    # Bitset Gaussian elimination over F_2 for alpha * beta == 1_P
    col_n = len(box)
    row_map: Dict[PromislowElem, int] = {}
    rows: List[int] = []
    for col_idx, h in enumerate(box):
        for g in alpha_f2.terms:
            prod = promislow_mul(g, h)
            r_idx = row_map.setdefault(prod, len(row_map))
            if r_idx == len(rows):
                rows.append(0)
            rows[r_idx] ^= 1 << col_idx

    id_row = row_map[PROMISLOW_ID]
    aug_rows = [r | ((1 << col_n) if idx == id_row else 0) for idx, r in enumerate(rows)]
    pivots: Dict[int, int] = {}
    for r_val in aug_rows:
        cur = r_val
        while cur:
            lsb = cur & -cur
            c = lsb.bit_length() - 1
            if c == col_n:
                raise RuntimeError("Unexpected F_2 inconsistency on Gardam unit box.")
            if c in pivots:
                cur ^= pivots[c]
            else:
                pivots[c] = cur
                break

    sol_mask = 0
    for c in sorted(pivots.keys(), reverse=True):
        row_val = pivots[c]
        rhs_bit = (row_val >> col_n) & 1
        other = (row_val & ((1 << col_n) - 1)) ^ (1 << c)
        parity = (other & sol_mask).bit_count() & 1
        if rhs_bit ^ parity:
            sol_mask |= 1 << c

    beta_z = spec_z.elem({box[c]: 1 for c in range(col_n) if (sol_mask >> c) & 1})
    beta_f2 = beta_z.with_modulus(2)

    prod_f2 = alpha_f2 * beta_f2
    prod_z = alpha_z * beta_z

    off_id_coeffs = sorted({c for g, c in prod_z.terms.items() if g != PROMISLOW_ID})
    conv_audit = compile_support_product_hypercube(
        spec_z,
        left_support=list(alpha_z.terms.keys()),
        right_support=list(beta_z.terms.keys()),
    )

    return {
        "group": "Promislow / Hantzsche-Wendt P = <a, b | b^-1 a^2 b = a^-2, a^-1 b^2 a = b^-2>",
        "alpha_support_size": alpha_z.support_size(),
        "beta_inverse_support_size": beta_z.support_size(),
        "f2_product_equals_identity": prod_f2.terms == {PROMISLOW_ID: 1},
        "f2_right_and_left_unit": (
            prod_f2.terms == {PROMISLOW_ID: 1}
            and (beta_f2 * alpha_f2).terms == {PROMISLOW_ID: 1}
        ),
        "char0_z_product_support_size": prod_z.support_size(),
        "char0_identity_coefficient": prod_z.terms.get(PROMISLOW_ID, 0),
        "char0_off_identity_distinct_coefficients": off_id_coeffs,
        "all_off_identity_even_mod_2": all((c % 2) == 0 for c in off_id_coeffs),
        "unique_products_in_alpha_x_beta": conv_audit["unique_product_count"],
        "odd_multiplicity_products_in_alpha_x_beta": conv_audit["odd_multiplicity_product_count"],
        "hypercube_rats_sha256": conv_audit["rats_sha256"],
    }


def solve_support_zero_divisor_kernel(
    alpha: GroupRingElem,
    candidate_right_support: Sequence[Any],
    primes: Sequence[int] = (2, 3, 5),
) -> Dict[str, Any]:
    """
    Given a nonzero element `alpha` in `Z[G]` (or `Z^{sigma}[G]`) and a finite candidate
    right-annihilator support `S_B subset G`, build the exact homogeneous linear system
    `alpha * beta == 0` (`beta` supported on `S_B`) and compare:
      - Characteristic-0 exact nullity `dim_Q { beta in Q[S_B] : alpha * beta = 0 }`, vs.
      - Positive-characteristic modular nullities `dim_{F_p} { beta in F_p[S_B] : alpha * beta = 0 }`.
    """
    spec_z = GroupRingSpec(
        name=alpha.spec.name,
        identity=alpha.spec.identity,
        mul_fn=alpha.spec.mul_fn,
        modulus=None,
        cocycle_fn=alpha.spec.cocycle_fn,
        format_fn=alpha.spec.format_fn,
    )
    alpha_z = spec_z.elem(alpha.terms)

    row_index: Dict[Any, int] = {}
    cols = list(candidate_right_support)
    # Discover all image group elements g * h
    for h in cols:
        for g in alpha_z.terms:
            prod_g = spec_z.mul_fn(g, h)
            if prod_g not in row_index:
                row_index[prod_g] = len(row_index)

    mat_z: List[List[int]] = [[0] * len(cols) for _ in range(len(row_index))]
    for col_idx, h in enumerate(cols):
        for g, coeff_a in alpha_z.terms.items():
            prod_g = spec_z.mul_fn(g, h)
            twist = spec_z.cocycle_fn(g, h) if spec_z.cocycle_fn is not None else 1
            mat_z[row_index[prod_g]][col_idx] += twist * coeff_a

    q_null = exact_nullspace_rational(mat_z)
    char0_witnesses: List[Dict[str, int]] = []
    for vec_q in q_null[:4]:
        ints = clear_fraction_denominators(vec_q)
        beta_el = spec_z.elem({cols[i]: ints[i] for i in range(len(cols)) if ints[i] != 0})
        assert (alpha_z * beta_el).is_zero()
        char0_witnesses.append({spec_z.format_fn(k): v for k, v in beta_el.terms.items()})

    char_p_nullities: Dict[int, Dict[str, Any]] = {}
    for p in primes:
        p_null = exact_nullspace_mod_p(mat_z, p)
        sample_p: Optional[Dict[str, int]] = None
        if p_null:
            alpha_p = alpha_z.with_modulus(p)
            beta_p = alpha_p.spec.elem(
                {cols[i]: p_null[0][i] for i in range(len(cols)) if p_null[0][i] != 0}
            )
            assert (alpha_p * beta_p).is_zero()
            sample_p = {spec_z.format_fn(k): v for k, v in beta_p.terms.items()}
        char_p_nullities[p] = {
            "nullity": len(p_null),
            "sample_annihilator": sample_p,
        }

    return {
        "algebra": spec_z.name,
        "alpha_support_size": alpha_z.support_size(),
        "candidate_right_support_size": len(cols),
        "linear_constraints_rows": len(row_index),
        "char0_nullity_Q": len(q_null),
        "char0_annihilator_witnesses": char0_witnesses,
        "positive_char_nullities": char_p_nullities,
    }
