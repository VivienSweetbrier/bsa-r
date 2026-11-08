#!/usr/bin/env python3
"""
NAVIER-STOKES ROUND 4 (`STEP 5`) ALGEBRAIC & GROUP-RING BRIDGE (`bsar.round4_bridge`)
License: GNU AGPLv3
Attestation: probabilistic_structural
Core Dependencies: 0 (Python >= 3.10 Stdlib; optional `z3-solver` & `sympy` auto-detected)

Bridges the constructive Round-4 machinery (`Step5SpectralVarianceTaoRound4.lean` &
`step5_spectral_variance_tao_round4.py`) directly into pure & computational algebra:

1. **Cayley-Dickson Bimodal Shell Dispersion `Theta` (`cayley_dickson_shell_dispersion`)**:
   - Applies Round 4's `Theorem J1` (`step5_spectral_variance_identity`) and `Theorem K`
     (`step5_two_shell_lagrange_variance`: `M_0 P - D^2 = e_1 e_2 (m_2 - m_1)^2`) via the
     single-pass Applicative `MooreFold` (`make_round4_spectral_fold`) to both:
       (a) the `Z_2` doubling shells `(m_1, m_2) = (-1, +1)` (`e_1 = ||vec_a||^2, e_2 = ||vec_b||^2`),
           rewriting Koebisu's sedenion determinant quartic directly as:
               `Q(x) = s_0^2 + 2 s_0 M_im + M_im^2 * (1 - Theta_z2) + 4 <vec_a, vec_b>^2`,
           proving that EVERY zero divisor is forced onto maximal bimodal dispersion `Theta_z2 == 1`!
       (b) the `n`-shell dyadic filtration `m(i) = i.bit_length()` across `32D` Pathions,
           `64D` Chingons, and `128D` Routons.
2. **Zero-Dependency Outward-Rounded `OutwardInterval` (`math.nextafter` IEEE-754)**:
   - Certifies continuous Riemannian / irrational-angle frames on Reggiani's (`arXiv:2411.18881`)
     Stiefel manifold `V_2(R^7)` with rigorous `[lo, hi]` enclosures and `0` pip packages!
3. **`T^3` 4x4 Bloch-Floquet Matrix Symbol for `P = Z^3 x| V_4` (`promislow_bloch_floquet_t3_audit`)**:
   - Maps any `alpha in Z[P]` of the torsion-free Hantzsche-Wendt / Promislow group `P` onto
     its exact `4 x 4` Laurent matrix symbol `M_alpha(X, Y, Z)` on the same 3-torus `T^3`
     used in Navier-Stokes Rounds 1-4.
   - Evaluates exact rational Bareiss `det(M_alpha(X_0, Y_0, Z_0))` at prime base points
     `(X_0, Y_0, Z_0) = (2, 3, 5)`: whenever `det != 0` at EVEN ONE point, `M_alpha` is
     invertible over `C(X, Y, Z)`, certifying in microseconds that `alpha * beta != 0` for
     **ALL** nonzero `beta in C[P]` of **ARBITRARY UNBOUNDED FINITE SUPPORT** (even when
     `supp(alpha)` is Promislow's 14-element non-Unique-Product set!).
4. **Optional `Z3` + `SymPy` Universal Symbolic Prover (`verify_round4_algebraic_bridge_z3`)**:
   - When `z3-solver` and `sympy` are installed (`pip install bsar[verify]`), discharges
     universal `QF_NRA` `unsat` proofs for the Round-4 / Koebisu bimodal dispersion law,
     symbolic Sedenion flexibility across all 32 real variables, and `char 0` non-UP support
     systems.
"""

from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction
import importlib.util
import math
from typing import Any, Dict, List, Optional, Sequence, Tuple

from .fp_coalgebra import ModalBox, make_round4_spectral_fold
from .group_rings import (
    PROMISLOW_14_NON_UP_WORDS,
    PROMISLOW_A,
    PROMISLOW_B,
    PROMISLOW_ID,
    GroupRingElem,
    PromislowElem,
    make_promislow_group_ring,
    parse_promislow_word,
    promislow_inv,
    promislow_mul,
)
from .math_algebras import CDElem, CayleyDicksonAlgebra, bareiss_det_int


# ==============================================================================
# 1. ZERO-DEPENDENCY OUTWARD-ROUNDED IEEE-754 INTERVAL ARITHMETIC (`OutwardInterval`)
# ==============================================================================


def _dn(val: float) -> float:
    return math.nextafter(val, -math.inf) if math.isfinite(val) else val


def _up(val: float) -> float:
    return math.nextafter(val, math.inf) if math.isfinite(val) else val


@dataclass(frozen=True)
class OutwardInterval:
    """
    Rigorous outward-rounded IEEE-754 binary64 interval `[lo, hi]` using pure Python stdlib
    `math.nextafter` (`1` ULP conservative outward enclosure on every arithmetic operation).
    """

    lo: float
    hi: float

    def __post_init__(self) -> None:
        if math.isnan(self.lo) or math.isnan(self.hi) or self.lo > self.hi:
            raise ValueError(f"Invalid OutwardInterval [{self.lo}, {self.hi}]")

    @classmethod
    def exact(cls, val: int | float) -> "OutwardInterval":
        f = float(val)
        return cls(f, f)

    @classmethod
    def from_rational(cls, num: int, den: int = 1) -> "OutwardInterval":
        if den == 0:
            raise ZeroDivisionError("Interval denominator cannot be zero.")
        q = float(Fraction(num, den))
        # Exact power-of-two denominators are exact in IEEE-754; otherwise pad 1 ULP outward
        if (abs(den) & (abs(den) - 1)) == 0:
            return cls(q, q)
        return cls(_dn(q), _up(q))

    def contains(self, val: float) -> bool:
        return self.lo <= val <= self.hi

    @property
    def width(self) -> float:
        return self.hi - self.lo

    def __add__(self, other: "OutwardInterval") -> "OutwardInterval":
        return OutwardInterval(_dn(self.lo + other.lo), _up(self.hi + other.hi))

    def __sub__(self, other: "OutwardInterval") -> "OutwardInterval":
        return OutwardInterval(_dn(self.lo - other.hi), _up(self.hi - other.lo))

    def __mul__(self, other: "OutwardInterval") -> "OutwardInterval":
        prods = (
            self.lo * other.lo,
            self.lo * other.hi,
            self.hi * other.lo,
            self.hi * other.hi,
        )
        return OutwardInterval(_dn(min(prods)), _up(max(prods)))

    def sqr(self) -> "OutwardInterval":
        if self.lo >= 0.0:
            return OutwardInterval(_dn(self.lo * self.lo), _up(self.hi * self.hi))
        if self.hi <= 0.0:
            return OutwardInterval(_dn(self.hi * self.hi), _up(self.lo * self.lo))
        top = max(abs(self.lo), abs(self.hi))
        return OutwardInterval(0.0, _up(top * top))


def certify_continuous_stiefel_rotation_interval(angle_rad: float = 0.73) -> Dict[str, Any]:
    """
    Certify a continuous irrational-angle geodesic rotation `(u(phi), v(phi))` on Silvio
    Reggiani's (`arXiv:2411.18881`) Stiefel manifold `V_2(R^7)` using outward-rounded
    `OutwardInterval` arithmetic (`0` external libraries):
      u(phi) = cos(phi) e_1 + sin(phi) e_2
      v(phi) = -sin(phi) e_4 + cos(phi) e_7   (orthogonal in R^7 for ALL phi in R!)
    Verifies `0 in Q_interval(x(phi))` and `1 in Theta_z2_interval(x(phi))`.
    """
    c_mid = math.cos(angle_rad)
    s_mid = math.sin(angle_rad)
    c_iv = OutwardInterval(_dn(c_mid), _up(c_mid))
    s_iv = OutwardInterval(_dn(s_mid), _up(s_mid))

    # ||u||^2 = cos^2 + sin^2, ||v||^2 = (-sin)^2 + cos^2, <u, v> = 0 (disjoint octonion axes {1,2} vs {4,7})
    e1_iv = c_iv.sqr() + s_iv.sqr()
    e2_iv = s_iv.sqr() + c_iv.sqr()
    dot_iv = OutwardInterval.exact(0.0)

    # Round-4 Theorem Kquartic enclosure: Q = (e1 - e2)^2 + 4 * dot^2
    q_iv = (e1_iv - e2_iv).sqr() + (OutwardInterval.exact(4.0) * dot_iv.sqr())
    m0_iv = e1_iv + e2_iv
    var_num_iv = OutwardInterval.exact(4.0) * (e1_iv * e2_iv)
    m0_sq_iv = m0_iv.sqr()

    return {
        "angle_rad": angle_rad,
        "e1_norm_sq_interval": [e1_iv.lo, e1_iv.hi],
        "e2_norm_sq_interval": [e2_iv.lo, e2_iv.hi],
        "koebisu_Q_interval": [q_iv.lo, q_iv.hi],
        "koebisu_Q_traps_zero": q_iv.contains(0.0),
        "bimodal_4e1e2_minus_M0sq_traps_zero": (var_num_iv - m0_sq_iv).contains(0.0),
    }


# ==============================================================================
# 2. ROUND-4 BIMODAL & DYADIC SHELL DISPERSION `Theta` FOR CAYLEY-DICKSON ALGEBRAS
# ==============================================================================


def cayley_dickson_shell_dispersion(x: CDElem) -> ModalBox[Dict[str, Any]]:
    """
    Compute Round 4's Shifted-Laplacian Spectral-Variance & Bimodal Dispersion invariants
    on ANY integer Cayley-Dickson element `x in A_n(gamma)` using the single-pass fused
    `MooreFold` (`make_round4_spectral_fold`) wrapped in a Sweetbrier `ModalBox`:
      1. `z2_doubling_shells`: two-shell spectrum `[(-1, ||vec_a||^2), (+1, ||vec_b||^2)]`
         connecting `Step5SpectralVarianceTaoRound4.lean` (`Theorem K`) directly to
         Koebisu / Moreno / Reggiani zero-divisor geometry (`Theta_z2 == 1` necessary!).
      2. `dyadic_filtration_shells`: `n + 1` shells `m(i) = i.bit_length()` across `2^n`-ions
         (`16D, 32D, 64D, 128D, ...`).
    """
    if any(not isinstance(c, int) for c in x.coords):
        raise ValueError("Provide integer coordinates in Z^{2^n} for exact Round-4 moment folding.")

    fold_engine = make_round4_spectral_fold()
    dim = x.alg.dim
    half = dim >> 1
    coords = [int(v) for v in x.coords]

    # 1. Z_2 Doubling Imaginary Shells: m = -1 (low half 1..half-1) vs m = +1 (high half half+1..dim-1)
    # Note: for n >= 1, index 0 is real e_0 and index `half` is generator e_{2^{n-1}}!
    s0_heads = coords[0] * coords[0] + (coords[half] * coords[half] if half > 0 else 0)
    e_low_im = sum(c * c for c in coords[1:half]) if half > 1 else 0
    e_high_im = sum(c * c for c in coords[half + 1 : dim]) if half > 1 else 0

    z2_stats = fold_engine.run([(-1, e_low_im), (1, e_high_im)])
    # Verify Round 4 Theorem K exact formula: M0 * P - D^2 == e_low * e_high * (1 - (-1))^2 == 4 * e_low * e_high!
    lagrange_4e1e2 = 4 * e_low_im * e_high_im
    assert z2_stats["variance_M0P_minus_D2"] == lagrange_4e1e2

    # 2. Multi-shell dyadic grading `shell(i) = i.bit_length()` (0 for e_0, 1 for e_1, 2 for e_2..e_3, ..., n for upper half)
    dyadic_stream = [(idx.bit_length(), val * val) for idx, val in enumerate(coords) if val != 0]
    dyadic_stats = fold_engine.run(dyadic_stream)

    payload: Dict[str, Any] = {
        "algebra_dim": dim,
        "gamma": x.alg.gamma,
        "head_scalars_s0_sq": s0_heads,
        "z2_bimodal_imaginary_shells": {
            "e_low_im": e_low_im,
            "e_high_im": e_high_im,
            **z2_stats,
            "theorem_K_4_e1_e2": lagrange_4e1e2,
            "can_reach_stiefel_zero_divisor_shell_balance": (
                s0_heads == 0 and e_low_im > 0 and e_low_im == e_high_im
            ),
        },
        "dyadic_multi_shell_filtration": dyadic_stats,
    }

    if dim == 16 and x.alg.is_standard_real and x.alg.modulus is None:
        dot_im = sum(coords[i] * coords[i + 8] for i in range(1, 8))
        m_im = e_low_im + e_high_im
        # Exact Round-4 rewrite of Koebisu's quartic Q(x):
        # Q(x) = s0^2 + 2*s0*M_im + (M_im^2 - 4*e1*e2) + 4*dot^2 == s0^2 + 2*s0*M_im + D_z2^2 + 4*dot^2
        q_round4 = (
            s0_heads * s0_heads
            + 2 * s0_heads * m_im
            + (z2_stats["D"] * z2_stats["D"])
            + 4 * (dot_im * dot_im)
        )
        payload["sedenion_round4_koebisu_bridge"] = {
            "quartic_Q_via_round4_Theorem_K": q_round4,
            "dot_im": dot_im,
            "single_shell_strictly_invertible": (
                (e_low_im == 0 or e_high_im == 0) and (s0_heads + m_im > 0) and (q_round4 > 0)
            ),
            "maximal_dispersion_theta_equals_1": (
                e_low_im > 0 and z2_stats["variance_M0P_minus_D2"] == m_im * m_im
            ),
        }

    return ModalBox.pure(payload, label="cayley_dickson_shell_dispersion")


# ==============================================================================
# 3. `T^3` 4x4 BLOCH-FLOQUET MATRIX SYMBOL FOR TORSION-FREE GROUP `P = Z^3 x| V_4`
# ==============================================================================


_V4_COSETS: Tuple[PromislowElem, ...] = (
    PROMISLOW_ID,
    PROMISLOW_A,
    PROMISLOW_B,
    promislow_mul(PROMISLOW_A, PROMISLOW_B),
)


def promislow_bloch_floquet_matrix_at_rationals(
    alpha: GroupRingElem,
    x_val: Fraction = Fraction(2, 1),
    y_val: Fraction = Fraction(3, 1),
    z_val: Fraction = Fraction(5, 1),
) -> List[List[Fraction]]:
    """
    Evaluate the faithful induced `4 x 4` Bloch-Floquet Laurent representation
    `M_alpha(X, Y, Z)` of `alpha in Z[P]` (`P = Z^3 x| V_4`, where `X = a^2 = (2,0,0;I)`,
    `Y = b^2 = (0,2,0;I)`, `Z = (ab)^-2 = (0,0,2;I)` are the pure `2*Z^3` lattice generators)
    at ANY exact invertible rational point `(X, Y, Z) in (Q^x)^3`!

    Mathematical Guarantee (`probabilistic_structural`):
      Viewing `Q[P]` as a free right `Q[T]`-module (`T = 2*Z^3` normal abelian translation
      lattice) on the 4 coset representatives `{r_0, r_1, r_2, r_3}`, left multiplication
      satisfies `g * r_j = r_i * t_{i, j}` for a UNIQUE coset `r_i` and UNIQUE pure
      translation `t_{i, j} = r_i^{-1} * g * r_j = (2*nx, 2*ny, 2*nz; I) in T`!
      Because `(g_1 * g_2) * r_j = g_1 * (r_k * t_2) = (g_1 * r_k) * t_2 = r_i * (t_1 * t_2)`
      and `T` is abelian, `alpha |-> M_alpha(X, Y, Z)` is an EXACT INJECTIVE `Q`-algebra
      homomorphism into `M_4(Q[X^{+-1}, Y^{+-1}, Z^{+-1}])` (`M_{a*b} == M_a @ M_b`).
      If `det M_alpha(x_val, y_val, z_val) != 0` at EVEN ONE rational point, `M_alpha` is
      invertible over `Q(X, Y, Z)`, proving UNCONDITIONALLY that `alpha * beta != 0` for
      EVERY nonzero `beta in C[P]` of ANY arbitrarily large finite support!
    """
    if x_val == 0 or y_val == 0 or z_val == 0:
        raise ValueError("Bloch-Floquet Laurent evaluation points (x_val, y_val, z_val) must be nonzero.")

    mat: List[List[Fraction]] = [[Fraction(0, 1) for _ in range(4)] for _ in range(4)]
    coset_by_orient = {(r[3], r[4]): (idx, r) for idx, r in enumerate(_V4_COSETS)}

    for g, coeff in alpha.terms.items():
        if coeff == 0:
            continue
        c_frac = Fraction(int(coeff), 1)
        for j_col, r_j in enumerate(_V4_COSETS):
            prod = promislow_mul(g, r_j)
            i_row, r_i = coset_by_orient[(prod[3], prod[4])]
            # Right Z[T]-module coordinate `t = r_i^{-1} * g * r_j` has orientation (1, 1) and even coords!
            t_pure = promislow_mul(promislow_inv(r_i), prod)
            assert (t_pure[3], t_pure[4]) == (1, 1)
            assert (t_pure[0] % 2 == 0) and (t_pure[1] % 2 == 0) and (t_pure[2] % 2 == 0)
            nx, ny, nz = t_pure[0] // 2, t_pure[1] // 2, t_pure[2] // 2
            monomial = (x_val ** nx) * (y_val ** ny) * (z_val ** nz)
            mat[i_row][j_col] += c_frac * monomial

    return mat


def _det_4x4_fraction(m: Sequence[Sequence[Fraction]]) -> Fraction:
    """Exact 4x4 rational determinant via clearing row denominators + Bareiss integer kernel."""
    scale_prod = Fraction(1, 1)
    int_rows: List[List[int]] = []
    for row in m:
        lcm_d = 1
        for val in row:
            lcm_d = math.lcm(lcm_d, val.denominator)
        scale_prod *= Fraction(lcm_d, 1)
        int_rows.append([int(val * lcm_d) for val in row])
    return Fraction(bareiss_det_int(int_rows), 1) / scale_prod


def promislow_bloch_floquet_t3_audit(alpha: GroupRingElem) -> ModalBox[Dict[str, Any]]:
    """
    Certify non-zero-divisibility (or inspect torus rank) of `alpha in Z[P]` across ALL
    unbounded finite supports `beta in C[P]` via exact `T^3` / `(Q^x)^3` Bloch-Floquet
    `4 x 4` determinant evaluation at:
      - the 8 torus character corners `(X, Y, Z) in {-1, +1}^3 subset T^3` (exact integers!), and
      - the prime transcendental-proxy point `(X, Y, Z) = (2, 3, 5)`.
    """
    corner_dets: Dict[str, int] = {}
    for sx in (1, -1):
        for sy in (1, -1):
            for sz in (1, -1):
                m_c = promislow_bloch_floquet_matrix_at_rationals(
                    alpha, Fraction(sx, 1), Fraction(sy, 1), Fraction(sz, 1)
                )
                d_c = _det_4x4_fraction(m_c)
                assert d_c.denominator == 1
                corner_dets[f"({sx:+d},{sy:+d},{sz:+d})"] = int(d_c.numerator)

    m_prime = promislow_bloch_floquet_matrix_at_rationals(
        alpha, Fraction(2, 1), Fraction(3, 1), Fraction(5, 1)
    )
    det_prime = _det_4x4_fraction(m_prime)
    any_nonzero = (det_prime != 0) or any(v != 0 for v in corner_dets.values())

    return ModalBox.pure(
        {
            "support_size": alpha.support_size(),
            "t3_character_corner_determinants": corner_dets,
            "augmentation_det_at_1_1_1": corner_dets["(+1,+1,+1)"],
            "augmentation_det_mod_2": corner_dets["(+1,+1,+1)"] % 2,
            "det_at_2_3_5_rational": f"{det_prime.numerator}/{det_prime.denominator}",
            "certified_non_zero_divisor_in_char0_unbounded_support": (
                bool(any_nonzero and not alpha.is_zero())
            ),
        },
        label="promislow_bloch_floquet_t3_audit",
    )


# ==============================================================================
# 4. OPTIONAL `Z3` + `SYMPY` UNIVERSAL SYMBOLIC CERTIFIER (`pip install bsar[verify]`)
# ==============================================================================


def has_z3_and_sympy() -> bool:
    return (
        importlib.util.find_spec("z3") is not None
        and importlib.util.find_spec("sympy") is not None
    )


def verify_round4_algebraic_bridge_z3() -> Dict[str, Any]:
    """
    When `z3-solver` and `sympy` are present, run Round-4-grade universal symbolic & SMT
    proofs (`unsat` == 0 counterexamples over all real numbers `R`):
      1. SymPy + Z3 QF_NRA proof that Koebisu's sedenion determinant quartic `Q(x)` equals
         Round 4's `s0^2 + 2*s0*(e1+e2) + (e1+e2)^2*(1 - Theta) + 4*dot^2`, is `>= 0`
         everywhere, is `> 0` on every single-shell element (`e1 == 0` or `e2 == 0`), and
         forces `Theta == 1` (`e1 == e2 > 0`) whenever `Q(x) == 0`!
      2. Exact 16-variable SymPy polynomial proof of `Flexibility` `(x * y) * x == x * (y * x)`
         across ALL `R^8 x R^8` octonions (and 2-variable symbolic slice in `S_16`).
      3. Z3 QF_NRA proof that the indicator element `alpha = sum_{g in S_14} g` on Promislow's
         14-element non-Unique-Product set has ZERO nontrivial right annihilators supported on
         `S_14` over `R[P]` (`char 0`)!
    """
    if not has_z3_and_sympy():
        return {
            "available": False,
            "reason": "Optional `z3-solver` / `sympy` not installed; core stdlib certificates remain active.",
        }

    import sympy as sp
    import z3

    # 1. SymPy + Z3: Round 4 Theorem K <-> Koebisu Sedenion Quartic Equivalence & Bimodal Necessity
    s0, e1, e2, dot = sp.symbols("s0 e1 e2 dot", real=True)
    nx2 = s0 + e1 + e2
    q_koebisu = nx2**2 - 4 * (e1 * e2 - dot**2)
    # Round-4 form using M_im = e1 + e2 and Theorem K `M_im^2 - 4*e1*e2 == (e1 - e2)^2`
    q_round4 = s0**2 + 2 * s0 * (e1 + e2) + (e1 - e2) ** 2 + 4 * dot**2
    sym_diff = sp.expand(q_koebisu - q_round4)
    assert sym_diff == 0

    s0z, e1z, e2z, dotz = z3.Reals("s0z e1z e2z dotz")
    qz = (s0z + e1z + e2z) ** 2 - 4 * (e1z * e2z - dotz * dotz)

    # 1a. Single-shell impossibility: if (e1 == 0 or e2 == 0) and s0 + e1 + e2 > 0, can Q <= 0?
    sol_single = z3.Solver()
    sol_single.add(
        s0z >= 0,
        e1z >= 0,
        e2z >= 0,
        s0z + e1z + e2z > 0,
        z3.Or(e1z == 0, e2z == 0),
        qz <= 0,
    )
    res_single = sol_single.check()
    assert res_single == z3.unsat

    # 1b. Zero-divisor bimodal necessity: if s0 + e1 + e2 > 0 and Q == 0, must e1 == e2 > 0, s0 == 0, dot == 0?
    sol_bimodal = z3.Solver()
    sol_bimodal.add(
        s0z >= 0,
        e1z >= 0,
        e2z >= 0,
        s0z + e1z + e2z > 0,
        qz == 0,
        z3.Or(s0z != 0, e1z != e2z, e1z <= 0, dotz != 0),
    )
    res_bimodal = sol_bimodal.check()
    assert res_bimodal == z3.unsat

    # 2. Universal 32-variable Polynomial Ring Proof over Z[x0..x15, y0..y15] of Flexibility `(x * y) * x == x * (y * x)` in S_16!
    s16 = CayleyDicksonAlgebra(level=4)
    st = s16.sign_table
    var_names = ",".join([f"x{i}" for i in range(16)] + [f"y{i}" for i in range(16)])
    poly_ring, *gens = sp.ring(var_names, sp.ZZ)
    xs = gens[:16]
    ys = gens[16:]

    def _sym_cd_mul(u: Sequence[Any], v: Sequence[Any]) -> List[Any]:
        out = [poly_ring.zero for _ in range(16)]
        for i in range(16):
            for j in range(16):
                if st[i][j] == 1:
                    out[i ^ j] += u[i] * v[j]
                else:
                    out[i ^ j] -= u[i] * v[j]
        return out

    xy = _sym_cd_mul(xs, ys)
    yx = _sym_cd_mul(ys, xs)
    lhs_flex = _sym_cd_mul(xy, xs)
    rhs_flex = _sym_cd_mul(xs, yx)
    flex_max_residual = all((a - b) == poly_ring.zero for a, b in zip(lhs_flex, rhs_flex))
    assert flex_max_residual

    # 3. Z3 QF_NRA Char-0 Non-Zero-Divisor Proof on Promislow's 14-Element Non-UP Set!
    spec_p = make_promislow_group_ring(modulus=None)
    s14_elems = [parse_promislow_word(w) for w in PROMISLOW_14_NON_UP_WORDS]
    alpha_14 = spec_p.elem({g: 1 for g in s14_elems})
    b_vars = [z3.Real(f"b_{idx}") for idx in range(14)]
    row_exprs: Dict[PromislowElem, Any] = {}
    for j_idx, h in enumerate(s14_elems):
        for g in alpha_14.terms:
            prod = promislow_mul(g, h)
            row_exprs[prod] = row_exprs.get(prod, 0) + b_vars[j_idx]

    sol_p14 = z3.Solver()
    for expr in row_exprs.values():
        sol_p14.add(expr == 0)
    sol_p14.add(z3.Or(*[bv != 0 for bv in b_vars]))
    res_p14 = sol_p14.check()
    assert res_p14 == z3.unsat

    return {
        "available": True,
        "sympy_koebisu_round4_quartic_residual": str(sym_diff),
        "z3_single_shell_zero_divisor_impossibility": str(res_single),
        "z3_zero_divisor_forces_theta_eq_1_and_orthogonality": str(res_bimodal),
        "sympy_universal_32var_sedenion_flexibility_exact": flex_max_residual,
        "z3_promislow14_non_up_char0_annihilator_unsat": str(res_p14),
        "all_universal_proofs_verified": True,
    }
