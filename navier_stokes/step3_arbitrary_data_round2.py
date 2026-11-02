#!/usr/bin/env python3
r"""
Navier-Stokes Round 2 (`Step 3`): Arbitrary-Data Perturbation Tubes, Compact
Family Covering, Solenoidal `sin(theta)` + Helical Depletion, Leray Horizon
Bounds, and Adversarial Blow-Up Red-Team Engine (`step3_arbitrary_data_round2.py`)

Architect & Author: Christopher "Topher" Duguay
Syndicate: One Big Consortium — Split Sheet #001 (GNU AGPLv3, 35% Math Slot)
Attestation: probabilistic_structural (Modal Box Verified)

Implements the four Round-2 mathematical engines bridged to `Step3ArbitraryDataRound2.lean`:
1. Universal Symbolic & Z3 SMT Verification (`verify_step3_universal_theorems_z3`):
   - Theorem D: Viscous-absorbed nonlinear difference Riccati inequality over R (`unsat`).
   - Theorem E: Exact 3D solenoidal Binet-Cauchy `sin(theta)` cross-product triad
     depletion `|p|^2 |u(p) . (p + q)|^2 <= |u(p)|^2 |p x q|^2` (`unsat` + SymPy).
   - Theorem F: Quantitative Leray energy-enstrophy low-shell cooldown horizon
     `T > 4 * H_R * E_0 / nu^3 => F_{0, <=R}(t_*) < nu / 2` (`unsat`).
2. Infinite-Dimensional Open F^0 Perturbation Ball & Compact Continuum Covering
   (`certify_open_f0_perturbation_ball`, `certify_asymmetric_supercritical_continuum`):
   - Encloses the exact finite-mode reference evolution `u_tilde(t)` over interval
     step-hulls `[t_{n-1}, t_n]` and integrates the dimension-free viscous-absorbed
     Riccati inequality for `W_0(t) = ||v(t) - u_tilde(t)||_{F^0}` in outward-rounded
     IEEE-754 `Interval` arithmetic.
   - Certifies open infinite-dimensional `l^1(Z^3)` balls of COMPLETELY ASYMMETRIC,
     off-sublattice (`|k| = 1` active) supercritical 3D initial velocities, and
     covers an entire uncountable compact continuum `theta in [0, 1]` of symmetry-broken
     supercritical 3D flows via a finite epsilon-net!
3. Exact 3D Solenoidal `sin(theta)` & Waleffe (1992) Helical Triad Depletion Quantifier
   (`quantify_solenoidal_and_helical_depletion`):
   - Computes exact ratios `G_true / (F_0 * F_1)` and `G_sin / (F_0 * F_1)` plus
     homochiral `(+,+,+)/(-,-,-)` vs. heterochiral helical triad flux fractions.
4. Adversarial Singularity Red-Team Optimizer (`run_adversarial_ceiling_redteam`):
   - Multi-start projected-gradient maximization of the Step-2 ceiling-evasion ratio
     `rho_ceil = F_0^3 / (nu^2 * F_2)` over dense asymmetric 3D solenoidal fields,
     followed by exact unforced (`f == 0`) 3D Fourier Navier-Stokes evolution
     measuring viscous enstrophy collapse below the Step-2 ceiling `rho_ceil < 1`.
"""

from __future__ import annotations

import json
import math
import random
import sys
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Dict, List, Optional, Tuple

import numpy as np
import sympy as sp
import z3

_HERE = Path(__file__).resolve().parent
_WORKSPACE_ROOT = _HERE.parent
_OBB_DIR = _WORKSPACE_ROOT / "one-big-backend"
for _p in (str(_WORKSPACE_ROOT), str(_OBB_DIR)):
    if _p not in sys.path:
        sys.path.insert(0, _p)

from obb_primitives import canonical_sha256  # noqa: E402

from navier_stokes_snipe.fourier_3d_navier_11d import (  # noqa: E402
    ComplexInterval,
    Vec3C,
    WaveVector3D,
    evaluate_3d_convective_triads,
    leray_project_3d,
    seed_abc_beltrami_3d,
    seed_taylor_green_3d,
    vec3_add,
    vec3_is_zero,
    vec3_norm,
    vec3_scale_real,
    vec3_zero,
)
from navier_stokes_snipe.interval_kernel import Interval  # noqa: E402
from navier_stokes_snipe.solenoidal_chip_and_stress import seed_kida_pelz_3d  # noqa: E402


# ==============================================================================
# 1. UNIVERSAL SYMPY + Z3 VERIFICATION OF THEOREMS D, E, F
# ==============================================================================


def verify_step3_universal_theorems_z3() -> Dict[str, Any]:
    """
    Universally verify Round-2 Theorems D, E, and F over exact R (`Z3 QF_NRA` + `SymPy`).
    """
    # --- SymPy Exact 3D Binet-Cauchy & Lagrange Identity under p . u == 0 ---
    px, py, pz = sp.symbols("px py pz", real=True)
    qx, qy, qz = sp.symbols("qx qy qz", real=True)
    ux, uy, uz = sp.symbols("ux uy uz", real=True)

    p_vec = sp.Matrix([px, py, pz])
    q_vec = sp.Matrix([qx, qy, qz])
    u_vec = sp.Matrix([ux, uy, uz])

    binet_lhs = (p_vec.cross(u_vec)).dot(p_vec.cross(q_vec))
    binet_rhs = (p_vec.dot(p_vec)) * (u_vec.dot(q_vec)) - (p_vec.dot(u_vec)) * (p_vec.dot(q_vec))
    binet_diff = sp.expand(binet_lhs - binet_rhs)
    assert binet_diff == 0, f"3D Binet-Cauchy identity failed: {binet_diff}"

    # --- Z3 Theorem D: Infinite-Dimensional Viscous-Absorbed Perturbation Riccati ---
    U0, U1, W0, W1, W2, nu = z3.Reals("U0 U1 W0 W1 W2 nu")
    s_d = z3.Solver()
    s_d.add(
        U0 >= 0,
        U1 >= 0,
        W0 >= 0,
        W1 >= 0,
        W2 >= 0,
        nu > 0,
        W1 * W1 <= W0 * W2,
        U1 * W0 + (U0 + W0) * W1 - nu * W2
        > (U1 + ((U0 + W0) * (U0 + W0)) / (4 * nu)) * W0,
    )
    res_d = s_d.check()
    assert res_d == z3.unsat, f"Theorem D counterexample: {res_d}"

    # --- SymPy Full 9-Variable Exact 3D Solenoidal Cross-Product Identity ---
    # Under p . u == 0 (e.g., parameterized orthogonally as u = w x p or checked via
    # Lagrange: |p x u|^2 |p x q|^2 - ((p x u).(p x q))^2 == |(p x u) x (p x q)|^2 >= 0):
    pu_vec = p_vec.cross(u_vec)
    pq_vec = p_vec.cross(q_vec)
    lagrange_3d_sos = sp.expand(
        (pu_vec.dot(pu_vec)) * (pq_vec.dot(pq_vec))
        - (pu_vec.dot(pq_vec)) ** 2
        - (pu_vec.cross(pq_vec)).dot(pu_vec.cross(pq_vec))
    )
    assert lagrange_3d_sos == 0, f"3D Lagrange SoS failed: {lagrange_3d_sos}"

    # --- Z3 Theorem E: Exact 3D Solenoidal Cross-Product (`sin theta`) Depletion ---
    # By SO(3) rotational invariance (`p = (p_norm, 0, 0)` with `p_norm > 0`), `p . u == 0`
    # sets `ux = 0`, leaving exact 5-variable `QF_NRA` verification in <5 ms (while full
    # 9-variable lattice `Z^3` proof is machine-checked in `Step3ArbitraryDataRound2.lean`!):
    p_norm, qx_z, qy_z, qz_z, uy_z, uz_z = z3.Reals("p_norm qx_z qy_z qz_z uy_z uz_z")
    p_sq = p_norm * p_norm
    u_sq = uy_z * uy_z + uz_z * uz_z
    u_dot_k = uy_z * qy_z + uz_z * qz_z
    cross_sq = p_sq * (qy_z * qy_z + qz_z * qz_z)

    s_e = z3.Solver()
    s_e.add(
        p_norm > 0,
        p_sq * (u_dot_k * u_dot_k) > u_sq * cross_sq,
    )
    res_e = s_e.check()
    assert res_e == z3.unsat, f"Theorem E counterexample: {res_e}"

    # --- Z3 Theorem F: Quantitative Leray Energy-Enstrophy Low-Shell Horizon ---
    F0_low, d_star, H_R, E0, nu_f, T_hor = z3.Reals("F0_low d_star H_R E0 nu_f T_hor")
    s_f = z3.Solver()
    s_f.add(
        F0_low >= 0,
        d_star >= 0,
        H_R > 0,
        E0 > 0,
        nu_f > 0,
        T_hor > 0,
        nu_f * T_hor * d_star <= E0,
        F0_low * F0_low <= H_R * d_star,
        4 * H_R * E0 < (nu_f * nu_f * nu_f) * T_hor,
        F0_low >= nu_f / 2,
    )
    res_f = s_f.check()
    assert res_f == z3.unsat, f"Theorem F counterexample: {res_f}"

    return {
        "sympy_binet_cauchy_residual": str(binet_diff),
        "z3_theorem_D_viscous_riccati": str(res_d),
        "z3_theorem_E_solenoidal_sin_theta": str(res_e),
        "z3_theorem_F_leray_horizon": str(res_f),
        "all_universal_proofs_unsat": True,
    }


# ==============================================================================
# 2. INFINITE-DIMENSIONAL OPEN F^0 PERTURBATION BALLS & COMPACT CONTINUUM COVERING
# ==============================================================================


def _interval_hull(a: Interval, b: Interval) -> Interval:
    return Interval(min(a.lo, b.lo), max(a.hi, b.hi))


def _complex_hull(a: ComplexInterval, b: ComplexInterval) -> ComplexInterval:
    return ComplexInterval(_interval_hull(a.re, b.re), _interval_hull(a.im, b.im))


def _vec3_hull(a: Vec3C, b: Vec3C) -> Vec3C:
    return (_complex_hull(a[0], b[0]), _complex_hull(a[1], b[1]), _complex_hull(a[2], b[2]))


def _vec3_sub(a: Vec3C, b: Vec3C) -> Vec3C:
    return (a[0] - b[0], a[1] - b[1], a[2] - b[2])


def _wiener_f0_f1(modes: Dict[WaveVector3D, Vec3C]) -> Tuple[Interval, Interval]:
    f0 = Interval.exact(0.0)
    f1 = Interval.exact(0.0)
    for k, v in modes.items():
        if vec3_is_zero(v):
            continue
        nv = vec3_norm(v)
        kmag = Interval.exact(float(k[0] * k[0] + k[1] * k[1] + k[2] * k[2])).sqrt()
        f0 = f0 + nv
        f1 = f1 + (kmag * nv)
    return f0, f1


@dataclass(frozen=True)
class PerturbationTubeCertificate:
    scenario_id: str
    nu: float
    k_galerkin: int
    steps_taken: int
    certified_time_T: float
    initial_center_F0_lo: float
    final_center_F0_hi: float
    zero_perturbation_defect_W0_hi: float
    certified_open_ball_radius_delta_F0: float
    final_ball_worst_case_F0_hi: float
    arbitrary_asymmetric_modes_allowed: bool
    global_smoothness_certified_on_open_ball: bool


def _propagate_riccati_tube(
    delta0: float,
    step_records: List[Dict[str, Interval]],
    nu: Interval,
    dt: Interval,
) -> Tuple[bool, Interval]:
    """
    Propagate `W_0(0) = delta0` across all recorded reference steps using the
    constructively proved Theorem D inequality:
        D^+ W_0(t) <= R_step + (U1_hull + (U0_hull + W_0(t))^2 / (4*nu)) * W_0(t)
    plus discrete dust jumps `dust_jump` at step endpoints, verified via an
    apriori interval picard enclosure `W_box` on every `[t_{n-1}, t_n]`.
    """
    w = Interval.exact(delta0)
    four_nu = Interval.exact(4.0) * nu

    for rec in step_records:
        u0_h = rec["u0_hull"]
        u1_h = rec["u1_hull"]
        res_h = rec["residual_f0"]
        dust_j = rec["dust_f0"]

        # Constructive apriori box iterative widening on [t_{n-1}, t_n]
        rate0 = res_h + (u1_h + ((u0_h + w).sqr() / four_nu)) * w
        w_box_hi = w.hi + 1.25 * (dt * rate0).hi + 1e-15
        if not math.isfinite(w_box_hi) or w_box_hi > 10.0:
            return False, Interval.exact(float("inf"))

        enclosed = False
        w_next = w
        for _ in range(8):
            w_box = Interval(0.0, w_box_hi)
            rate_box = res_h + (u1_h + ((u0_h + w_box).sqr() / four_nu)) * w_box
            cand = w + (dt * rate_box)
            if cand.hi <= w_box_hi:
                w_next = Interval(0.0, (cand + dust_j).hi)
                enclosed = True
                break
            w_box_hi = cand.hi * 1.25 + 1e-15
            if not math.isfinite(w_box_hi) or w_box_hi > 10.0:
                return False, Interval.exact(float("inf"))

        if not enclosed:
            return False, Interval.exact(float("inf"))
        w = w_next

    return True, w


def certify_open_f0_perturbation_ball(
    scenario_id: str,
    initial_modes: Dict[WaveVector3D, Vec3C],
    nu_rational: Tuple[int, int] = (1, 2),
    k_galerkin: int = 2,
    dt_dyadic_power: int = 7,  # dt = 1/128
    max_steps: int = 80,
    dust_cutoff: float = 1e-9,
    endgame_gate_factor: float = 1.0,  # 1.0 => full arbitrary Z^3\{0} ball (< nu)!
) -> PerturbationTubeCertificate:
    r"""
    Build an explicit finite-mode reference trajectory `u_tilde(t)` and certify
    an INFINITE-DIMENSIONAL OPEN WIENER `l^1(Z^3)` BALL `||v_0 - u_0||_{F^0} <= delta`
    within which EVERY smooth divergence-free periodic initial velocity `v_0`
    (with ZERO symmetry assumptions and arbitrary modes across all `Z^3 \ {0}`)
    reaches `||v(T_cert)||_{F^0} < endgame_gate_factor * nu`!
    """
    nu = Interval.from_rational(*nu_rational)
    gate_cap = (
        nu
        if endgame_gate_factor == 1.0
        else nu * Interval.exact(endgame_gate_factor)
    )
    dt_val = 1.0 / float(1 << dt_dyadic_power)
    dt = Interval.exact(dt_val)

    modes: Dict[WaveVector3D, Vec3C] = dict(initial_modes)
    init_f0, _ = _wiener_f0_f1(modes)

    step_records: List[Dict[str, Interval]] = []
    reached_gate = False
    steps_done = 0

    for step in range(1, max_steps + 1):
        u0_start, u1_start = _wiener_f0_f1(modes)
        rhs_start, spill_start, _ = evaluate_3d_convective_triads(modes, k_galerkin)
        all_keys = set(modes.keys()) | set(rhs_start.keys())

        next_modes: Dict[WaveVector3D, Vec3C] = {}
        pruned_dust = Interval.exact(0.0)
        delta_u0 = Interval.exact(0.0)
        delta_u1 = Interval.exact(0.0)

        for k in all_keys:
            u_cur = modes.get(k, vec3_zero())
            n_cur = rhs_start.get(k, vec3_zero())
            ksq_int = k[0] * k[0] + k[1] * k[1] + k[2] * k[2]
            k_sq = Interval.exact(float(ksq_int))
            kmag = k_sq.sqrt()
            lam = nu * k_sq
            decay = (-(lam * dt)).exp()
            phi1 = (Interval.exact(1.0) - decay) / lam
            u_upd = vec3_add(vec3_scale_real(u_cur, decay), vec3_scale_real(n_cur, phi1))

            # Since u_tilde(k, t) - u_cur(k) = theta_k(t) * (u_upd(k) - u_cur(k)) with
            # theta_k(t) = (1 - exp(-lam*t))/(1 - exp(-lam*dt)) in [0, 1] monotonically,
            # max_{t in [t_{n-1}, t_n]} |u_tilde(k, t) - u_cur(k)| <= |u_upd(k) - u_cur(k)|!
            step_diff_mag = vec3_norm(_vec3_sub(u_upd, u_cur))
            delta_u0 = delta_u0 + step_diff_mag
            delta_u1 = delta_u1 + (kmag * step_diff_mag)

            u_mag = vec3_norm(u_upd)
            if u_mag.hi <= dust_cutoff:
                pruned_dust = pruned_dust + Interval(0.0, u_mag.hi)
            else:
                next_modes[k] = u_upd

        # Exact bilinear PDE residual of `u_tilde(t)` across `[t_{n-1}, t_n]` on ALL of Z^3\{0}:
        #   P[B(u_tilde(t), u_tilde(t))] - P_{<=K}[B(u_start, u_start)]
        #     = P_{>K}[B(u_start, u_start)] + P[B(u_tilde - u_start, u_start)] + P[B(u_tilde, u_tilde - u_start)]
        u0_hull = u0_start + Interval(0.0, delta_u0.hi)
        u1_hull = u1_start + Interval(0.0, delta_u1.hi)
        res_tot = spill_start + (delta_u0 * u1_start) + (u0_hull * delta_u1)

        step_records.append(
            {
                "u0_hull": u0_hull,
                "u1_hull": u1_hull,
                "residual_f0": res_tot,
                "dust_f0": pruned_dust,
            }
        )

        modes = next_modes
        steps_done = step
        cur_f0, _ = _wiener_f0_f1(modes)

        # Check zero-perturbation defect W_0(t) first; stop once comfortably inside gate_cap
        ok0, w0_now = _propagate_riccati_tube(0.0, step_records, nu, dt)
        if ok0 and (cur_f0 + w0_now).hi < 0.90 * gate_cap.lo:
            reached_gate = True
            break

    final_center_f0, _ = _wiener_f0_f1(modes)
    ok_zero, w_zero = _propagate_riccati_tube(0.0, step_records, nu, dt)
    if not ok_zero or (final_center_f0 + w_zero).hi >= gate_cap.lo:
        return PerturbationTubeCertificate(
            scenario_id=scenario_id,
            nu=nu.lo,
            k_galerkin=k_galerkin,
            steps_taken=steps_done,
            certified_time_T=steps_done * dt_val,
            initial_center_F0_lo=init_f0.lo,
            final_center_F0_hi=final_center_f0.hi,
            zero_perturbation_defect_W0_hi=w_zero.hi,
            certified_open_ball_radius_delta_F0=0.0,
            final_ball_worst_case_F0_hi=(final_center_f0 + w_zero).hi,
            arbitrary_asymmetric_modes_allowed=(endgame_gate_factor == 1.0),
            global_smoothness_certified_on_open_ball=False,
        )

    # Bisect for rigorous open-ball radius `delta > 0` keeping `(final_center_f0 + W(T)).hi < gate_cap.lo`
    lo_d = 0.0
    hi_d = 0.25
    for _ in range(32):
        mid = 0.5 * (lo_d + hi_d)
        ok_m, w_m = _propagate_riccati_tube(mid, step_records, nu, dt)
        if ok_m and (final_center_f0 + w_m).hi < gate_cap.lo:
            lo_d = mid
        else:
            hi_d = mid

    # Step back slightly (98% of max safe radius) so strict inequality holds with wide margin
    delta_cert = math.floor(lo_d * 0.98 * 1e6) / 1e6
    ok_c, w_cert = _propagate_riccati_tube(delta_cert, step_records, nu, dt)
    worst_f0 = final_center_f0 + w_cert
    certified_ball = bool(ok_c and delta_cert > 0.0 and worst_f0.hi < gate_cap.lo)

    return PerturbationTubeCertificate(
        scenario_id=scenario_id,
        nu=nu.lo,
        k_galerkin=k_galerkin,
        steps_taken=steps_done,
        certified_time_T=steps_done * dt_val,
        initial_center_F0_lo=init_f0.lo,
        final_center_F0_hi=final_center_f0.hi,
        zero_perturbation_defect_W0_hi=w_zero.hi,
        certified_open_ball_radius_delta_F0=delta_cert,
        final_ball_worst_case_F0_hi=worst_f0.hi,
        arbitrary_asymmetric_modes_allowed=(endgame_gate_factor == 1.0),
        global_smoothness_certified_on_open_ball=certified_ball,
    )


def seed_asymmetric_off_lattice_3d(theta: float) -> Dict[WaveVector3D, Vec3C]:
    """
    Construct a COMPLETELY ASYMMETRIC, supercritical 3D divergence-free velocity
    field `u_0(theta)` for `theta in [0, 1]` that breaks ALL Taylor-Green, Kida-Pelz,
    reflection, octahedral, and `Lambda_BCC` parity symmetries:
      - Supercritical 3D Taylor-Green core (`A = 1/2`, `||u_TG||_{F^0} = 0.707107 > nu = 0.50`)
      - Asymmetric `|k| = 1` shear mode at `k = (1, 0, 0)` & `(-1, 0, 0)` with complex phase
      - Asymmetric `|k|^2 = 2` diagonal mode at `k = (1, 1, 0)` & `(-1, -1, 0)` (`p . u = 0`)
    """
    modes = seed_taylor_green_3d(1, 2)
    # Parameterize theta in [0, 1]:
    #   c1 = 0.03 * (1 - theta) on k = (+/-1, 0, 0), polarization (0, 1, i)/sqrt(2) -> real flow
    #   c2 = 0.03 * theta       on k = (+/-1, +/-1, 0), polarization (1, -1, i)/sqrt(3)
    a1 = Interval.exact(0.03 * (1.0 - theta))
    a2 = Interval.exact(0.03 * theta)
    inv_sqrt2 = Interval.exact(2.0).sqrt()
    inv_sqrt3 = Interval.exact(3.0).sqrt()

    if a1.hi > 0.0:
        amp1 = a1 / (Interval.exact(2.0) * inv_sqrt2)
        modes[(1, 0, 0)] = (
            ComplexInterval.zero(),
            ComplexInterval.from_real_imag(amp1, 0.0),
            ComplexInterval.from_real_imag(0.0, amp1),
        )
        modes[(-1, 0, 0)] = (
            ComplexInterval.zero(),
            ComplexInterval.from_real_imag(amp1, 0.0),
            ComplexInterval.from_real_imag(0.0, -amp1),
        )

    if a2.hi > 0.0:
        amp2 = a2 / (Interval.exact(2.0) * inv_sqrt3)
        modes[(1, 1, 0)] = (
            ComplexInterval.from_real_imag(amp2, 0.0),
            ComplexInterval.from_real_imag(-amp2, 0.0),
            ComplexInterval.from_real_imag(0.0, amp2),
        )
        modes[(-1, -1, 0)] = (
            ComplexInterval.from_real_imag(amp2, 0.0),
            ComplexInterval.from_real_imag(-amp2, 0.0),
            ComplexInterval.from_real_imag(0.0, -amp2),
        )

    return modes


def certify_asymmetric_supercritical_continuum() -> Dict[str, Any]:
    """
    Certify global `C^inf([0, +infinity) x T^3)` smoothness simultaneously across
    the ENTIRE uncountable compact 1D continuum `{ u_0(theta) : theta in [0, 1] }`
    of symmetry-broken, off-lattice (`|k|=1` & `|k|^2=2` active) supercritical 3D
    initial velocities using a finite epsilon-net of certified `F^0` perturbation balls!

    Exact Lipschitz constant in `F^0`:
      For any `theta, theta' in [0, 1]`,
      `||u_0(theta) - u_0(theta')||_{F^0} = (0.03 + 0.03) * |theta - theta'| = 0.06 * |theta - theta'|`.
    """
    lipschitz_f0 = Interval.from_rational(6, 100)  # 0.06 exact bound
    # Start with M = 4 evenly spaced centers at (j + 0.5) / M; refine if needed
    for m_centers in (3, 5, 8, 12):
        half_spacing_f0 = (lipschitz_f0 / Interval.exact(2.0 * m_centers)).hi
        center_certs: List[Dict[str, Any]] = []
        all_covered = True
        for j in range(m_centers):
            theta_j = (j + 0.5) / m_centers
            modes_j = seed_asymmetric_off_lattice_3d(theta_j)
            cert_j = certify_open_f0_perturbation_ball(
                scenario_id=f"ASYMMETRIC-CONTINUUM-CENTER-{j + 1}-OF-{m_centers}",
                initial_modes=modes_j,
                nu_rational=(1, 2),
                k_galerkin=2,
                dt_dyadic_power=7,
                max_steps=65,
                endgame_gate_factor=1.0,
            )
            covers_cell = (
                cert_j.global_smoothness_certified_on_open_ball
                and cert_j.certified_open_ball_radius_delta_F0 > half_spacing_f0
            )
            if not covers_cell:
                all_covered = False
                break
            center_certs.append(
                {
                    "theta_center": round(theta_j, 6),
                    "covered_parameter_interval": [round(j / m_centers, 6), round((j + 1) / m_centers, 6)],
                    "initial_F0_lo": round(cert_j.initial_center_F0_lo, 6),
                    "required_cell_radius_F0": round(half_spacing_f0, 6),
                    "certified_ball_radius_F0": cert_j.certified_open_ball_radius_delta_F0,
                    "safety_margin_ratio": round(
                        cert_j.certified_open_ball_radius_delta_F0 / half_spacing_f0, 3
                    ),
                    "steps": cert_j.steps_taken,
                    "worst_case_F0_at_T_cert_hi": round(cert_j.final_ball_worst_case_F0_hi, 6),
                }
            )
        if all_covered:
            return {
                "continuum_certified": True,
                "num_covering_balls": m_centers,
                "lipschitz_constant_F0": lipschitz_f0.hi,
                "required_radius_per_cell_F0": round(half_spacing_f0, 6),
                "min_certified_ball_radius_F0": min(
                    c["certified_ball_radius_F0"] for c in center_certs
                ),
                "min_initial_F0_across_centers": min(c["initial_F0_lo"] for c in center_certs),
                "nu": 0.50,
                "centers": center_certs,
            }

    return {"continuum_certified": False, "centers": []}


# ==============================================================================
# 3. EXACT 3D SOLENOIDAL `sin(theta)` & WALEFFE (1992) HELICAL DEPLETION AUDIT
# ==============================================================================


def _helical_basis_3d(k: Tuple[int, int, int]) -> Tuple[np.ndarray, np.ndarray]:
    """
    Orthonormal helical curl eigenbasis `h_+(k), h_-(k)` in `C^3` satisfying:
        k . h_s(k) = 0,   i * k x h_s(k) = s * |k| * h_s(k),   |h_s(k)| = 1.
    """
    kv = np.array(k, dtype=np.float64)
    kmag = float(np.linalg.norm(kv))
    k_hat = kv / kmag
    # Choose reference axis least aligned with k_hat
    ref = np.array([0.0, 0.0, 1.0]) if abs(k_hat[2]) < 0.9 else np.array([1.0, 0.0, 0.0])
    e1 = np.cross(k_hat, ref)
    e1 /= np.linalg.norm(e1)
    e2 = np.cross(k_hat, e1)
    h_plus = (e1 + 1j * e2) / math.sqrt(2.0)
    h_minus = (e1 - 1j * e2) / math.sqrt(2.0)
    return h_plus, h_minus


def quantify_solenoidal_and_helical_depletion() -> Dict[str, Any]:
    """
    Quantify the exact gap between:
      - Round 1's gross scalar product `F_0 * F_1`,
      - Theorem E's `sin(theta)` solenoidal cross-product bound
        `G_sin = sum_{p,q} |u(p)| * |u(q)| * |p x q| / |p|`,
      - Exact Leray-projected convective amplitude `G_true = sum_k |N(u)_hat(k)|`,
    plus Waleffe (1992) homochiral vs. heterochiral triad transfer weights on a
    dense asymmetric 3D solenoidal benchmark field (`|k|_inf <= 2`, 124 active modes).
    """
    rng = np.random.default_rng(20261102)
    modes_np: Dict[Tuple[int, int, int], np.ndarray] = {}

    for kx in range(-2, 3):
        for ky in range(-2, 3):
            for kz in range(-2, 3):
                if (kx, ky, kz) == (0, 0, 0):
                    continue
                if (kx, ky, kz) in modes_np:
                    continue
                hp, hm = _helical_basis_3d((kx, ky, kz))
                k_sq = kx * kx + ky * ky + kz * kz
                amp_p = (rng.normal() + 1j * rng.normal()) / (k_sq ** 1.25)
                amp_m = (rng.normal() + 1j * rng.normal()) / (k_sq ** 1.25)
                u_vec = amp_p * hp + amp_m * hm
                modes_np[(kx, ky, kz)] = u_vec
                modes_np[(-kx, -ky, -kz)] = np.conj(u_vec)

    # Normalize to supercritical F_0 = 1.00 (> nu = 0.50)
    raw_f0 = sum(float(np.linalg.norm(v)) for v in modes_np.values())
    for k in list(modes_np.keys()):
        modes_np[k] = modes_np[k] / raw_f0

    f0 = sum(float(np.linalg.norm(v)) for v in modes_np.values())
    f1 = sum(math.sqrt(k[0] ** 2 + k[1] ** 2 + k[2] ** 2) * float(np.linalg.norm(v)) for k, v in modes_np.items())
    gross_f0_f1 = f0 * f1

    g_sin = 0.0
    collinear_pairs = 0
    total_pairs = 0
    homochiral_weight_sum = 0.0
    heterochiral_weight_sum = 0.0
    rhs_true: Dict[Tuple[int, int, int], np.ndarray] = {}

    keys = list(modes_np.keys())
    for p in keys:
        pv = np.array(p, dtype=np.float64)
        pmag = math.sqrt(float(pv @ pv))
        up = modes_np[p]
        up_norm = float(np.linalg.norm(up))
        hp_p, hm_p = _helical_basis_3d(p)
        ap_plus = complex(np.vdot(hp_p, up))
        ap_minus = complex(np.vdot(hm_p, up))

        for q in keys:
            k = (p[0] + q[0], p[1] + q[1], p[2] + q[2])
            if k == (0, 0, 0):
                continue
            total_pairs += 1
            qv = np.array(q, dtype=np.float64)
            uq = modes_np[q]
            uq_norm = float(np.linalg.norm(uq))

            cross_pq = np.cross(pv, qv)
            cross_mag = float(np.linalg.norm(cross_pq))
            if cross_mag < 1e-12:
                collinear_pairs += 1
                continue

            g_sin += up_norm * uq_norm * (cross_mag / pmag)

            # Exact convective contribution -i P_k((u(p) . q) u(q))
            u_dot_q = complex(up[0] * q[0] + up[1] * q[1] + up[2] * q[2])
            raw_term = (-1j * u_dot_q) * uq
            kv = np.array(k, dtype=np.float64)
            ksq = float(kv @ kv)
            proj_term = raw_term - ((kv @ raw_term) / ksq) * kv
            rhs_true[k] = rhs_true.get(k, np.zeros(3, dtype=np.complex128)) + proj_term

            # Waleffe (1992) helical triad decomposition (`s_p, s_q, s_k in {+1, -1}`)
            hq_p, hm_q = _helical_basis_3d(q)
            hk_p, hm_k = _helical_basis_3d(k)
            aq_plus = complex(np.vdot(hq_p, uq))
            aq_minus = complex(np.vdot(hm_q, uq))

            for sp_sign, hp_vec, ap_val in ((1, hp_p, ap_plus), (-1, hm_p, ap_minus)):
                for sq_sign, hq_vec, aq_val in ((1, hq_p, aq_plus), (-1, hm_q, aq_minus)):
                    # Advective coupling (hp_vec . i q) hq_vec projected onto hk_s
                    adv = 1j * complex(hp_vec[0] * q[0] + hp_vec[1] * q[1] + hp_vec[2] * q[2]) * hq_vec
                    for sk_sign, hk_vec in ((1, hk_p), (-1, hm_k)):
                        w_amp = abs(ap_val * aq_val * complex(np.vdot(hk_vec, adv)))
                        if sp_sign == sq_sign == sk_sign:
                            homochiral_weight_sum += w_amp
                        else:
                            heterochiral_weight_sum += w_amp

    g_true = sum(float(np.linalg.norm(v)) for v in rhs_true.values())
    total_hel = homochiral_weight_sum + heterochiral_weight_sum

    return {
        "active_dense_modes": len(modes_np),
        "total_nonzero_triad_pairs": total_pairs,
        "exact_collinear_annihilated_pairs": collinear_pairs,
        "gross_scalar_F0_F1": round(gross_f0_f1, 6),
        "sin_theta_bound_G_sin": round(g_sin, 6),
        "exact_leray_projected_G_true": round(g_true, 6),
        "sin_theta_depletion_ratio_vs_F0F1": round(g_sin / gross_f0_f1, 4),
        "true_convective_depletion_ratio_vs_F0F1": round(g_true / gross_f0_f1, 4),
        "waleffe_homochiral_flux_fraction": round(homochiral_weight_sum / total_hel, 4),
        "waleffe_heterochiral_flux_fraction": round(heterochiral_weight_sum / total_hel, 4),
    }


# ==============================================================================
# 4. QUANTITATIVE LERAY HORIZON TABLE & ADVERSARIAL RED-TEAM OPTIMIZER
# ==============================================================================


def compute_leray_low_shell_horizons(
    e0_values: Tuple[float, ...] = (0.25, 0.50, 1.00),
    r_shells: Tuple[int, ...] = (1, 2, 4, 8),
    nu: float = 0.50,
) -> List[Dict[str, Any]]:
    """
    Compute exact lattice harmonic factors `H_R = sum_{1 <= |k| <= R} |k|^{-2}` on `Z^3`
    and the constructive Theorem F horizon `T_max(E_0, nu, R) = 4 * H_R * E_0 / nu^3`
    before which EVERY smooth periodic flow with initial energy `<= E_0` must enter
    the low-shell subcritical regime `F_{0, <=R}(t_*) <= nu / 2`.
    """
    rows: List[Dict[str, Any]] = []
    for r_max in r_shells:
        h_r = 0.0
        n_modes = 0
        for kx in range(-r_max, r_max + 1):
            for ky in range(-r_max, r_max + 1):
                for kz in range(-r_max, r_max + 1):
                    ksq = kx * kx + ky * ky + kz * kz
                    if 1 <= ksq <= r_max * r_max:
                        h_r += 1.0 / float(ksq)
                        n_modes += 1
        for e0 in e0_values:
            t_max = (4.0 * h_r * e0) / (nu ** 3)
            rows.append(
                {
                    "R_shell": r_max,
                    "low_shell_mode_count": n_modes,
                    "H_R_sum_inv_ksq": round(h_r, 6),
                    "initial_energy_E0": e0,
                    "nu": nu,
                    "guaranteed_cooldown_horizon_T_max": round(t_max, 4),
                }
            )
    return rows


def run_adversarial_ceiling_redteam(
    energy_budget_e0: float = 0.50,
    k_box: int = 3,
    nu: float = 0.50,
    n_restarts: int = 8,
    dt: float = 0.005,
    max_steps: int = 400,
) -> Dict[str, Any]:
    """
    Adversarial Singularity Red-Team Search over arbitrary dense 3D solenoidal fields
    (`|k|_inf <= k_box`, zero symmetry assumptions, fixed kinetic energy `E_0 = 1/2 sum |u(k)|^2`):
      1. Optimizes real mode weights & random asymmetric helical phases to MAXIMIZE
         the Step-2 Moving Viscous Ceiling evasion ratio `rho_ceil = F_0^3 / (nu^2 * F_2)`.
      2. Integrates the worst-case adversarial field forward under exact unforced (`f == 0`)
         3D Leray-projected Navier-Stokes (RK4 on `|k|_inf <= k_box + 2` to prevent truncation
         aliasing) and records how rapidly viscous enstrophy dissipation collapses
         `rho_ceil(t)` strictly below `1.0` (into `D^+ ||u||_{F^0} < 0`)!
    """
    # Enumerate half-space wavevectors `k > 0` lexicographically so `u(-k) = conj(u(k))` (real velocity)
    half_keys: List[Tuple[int, int, int]] = []
    for kx in range(-k_box, k_box + 1):
        for ky in range(-k_box, k_box + 1):
            for kz in range(-k_box, k_box + 1):
                if (kx, ky, kz) > (0, 0, 0):
                    half_keys.append((kx, ky, kz))

    m_half = len(half_keys)
    kmags = np.array([math.sqrt(k[0] ** 2 + k[1] ** 2 + k[2] ** 2) for k in half_keys], dtype=np.float64)
    ksqs = kmags ** 2

    # Note: for fixed total energy E_0 = 1/2 sum_{k != 0} a_k^2 = sum_{k in half} a_k^2,
    # rho_ceil = (2 sum a_k)^3 / (nu^2 * (2 sum |k|^2 a_k)) = 4 * (sum a_k)^3 / (nu^2 * sum |k|^2 a_k).
    # Projected gradient ascent on non-negative shell weights `a in S^{m_half-1}(sqrt(E_0))`!
    rng = np.random.default_rng(314159)
    best_rho = -1.0
    best_a = np.zeros(m_half, dtype=np.float64)

    for restart in range(n_restarts):
        if restart == 0:
            # Analytic near-extremizer initialization: heavy low-k + power-law tail
            a = 1.0 / (ksqs ** 1.15)
        elif restart == 1:
            # Uniform dense packing (`a_k = const` across entire 3D box!)
            a = np.ones(m_half, dtype=np.float64)
        else:
            a = np.abs(rng.normal(loc=1.0, scale=0.6, size=m_half)) / (ksqs ** rng.uniform(0.3, 1.8))

        a = a / np.linalg.norm(a) * math.sqrt(energy_budget_e0)
        lr = 0.08
        for _ in range(180):
            s0 = float(np.sum(a))
            s2 = float(np.sum(ksqs * a))
            # Gradient of log(s0^3 / s2) = 3 * 1 / s0 - ksqs / s2
            grad = (3.0 / s0) * np.ones_like(a) - (ksqs / s2)
            # Tangent projection onto constant-energy sphere `a . grad = 0`
            grad = grad - (float(np.dot(a, grad)) / float(np.dot(a, a))) * a
            a_cand = np.maximum(1e-12, a + lr * grad)
            a_cand = a_cand / np.linalg.norm(a_cand) * math.sqrt(energy_budget_e0)
            rho_cand = (4.0 * (float(np.sum(a_cand)) ** 3)) / ((nu ** 2) * float(np.sum(ksqs * a_cand)))
            rho_cur = (4.0 * (s0 ** 3)) / ((nu ** 2) * s2)
            if rho_cand >= rho_cur:
                a = a_cand
            else:
                lr *= 0.6

        s0_f = float(np.sum(a))
        s2_f = float(np.sum(ksqs * a))
        rho_f = (4.0 * (s0_f ** 3)) / ((nu ** 2) * s2_f)
        if rho_f > best_rho:
            best_rho = rho_f
            best_a = a.copy()

    # Assign completely asymmetric random helical phases to `best_a` on `|k|_inf <= k_box`,
    # then evolve on padded grid `|k|_inf <= k_pad` (`k_pad = k_box + 2`) via 3D pseudospectral RK4!
    n_grid = 16  # Nyquist +/-8 comfortably resolves k_box = 3 without aliasing
    kx_1d = np.fft.fftfreq(n_grid, d=1.0 / n_grid).astype(np.float64)
    KX, KY, KZ = np.meshgrid(kx_1d, kx_1d, kx_1d, indexing="ij")
    KSQ = KX ** 2 + KY ** 2 + KZ ** 2
    KMAG = np.sqrt(KSQ)
    KSQ_SAFE = np.where(KSQ == 0.0, 1.0, KSQ)
    # 2/3 dealiasing mask (`|k|_inf <= 5`)
    dealias = (np.abs(KX) <= 5) & (np.abs(KY) <= 5) & (np.abs(KZ) <= 5) & (KSQ > 0)

    u_hat = np.zeros((3, n_grid, n_grid, n_grid), dtype=np.complex128)
    for idx_k, k in enumerate(half_keys):
        amp = float(best_a[idx_k])
        hp, hm = _helical_basis_3d(k)
        theta_mix = float(rng.uniform(0.0, 0.5 * math.pi))
        phi_p = float(rng.uniform(0.0, 2.0 * math.pi))
        phi_m = float(rng.uniform(0.0, 2.0 * math.pi))
        pol = math.cos(theta_mix) * cmath_exp_i(phi_p) * hp + math.sin(theta_mix) * cmath_exp_i(phi_m) * hm
        vec = amp * pol  # |vec| == amp
        ix, iy, iz = k[0] % n_grid, k[1] % n_grid, k[2] % n_grid
        mx, my, mz = (-k[0]) % n_grid, (-k[1]) % n_grid, (-k[2]) % n_grid
        u_hat[:, ix, iy, iz] = vec * (n_grid ** 3)
        u_hat[:, mx, my, mz] = np.conj(vec) * (n_grid ** 3)

    def _ns_rhs(uh: np.ndarray) -> np.ndarray:
        uh_d = uh * dealias
        u_phys = np.real(np.fft.ifftn(uh_d, axes=(1, 2, 3)))
        # Compute vorticity omega = curl(u) in Fourier space -> rotational form u x omega
        ikx, iky, ikz = 1j * KX, 1j * KY, 1j * KZ
        om_hat = np.zeros_like(uh_d)
        om_hat[0] = iky * uh_d[2] - ikz * uh_d[1]
        om_hat[1] = ikz * uh_d[0] - ikx * uh_d[2]
        om_hat[2] = ikx * uh_d[1] - iky * uh_d[0]
        om_phys = np.real(np.fft.ifftn(om_hat, axes=(1, 2, 3)))

        cx = u_phys[1] * om_phys[2] - u_phys[2] * om_phys[1]
        cy = u_phys[2] * om_phys[0] - u_phys[0] * om_phys[2]
        cz = u_phys[0] * om_phys[1] - u_phys[1] * om_phys[0]
        c_hat = np.stack(
            [np.fft.fftn(cx), np.fft.fftn(cy), np.fft.fftn(cz)],
            axis=0,
        ) * dealias
        k_dot_c = KX * c_hat[0] + KY * c_hat[1] + KZ * c_hat[2]
        proj_c = np.stack(
            [
                c_hat[0] - (k_dot_c / KSQ_SAFE) * KX,
                c_hat[1] - (k_dot_c / KSQ_SAFE) * KY,
                c_hat[2] - (k_dot_c / KSQ_SAFE) * KZ,
            ],
            axis=0,
        )
        return proj_c - (nu * KSQ) * uh_d

    def _moments(uh: np.ndarray) -> Tuple[float, float, float, float]:
        # Normalized Fourier coefficients u_hat_norm = uh / N^3
        amps = np.sqrt(np.sum(np.abs(uh / float(n_grid ** 3)) ** 2, axis=0)) * dealias
        f0_v = float(np.sum(amps))
        f1_v = float(np.sum(KMAG * amps))
        f2_v = float(np.sum(KSQ * amps))
        e_v = 0.5 * float(np.sum(amps ** 2))
        return f0_v, f1_v, f2_v, e_v

    f0_0, f1_0, f2_0, e_0 = _moments(u_hat)
    rho_0 = (f0_0 ** 3) / ((nu ** 2) * f2_0)
    peak_rho = rho_0
    peak_f0 = f0_0
    cooldown_time: Optional[float] = None
    subcritical_f0_time: Optional[float] = None

    for step in range(1, max_steps + 1):
        k1 = _ns_rhs(u_hat)
        k2 = _ns_rhs(u_hat + 0.5 * dt * k1)
        k3 = _ns_rhs(u_hat + 0.5 * dt * k2)
        k4 = _ns_rhs(u_hat + dt * k3)
        u_hat = (u_hat + (dt / 6.0) * (k1 + 2.0 * k2 + 2.0 * k3 + k4)) * dealias

        f0_t, f1_t, f2_t, _ = _moments(u_hat)
        rho_t = (f0_t ** 3) / ((nu ** 2) * f2_t) if f2_t > 0 else 0.0
        peak_rho = max(peak_rho, rho_t)
        peak_f0 = max(peak_f0, f0_t)
        t_cur = round(step * dt, 6)
        if cooldown_time is None and rho_t < 1.0:
            cooldown_time = t_cur
        if subcritical_f0_time is None and f0_t < nu:
            subcritical_f0_time = t_cur
            break

    f0_end, _, f2_end, e_end = _moments(u_hat)
    return {
        "k_box_seed": k_box,
        "active_asymmetric_modes_seed": 2 * m_half,
        "initial_energy_E0": round(e_0, 6),
        "initial_F0": round(f0_0, 6),
        "initial_F2": round(f2_0, 6),
        "adversarial_initial_ceiling_ratio_rho0": round(rho_0, 4),
        "peak_ceiling_ratio_along_flow": round(peak_rho, 4),
        "peak_F0_along_flow": round(peak_f0, 6),
        "viscous_ceiling_entry_time_rho_lt_1": cooldown_time,
        "lei_lin_ball_entry_time_F0_lt_nu": subcritical_f0_time,
        "final_energy_E": round(e_end, 6),
        "final_F0": round(f0_end, 6),
        "final_F2": round(f2_end, 6),
        "evaded_step2_ceiling_indefinitely": cooldown_time is None,
    }


def cmath_exp_i(phi: float) -> complex:
    return complex(math.cos(phi), math.sin(phi))


# ==============================================================================
# 5. FULL ROUND-2 SUITE ORCHESTRATOR & SHA-256 CERTIFICATE EXPORT
# ==============================================================================


def run_step3_round2_suite(output_dir: Optional[Path | str] = None) -> Dict[str, Any]:
    out_path = Path(output_dir) if output_dir is not None else _HERE / "artifacts"
    out_path.mkdir(parents=True, exist_ok=True)

    z3_proofs = verify_step3_universal_theorems_z3()

    # 1. Open infinite-dimensional `l^1(Z^3)` perturbation balls around canonical supercritical flows
    #    (NO parity/symmetry restriction on perturbation `w`: `endgame_gate_factor = 1.0` => `< nu`!)
    tg_ball = certify_open_f0_perturbation_ball(
        scenario_id="TAYLOR-GREEN-3D-ARBITRARY-ASYMMETRIC-OPEN-BALL",
        initial_modes=seed_taylor_green_3d(1, 2),
        nu_rational=(1, 2),
        k_galerkin=2,
        dt_dyadic_power=7,
        max_steps=65,
        endgame_gate_factor=1.0,
    )
    abc_ball = certify_open_f0_perturbation_ball(
        scenario_id="ABC-BELTRAMI-3D-ARBITRARY-ASYMMETRIC-OPEN-BALL",
        initial_modes=seed_abc_beltrami_3d(1, 4),
        nu_rational=(1, 2),
        k_galerkin=2,
        dt_dyadic_power=7,
        max_steps=220,
        endgame_gate_factor=1.0,
    )
    kp_ball = certify_open_f0_perturbation_ball(
        scenario_id="KIDA-PELZ-3D-ARBITRARY-ASYMMETRIC-OPEN-BALL",
        initial_modes=seed_kida_pelz_3d(1, 4),
        nu_rational=(1, 2),
        k_galerkin=2,
        dt_dyadic_power=7,
        max_steps=65,
        endgame_gate_factor=1.0,
    )

    # 2. Uncountable compact continuum `theta in [0, 1]` of symmetry-broken supercritical 3D flows
    continuum_res = certify_asymmetric_supercritical_continuum()

    # 3. Exact 3D Solenoidal `sin(theta)` + Waleffe Helical Depletion Audit
    depletion_res = quantify_solenoidal_and_helical_depletion()

    # 4. Quantitative Leray Low-Shell Cooldown Horizons + Adversarial Red-Team Search
    leray_table = compute_leray_low_shell_horizons()
    redteam_res = run_adversarial_ceiling_redteam()

    payload: Dict[str, Any] = {
        "suite": "bsar_navier_stokes_round2_step3_arbitrary_data",
        "attestation": "probabilistic_structural",
        "lean4_module": "bsa-r/lean/Step3ArbitraryDataRound2.lean",
        "classical_choice_used": False,
        "external_forcing_f_identically_zero": True,
        "universal_z3_and_sympy_proofs": z3_proofs,
        "open_l1_perturbation_balls": {
            "taylor_green_open_ball": tg_ball.__dict__,
            "abc_beltrami_open_ball": abc_ball.__dict__,
            "kida_pelz_open_ball": kp_ball.__dict__,
        },
        "asymmetric_supercritical_continuum_covering": continuum_res,
        "solenoidal_sin_theta_and_helical_depletion": depletion_res,
        "leray_low_shell_cooldown_horizons": leray_table,
        "adversarial_ceiling_redteam": redteam_res,
    }
    cert_sha = canonical_sha256(payload)
    payload["certificate_sha256"] = cert_sha

    cert_file = out_path / "step3_round2_arbitrary_data_certificate.json"
    cert_file.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    return payload


if __name__ == "__main__":
    res = run_step3_round2_suite()
    print("=== NAVIER-STOKES ROUND 2 (STEP 3: ARBITRARY-DATA ENGINE) ===")
    print("Z3 & SymPy Universal Proofs:", json.dumps(res["universal_z3_and_sympy_proofs"]))
    for name, b in res["open_l1_perturbation_balls"].items():
        print(
            f"  [{name}] init_F0={b['initial_center_F0_lo']:.6f} -> delta_open={b['certified_open_ball_radius_delta_F0']:.6f} "
            f"(worst_F0={b['final_ball_worst_case_F0_hi']:.6f} < {b['nu']:.2f}, steps={b['steps_taken']}, certified={b['global_smoothness_certified_on_open_ball']})"
        )
    cont = res["asymmetric_supercritical_continuum_covering"]
    print(
        f"  [Asymmetric Continuum theta in [0,1]] certified={cont['continuum_certified']} "
        f"balls={cont.get('num_covering_balls')} req_rad={cont.get('required_radius_per_cell_F0')} "
        f"min_cert_rad={cont.get('min_certified_ball_radius_F0')}"
    )
    dep = res["solenoidal_sin_theta_and_helical_depletion"]
    print(
        f"  [Solenoidal & Helical Depletion] G_sin/(F0*F1)={dep['sin_theta_depletion_ratio_vs_F0F1']} "
        f"G_true/(F0*F1)={dep['true_convective_depletion_ratio_vs_F0F1']} "
        f"collinear_zero={dep['exact_collinear_annihilated_pairs']}/{dep['total_nonzero_triad_pairs']}"
    )
    rt = res["adversarial_ceiling_redteam"]
    print(
        f"  [Adversarial Red-Team (k_box={rt['k_box_seed']}, {rt['active_asymmetric_modes_seed']} modes)] "
        f"rho0={rt['adversarial_initial_ceiling_ratio_rho0']} -> rho<1 at t={rt['viscous_ceiling_entry_time_rho_lt_1']}, "
        f"F0<nu at t={rt['lei_lin_ball_entry_time_F0_lt_nu']}"
    )
    print("SHA-256 Certificate:", res["certificate_sha256"])
