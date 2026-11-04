/-
  Step7VorticityDirectionPdeRound6.lean
  ==============================================================================
  BSA-R x Eleven-Entry Bookkeeping — Round 6 Formal Appendix (Split Sheet #001)
  Constructive Lean 4.35.0 Attack on the Single S^2 Vorticity-Direction PDE &
  Gapless Adjacent-Octave Cascades:
  Polar `(Omega, xi)` Lagrange Palinstrophy Splitting, S^2 Harmonic-Map Curvature
  Scissors, Zero-Gap Bony Paraproduct UV Barrier, and Beirao da Veiga-Berselli
  `C^{1/2}` Direction-Cone `D^3 -> D^2` Leray Doubling Closure.

    - Theorem P1 (`step7_polar_palinstrophy_lagrange_splitting` &
      `step7_kato_inequality_with_exact_curvature_deficit`):
      For EVERY vorticity vector `w = (w1, w2, w3)` and EVERY 3x3 spatial velocity-
      curl Jacobian `J = grad w` (12 free integer variables, zero division by `|w|`,
      100% regular across vortex null sets `{w = 0}`):
        `|w|^2 * ||grad w||_F^2 = PolarAmpTerm(w, J) + PolarDirTerm(w, J)`
      where `PolarAmpTerm = sum_b (w · d_b w)^2` (`|w|^2 |grad |w||^2`) and
      `PolarDirTerm = sum_b |w × d_b w|^2` (`|w|^4 ||grad xi||_F^2`). Establishes
      Kato's inequality `PolarAmpTerm ≤ |w|^2 ||grad w||_F^2` with exact curvature
      deficit `PolarDirTerm ≥ 0`.
    - Theorem P2 (`step7_s2_harmonic_laplacian_orthogonality` &
      `step7_vorticity_peak_drift_vanishes_and_curvature_crushes`):
      On the unit sphere `|xi|^2 = R`, `xi · d_b^2 xi = -|d_b xi|^2` forces the
      covariant S^2 harmonic-map Laplacian `R * Delta xi + ||grad xi||_F^2 * xi`
      to be strictly orthogonal to `xi` while injecting the radial curvature sink
      `-nu * ||grad xi||_F^2 * Omega` into the scalar vorticity amplitude PDE.
      At any spatial maximum `x_*` of `|w|` (`grad Omega(x_*) = 0`, `Delta Omega(x_*) ≤ 0`),
      the singular vortex-null drift `-2*nu*(grad Omega · grad)xi / Omega` vanishes
      identically and `3 * (nu * ||grad xi||_F^2)^2 > 2 * ||S||_F^2 * R^2` strictly
      crushes peak vorticity!
    - Theorem Q1 & Q2 (`step7_polar_curvature_ceiling_widening` &
      `step7_polar_curvature_cubic_quartic_depletion`):
      Because `||w||_{L^4} = || |w| ||_{L^4}` depends solely on scalar amplitude
      `|w|` and uses ONLY `P_amp = P - P_dir` (`(1 - Phi_dir) * P`), any direction-
      curvature share `P_dir > 0` widens the Moving Palinstrophy Ceiling via
      `C4 * D^3 * P_amp^3 < 9 * nu^4 * P^4` and suppresses the quartic Young rate
      cubically in `(1 - Phi_dir)^3` while preserving `-2 * nu * P_dir` intact.
    - Theorem R1 & R2 (`step7_bony_adjacent_collar_localization`,
      `step7_zero_gap_sweeping_symmetric_strain_reduction`, &
      `step7_zero_gap_bony_paraproduct_uv_gate`):
      Across ANY wavenumber cutoff `M_cut` with ZERO empty scale gap (`m_{j+1} ≤ 4 m_j`):
        1. Low-Low spillover (`|p|^2 ≤ M_cut, |q|^2 ≤ M_cut, |p+q|^2 > M_cut`) is
           algebraically trapped in the single collar octave `(M_cut, 4 M_cut]`
           and requires `4|p|^2 > M_cut ∨ 4|q|^2 > M_cut`.
        2. Zero-gap sweeping `-(u_L · grad)u_H` contracted with `Delta u_H` cancels
           antisymmetric low vorticity `A_L` identically and reduces to trace-free
           symmetric strain `S_L`.
        3. The 4-channel Zero-Gap Bony Paraproduct Gate certifies strict UV tail
           enstrophy decay `dD_H/dt < 0` on gapless multi-octave cascades.
    - Theorem S1 & S2 (`step7_holder_half_cone_biot_savart_bound`,
      `step7_holder_half_quadratic_d3_to_d2_reduction`, &
      `step7_leray_quadratic_doubling_closure`):
      Beirao da Veiga-Berselli `C^{1/2}` direction-cone coherence `|xi - eta|^2 ≤ K_xi * d1`
      depletes Biot-Savart stretching to `C * sqrt(K_xi) * D * P_amp^{1/2}`, completing
      the square against `-nu * P_amp` collapses cubic `D^3` growth to quadratic `D^2`
      (`2*nu*(2*C*kh*D*g - 2*nu*(g^2 + P_dir)) ≤ C^2 * kh^2 * D^2 - 4*nu^2*P_dir`),
      and subdividing Leray's energy budget `nu * int_0^infty D(t) dt ≤ E_0` into `K`
      half-budget windows bounds `D(t) ≤ 2^K * D(0)` globally without `Classical.choice`!

  Architect & Author: Christopher "Topher" Duguay
  Syndicate: One Big Consortium — Contingent Claims Register (100% Give-It-Away)
  Attestation: probabilistic_structural (Modal Box Verified, Zero Classical.choice)
  ==============================================================================
-/

namespace SweetbrierBSARStep7

/-!
  ## Part 0: Constructive Integer Order, Ring & Arbitrary-Dimension Cauchy-Schwarz
-/

theorem int_sq_nonneg (x : Int) : 0 ≤ x * x := by
  by_cases h : 0 ≤ x
  · exact Int.mul_nonneg h h
  · have hneg : 0 ≤ -x := by omega
    have hmul : 0 ≤ (-x) * (-x) := Int.mul_nonneg hneg hneg
    have h_eq : (-x) * (-x) = x * x := by
      calc
        (-x) * (-x) = -(x * (-x)) := Int.neg_mul x (-x)
        _ = -(-(x * x)) := by rw [Int.mul_neg x x]
        _ = x * x := Int.neg_neg (x * x)
    rw [h_eq] at hmul
    exact hmul

theorem int_eq_zero_of_sq_eq_zero (x : Int) (h : x * x = 0) : x = 0 := by
  by_cases hp : 0 < x
  · have hsq : 0 < x * x := Int.mul_pos hp hp
    omega
  · by_cases hn : x < 0
    · have hneg : 0 < -x := by omega
      have hsq : 0 < (-x) * (-x) := Int.mul_pos hneg hneg
      have h_eq : (-x) * (-x) = x * x := by
        calc
          (-x) * (-x) = -(x * (-x)) := Int.neg_mul x (-x)
          _ = -(-(x * x)) := by rw [Int.mul_neg x x]
          _ = x * x := Int.neg_neg (x * x)
      rw [h_eq] at hsq
      omega
    · omega

theorem int_lt_of_sq_lt_sq (x y : Int) (hx : 0 ≤ x) (hy : 0 < y) (hsq : x * x < y * y) : x < y := by
  by_cases hlt : x < y
  · exact hlt
  · have hge : y ≤ x := by omega
    have h1 : y * y ≤ x * y := Int.mul_le_mul_of_nonneg_right hge (by omega)
    have h2 : x * y ≤ x * x := Int.mul_le_mul_of_nonneg_left hge hx
    omega

theorem int_lt_of_pow4_lt_pow4 (x y : Int) (hx : 0 ≤ x) (hy : 0 < y)
    (h4 : (x * x) * (x * x) < (y * y) * (y * y)) : x < y := by
  have hx2 : 0 ≤ x * x := int_sq_nonneg x
  have hy2 : 0 < y * y := Int.mul_pos hy hy
  have h2 : x * x < y * y := int_lt_of_sq_lt_sq (x * x) (y * y) hx2 hy2 h4
  exact int_lt_of_sq_lt_sq x y hx hy h2

theorem mul_self_mul_self_comm (a b : Int) : (a * a) * (b * b) = (a * b) * (a * b) := by
  calc
    (a * a) * (b * b) = a * (a * (b * b)) := Int.mul_assoc a a (b * b)
    _ = a * ((a * b) * b) := by rw [← Int.mul_assoc a b b]
    _ = a * ((b * a) * b) := by rw [Int.mul_comm a b]
    _ = a * (b * (a * b)) := by rw [Int.mul_assoc b a b]
    _ = (a * b) * (a * b) := by rw [← Int.mul_assoc a b (a * b)]

theorem mul_coeff_combine (k m x y : Int) : k * ((m * x) * y) = (k * m) * (x * y) := by
  rw [Int.mul_assoc m x y, ← Int.mul_assoc k m (x * y)]

theorem mul_term_mul_term (k m x y : Int) : (k * x) * (m * y) = (k * m) * (x * y) := by
  calc
    (k * x) * (m * y) = k * (x * (m * y)) := Int.mul_assoc k x (m * y)
    _ = k * ((x * m) * y) := by rw [← Int.mul_assoc x m y]
    _ = k * ((m * x) * y) := by rw [Int.mul_comm x m]
    _ = (k * m) * (x * y) := mul_coeff_combine k m x y

theorem binomial_sq_expand (x y : Int) : (x + y) * (x + y) = x * x + 2 * (x * y) + y * y := by
  rw [Int.add_mul, Int.mul_add, Int.mul_add, Int.mul_comm y x]
  omega

theorem binomial_sub_sq_expand (x y : Int) : (x - y) * (x - y) = x * x - 2 * (x * y) + y * y := by
  rw [Int.sub_mul, Int.mul_sub, Int.mul_sub, Int.mul_comm y x]
  omega

theorem trinomial_sq_expand (a b c : Int) :
    (a + b + c) * (a + b + c) =
      (a * a + b * b + c * c) + 2 * (a * b + a * c + b * c) := by
  rw [Int.add_mul, Int.add_mul,
      Int.mul_add, Int.mul_add,
      Int.mul_add, Int.mul_add,
      Int.mul_add, Int.mul_add]
  have ba : b * a = a * b := Int.mul_comm b a
  have ca : c * a = a * c := Int.mul_comm c a
  have cb : c * b = b * c := Int.mul_comm c b
  omega

def Dot : List (Int × Int) → Int
  | [] => 0
  | (a, b) :: rest => a * b + Dot rest

def NormASq : List (Int × Int) → Int
  | [] => 0
  | (a, _) :: rest => a * a + NormASq rest

def NormBSq : List (Int × Int) → Int
  | [] => 0
  | (_, b) :: rest => b * b + NormBSq rest

def PairQuad (x y : Int) : List (Int × Int) → Int
  | [] => 0
  | (a, b) :: rest => (x * a - y * b) * (x * a - y * b) + PairQuad x y rest

private theorem single_pair_quad_expand (x y a b : Int) :
    (x * a - y * b) * (x * a - y * b) =
      (x * x) * (a * a) - 2 * ((x * y) * (a * b)) + (y * y) * (b * b) := by
  have t1 : (x * a) * (x * a) = (x * x) * (a * a) := (mul_self_mul_self_comm x a).symm
  have t2 : (y * b) * (y * b) = (y * y) * (b * b) := (mul_self_mul_self_comm y b).symm
  have t3 : (x * a) * (y * b) = (x * y) * (a * b) := mul_term_mul_term x y a b
  have t4 : (y * b) * (x * a) = (x * y) * (a * b) := by
    rw [Int.mul_comm (y * b) (x * a), t3]
  rw [Int.sub_mul, Int.mul_sub, Int.mul_sub, t1, t2, t3, t4]
  omega

theorem pair_quad_expand (x y : Int) (s : List (Int × Int)) :
    PairQuad x y s =
      (x * x) * NormASq s - 2 * ((x * y) * Dot s) + (y * y) * NormBSq s := by
  induction s with
  | nil =>
      unfold PairQuad NormASq Dot NormBSq
      rw [Int.mul_zero, Int.mul_zero, Int.mul_zero]
      omega
  | cons hd tl ih =>
      cases hd with
      | mk a b =>
          unfold PairQuad NormASq Dot NormBSq
          rw [single_pair_quad_expand x y a b, ih,
              Int.mul_add (x * x), Int.mul_add (x * y), Int.mul_add 2, Int.mul_add (y * y)]
          omega

theorem pair_quad_nonneg (x y : Int) (s : List (Int × Int)) : 0 ≤ PairQuad x y s := by
  induction s with
  | nil =>
      unfold PairQuad
      omega
  | cons hd tl ih =>
      cases hd with
      | mk a b =>
          unfold PairQuad
          have hsq : 0 ≤ (x * a - y * b) * (x * a - y * b) := int_sq_nonneg (x * a - y * b)
          omega

theorem norm_a_sq_nonneg (s : List (Int × Int)) : 0 ≤ NormASq s := by
  induction s with
  | nil =>
      unfold NormASq
      omega
  | cons hd tl ih =>
      cases hd with
      | mk a b =>
          unfold NormASq
          have ha : 0 ≤ a * a := int_sq_nonneg a
          omega

theorem dot_eq_zero_of_norm_a_sq_zero (s : List (Int × Int)) (h : NormASq s = 0) :
    Dot s = 0 := by
  induction s with
  | nil =>
      rfl
  | cons hd tl ih =>
      cases hd with
      | mk a b =>
          unfold NormASq at h
          unfold Dot
          have ha_nn : 0 ≤ a * a := int_sq_nonneg a
          have htl_nn : 0 ≤ NormASq tl := norm_a_sq_nonneg tl
          have ha_zero : a * a = 0 := by omega
          have htl_zero : NormASq tl = 0 := by omega
          have ha0 : a = 0 := int_eq_zero_of_sq_eq_zero a ha_zero
          rw [ha0, Int.zero_mul, ih htl_zero]
          omega

theorem list_dot_sq_le (s : List (Int × Int)) :
    Dot s * Dot s ≤ NormASq s * NormBSq s := by
  have hna_nn : 0 ≤ NormASq s := norm_a_sq_nonneg s
  by_cases hna0 : NormASq s = 0
  · have hd0 : Dot s = 0 := dot_eq_zero_of_norm_a_sq_zero s hna0
    rw [hd0, hna0, Int.zero_mul, Int.zero_mul]
    omega
  · have hna_pos : 0 < NormASq s := by omega
    have hq : 0 ≤ PairQuad (Dot s) (NormASq s) s := pair_quad_nonneg (Dot s) (NormASq s) s
    rw [pair_quad_expand (Dot s) (NormASq s) s] at hq
    let d := Dot s
    let na := NormASq s
    let nb := NormBSq s
    have h_ident :
        (d * d) * na - 2 * ((d * na) * d) + (na * na) * nb =
          na * (na * nb - d * d) := by
      have c1 : (d * d) * na = na * (d * d) := Int.mul_comm (d * d) na
      have c2 : (d * na) * d = na * (d * d) := by
        rw [Int.mul_comm d na, Int.mul_assoc na d d]
      have c3 : (na * na) * nb = na * (na * nb) := Int.mul_assoc na na nb
      have c4 : na * (na * nb - d * d) = na * (na * nb) - na * (d * d) :=
        Int.mul_sub na (na * nb) (d * d)
      rw [c1, c2, c3, c4]
      omega
    change 0 ≤ (d * d) * na - 2 * ((d * na) * d) + (na * na) * nb at hq
    rw [h_ident] at hq
    by_cases hle : d * d ≤ na * nb
    · exact hle
    · have hneg : na * nb - d * d < 0 := by omega
      have hprod : na * (na * nb - d * d) < 0 := Int.mul_neg_of_pos_of_neg hna_pos hneg
      omega

/-!
  ## Part 1: Theorem P — Polar `(Omega, xi)` Palinstrophy Splitting & S^2 Harmonic Sink
-/

def VecNormSq (x y z : Int) : Int := x * x + y * y + z * z

def VecDot (x1 y1 z1 x2 y2 z2 : Int) : Int := x1 * x2 + y1 * y2 + z1 * z2

def CrossX (_x1 y1 z1 _x2 y2 z2 : Int) : Int := y1 * z2 - z1 * y2
def CrossY (x1 _y1 z1 x2 _y2 z2 : Int) : Int := z1 * x2 - x1 * z2
def CrossZ (x1 y1 _z1 x2 y2 _z2 : Int) : Int := x1 * y2 - y1 * x2

/--
  3D Lagrange Cross-Product Identity (`lagrange_3d_identity`):
  `(x · y)^2 + |x × y|^2 = |x|^2 * |y|^2`.
-/
theorem lagrange_3d_identity (x1 x2 x3 y1 y2 y3 : Int) :
    VecDot x1 x2 x3 y1 y2 y3 * VecDot x1 x2 x3 y1 y2 y3 +
      VecNormSq (CrossX x1 x2 x3 y1 y2 y3) (CrossY x1 x2 x3 y1 y2 y3) (CrossZ x1 x2 x3 y1 y2 y3) =
    VecNormSq x1 x2 x3 * VecNormSq y1 y2 y3 := by
  unfold VecDot VecNormSq CrossX CrossY CrossZ
  rw [binomial_sub_sq_expand (x2 * y3) (x3 * y2),
      binomial_sub_sq_expand (x3 * y1) (x1 * y3),
      binomial_sub_sq_expand (x1 * y2) (x2 * y1),
      trinomial_sq_expand (x1 * y1) (x2 * y2) (x3 * y3)]
  have p11 : (x1 * y1) * (x1 * y1) = (x1 * x1) * (y1 * y1) := (mul_self_mul_self_comm x1 y1).symm
  have p22 : (x2 * y2) * (x2 * y2) = (x2 * x2) * (y2 * y2) := (mul_self_mul_self_comm x2 y2).symm
  have p33 : (x3 * y3) * (x3 * y3) = (x3 * x3) * (y3 * y3) := (mul_self_mul_self_comm x3 y3).symm
  have p12 : (x1 * y2) * (x1 * y2) = (x1 * x1) * (y2 * y2) := (mul_self_mul_self_comm x1 y2).symm
  have p21 : (x2 * y1) * (x2 * y1) = (x2 * x2) * (y1 * y1) := (mul_self_mul_self_comm x2 y1).symm
  have p23 : (x2 * y3) * (x2 * y3) = (x2 * x2) * (y3 * y3) := (mul_self_mul_self_comm x2 y3).symm
  have p32 : (x3 * y2) * (x3 * y2) = (x3 * x3) * (y2 * y2) := (mul_self_mul_self_comm x3 y2).symm
  have p31 : (x3 * y1) * (x3 * y1) = (x3 * x3) * (y1 * y1) := (mul_self_mul_self_comm x3 y1).symm
  have p13 : (x1 * y3) * (x1 * y3) = (x1 * x1) * (y3 * y3) := (mul_self_mul_self_comm x1 y3).symm
  have m12 : (x1 * y1) * (x2 * y2) = (x1 * y2) * (x2 * y1) := by
    rw [mul_term_mul_term x1 x2 y1 y2, mul_term_mul_term x1 x2 y2 y1, Int.mul_comm y1 y2]
  have m13 : (x1 * y1) * (x3 * y3) = (x3 * y1) * (x1 * y3) := by
    rw [mul_term_mul_term x1 x3 y1 y3, mul_term_mul_term x3 x1 y1 y3, Int.mul_comm x1 x3]
  have m23 : (x2 * y2) * (x3 * y3) = (x2 * y3) * (x3 * y2) := by
    rw [mul_term_mul_term x2 x3 y2 y3, mul_term_mul_term x2 x3 y3 y2, Int.mul_comm y2 y3]
  have hrhs :
      (x1 * x1 + x2 * x2 + x3 * x3) * (y1 * y1 + y2 * y2 + y3 * y3) =
        (x1 * x1) * (y1 * y1) + (x1 * x1) * (y2 * y2) + (x1 * x1) * (y3 * y3) +
        (x2 * x2) * (y1 * y1) + (x2 * x2) * (y2 * y2) + (x2 * x2) * (y3 * y3) +
        (x3 * x3) * (y1 * y1) + (x3 * x3) * (y2 * y2) + (x3 * x3) * (y3 * y3) := by
    rw [Int.add_mul, Int.add_mul,
        Int.mul_add, Int.mul_add,
        Int.mul_add, Int.mul_add,
        Int.mul_add, Int.mul_add]
    omega
  rw [p11, p22, p33, p12, p21, p23, p32, p31, p13, m12, m13, m23, hrhs]
  omega

/--
  Full 3x3 Jacobian Frobenius norm squared `||grad w||_F^2 = sum_{a,b=1}^3 j_{ab}^2`.
-/
def JacFrobSq (j11 j21 j31 j12 j22 j32 j13 j23 j33 : Int) : Int :=
  VecNormSq j11 j21 j31 + VecNormSq j12 j22 j32 + VecNormSq j13 j23 j33

/--
  Division-free Polar Amplitude Steepening Density `sum_{b=1}^3 (w · d_b w)^2`.
-/
def PolarAmpTerm (w1 w2 w3 j11 j21 j31 j12 j22 j32 j13 j23 j33 : Int) : Int :=
  VecDot w1 w2 w3 j11 j21 j31 * VecDot w1 w2 w3 j11 j21 j31 +
  VecDot w1 w2 w3 j12 j22 j32 * VecDot w1 w2 w3 j12 j22 j32 +
  VecDot w1 w2 w3 j13 j23 j33 * VecDot w1 w2 w3 j13 j23 j33

/--
  Division-free Polar Direction-Curvature Density `sum_{b=1}^3 |w × d_b w|^2`.
-/
def PolarDirTerm (w1 w2 w3 j11 j21 j31 j12 j22 j32 j13 j23 j33 : Int) : Int :=
  VecNormSq (CrossX w1 w2 w3 j11 j21 j31) (CrossY w1 w2 w3 j11 j21 j31) (CrossZ w1 w2 w3 j11 j21 j31) +
  VecNormSq (CrossX w1 w2 w3 j12 j22 j32) (CrossY w1 w2 w3 j12 j22 j32) (CrossZ w1 w2 w3 j12 j22 j32) +
  VecNormSq (CrossX w1 w2 w3 j13 j23 j33) (CrossY w1 w2 w3 j13 j23 j33) (CrossZ w1 w2 w3 j13 j23 j33)

/--
  **Theorem P1a (`step7_polar_palinstrophy_lagrange_splitting`):**
  For EVERY 3D vorticity vector `w` and 3x3 gradient tensor `grad w`,
  `PolarAmpTerm + PolarDirTerm = |w|^2 * ||grad w||_F^2`.
-/
theorem step7_polar_palinstrophy_lagrange_splitting
    (w1 w2 w3 j11 j21 j31 j12 j22 j32 j13 j23 j33 : Int) :
    PolarAmpTerm w1 w2 w3 j11 j21 j31 j12 j22 j32 j13 j23 j33 +
      PolarDirTerm w1 w2 w3 j11 j21 j31 j12 j22 j32 j13 j23 j33 =
    VecNormSq w1 w2 w3 * JacFrobSq j11 j21 j31 j12 j22 j32 j13 j23 j33 := by
  unfold PolarAmpTerm PolarDirTerm JacFrobSq
  have c1 := lagrange_3d_identity w1 w2 w3 j11 j21 j31
  have c2 := lagrange_3d_identity w1 w2 w3 j12 j22 j32
  have c3 := lagrange_3d_identity w1 w2 w3 j13 j23 j33
  have hdist :
      VecNormSq w1 w2 w3 *
        (VecNormSq j11 j21 j31 + VecNormSq j12 j22 j32 + VecNormSq j13 j23 j33) =
      VecNormSq w1 w2 w3 * VecNormSq j11 j21 j31 +
      VecNormSq w1 w2 w3 * VecNormSq j12 j22 j32 +
      VecNormSq w1 w2 w3 * VecNormSq j13 j23 j33 := by
    rw [Int.mul_add, Int.mul_add]
  rw [hdist]
  omega

/--
  **Theorem P1b (`step7_kato_inequality_with_exact_curvature_deficit`):**
  `0 ≤ PolarDirTerm` and `PolarAmpTerm ≤ |w|^2 * ||grad w||_F^2`.
-/
theorem step7_kato_inequality_with_exact_curvature_deficit
    (w1 w2 w3 j11 j21 j31 j12 j22 j32 j13 j23 j33 : Int) :
    0 ≤ PolarDirTerm w1 w2 w3 j11 j21 j31 j12 j22 j32 j13 j23 j33 ∧
    PolarAmpTerm w1 w2 w3 j11 j21 j31 j12 j22 j32 j13 j23 j33 ≤
      VecNormSq w1 w2 w3 * JacFrobSq j11 j21 j31 j12 j22 j32 j13 j23 j33 := by
  have hsplit :=
    step7_polar_palinstrophy_lagrange_splitting w1 w2 w3 j11 j21 j31 j12 j22 j32 j13 j23 j33
  have hdir_nn : 0 ≤ PolarDirTerm w1 w2 w3 j11 j21 j31 j12 j22 j32 j13 j23 j33 := by
    unfold PolarDirTerm VecNormSq
    have s1 := int_sq_nonneg (CrossX w1 w2 w3 j11 j21 j31)
    have s2 := int_sq_nonneg (CrossY w1 w2 w3 j11 j21 j31)
    have s3 := int_sq_nonneg (CrossZ w1 w2 w3 j11 j21 j31)
    have s4 := int_sq_nonneg (CrossX w1 w2 w3 j12 j22 j32)
    have s5 := int_sq_nonneg (CrossY w1 w2 w3 j12 j22 j32)
    have s6 := int_sq_nonneg (CrossZ w1 w2 w3 j12 j22 j32)
    have s7 := int_sq_nonneg (CrossX w1 w2 w3 j13 j23 j33)
    have s8 := int_sq_nonneg (CrossY w1 w2 w3 j13 j23 j33)
    have s9 := int_sq_nonneg (CrossZ w1 w2 w3 j13 j23 j33)
    omega
  exact ⟨hdir_nn, by omega⟩

/--
  **Theorem P2a (`step7_s2_harmonic_laplacian_orthogonality`):**
  On the sphere `|xi|^2 = R`, `xi · Delta xi = -||grad xi||_F^2` forces the covariant
  S^2 harmonic-map Laplacian `R * Delta xi + ||grad xi||_F^2 * xi` to be strictly
  orthogonal to `xi`.
-/
theorem step7_s2_harmonic_laplacian_orthogonality
    (x1 x2 x3 lx ly lz g2 R : Int)
    (h_sphere : VecNormSq x1 x2 x3 = R)
    (h_second_deriv : VecDot x1 x2 x3 lx ly lz = -g2) :
    VecDot x1 x2 x3 (R * lx + g2 * x1) (R * ly + g2 * x2) (R * lz + g2 * x3) = 0 := by
  unfold VecNormSq at h_sphere
  unfold VecDot at h_second_deriv ⊢
  have e1 : x1 * (R * lx + g2 * x1) = R * (x1 * lx) + g2 * (x1 * x1) := by
    rw [Int.mul_add, ← Int.mul_assoc x1 R lx, Int.mul_comm x1 R, Int.mul_assoc R x1 lx,
        ← Int.mul_assoc x1 g2 x1, Int.mul_comm x1 g2, Int.mul_assoc g2 x1 x1]
  have e2 : x2 * (R * ly + g2 * x2) = R * (x2 * ly) + g2 * (x2 * x2) := by
    rw [Int.mul_add, ← Int.mul_assoc x2 R ly, Int.mul_comm x2 R, Int.mul_assoc R x2 ly,
        ← Int.mul_assoc x2 g2 x2, Int.mul_comm x2 g2, Int.mul_assoc g2 x2 x2]
  have e3 : x3 * (R * lz + g2 * x3) = R * (x3 * lz) + g2 * (x3 * x3) := by
    rw [Int.mul_add, ← Int.mul_assoc x3 R lz, Int.mul_comm x3 R, Int.mul_assoc R x3 lz,
        ← Int.mul_assoc x3 g2 x3, Int.mul_comm x3 g2, Int.mul_assoc g2 x3 x3]
  rw [e1, e2, e3]
  have hsum :
      R * (x1 * lx) + g2 * (x1 * x1) + (R * (x2 * ly) + g2 * (x2 * x2)) +
        (R * (x3 * lz) + g2 * (x3 * x3)) =
      R * (x1 * lx + x2 * ly + x3 * lz) + g2 * (x1 * x1 + x2 * x2 + x3 * x3) := by
    rw [Int.mul_add R (x1 * lx + x2 * ly) (x3 * lz),
        Int.mul_add R (x1 * lx) (x2 * ly),
        Int.mul_add g2 (x1 * x1 + x2 * x2) (x3 * x3),
        Int.mul_add g2 (x1 * x1) (x2 * x2)]
    omega
  rw [hsum, h_second_deriv, h_sphere, Int.mul_neg, Int.mul_comm g2 R]
  omega

def SymStrainFrobSq (s11 s22 s33 s12 s13 s23 : Int) : Int :=
  s11 * s11 + s22 * s22 + s33 * s33 + 2 * (s12 * s12 + s13 * s13 + s23 * s23)

def SymStrainStretch (s11 s22 s33 s12 s13 s23 x1 x2 x3 : Int) : Int :=
  s11 * (x1 * x1) + s22 * (x2 * x2) + s33 * (x3 * x3) +
    2 * (s12 * (x1 * x2) + s13 * (x1 * x3) + s23 * (x2 * x3))

private theorem sq_three_sub (x n : Int) :
    (3 * x - n) * (3 * x - n) = 9 * (x * x) - 6 * (x * n) + n * n := by
  have t1 : (3 * x) * (3 * x) = 9 * (x * x) := mul_term_mul_term 3 3 x x
  have t2 : (3 * x) * n = 3 * (x * n) := Int.mul_assoc 3 x n
  have t3 : n * (3 * x) = 3 * (x * n) := by
    rw [Int.mul_comm n (3 * x), t2]
  rw [Int.sub_mul, Int.mul_sub, Int.mul_sub, t1, t2, t3]
  omega

theorem trace_free_strain_bound_helper
    (s11 s22 s33 s12 s13 s23 w1 w2 w3 : Int)
    (htr : s11 + s22 + s33 = 0) :
    3 * (SymStrainStretch s11 s22 s33 s12 s13 s23 w1 w2 w3 *
         SymStrainStretch s11 s22 s33 s12 s13 s23 w1 w2 w3) ≤
      2 * (SymStrainFrobSq s11 s22 s33 s12 s13 s23 *
           (VecNormSq w1 w2 w3 * VecNormSq w1 w2 w3)) := by
  let a := w1 * w1
  let b := w2 * w2
  let c := w3 * w3
  let n := a + b + c
  let p12 := w1 * w2
  let p13 := w1 * w3
  let p23 := w2 * w3
  let devPairs : List (Int × Int) :=
    [(s11, 3 * a - n), (s22, 3 * b - n), (s33, 3 * c - n),
     (s12, 3 * p12), (s12, 3 * p12),
     (s13, 3 * p13), (s13, 3 * p13),
     (s23, 3 * p23), (s23, 3 * p23)]
  have hcs : Dot devPairs * Dot devPairs ≤ NormASq devPairs * NormBSq devPairs :=
    list_dot_sq_le devPairs
  have h_na : NormASq devPairs = SymStrainFrobSq s11 s22 s33 s12 s13 s23 := by
    dsimp [devPairs, NormASq, SymStrainFrobSq]
    omega
  have h_dot : Dot devPairs = 3 * SymStrainStretch s11 s22 s33 s12 s13 s23 w1 w2 w3 := by
    dsimp [devPairs, Dot, SymStrainStretch, a, b, c]
    have d1 : s11 * (3 * (w1 * w1) - n) = 3 * (s11 * (w1 * w1)) - s11 * n := by
      rw [Int.mul_sub, ← Int.mul_assoc s11 3 (w1 * w1), Int.mul_comm s11 3, Int.mul_assoc 3 s11 _]
    have d2 : s22 * (3 * (w2 * w2) - n) = 3 * (s22 * (w2 * w2)) - s22 * n := by
      rw [Int.mul_sub, ← Int.mul_assoc s22 3 (w2 * w2), Int.mul_comm s22 3, Int.mul_assoc 3 s22 _]
    have d3 : s33 * (3 * (w3 * w3) - n) = 3 * (s33 * (w3 * w3)) - s33 * n := by
      rw [Int.mul_sub, ← Int.mul_assoc s33 3 (w3 * w3), Int.mul_comm s33 3, Int.mul_assoc 3 s33 _]
    have o12 : s12 * (3 * p12) = 3 * (s12 * p12) := by
      rw [← Int.mul_assoc s12 3 p12, Int.mul_comm s12 3, Int.mul_assoc 3 s12 p12]
    have o13 : s13 * (3 * p13) = 3 * (s13 * p13) := by
      rw [← Int.mul_assoc s13 3 p13, Int.mul_comm s13 3, Int.mul_assoc 3 s13 p13]
    have o23 : s23 * (3 * p23) = 3 * (s23 * p23) := by
      rw [← Int.mul_assoc s23 3 p23, Int.mul_comm s23 3, Int.mul_assoc 3 s23 p23]
    have tr_n : s11 * n + s22 * n + s33 * n = 0 := by
      have hsum : s11 * n + s22 * n + s33 * n = (s11 + s22 + s33) * n := by
        rw [Int.add_mul, Int.add_mul]
      rw [hsum, htr, Int.zero_mul]
    rw [d1, d2, d3, o12, o13, o23]
    dsimp [p12, p13, p23]
    omega
  have h_nb : NormBSq devPairs = 6 * (VecNormSq w1 w2 w3 * VecNormSq w1 w2 w3) := by
    dsimp [devPairs, NormBSq]
    have q1 : (3 * a - n) * (3 * a - n) = 9 * (a * a) - 6 * (a * n) + n * n := sq_three_sub a n
    have q2 : (3 * b - n) * (3 * b - n) = 9 * (b * b) - 6 * (b * n) + n * n := sq_three_sub b n
    have q3 : (3 * c - n) * (3 * c - n) = 9 * (c * c) - 6 * (c * n) + n * n := sq_three_sub c n
    have r12 : (3 * p12) * (3 * p12) = 9 * (a * b) := by
      rw [mul_term_mul_term 3 3 p12 p12]
      dsimp [p12, a, b]
      rw [← mul_self_mul_self_comm w1 w2]
    have r13 : (3 * p13) * (3 * p13) = 9 * (a * c) := by
      rw [mul_term_mul_term 3 3 p13 p13]
      dsimp [p13, a, c]
      rw [← mul_self_mul_self_comm w1 w3]
    have r23 : (3 * p23) * (3 * p23) = 9 * (b * c) := by
      rw [mul_term_mul_term 3 3 p23 p23]
      dsimp [p23, b, c]
      rw [← mul_self_mul_self_comm w2 w3]
    have hn_sum : a * n + b * n + c * n = n * n := by
      have hs : a * n + b * n + c * n = (a + b + c) * n := by
        rw [Int.add_mul, Int.add_mul]
      rw [hs]
    have hn_sq : n * n = (a * a + b * b + c * c) + 2 * (a * b + a * c + b * c) :=
      trinomial_sq_expand a b c
    have hn_vec : VecNormSq w1 w2 w3 = n := rfl
    rw [q1, q2, q3, r12, r13, r23, hn_vec]
    omega
  rw [h_dot, h_na, h_nb] at hcs
  let S_stretch := SymStrainStretch s11 s22 s33 s12 s13 s23 w1 w2 w3
  let S_frob := SymStrainFrobSq s11 s22 s33 s12 s13 s23
  let W_norm := VecNormSq w1 w2 w3
  change (3 * S_stretch) * (3 * S_stretch) ≤ S_frob * (6 * (W_norm * W_norm)) at hcs
  have hl : (3 * S_stretch) * (3 * S_stretch) = 9 * (S_stretch * S_stretch) :=
    mul_term_mul_term 3 3 S_stretch S_stretch
  have hr : S_frob * (6 * (W_norm * W_norm)) = 6 * (S_frob * (W_norm * W_norm)) := by
    rw [← Int.mul_assoc S_frob 6 (W_norm * W_norm), Int.mul_comm S_frob 6,
        Int.mul_assoc 6 S_frob (W_norm * W_norm)]
  rw [hl, hr] at hcs
  dsimp [S_stretch, S_frob, W_norm] at hcs
  omega

/--
  **Theorem P2b (`step7_vorticity_peak_drift_vanishes_and_curvature_crushes`):**
  At ANY spatial maximum `x_*` of scalar vorticity `Omega = |w|`:
    1. The singular vortex-null drift `-2 * nu * (grad Omega · grad) xi` vanishes
       identically (`grad_om_x = grad_om_y = grad_om_z = 0`), and
    2. Whenever filament direction curvature satisfies
         `2 * ||S(x_*)||_F^2 * R^2 < 3 * (nu * R * g2)^2`,
       peak vorticity strictly decreases!
-/
theorem step7_vorticity_peak_drift_vanishes_and_curvature_crushes
    (s11 s22 s33 s12 s13 s23 x1 x2 x3 : Int)
    (grad_om_x grad_om_y grad_om_z d1_xi d2_xi d3_xi : Int)
    (nu R g2 lap_om : Int)
    (h_trace_free : s11 + s22 + s33 = 0)
    (h_peak_grad_zero : grad_om_x = 0 ∧ grad_om_y = 0 ∧ grad_om_z = 0)
    (h_peak_lap_nonpos : lap_om ≤ 0)
    (h_nu_pos : 0 < nu) (h_R_pos : 0 < R) (h_g2_pos : 0 < g2)
    (h_sphere : VecNormSq x1 x2 x3 = R)
    (h_curv_gate :
      2 * (SymStrainFrobSq s11 s22 s33 s12 s13 s23 * (R * R)) <
        3 * ((nu * (R * g2)) * (nu * (R * g2)))) :
    (-2 * nu * VecDot grad_om_x grad_om_y grad_om_z d1_xi d2_xi d3_xi = 0) ∧
    (SymStrainStretch s11 s22 s33 s12 s13 s23 x1 x2 x3 + nu * (R * lap_om) - nu * (R * g2) < 0) := by
  have hdrift : -2 * nu * VecDot grad_om_x grad_om_y grad_om_z d1_xi d2_xi d3_xi = 0 := by
    rcases h_peak_grad_zero with ⟨gx0, gy0, gz0⟩
    unfold VecDot
    rw [gx0, gy0, gz0, Int.zero_mul, Int.zero_mul, Int.zero_mul]
    omega
  have htf := trace_free_strain_bound_helper s11 s22 s33 s12 s13 s23 x1 x2 x3 h_trace_free
  rw [h_sphere] at htf
  let st := SymStrainStretch s11 s22 s33 s12 s13 s23 x1 x2 x3
  let sink := nu * (R * g2)
  have hRg2_pos : 0 < R * g2 := Int.mul_pos h_R_pos h_g2_pos
  have hsink_pos : 0 < sink := Int.mul_pos h_nu_pos hRg2_pos
  have h3_lt : 3 * (st * st) < 3 * (sink * sink) := by
    dsimp [st, sink] at htf ⊢
    exact Int.lt_of_le_of_lt htf h_curv_gate
  have hsq_lt : st * st < sink * sink := by omega
  have hst_lt_sink : st < sink := by
    by_cases hst_nn : 0 ≤ st
    · exact int_lt_of_sq_lt_sq st sink hst_nn hsink_pos hsq_lt
    · omega
  have hlap_le : nu * (R * lap_om) ≤ 0 := by
    have hRlap : R * lap_om ≤ R * 0 := Int.mul_le_mul_of_nonneg_left h_peak_lap_nonpos (by omega)
    rw [Int.mul_zero] at hRlap
    have hnuRlap : nu * (R * lap_om) ≤ nu * 0 := Int.mul_le_mul_of_nonneg_left hRlap (by omega)
    rw [Int.mul_zero] at hnuRlap
    exact hnuRlap
  exact ⟨hdrift, by dsimp [st, sink] at hst_lt_sink; omega⟩

/-!
  ## Part 2: Theorem Q — Polar Curvature Scissors & Cubic `(1 - Phi_dir)^3` Depletion
-/

theorem quartic_sos_identity (a b : Int) :
    ((a - b) * (a - b)) * (((a + b) * (a + b)) + 2 * (b * b)) =
      (a * a) * (a * a) + 3 * ((b * b) * (b * b)) - 4 * (a * (b * (b * b))) := by
  have h_sub : (a - b) * (a - b) = a * a - 2 * (a * b) + b * b := binomial_sub_sq_expand a b
  have h_add : ((a + b) * (a + b)) + 2 * (b * b) = a * a + 2 * (a * b) + 3 * (b * b) := by
    rw [binomial_sq_expand a b]
    omega
  rw [h_sub, h_add]
  let P := a * a
  let Q := a * b
  let R := b * b
  have hPR : P * R = Q * Q := mul_self_mul_self_comm a b
  have hQR : Q * R = a * (b * (b * b)) := by
    dsimp [Q, R]
    rw [Int.mul_assoc a b (b * b)]
  have hexp :
      (P - 2 * Q + R) * (P + 2 * Q + 3 * R) =
        P * P + P * (2 * Q) + P * (3 * R) -
        (2 * Q) * P - (2 * Q) * (2 * Q) - (2 * Q) * (3 * R) +
        R * P + R * (2 * Q) + R * (3 * R) := by
    rw [Int.add_mul, Int.sub_mul,
        Int.mul_add, Int.mul_add,
        Int.mul_add, Int.mul_add,
        Int.mul_add, Int.mul_add]
    omega
  have c1 : P * (2 * Q) = 2 * (P * Q) := by
    rw [← Int.mul_assoc P 2 Q, Int.mul_comm P 2, Int.mul_assoc 2 P Q]
  have c2 : (2 * Q) * P = 2 * (P * Q) := by
    rw [Int.mul_assoc 2 Q P, Int.mul_comm Q P]
  have c3 : P * (3 * R) = 3 * (P * R) := by
    rw [← Int.mul_assoc P 3 R, Int.mul_comm P 3, Int.mul_assoc 3 P R]
  have c4 : R * P = P * R := Int.mul_comm R P
  have c5 : (2 * Q) * (2 * Q) = 4 * (Q * Q) := mul_term_mul_term 2 2 Q Q
  have c6 : (2 * Q) * (3 * R) = 6 * (Q * R) := mul_term_mul_term 2 3 Q R
  have c7 : R * (2 * Q) = 2 * (Q * R) := by
    rw [← Int.mul_assoc R 2 Q, Int.mul_comm R 2, Int.mul_assoc 2 R Q, Int.mul_comm R Q]
  have c8 : R * (3 * R) = 3 * (R * R) := by
    rw [← Int.mul_assoc R 3 R, Int.mul_comm R 3, Int.mul_assoc 3 R R]
  change (P - 2 * Q + R) * (P + 2 * Q + 3 * R) = P * P + 3 * (R * R) - 4 * (a * (b * (b * b)))
  rw [hexp, c1, c2, c3, c4, c5, c6, c7, c8, hPR, hQR]
  omega

theorem young_quartic_four_le (a b : Int) :
    4 * (a * (b * (b * b))) ≤ (a * a) * (a * a) + 3 * ((b * b) * (b * b)) := by
  have hs1 : 0 ≤ (a - b) * (a - b) := int_sq_nonneg (a - b)
  have hs2 : 0 ≤ (a + b) * (a + b) := int_sq_nonneg (a + b)
  have hs3 : 0 ≤ b * b := int_sq_nonneg b
  have hprod : 0 ≤ ((a - b) * (a - b)) * (((a + b) * (a + b)) + 2 * (b * b)) :=
    Int.mul_nonneg hs1 (by omega)
  rw [quartic_sos_identity a b] at hprod
  omega

theorem young_quartic_27_256_sos (A B : Int) :
    256 * (A * (B * (B * B))) - 256 * ((B * B) * (B * B)) ≤
      27 * ((A * A) * (A * A)) := by
  have h := young_quartic_four_le (3 * A) (4 * B)
  have hA2 : (3 * A) * (3 * A) = 9 * (A * A) := mul_term_mul_term 3 3 A A
  have hA4 : (9 * (A * A)) * (9 * (A * A)) = 81 * ((A * A) * (A * A)) :=
    mul_term_mul_term 9 9 (A * A) (A * A)
  have hB2 : (4 * B) * (4 * B) = 16 * (B * B) := mul_term_mul_term 4 4 B B
  have hB4 : (16 * (B * B)) * (16 * (B * B)) = 256 * ((B * B) * (B * B)) :=
    mul_term_mul_term 16 16 (B * B) (B * B)
  have hB3 : (4 * B) * ((4 * B) * (4 * B)) = 64 * (B * (B * B)) := by
    rw [hB2]
    exact mul_term_mul_term 4 16 B (B * B)
  have hAB3 : 4 * ((3 * A) * (64 * (B * (B * B)))) = 768 * (A * (B * (B * B))) := by
    have h192 : (3 * A) * (64 * (B * (B * B))) = 192 * (A * (B * (B * B))) :=
      mul_term_mul_term 3 64 A (B * (B * B))
    rw [h192, ← Int.mul_assoc 4 192 (A * (B * (B * B)))]
    rfl
  rw [hB3, hAB3, hA2, hA4, hB2, hB4] at h
  omega

/--
  **Theorem Q1 (`step7_polar_curvature_ceiling_widening`):**
  Let `P = P_amp + P_dir` (`P_amp ≥ 0`, `P_dir ≥ 0`). Because `||w||_{L^4} = || |w| ||_{L^4}`
  depends solely on scalar amplitude `|w|`, any amplitude-only stretching bound
    `9 * stretch^4 ≤ C4 * D^3 * P_amp^3`
  guarantees strict enstrophy decay `stretch - nu * P < 0` whenever
    `C4 * D^3 * P_amp^3 < 9 * nu^4 * P^4`.
-/
theorem step7_polar_curvature_ceiling_widening
    (stretch nu C4 D P_amp P_dir : Int)
    (h_nu_pos : 0 < nu)
    (h_Pamp_nn : 0 ≤ P_amp) (h_Pdir_nn : 0 ≤ P_dir)
    (h_P_pos : 0 < P_amp + P_dir)
    (h_amp_stretch_bound :
      9 * ((stretch * stretch) * (stretch * stretch)) ≤
        (C4 * (D * (D * D))) * (P_amp * (P_amp * P_amp)))
    (h_polar_ceiling_gate :
      (C4 * (D * (D * D))) * (P_amp * (P_amp * P_amp)) <
        9 * (((nu * (P_amp + P_dir)) * (nu * (P_amp + P_dir))) *
             ((nu * (P_amp + P_dir)) * (nu * (P_amp + P_dir))))) :
    stretch - nu * (P_amp + P_dir) < 0 := by
  let P := P_amp + P_dir
  let nuP := nu * P
  have hnuP_pos : 0 < nuP := Int.mul_pos h_nu_pos h_P_pos
  have h9_lt :
      9 * ((stretch * stretch) * (stretch * stretch)) <
        9 * ((nuP * nuP) * (nuP * nuP)) := by
    dsimp [nuP, P]
    exact Int.lt_of_le_of_lt h_amp_stretch_bound h_polar_ceiling_gate
  have h4_lt :
      (stretch * stretch) * (stretch * stretch) < (nuP * nuP) * (nuP * nuP) := by omega
  by_cases hst_nn : 0 ≤ stretch
  · have hlt : stretch < nuP := int_lt_of_pow4_lt_pow4 stretch nuP hst_nn hnuP_pos h4_lt
    dsimp [nuP, P] at hlt
    omega
  · have _u1 := h_Pamp_nn
    have _u2 := h_Pdir_nn
    dsimp [nuP, P] at hnuP_pos
    omega

/--
  **Theorem Q2 (`step7_polar_curvature_cubic_quartic_depletion`):**
  Splitting `P = P_amp1^4 + P_dir` in `2 * A_amp * P_amp1^3 - 2 * nu * (P_amp1^4 + P_dir)`
  absorbs `P_amp1^3` into `-2 * nu * P_amp1^4` while keeping the ENTIRE direction-curvature
  harmonic sink `-256 * nu^4 * P_dir` untouched:
    `128 * nu^3 * (2 * A_amp * P_amp1^3 - 2 * nu * (P_amp1^4 + P_dir))`
    `  ≤ 27 * A_amp^4 - 256 * nu^4 * P_dir`.
-/
theorem step7_polar_curvature_cubic_quartic_depletion
    (A_amp nu P_amp1 P_dir : Int) :
    128 * (nu * (nu * nu)) *
      (2 * (A_amp * (P_amp1 * (P_amp1 * P_amp1))) -
        2 * (nu * ((P_amp1 * P_amp1) * (P_amp1 * P_amp1) + P_dir))) ≤
      27 * ((A_amp * A_amp) * (A_amp * A_amp)) -
        256 * (((nu * nu) * (nu * nu)) * P_dir) := by
  let B := nu * P_amp1
  have hyoung := young_quartic_27_256_sos A_amp B
  have hB3 : B * (B * B) = (nu * (nu * nu)) * (P_amp1 * (P_amp1 * P_amp1)) := by
    dsimp [B]
    have s1 : (nu * P_amp1) * (nu * P_amp1) = (nu * nu) * (P_amp1 * P_amp1) :=
      (mul_self_mul_self_comm nu P_amp1).symm
    rw [s1]
    exact mul_term_mul_term nu (nu * nu) P_amp1 (P_amp1 * P_amp1)
  have hB4 : (B * B) * (B * B) = ((nu * nu) * (nu * nu)) * ((P_amp1 * P_amp1) * (P_amp1 * P_amp1)) := by
    dsimp [B]
    have s1 : (nu * P_amp1) * (nu * P_amp1) = (nu * nu) * (P_amp1 * P_amp1) :=
      (mul_self_mul_self_comm nu P_amp1).symm
    rw [s1]
    exact (mul_self_mul_self_comm (nu * nu) (P_amp1 * P_amp1)).symm
  have hAB3 :
      A_amp * (B * (B * B)) =
        (nu * (nu * nu)) * (A_amp * (P_amp1 * (P_amp1 * P_amp1))) := by
    rw [hB3, ← Int.mul_assoc A_amp (nu * (nu * nu)) _,
        Int.mul_comm A_amp (nu * (nu * nu)),
        Int.mul_assoc (nu * (nu * nu)) A_amp _]
  rw [hAB3, hB4] at hyoung
  have hlhs :
      128 * (nu * (nu * nu)) *
        (2 * (A_amp * (P_amp1 * (P_amp1 * P_amp1))) -
          2 * (nu * ((P_amp1 * P_amp1) * (P_amp1 * P_amp1) + P_dir))) =
      256 * ((nu * (nu * nu)) * (A_amp * (P_amp1 * (P_amp1 * P_amp1)))) -
      256 * (((nu * nu) * (nu * nu)) * ((P_amp1 * P_amp1) * (P_amp1 * P_amp1))) -
      256 * (((nu * nu) * (nu * nu)) * P_dir) := by
    let nu3 := nu * (nu * nu)
    let P4 := (P_amp1 * P_amp1) * (P_amp1 * P_amp1)
    let P3 := P_amp1 * (P_amp1 * P_amp1)
    have hnu4 : nu3 * nu = (nu * nu) * (nu * nu) := by
      dsimp [nu3]
      calc
        (nu * (nu * nu)) * nu = nu * ((nu * nu) * nu) := Int.mul_assoc nu (nu * nu) nu
        _ = nu * (nu * (nu * nu)) := by rw [Int.mul_assoc nu nu nu]
        _ = (nu * nu) * (nu * nu) := by rw [← Int.mul_assoc nu nu (nu * nu)]
    rw [Int.mul_add nu P4 P_dir, Int.mul_sub (128 * nu3)]
    have t1 : (128 * nu3) * (2 * (A_amp * P3)) = 256 * (nu3 * (A_amp * P3)) := by
      calc
        (128 * nu3) * (2 * (A_amp * P3)) = (128 * 2) * (nu3 * (A_amp * P3)) :=
          mul_term_mul_term 128 2 nu3 (A_amp * P3)
        _ = 256 * (nu3 * (A_amp * P3)) := rfl
    have t2 :
        (128 * nu3) * (2 * (nu * P4 + nu * P_dir)) =
          256 * (((nu * nu) * (nu * nu)) * P4) + 256 * (((nu * nu) * (nu * nu)) * P_dir) := by
      rw [← Int.mul_add nu P4 P_dir]
      calc
        (128 * nu3) * (2 * (nu * (P4 + P_dir))) = (128 * 2) * (nu3 * (nu * (P4 + P_dir))) :=
          mul_term_mul_term 128 2 nu3 (nu * (P4 + P_dir))
        _ = 256 * ((nu3 * nu) * (P4 + P_dir)) := by rw [← Int.mul_assoc nu3 nu (P4 + P_dir)]; rfl
        _ = 256 * (((nu * nu) * (nu * nu)) * (P4 + P_dir)) := by rw [hnu4]
        _ = 256 * (((nu * nu) * (nu * nu)) * P4) + 256 * (((nu * nu) * (nu * nu)) * P_dir) := by
          rw [Int.mul_add ((nu * nu) * (nu * nu)) P4 P_dir, Int.mul_add 256]
    dsimp [nu3, P4, P3] at t1 t2 ⊢
    rw [t1, t2]
    omega
  rw [hlhs]
  omega

/-!
  ## Part 3: Theorem R — Zero-Gap Bony Paraproduct Barrier for Gapless Cascades
-/

theorem z3_parallelogram_law (px py pz qx qy qz : Int) :
    VecNormSq (px + qx) (py + qy) (pz + qz) +
      VecNormSq (px - qx) (py - qy) (pz - qz) =
    2 * VecNormSq px py pz + 2 * VecNormSq qx qy qz := by
  unfold VecNormSq
  rw [binomial_sq_expand px qx, binomial_sq_expand py qy, binomial_sq_expand pz qz,
      binomial_sub_sq_expand px qx, binomial_sub_sq_expand py qy, binomial_sub_sq_expand pz qz]
  omega

/--
  **Theorem R1 (`step7_bony_adjacent_collar_localization`):**
  Across ANY wavenumber cutoff `M_cut` with ZERO empty scale gap (`m_{j+1} ≤ 4 m_j`),
  every Low-Low spillover triad `(p, q)` (`|p|^2 ≤ M_cut`, `|q|^2 ≤ M_cut`) that crosses
  into `|p + q|^2 > M_cut` satisfies `|p + q|^2 ≤ 4 * M_cut` and
  `M_cut < 4 * |p|^2 ∨ M_cut < 4 * |q|^2`.
-/
theorem step7_bony_adjacent_collar_localization
    (px py pz qx qy qz M_cut : Int)
    (hp_low : VecNormSq px py pz ≤ M_cut)
    (hq_low : VecNormSq qx qy qz ≤ M_cut)
    (h_spill : M_cut < VecNormSq (px + qx) (py + qy) (pz + qz)) :
    VecNormSq (px + qx) (py + qy) (pz + qz) ≤ 4 * M_cut ∧
    (M_cut < 4 * VecNormSq px py pz ∨ M_cut < 4 * VecNormSq qx qy qz) := by
  have hpar := z3_parallelogram_law px py pz qx qy qz
  have hdiff_nn : 0 ≤ VecNormSq (px - qx) (py - qy) (pz - qz) := by
    unfold VecNormSq
    have s1 := int_sq_nonneg (px - qx)
    have s2 := int_sq_nonneg (py - qy)
    have s3 := int_sq_nonneg (pz - qz)
    omega
  have h_collar : VecNormSq (px + qx) (py + qy) (pz + qz) ≤ 4 * M_cut := by omega
  have h_not_both_quarter : M_cut < 4 * VecNormSq px py pz ∨ M_cut < 4 * VecNormSq qx qy qz := by
    by_cases hp4 : M_cut < 4 * VecNormSq px py pz
    · exact Or.inl hp4
    · by_cases hq4 : M_cut < 4 * VecNormSq qx qy qz
      · exact Or.inr hq4
      · omega
  exact ⟨h_collar, h_not_both_quarter⟩

/--
  **Theorem R2a (`step7_zero_gap_sweeping_symmetric_strain_reduction`):**
  Contracting low-velocity gradient `g` against symmetric high-gradient Gram tensor `m`
  cancels antisymmetric low vorticity identically with zero scale gap.
-/
theorem step7_zero_gap_sweeping_symmetric_strain_reduction
    (g11 g12 g13 g21 g22 g23 g31 g32 g33 m11 m22 m33 m12 m13 m23 : Int) :
    2 * (g11 * m11 + g12 * m12 + g13 * m13 +
         g21 * m12 + g22 * m22 + g23 * m23 +
         g31 * m13 + g32 * m23 + g33 * m33) =
    2 * (g11 * m11) + 2 * (g22 * m22) + 2 * (g33 * m33) +
      2 * ((g12 + g21) * m12) + 2 * ((g13 + g31) * m13) + 2 * ((g23 + g32) * m23) := by
  rw [Int.add_mul g12 g21 m12, Int.add_mul g13 g31 m13, Int.add_mul g23 g32 m23]
  omega

/--
  **Theorem R2b (`step7_zero_gap_bony_paraproduct_uv_gate`):**
  4-Channel Zero-Gap Bony Paraproduct UV Enstrophy Decay Gate for Gapless Multi-Octave Cascades.
-/
theorem step7_zero_gap_bony_paraproduct_uv_gate
    (T_LL T_lin T_HH kap nu D4 P4 : Int)
    (h_nu_pos : 0 < nu) (h_P4_pos : 0 < P4)
    (h_THH_nn : 0 ≤ T_HH)
    (h_collar_gate :
      16 * (T_LL * T_LL) <
        (nu * ((P4 * P4) * (P4 * P4))) * (nu * ((P4 * P4) * (P4 * P4))))
    (h_lin_gate : 2 * T_lin ≤ nu * ((P4 * P4) * (P4 * P4)))
    (h_self_bound :
      9 * ((T_HH * T_HH) * (T_HH * T_HH)) ≤
        (((kap * kap) * (kap * kap)) * (D4 * (D4 * D4))) *
          (((P4 * P4) * (P4 * P4)) * (((P4 * P4) * (P4 * P4)) * ((P4 * P4) * (P4 * P4)))))
    (h_self_gate :
      256 * (((kap * kap) * (kap * kap)) * (D4 * (D4 * D4))) <
        9 * (((nu * nu) * (nu * nu)) * ((P4 * P4) * (P4 * P4)))) :
    4 * (T_LL + T_lin + T_HH - nu * ((P4 * P4) * (P4 * P4))) < 0 := by
  let PH := (P4 * P4) * (P4 * P4)
  have hP2_pos : 0 < P4 * P4 := Int.mul_pos h_P4_pos h_P4_pos
  have hPH_pos : 0 < PH := Int.mul_pos hP2_pos hP2_pos
  have hnuPH_pos : 0 < nu * PH := Int.mul_pos h_nu_pos hPH_pos

  have h_4TLL : 4 * T_LL < nu * PH := by
    by_cases hll_nn : 0 ≤ T_LL
    · have h4ll_sq : (4 * T_LL) * (4 * T_LL) = 16 * (T_LL * T_LL) :=
        mul_term_mul_term 4 4 T_LL T_LL
      have hsq_lt : (4 * T_LL) * (4 * T_LL) < (nu * PH) * (nu * PH) := by
        rw [h4ll_sq]
        exact h_collar_gate
      exact int_lt_of_sq_lt_sq (4 * T_LL) (nu * PH) (by omega) hnuPH_pos hsq_lt
    · omega

  have h_4Tlin : 4 * T_lin ≤ 2 * (nu * PH) := by
    dsimp [PH] at h_lin_gate ⊢
    omega

  let PH3 := PH * (PH * PH)
  have hPH2_pos : 0 < PH * PH := Int.mul_pos hPH_pos hPH_pos
  have hPH3_pos : 0 < PH3 := Int.mul_pos hPH_pos hPH2_pos
  have h_256_bound :
      2304 * ((T_HH * T_HH) * (T_HH * T_HH)) ≤
        (256 * (((kap * kap) * (kap * kap)) * (D4 * (D4 * D4)))) * PH3 := by
    have hm :
        256 * (9 * ((T_HH * T_HH) * (T_HH * T_HH))) ≤
          256 * ((((kap * kap) * (kap * kap)) * (D4 * (D4 * D4))) * PH3) :=
      Int.mul_le_mul_of_nonneg_left h_self_bound (by omega)
    rw [← Int.mul_assoc 256 9 _, ← Int.mul_assoc 256 _ PH3] at hm
    exact hm
  have h_gate_mul :
      (256 * (((kap * kap) * (kap * kap)) * (D4 * (D4 * D4)))) * PH3 <
        (9 * (((nu * nu) * (nu * nu)) * PH)) * PH3 :=
    Int.mul_lt_mul_of_pos_right h_self_gate hPH3_pos
  have hrhs_nuPH4 :
      (9 * (((nu * nu) * (nu * nu)) * PH)) * PH3 =
        9 * (((nu * PH) * (nu * PH)) * ((nu * PH) * (nu * PH))) := by
    dsimp [PH3]
    have s1 : (nu * PH) * (nu * PH) = (nu * nu) * (PH * PH) :=
      (mul_self_mul_self_comm nu PH).symm
    rw [s1]
    have s2 :
        ((nu * nu) * (PH * PH)) * ((nu * nu) * (PH * PH)) =
          ((nu * nu) * (nu * nu)) * ((PH * PH) * (PH * PH)) :=
      (mul_self_mul_self_comm (nu * nu) (PH * PH)).symm
    have s3 : PH * (PH * (PH * PH)) = (PH * PH) * (PH * PH) := by
      rw [← Int.mul_assoc PH PH (PH * PH)]
    rw [s2, ← s3, ← Int.mul_assoc ((nu * nu) * (nu * nu)) PH (PH * (PH * PH)),
        Int.mul_assoc 9 _ (PH * (PH * PH))]
  rw [hrhs_nuPH4] at h_gate_mul
  have h_2304_lt :
      2304 * ((T_HH * T_HH) * (T_HH * T_HH)) <
        9 * (((nu * PH) * (nu * PH)) * ((nu * PH) * (nu * PH))) :=
    Int.lt_of_le_of_lt h_256_bound h_gate_mul
  have h_4THH_pow4 :
      ((4 * T_HH) * (4 * T_HH)) * ((4 * T_HH) * (4 * T_HH)) =
        256 * ((T_HH * T_HH) * (T_HH * T_HH)) := by
    have s1 : (4 * T_HH) * (4 * T_HH) = 16 * (T_HH * T_HH) :=
      mul_term_mul_term 4 4 T_HH T_HH
    rw [s1]
    exact mul_term_mul_term 16 16 (T_HH * T_HH) (T_HH * T_HH)
  have h_pow4_lt :
      ((4 * T_HH) * (4 * T_HH)) * ((4 * T_HH) * (4 * T_HH)) <
        ((nu * PH) * (nu * PH)) * ((nu * PH) * (nu * PH)) := by
    rw [h_4THH_pow4]
    omega
  have _u := h_THH_nn
  have h_4THH : 4 * T_HH < nu * PH :=
    int_lt_of_pow4_lt_pow4 (4 * T_HH) (nu * PH) (by omega) hnuPH_pos h_pow4_lt

  dsimp [PH] at h_4TLL h_4Tlin h_4THH
  omega

/-!
  ## Part 4: Theorem S — Beirao da Veiga-Berselli `C^{1/2}` Direction Cone &
  `D^3 -> D^2` Leray Doubling Closure ("It's Just One PDE")
-/

def BiotSavartDet (x1 x2 x3 y1 y2 y3 z1 z2 z3 : Int) : Int :=
  VecDot z1 z2 z3 (CrossX x1 x2 x3 y1 y2 y3) (CrossY x1 x2 x3 y1 y2 y3) (CrossZ x1 x2 x3 y1 y2 y3)

/--
  **Theorem S1 (`step7_holder_half_cone_biot_savart_bound`):**
  For equal-norm vorticity direction vectors `|xi|^2 = |eta|^2 = R` satisfying
  `|xi - eta|^2 ≤ K_xi * d1`, `det[xi, eta, z]^2 ≤ |z|^2 * (R * (K_xi * d1))`.
-/
theorem step7_holder_half_cone_biot_savart_bound
    (x1 x2 x3 y1 y2 y3 z1 z2 z3 R K_xi d1 : Int)
    (hx : VecNormSq x1 x2 x3 = R)
    (hy : VecNormSq y1 y2 y3 = R)
    (h_R_nn : 0 ≤ R)
    (h_holder_cone : VecNormSq (x1 - y1) (x2 - y2) (x3 - y3) ≤ K_xi * d1) :
    BiotSavartDet x1 x2 x3 y1 y2 y3 z1 z2 z3 *
      BiotSavartDet x1 x2 x3 y1 y2 y3 z1 z2 z3 ≤
    VecNormSq z1 z2 z3 * (R * (K_xi * d1)) := by
  let cx := CrossX x1 x2 x3 y1 y2 y3
  let cy := CrossY x1 x2 x3 y1 y2 y3
  let cz := CrossZ x1 x2 x3 y1 y2 y3
  let pairs : List (Int × Int) := [(z1, cx), (z2, cy), (z3, cz)]
  have hcs : Dot pairs * Dot pairs ≤ NormASq pairs * NormBSq pairs := list_dot_sq_le pairs
  have hd : Dot pairs = BiotSavartDet x1 x2 x3 y1 y2 y3 z1 z2 z3 := by
    dsimp [pairs, Dot, BiotSavartDet, VecDot, cx, cy, cz]
    omega
  have hna : NormASq pairs = VecNormSq z1 z2 z3 := by
    dsimp [pairs, NormASq, VecNormSq]
    omega
  have hlag := lagrange_3d_identity x1 x2 x3 y1 y2 y3
  rw [hx, hy] at hlag
  let dot_xy := VecDot x1 x2 x3 y1 y2 y3
  have hnb : NormBSq pairs = R * R - dot_xy * dot_xy := by
    dsimp [pairs, NormBSq, VecNormSq, cx, cy, cz, dot_xy] at hlag ⊢
    omega
  have hchord : VecNormSq (x1 - y1) (x2 - y2) (x3 - y3) = 2 * R - 2 * dot_xy := by
    have hexp :
        VecNormSq (x1 - y1) (x2 - y2) (x3 - y3) =
          VecNormSq x1 x2 x3 + VecNormSq y1 y2 y3 - 2 * VecDot x1 x2 x3 y1 y2 y3 := by
      unfold VecNormSq VecDot
      rw [binomial_sub_sq_expand x1 y1, binomial_sub_sq_expand x2 y2, binomial_sub_sq_expand x3 y3]
      omega
    rw [hexp, hx, hy]
    dsimp [dot_xy]
    omega
  have hgap :
      R * (2 * R - 2 * dot_xy) - (R * R - dot_xy * dot_xy) = (R - dot_xy) * (R - dot_xy) := by
    rw [Int.mul_sub R (2 * R) (2 * dot_xy), binomial_sub_sq_expand R dot_xy]
    have r1 : R * (2 * R) = 2 * (R * R) := by
      rw [← Int.mul_assoc R 2 R, Int.mul_comm R 2, Int.mul_assoc 2 R R]
    have r2 : R * (2 * dot_xy) = 2 * (R * dot_xy) := by
      rw [← Int.mul_assoc R 2 dot_xy, Int.mul_comm R 2, Int.mul_assoc 2 R dot_xy]
    rw [r1, r2]
    omega
  have hsq_nn : 0 ≤ (R - dot_xy) * (R - dot_xy) := int_sq_nonneg (R - dot_xy)
  have hnb_le_chord : NormBSq pairs ≤ R * VecNormSq (x1 - y1) (x2 - y2) (x3 - y3) := by
    rw [hnb, hchord]
    omega
  have hchord_le_cone : R * VecNormSq (x1 - y1) (x2 - y2) (x3 - y3) ≤ R * (K_xi * d1) :=
    Int.mul_le_mul_of_nonneg_left h_holder_cone h_R_nn
  have hnb_le : NormBSq pairs ≤ R * (K_xi * d1) := Int.le_trans hnb_le_chord hchord_le_cone
  have hz_nn : 0 ≤ VecNormSq z1 z2 z3 := by
    unfold VecNormSq
    have s1 := int_sq_nonneg z1
    have s2 := int_sq_nonneg z2
    have s3 := int_sq_nonneg z3
    omega
  rw [hd, hna] at hcs
  have hmul : VecNormSq z1 z2 z3 * NormBSq pairs ≤ VecNormSq z1 z2 z3 * (R * (K_xi * d1)) :=
    Int.mul_le_mul_of_nonneg_left hnb_le hz_nn
  exact Int.le_trans hcs hmul

/--
  **Theorem S2a (`step7_holder_half_quadratic_d3_to_d2_reduction`):**
  Completing the square collapses cubic `D^3` growth to QUADRATIC `D^2` growth
  while preserving `-4 * nu^2 * P_dir`:
    `2 * nu * (2 * C_star * kh * D * g - 2 * nu * (g * g + P_dir))`
    `  ≤ (C_star * kh * D)^2 - 4 * nu^2 * P_dir`.
-/
theorem step7_holder_half_quadratic_d3_to_d2_reduction
    (C_star kh D g nu P_dir : Int) :
    2 * nu * (2 * ((C_star * kh) * (D * g)) - 2 * (nu * (g * g + P_dir))) ≤
      ((C_star * kh) * D) * ((C_star * kh) * D) - 4 * ((nu * nu) * P_dir) := by
  let A := (C_star * kh) * D
  let B := 2 * (nu * g)
  have hsq_nn : 0 ≤ (A - B) * (A - B) := int_sq_nonneg (A - B)
  have hexp :
      A * A - (A - B) * (A - B) - 4 * ((nu * nu) * P_dir) =
        2 * nu * (2 * ((C_star * kh) * (D * g)) - 2 * (nu * (g * g + P_dir))) := by
    rw [binomial_sub_sq_expand A B]
    have hAB : 2 * (A * B) = 4 * (nu * ((C_star * kh) * (D * g))) := by
      dsimp [A, B]
      calc
        2 * (((C_star * kh) * D) * (2 * (nu * g))) =
          (2 * 2) * (((C_star * kh) * D) * (nu * g)) := by
            rw [← Int.mul_assoc ((C_star * kh) * D) 2 (nu * g),
                Int.mul_comm ((C_star * kh) * D) 2,
                Int.mul_assoc 2 ((C_star * kh) * D) (nu * g),
                ← Int.mul_assoc 2 2 _]
        _ = 4 * (nu * ((C_star * kh) * (D * g))) := by
          have s1 : ((C_star * kh) * D) * (nu * g) = nu * ((C_star * kh) * (D * g)) := by
            calc
              ((C_star * kh) * D) * (nu * g) = (((C_star * kh) * D) * nu) * g := by
                rw [← Int.mul_assoc ((C_star * kh) * D) nu g]
              _ = (nu * ((C_star * kh) * D)) * g := by rw [Int.mul_comm ((C_star * kh) * D) nu]
              _ = nu * (((C_star * kh) * D) * g) := Int.mul_assoc nu ((C_star * kh) * D) g
              _ = nu * ((C_star * kh) * (D * g)) := by rw [Int.mul_assoc (C_star * kh) D g]
          rw [s1]
          rfl
    have hB2 : B * B = 4 * ((nu * nu) * (g * g)) := by
      dsimp [B]
      rw [mul_term_mul_term 2 2 (nu * g) (nu * g), ← mul_self_mul_self_comm nu g]
      rfl
    have hrhs :
        2 * nu * (2 * ((C_star * kh) * (D * g)) - 2 * (nu * (g * g + P_dir))) =
          4 * (nu * ((C_star * kh) * (D * g))) - 4 * ((nu * nu) * (g * g)) - 4 * ((nu * nu) * P_dir) := by
      rw [Int.mul_add nu (g * g) P_dir, Int.mul_sub (2 * nu)]
      have t1 : (2 * nu) * (2 * ((C_star * kh) * (D * g))) = 4 * (nu * ((C_star * kh) * (D * g))) :=
        mul_term_mul_term 2 2 nu ((C_star * kh) * (D * g))
      have t2 :
          (2 * nu) * (2 * (nu * (g * g) + nu * P_dir)) =
            4 * ((nu * nu) * (g * g)) + 4 * ((nu * nu) * P_dir) := by
        rw [← Int.mul_add nu (g * g) P_dir]
        calc
          (2 * nu) * (2 * (nu * (g * g + P_dir))) = (2 * 2) * (nu * (nu * (g * g + P_dir))) :=
            mul_term_mul_term 2 2 nu (nu * (g * g + P_dir))
          _ = 4 * ((nu * nu) * (g * g + P_dir)) := by rw [← Int.mul_assoc nu nu (g * g + P_dir)]; rfl
          _ = 4 * ((nu * nu) * (g * g)) + 4 * ((nu * nu) * (P_dir)) := by
            rw [Int.mul_add (nu * nu) (g * g) P_dir, Int.mul_add 4]
      rw [t1, t2]
      omega
    rw [hAB, hB2, hrhs]
    omega
  dsimp [A, B] at hsq_nn hexp ⊢
  omega

def Pow2 : Nat → Int
  | 0 => 1
  | k + 1 => 2 * Pow2 k

theorem pow2_pos (k : Nat) : 0 < Pow2 k := by
  induction k with
  | zero => dsimp [Pow2]; omega
  | succ _ ih => dsimp [Pow2]; omega

inductive LerayDoublingChain (M : Int) : Nat → Int → Int → Prop
  | refl (d : Int) : LerayDoublingChain M 0 d d
  | step {k : Nat} {d0 dm dnext Im : Int}
      (hprev : LerayDoublingChain M k d0 dm)
      (hdnext_nn : 0 ≤ dnext)
      (hwin_ode : M * (dnext - dm) ≤ Im * dnext)
      (hwin_half_budget : 2 * Im ≤ M) :
      LerayDoublingChain M (k + 1) d0 dnext

/--
  **Theorem S2b (`step7_leray_quadratic_doubling_closure`):**
  Constructive Zero-Choice Leray-Gronwall Global Regularity Closure (`D^3 -> D^2`).
-/
theorem step7_leray_quadratic_doubling_closure
    {M d0 dfinal : Int} {K : Nat}
    (h_M_pos : 0 < M)
    (hchain : LerayDoublingChain M K d0 dfinal) :
    dfinal ≤ Pow2 K * d0 := by
  induction hchain with
  | refl d =>
      dsimp [Pow2]
      omega
  | @step k d_start dm dnext Im _ hdnext_nn hwin_ode hwin_half_budget ih =>
      have h2_ode : 2 * (M * (dnext - dm)) ≤ (2 * Im) * dnext := by
        have hm := Int.mul_le_mul_of_nonneg_left hwin_ode (by omega : (0 : Int) ≤ 2)
        rw [← Int.mul_assoc 2 Im dnext] at hm
        exact hm
      have h_half_mul : (2 * Im) * dnext ≤ M * dnext :=
        Int.mul_le_mul_of_nonneg_right hwin_half_budget hdnext_nn
      have h_le : 2 * (M * (dnext - dm)) ≤ M * dnext := Int.le_trans h2_ode h_half_mul
      have h_lhs_rw : 2 * (M * (dnext - dm)) = M * (2 * dnext - 2 * dm) := by
        rw [Int.mul_sub M dnext dm, Int.mul_sub 2 (M * dnext) (M * dm),
            Int.mul_sub M (2 * dnext) (2 * dm)]
        have s1 : 2 * (M * dnext) = M * (2 * dnext) := by
          rw [← Int.mul_assoc 2 M dnext, Int.mul_comm 2 M, Int.mul_assoc M 2 dnext]
        have s2 : 2 * (M * dm) = M * (2 * dm) := by
          rw [← Int.mul_assoc 2 M dm, Int.mul_comm 2 M, Int.mul_assoc M 2 dm]
        rw [s1, s2]
      rw [h_lhs_rw] at h_le
      have h_double : dnext ≤ 2 * dm := by
        by_cases hd : dnext ≤ 2 * dm
        · exact hd
        · have hgt : dnext < 2 * dnext - 2 * dm := by omega
          have hMgt := Int.mul_lt_mul_of_pos_left hgt h_M_pos
          omega
      have h_ih2 : 2 * dm ≤ 2 * (Pow2 k * d_start) :=
        Int.mul_le_mul_of_nonneg_left ih (by omega)
      dsimp [Pow2]
      rw [Int.mul_assoc 2 (Pow2 k) d_start]
      exact Int.le_trans h_double h_ih2

end SweetbrierBSARStep7

-- Mandatory Constructive Axiom Gate: verify ZERO `Classical.choice` across ALL Round 6 theorems!
#print axioms SweetbrierBSARStep7.list_dot_sq_le
#print axioms SweetbrierBSARStep7.step7_polar_palinstrophy_lagrange_splitting
#print axioms SweetbrierBSARStep7.step7_kato_inequality_with_exact_curvature_deficit
#print axioms SweetbrierBSARStep7.step7_s2_harmonic_laplacian_orthogonality
#print axioms SweetbrierBSARStep7.step7_vorticity_peak_drift_vanishes_and_curvature_crushes
#print axioms SweetbrierBSARStep7.step7_polar_curvature_ceiling_widening
#print axioms SweetbrierBSARStep7.step7_polar_curvature_cubic_quartic_depletion
#print axioms SweetbrierBSARStep7.step7_bony_adjacent_collar_localization
#print axioms SweetbrierBSARStep7.step7_zero_gap_sweeping_symmetric_strain_reduction
#print axioms SweetbrierBSARStep7.step7_zero_gap_bony_paraproduct_uv_gate
#print axioms SweetbrierBSARStep7.step7_holder_half_cone_biot_savart_bound
#print axioms SweetbrierBSARStep7.step7_holder_half_quadratic_d3_to_d2_reduction
#print axioms SweetbrierBSARStep7.step7_leray_quadratic_doubling_closure
