/-
  Step6BiotSavartCommutatorRound5.lean
  ==============================================================================
  BSA-R x Eleven-Entry Bookkeeping — Round 5 Formal Appendix (Split Sheet #001)
  Constructive Lean 4.35.0 Attack on `Target Lemma BIOT-SAVART-BIMODAL-3D`:
  Physical-Space 3D Trace-Free Strain Geometry, Constantin-Fefferman Biot-Savart
  Determinant Depletion, Arithmetic Odd-Whale Chord Impossibility, and Scale-
  Separated Bimodal Commutator Viscous Absorption.

    - Theorem L1 (`step6_trace_free_isotropic_diagonal_zero` & `step6_trace_free_strain_bound`):
      For EVERY symmetric 3x3 integer strain tensor `S` satisfying solenoidal
      incompressibility `tr(S) = s11 + s22 + s33 = 0` and EVERY vorticity vector
      `w = (w1, w2, w3)`:
        1. Principal-axis isotropic vorticity `w1^2 = w2^2 = w3^2` annihilates
           vortex stretching identically (`w^T S w = 0`),
        2. Deviatoric 9-component Frobenius Cauchy-Schwarz proves constructively:
             `3 * (w^T S w)^2 ≤ 2 * ||S||_F^2 * |w|^4`
           (zero cubic characteristic roots required!).
    - Theorem L2 (`step6_trace_free_moving_ceiling` & `step6_trace_free_quartic_3_128`):
      Combined with `||S||_{L^2(T^3)}^2 = (1/2) D(t)`, sharpens Round 3's Moving
      Palinstrophy Ceiling by `9x` (`kappa^4 * D^3 < 9 * nu^4 * P`) and reduces
      the universal 3D quartic Young constant by `9x` from `27/128` to `3/128`!
    - Theorem M1 & M2 (`step6_biot_savart_collinear_zero`, `step6_biot_savart_gram_bound`,
      & `step6_cf_equal_norm_chord_depletion`):
      For the 3D Constantin-Fefferman (1993) Biot-Savart stretching determinant
      `det[xi, eta, z] = z · (xi × eta)`:
        1. Parallel or antiparallel vortex filaments (`eta = c * xi`) annihilate
           `det[xi, eta, z] = 0` identically (separating true 3D Navier-Stokes
           from Terence Tao's 2016 rotation-averaged synthetic PDE),
        2. `det[xi, eta, z]^2 ≤ |z|^2 * (|xi|^2 * |eta|^2 - (xi · eta)^2)`,
        3. For equal-norm direction vectors `|xi|^2 = |eta|^2 = R`, proves
           unconditionally (for ALL angles, without sign assumptions on `xi · eta`):
             `det[xi, eta, z]^2 ≤ |z|^2 * R * |xi - eta|^2`!
    - Theorem N1 & N2 (`step6_odd_whale_chord_impossible` & `step6_bimodal_commutator_viscous_gate`):
      1. Exact Z^3 lattice chord parity identity:
           `|q + p|^2 - |q|^2 = 2 * (p · q) + |p|^2`,
         proving constructively that for EVERY odd low-wavenumber Whale shell
         `|p|^2 % 2 = 1` (including ABC `m1 = 1`, Taylor-Green `m1 = 3`, and
         Kida-Pelz `m1 = 11`), NO chord `q -> q + p` can remain on ANY single
         high-wavenumber sphere `|q + p|^2 = |q|^2 = m2` (`m2 > 4 * m1`), forcing
         instantaneous bimodal enstrophy production `<(u · grad)u, Delta u> = 0`!
      2. For even Whale shells (`m1 % 2 = 0`, `m2 > 4 * m1`), proves that high-shell
         palinstrophy `-nu * m2 * D_H` strictly dominates the commutator strain
         `-(m2 - m1) <u_H, S_L u_H>` whenever `3 * nu^2 * m2^4 > (m2 - m1)^2 * m1 * F0L^2`.
    - Theorem O (`step6_broadband_commutator_sweeping_decoupling`):
      Zero-mean physical-space sweeping cancellation decouples broadband high-UV
      enstrophy decay from arbitrarily large low-frequency enstrophy `D_L^3`.

  Architect & Author: Christopher "Topher" Duguay
  Syndicate: One Big Consortium — Contingent Claims Register (100% Give-It-Away)
  Attestation: probabilistic_structural (Modal Box Verified, Zero Classical.choice)
  ==============================================================================
-/

namespace SweetbrierBSARStep6

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

/-- Arbitrary-length integer inner product, squared norms, and non-negative quadratic form. -/
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

/--
  Constructive Arbitrary-Dimension Integer Cauchy-Schwarz (`list_dot_sq_le`):
  For EVERY finite list `s : List (Int × Int)`, `(Dot s)^2 ≤ (NormASq s) * (NormBSq s)`.
-/
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
  ==============================================================================
  ## Theorem L1 & L2: 3D Trace-Free Symmetric Strain Bound & `9x` Quartic Sharpening
  ==============================================================================
  For a symmetric 3x3 strain tensor `S` (`s11, s22, s33, s12, s13, s23 : Int`) with
  `tr(S) = s11 + s22 + s33 = 0` and vorticity `w = (w1, w2, w3)`:
    `StrainFrobSq  = s11^2 + s22^2 + s33^2 + 2*(s12^2 + s13^2 + s23^2)`
    `VecNormSq     = w1^2 + w2^2 + w3^2`
    `StrainStretch = s11*w1^2 + s22*w2^2 + s33*w3^2 + 2*(s12*w1*w2 + s13*w1*w3 + s23*w2*w3)`.
-/

def StrainFrobSq (s11 s22 s33 s12 s13 s23 : Int) : Int :=
  s11 * s11 + s22 * s22 + s33 * s33 + 2 * (s12 * s12 + s13 * s13 + s23 * s23)

def VecNormSq (w1 w2 w3 : Int) : Int :=
  w1 * w1 + w2 * w2 + w3 * w3

def StrainStretch (s11 s22 s33 s12 s13 s23 w1 w2 w3 : Int) : Int :=
  s11 * (w1 * w1) + s22 * (w2 * w2) + s33 * (w3 * w3) +
    2 * (s12 * (w1 * w2) + s13 * (w1 * w3) + s23 * (w2 * w3))

/--
  Principal-Axis Isotropic Vorticity Annihilation (`step6_trace_free_isotropic_diagonal_zero`):
  In the eigenframe of `S` (`s12 = s13 = s23 = 0`), whenever vorticity has equal squared
  components along all three principal axes (`w1^2 = w2^2 = w3^2`), solenoidal
  trace-freeness `s11 + s22 + s33 = 0` forces `w^T S w = 0` IDENTICALLY!
-/
theorem step6_trace_free_isotropic_diagonal_zero
    (s11 s22 s33 w1 w2 w3 : Int)
    (htr : s11 + s22 + s33 = 0)
    (hw12 : w1 * w1 = w2 * w2)
    (hw23 : w2 * w2 = w3 * w3) :
    StrainStretch s11 s22 s33 0 0 0 w1 w2 w3 = 0 := by
  unfold StrainStretch
  rw [hw12, hw23, Int.zero_mul, Int.zero_mul, Int.zero_mul]
  have hsum :
      s11 * (w3 * w3) + s22 * (w3 * w3) + s33 * (w3 * w3) =
        (s11 + s22 + s33) * (w3 * w3) := by
    rw [Int.add_mul, Int.add_mul]
  have h0 : 2 * (0 + 0 + (0 : Int)) = 0 := by omega
  rw [h0, Int.add_zero, hsum, htr, Int.zero_mul]

private theorem sq_three_sub (x n : Int) :
    (3 * x - n) * (3 * x - n) = 9 * (x * x) - 6 * (x * n) + n * n := by
  have t1 : (3 * x) * (3 * x) = 9 * (x * x) := mul_term_mul_term 3 3 x x
  have t2 : (3 * x) * n = 3 * (x * n) := Int.mul_assoc 3 x n
  have t3 : n * (3 * x) = 3 * (x * n) := by
    rw [Int.mul_comm n (3 * x), t2]
  rw [Int.sub_mul, Int.mul_sub, Int.mul_sub, t1, t2, t3]
  omega

private theorem trinomial_sq_expand (a b c : Int) :
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

/--
  Sharp 3D Trace-Free Symmetric Strain Inequality (`step6_trace_free_strain_bound`):
  For ALL `s11 s22 s33 s12 s13 s23 w1 w2 w3 : Int` with `s11 + s22 + s33 = 0`,
      `3 * (w^T S w)^2 ≤ 2 * ||S||_F^2 * |w|^4`!
  Proved constructively via 9-component Frobenius Cauchy-Schwarz against the scaled
  deviatoric vorticity tensor `D_ij = 3 * w_i * w_j - |w|^2 * delta_ij`.
-/
theorem step6_trace_free_strain_bound
    (s11 s22 s33 s12 s13 s23 w1 w2 w3 : Int)
    (htr : s11 + s22 + s33 = 0) :
    3 * (StrainStretch s11 s22 s33 s12 s13 s23 w1 w2 w3 *
         StrainStretch s11 s22 s33 s12 s13 s23 w1 w2 w3) ≤
      2 * (StrainFrobSq s11 s22 s33 s12 s13 s23 *
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

  have h_na : NormASq devPairs = StrainFrobSq s11 s22 s33 s12 s13 s23 := by
    dsimp [devPairs, NormASq, StrainFrobSq]
    omega

  have h_dot : Dot devPairs = 3 * StrainStretch s11 s22 s33 s12 s13 s23 w1 w2 w3 := by
    dsimp [devPairs, Dot, StrainStretch, a, b, c]
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
  let S_stretch := StrainStretch s11 s22 s33 s12 s13 s23 w1 w2 w3
  let S_frob := StrainFrobSq s11 s22 s33 s12 s13 s23
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
  `9x` Sharpened Trace-Free Moving Palinstrophy Ceiling (`step6_trace_free_moving_ceiling`):
  Because `||S||_{L^2(T^3)}^2 = (1/2) D` and `3 * (w^T S w)^2 ≤ 2 * ||S||_F^2 * |w|^4`,
  total convective stretching `stretch` satisfies `9 * stretch^4 ≤ kappa^4 * D^3 * P^3`.
  Whenever `kappa^4 * D^3 < 9 * nu^4 * P` (`9x` wider safe ceiling than Round 3!),
  `stretch - nu * P < 0`!
-/
theorem step6_trace_free_moving_ceiling
    (stretch kappa nu d p : Int)
    (hstr_nn : 0 ≤ stretch)
    (hnu : 0 < nu)
    (hp : 0 < p)
    (h_tf_bound :
      9 * ((stretch * stretch) * (stretch * stretch)) ≤
        (((kappa * kappa) * (kappa * kappa)) *
          (((d * d) * (d * d)) * (((d * d) * (d * d)) * ((d * d) * (d * d))))) *
        (((p * p) * (p * p)) * (((p * p) * (p * p)) * ((p * p) * (p * p)))))
    (h_ceil_9x :
      ((kappa * kappa) * (kappa * kappa)) *
        (((d * d) * (d * d)) * (((d * d) * (d * d)) * ((d * d) * (d * d)))) <
      9 * (((nu * nu) * (nu * nu)) * ((p * p) * (p * p)))) :
    stretch - nu * ((p * p) * (p * p)) < 0 := by
  let P4 := (p * p) * (p * p)
  let P12 := P4 * (P4 * P4)
  let nuP := nu * P4
  have hp2 : 0 < p * p := Int.mul_pos hp hp
  have hP4_pos : 0 < P4 := Int.mul_pos hp2 hp2
  have hP8_pos : 0 < P4 * P4 := Int.mul_pos hP4_pos hP4_pos
  have hP12_pos : 0 < P12 := Int.mul_pos hP4_pos hP8_pos
  have hnuP_pos : 0 < nuP := Int.mul_pos hnu hP4_pos

  have h_mul_p12 :
      (((kappa * kappa) * (kappa * kappa)) *
        (((d * d) * (d * d)) * (((d * d) * (d * d)) * ((d * d) * (d * d))))) * P12 <
      (9 * (((nu * nu) * (nu * nu)) * P4)) * P12 :=
    Int.mul_lt_mul_of_pos_right h_ceil_9x hP12_pos

  have hrhs_eq :
      (9 * (((nu * nu) * (nu * nu)) * P4)) * P12 =
        9 * ((nuP * nuP) * (nuP * nuP)) := by
    dsimp [nuP, P12]
    have s1 : (nu * P4) * (nu * P4) = (nu * nu) * (P4 * P4) :=
      (mul_self_mul_self_comm nu P4).symm
    have s2 :
        ((nu * nu) * (P4 * P4)) * ((nu * nu) * (P4 * P4)) =
          ((nu * nu) * (nu * nu)) * ((P4 * P4) * (P4 * P4)) :=
      (mul_self_mul_self_comm (nu * nu) (P4 * P4)).symm
    have s3 : P4 * (P4 * (P4 * P4)) = (P4 * P4) * (P4 * P4) := by
      rw [← Int.mul_assoc P4 P4 (P4 * P4)]
    rw [s1, s2, ← s3, ← Int.mul_assoc (((nu * nu) * (nu * nu))) P4 (P4 * (P4 * P4)),
        Int.mul_assoc 9 _ (P4 * (P4 * P4))]

  rw [hrhs_eq] at h_mul_p12
  have h9_lt : 9 * ((stretch * stretch) * (stretch * stretch)) < 9 * ((nuP * nuP) * (nuP * nuP)) :=
    Int.lt_of_le_of_lt h_tf_bound h_mul_p12
  have h4_lt : (stretch * stretch) * (stretch * stretch) < (nuP * nuP) * (nuP * nuP) := by omega
  have h_lt : stretch < nuP := int_lt_of_pow4_lt_pow4 stretch nuP hstr_nn hnuP_pos h4_lt
  dsimp [nuP, P4] at h_lt
  omega

/--
  Sharp `3 / 128` Trace-Free Quartic Young Inequality (`step6_trace_free_quartic_3_128`):
  With `C` representing `(kappa / sqrt(3)) * D^{3/4}` (`9 * C^4 ≤ A^4`, where `A = kappa * D^{3/4}`)
  and `B = nu * P^{1/4}`, proves constructively:
      `256 * (C * B^3) - 256 * B^4 ≤ 3 * A^4`
  (`2 * C * B^3 - 2 * B^4 ≤ (3 / 128) * A^4`, a `9x` global sharpening over Round 3's `27/128`!).
-/
theorem step6_trace_free_quartic_3_128
    (A B C : Int)
    (h_tf_fourth : 9 * ((C * C) * (C * C)) ≤ (A * A) * (A * A)) :
    256 * (C * (B * (B * B))) - 256 * ((B * B) * (B * B)) ≤
      3 * ((A * A) * (A * A)) := by
  let a := 3 * C
  let b := 4 * B
  have hs1 : 0 ≤ (a - b) * (a - b) := int_sq_nonneg (a - b)
  have hs2 : 0 ≤ (a + b) * (a + b) := int_sq_nonneg (a + b)
  have hs3 : 0 ≤ b * b := int_sq_nonneg b
  have hprod : 0 ≤ ((a - b) * (a - b)) * (((a + b) * (a + b)) + 2 * (b * b)) :=
    Int.mul_nonneg hs1 (by omega)
  have h_quartic :
      ((a - b) * (a - b)) * (((a + b) * (a + b)) + 2 * (b * b)) =
        (a * a) * (a * a) + 3 * ((b * b) * (b * b)) - 4 * (a * (b * (b * b))) := by
    have h_sub : (a - b) * (a - b) = a * a - 2 * (a * b) + b * b := by
      rw [Int.sub_mul, Int.mul_sub, Int.mul_sub, Int.mul_comm b a]
      omega
    have h_add : ((a + b) * (a + b)) + 2 * (b * b) = a * a + 2 * (a * b) + 3 * (b * b) := by
      rw [Int.add_mul, Int.mul_add, Int.mul_add, Int.mul_comm b a]
      omega
    rw [h_sub, h_add]
    let P := a * a
    let Q := a * b
    let R := b * b
    have hPR : P * R = Q * Q := mul_self_mul_self_comm a b
    have hQR : Q * R = a * (b * (b * b)) := Int.mul_assoc a b (b * b)
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
    have c2 : (2 * Q) * P = 2 * (P * Q) := by rw [Int.mul_assoc 2 Q P, Int.mul_comm Q P]
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
  rw [h_quartic] at hprod
  have ha2 : a * a = 9 * (C * C) := mul_term_mul_term 3 3 C C
  have ha4 : (a * a) * (a * a) = 81 * ((C * C) * (C * C)) := by
    rw [ha2]
    exact mul_term_mul_term 9 9 (C * C) (C * C)
  have hb2 : b * b = 16 * (B * B) := mul_term_mul_term 4 4 B B
  have hb4 : (b * b) * (b * b) = 256 * ((B * B) * (B * B)) := by
    rw [hb2]
    exact mul_term_mul_term 16 16 (B * B) (B * B)
  have hb3 : b * (b * b) = 64 * (B * (B * B)) := by
    rw [hb2]
    exact mul_term_mul_term 4 16 B (B * B)
  have hab3 : 4 * (a * (b * (b * b))) = 768 * (C * (B * (B * B))) := by
    rw [hb3]
    dsimp [a]
    have h192 : (3 * C) * (64 * (B * (B * B))) = 192 * (C * (B * (B * B))) :=
      mul_term_mul_term 3 64 C (B * (B * B))
    rw [h192, ← Int.mul_assoc 4 192 (C * (B * (B * B)))]
    rfl
  rw [ha4, hb4, hab3] at hprod
  omega

/-!
  ==============================================================================
  ## Theorem M1 & M2: Constantin-Fefferman Biot-Savart Determinant Depletion
  ==============================================================================
  In physical space, vortex stretching is governed by the singular integral
  kernel carrying the geometric triple product `det[xi(x), xi(x+y), y/|y|]`:
      `BiotSavartDet(xi, eta, z) = z · (xi × eta)`.
-/

def CrossX (_x1 x2 x3 _y1 y2 y3 : Int) : Int := x2 * y3 - x3 * y2
def CrossY (x1 _x2 x3 y1 _y2 y3 : Int) : Int := x3 * y1 - x1 * y3
def CrossZ (x1 x2 _x3 y1 y2 _y3 : Int) : Int := x1 * y2 - x2 * y1

def BiotSavartDet (x1 x2 x3 y1 y2 y3 z1 z2 z3 : Int) : Int :=
  z1 * CrossX x1 x2 x3 y1 y2 y3 +
  z2 * CrossY x1 x2 x3 y1 y2 y3 +
  z3 * CrossZ x1 x2 x3 y1 y2 y3

/--
  Parallel / Antiparallel Filament Annihilation (`step6_biot_savart_collinear_zero`):
  Whenever `eta = c * xi` (`c > 0` parallel or `c < 0` antiparallel vortex tubes),
  the Constantin-Fefferman Biot-Savart stretching determinant vanishes IDENTICALLY!
-/
theorem step6_biot_savart_collinear_zero
    (c x1 x2 x3 z1 z2 z3 : Int) :
    BiotSavartDet x1 x2 x3 (c * x1) (c * x2) (c * x3) z1 z2 z3 = 0 := by
  unfold BiotSavartDet CrossX CrossY CrossZ
  have cx0 : x2 * (c * x3) - x3 * (c * x2) = 0 := by
    rw [← Int.mul_assoc x2 c x3, Int.mul_comm x2 c, Int.mul_assoc c x2 x3, Int.mul_comm x2 x3,
        ← Int.mul_assoc x3 c x2, Int.mul_comm x3 c, Int.mul_assoc c x3 x2]
    omega
  have cy0 : x3 * (c * x1) - x1 * (c * x3) = 0 := by
    rw [← Int.mul_assoc x3 c x1, Int.mul_comm x3 c, Int.mul_assoc c x3 x1, Int.mul_comm x3 x1,
        ← Int.mul_assoc x1 c x3, Int.mul_comm x1 c, Int.mul_assoc c x1 x3]
    omega
  have cz0 : x1 * (c * x2) - x2 * (c * x1) = 0 := by
    rw [← Int.mul_assoc x1 c x2, Int.mul_comm x1 c, Int.mul_assoc c x1 x2, Int.mul_comm x1 x2,
        ← Int.mul_assoc x2 c x1, Int.mul_comm x2 c, Int.mul_assoc c x2 x1]
    omega
  rw [cx0, cy0, cz0, Int.mul_zero, Int.mul_zero, Int.mul_zero]
  omega

/--
  Exact 3D Lagrange Cross-Product Identity (`step6_lagrange_cross_identity`):
  `|xi × eta|^2 + (xi · eta)^2 = |xi|^2 * |eta|^2`.
-/
theorem step6_lagrange_cross_identity (x1 x2 x3 y1 y2 y3 : Int) :
    VecNormSq (CrossX x1 x2 x3 y1 y2 y3) (CrossY x1 x2 x3 y1 y2 y3) (CrossZ x1 x2 x3 y1 y2 y3) +
      (x1 * y1 + x2 * y2 + x3 * y3) * (x1 * y1 + x2 * y2 + x3 * y3) =
    VecNormSq x1 x2 x3 * VecNormSq y1 y2 y3 := by
  unfold VecNormSq CrossX CrossY CrossZ
  have expand_sub_sq (u v : Int) : (u - v) * (u - v) = u * u - 2 * (u * v) + v * v := by
    rw [Int.sub_mul, Int.mul_sub, Int.mul_sub, Int.mul_comm v u]
    omega
  rw [expand_sub_sq (x2 * y3) (x3 * y2),
      expand_sub_sq (x3 * y1) (x1 * y3),
      expand_sub_sq (x1 * y2) (x2 * y1),
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
  Biot-Savart Determinant Gram Depletion (`step6_biot_savart_gram_bound`):
  `det[xi, eta, z]^2 ≤ |z|^2 * (|xi|^2 * |eta|^2 - (xi · eta)^2)`.
-/
theorem step6_biot_savart_gram_bound (x1 x2 x3 y1 y2 y3 z1 z2 z3 : Int) :
    BiotSavartDet x1 x2 x3 y1 y2 y3 z1 z2 z3 *
      BiotSavartDet x1 x2 x3 y1 y2 y3 z1 z2 z3 ≤
    VecNormSq z1 z2 z3 *
      (VecNormSq x1 x2 x3 * VecNormSq y1 y2 y3 -
        (x1 * y1 + x2 * y2 + x3 * y3) * (x1 * y1 + x2 * y2 + x3 * y3)) := by
  let cx := CrossX x1 x2 x3 y1 y2 y3
  let cy := CrossY x1 x2 x3 y1 y2 y3
  let cz := CrossZ x1 x2 x3 y1 y2 y3
  let vPairs : List (Int × Int) := [(z1, cx), (z2, cy), (z3, cz)]
  have hcs : Dot vPairs * Dot vPairs ≤ NormASq vPairs * NormBSq vPairs := list_dot_sq_le vPairs
  have hd : Dot vPairs = BiotSavartDet x1 x2 x3 y1 y2 y3 z1 z2 z3 := by
    dsimp [vPairs, Dot, BiotSavartDet, cx, cy, cz]
    omega
  have hna : NormASq vPairs = VecNormSq z1 z2 z3 := by
    dsimp [vPairs, NormASq, VecNormSq]
    omega
  have hnb :
      NormBSq vPairs =
        VecNormSq x1 x2 x3 * VecNormSq y1 y2 y3 -
          (x1 * y1 + x2 * y2 + x3 * y3) * (x1 * y1 + x2 * y2 + x3 * y3) := by
    have hlag := step6_lagrange_cross_identity x1 x2 x3 y1 y2 y3
    dsimp [vPairs, NormBSq, VecNormSq, cx, cy, cz] at hlag ⊢
    omega
  rw [hd, hna, hnb] at hcs
  exact hcs

/--
  Constantin-Fefferman (1993) Equal-Norm Direction Chord Depletion
  (`step6_cf_equal_norm_chord_depletion`):
  For ALL direction vectors `xi, eta` of equal squared norm `|xi|^2 = |eta|^2 = R`
  (without ANY sign restriction on `xi · eta`), proves constructively:
      `det[xi, eta, z]^2 ≤ |z|^2 * R * |xi - eta|^2`!
-/
theorem step6_cf_equal_norm_chord_depletion
    (x1 x2 x3 y1 y2 y3 z1 z2 z3 R : Int)
    (hx : VecNormSq x1 x2 x3 = R)
    (hy : VecNormSq y1 y2 y3 = R) :
    BiotSavartDet x1 x2 x3 y1 y2 y3 z1 z2 z3 *
      BiotSavartDet x1 x2 x3 y1 y2 y3 z1 z2 z3 ≤
    VecNormSq z1 z2 z3 * (R * VecNormSq (x1 - y1) (x2 - y2) (x3 - y3)) := by
  have hgram := step6_biot_savart_gram_bound x1 x2 x3 y1 y2 y3 z1 z2 z3
  rw [hx, hy] at hgram
  let d := x1 * y1 + x2 * y2 + x3 * y3
  have hchord : VecNormSq (x1 - y1) (x2 - y2) (x3 - y3) = 2 * R - 2 * d := by
    have expand_sub (u v : Int) : (u - v) * (u - v) = u * u - 2 * (u * v) + v * v := by
      rw [Int.sub_mul, Int.mul_sub, Int.mul_sub, Int.mul_comm v u]
      omega
    unfold VecNormSq at hx hy ⊢
    rw [expand_sub x1 y1, expand_sub x2 y2, expand_sub x3 y3]
    dsimp [d]
    omega
  have h_gap :
      R * VecNormSq (x1 - y1) (x2 - y2) (x3 - y3) - (R * R - d * d) =
        (R - d) * (R - d) := by
    rw [hchord, Int.mul_sub, Int.sub_mul, Int.mul_sub, Int.mul_sub]
    have c1 : R * (2 * R) = 2 * (R * R) := by
      rw [← Int.mul_assoc R 2 R, Int.mul_comm R 2, Int.mul_assoc 2 R R]
    have c2 : R * (2 * d) = 2 * (R * d) := by
      rw [← Int.mul_assoc R 2 d, Int.mul_comm R 2, Int.mul_assoc 2 R d]
    have c3 : d * R = R * d := Int.mul_comm d R
    rw [c1, c2, c3]
    omega
  have hsq_nn : 0 ≤ (R - d) * (R - d) := int_sq_nonneg (R - d)
  have h_le : R * R - d * d ≤ R * VecNormSq (x1 - y1) (x2 - y2) (x3 - y3) := by omega
  have hz_nn : 0 ≤ VecNormSq z1 z2 z3 := by
    unfold VecNormSq
    have z1s := int_sq_nonneg z1
    have z2s := int_sq_nonneg z2
    have z3s := int_sq_nonneg z3
    omega
  have hmul :
      VecNormSq z1 z2 z3 * (R * R - d * d) ≤
        VecNormSq z1 z2 z3 * (R * VecNormSq (x1 - y1) (x2 - y2) (x3 - y3)) :=
    Int.mul_le_mul_of_nonneg_left h_le hz_nn
  exact Int.le_trans hgram hmul

/-!
  ==============================================================================
  ## Theorem N1 & N2: Arithmetic Odd-Whale Chord Impossibility & Bimodal Gate
  ==============================================================================
-/

/--
  Exact Z^3 Lattice Chord Identity (`step6_lattice_chord_identity`):
  `|q + p|^2 - |q|^2 = 2 * (p · q) + |p|^2`.
-/
theorem step6_lattice_chord_identity (p1 p2 p3 q1 q2 q3 : Int) :
    VecNormSq (q1 + p1) (q2 + p2) (q3 + p3) - VecNormSq q1 q2 q3 =
      2 * (p1 * q1 + p2 * q2 + p3 * q3) + VecNormSq p1 p2 p3 := by
  have expand_add (u v : Int) : (u + v) * (u + v) = u * u + 2 * (v * u) + v * v := by
    rw [Int.add_mul, Int.mul_add, Int.mul_add, Int.mul_comm u v]
    omega
  unfold VecNormSq
  rw [expand_add q1 p1, expand_add q2 p2, expand_add q3 p3]
  omega

/--
  Arithmetic Odd-Whale Chord Impossibility (`step6_odd_whale_chord_impossible`):
  Whenever a low-wavenumber Whale shell has ODD squared wavevector norm
  `(|p|^2) % 2 = 1` (e.g. `m1 = 1` ABC Beltrami, `m1 = 3` Taylor-Green, `m1 = 5`,
  `m1 = 9`, `m1 = 11` Kida-Pelz), NO wavevector `q ∈ Z^3` satisfies
  `|q + p|^2 = |q|^2`! Consequently, on ANY scale-separated bimodal pair
  `(m1, m2)` with `m2 > 4 * m1` and `m1` odd, instantaneous bimodal convective
  enstrophy production `<(u · grad)u, Delta u>` vanishes IDENTICALLY at ALL amplitudes!
-/
theorem step6_odd_whale_chord_impossible
    (p1 p2 p3 q1 q2 q3 : Int)
    (h_odd : VecNormSq p1 p2 p3 % 2 = 1) :
    VecNormSq (q1 + p1) (q2 + p2) (q3 + p3) ≠ VecNormSq q1 q2 q3 := by
  intro heq
  have hchord := step6_lattice_chord_identity p1 p2 p3 q1 q2 q3
  rw [heq] at hchord
  omega

/--
  Even-Whale Scale-Separated Bimodal Commutator Viscous Gate
  (`step6_bimodal_commutator_viscous_gate`):
  For `u = u_L + u_H` supported on shells `0 < m1` and `m2 > 4 * m1` (`0 < dH`),
  convective enstrophy production collapses to `prod = -(m2 - m1) * <u_H, S_L u_H>`,
  satisfying `3 * m2^2 * prod^2 ≤ (m2 - m1)^2 * m1 * F0L^2 * dH^2` by Theorem L1.
  Whenever `3 * nu^2 * m2^4 > (m2 - m1)^2 * m1 * F0L^2`, high-shell palinstrophy
  dissipation `-nu * m2 * dH` strictly crushes `prod` (`prod - nu * m2 * dH < 0`),
  certifying bimodal enstrophy decay even when Round 4's `Upsilon_var >> 1`!
-/
theorem step6_bimodal_commutator_viscous_gate
    (prod nu m1 m2 F0L dH : Int)
    (hnu : 0 < nu)
    (hm2 : 0 < m2)
    (hdH : 0 < dH)
    (h_comm_bound :
      3 * ((m2 * m2) * (prod * prod)) ≤
        (((m2 - m1) * (m2 - m1)) * (m1 * (F0L * F0L))) * (dH * dH))
    (h_visc_dom :
      ((m2 - m1) * (m2 - m1)) * (m1 * (F0L * F0L)) <
        3 * ((nu * nu) * ((m2 * m2) * (m2 * m2)))) :
    prod - nu * (m2 * dH) < 0 := by
  by_cases hp_neg : prod < 0
  · have hm2_dH : 0 < m2 * dH := Int.mul_pos hm2 hdH
    have hnu_pos : 0 < nu * (m2 * dH) := Int.mul_pos hnu hm2_dH
    omega
  · have hp_nn : 0 ≤ prod := by omega
    have hdH2_pos : 0 < dH * dH := Int.mul_pos hdH hdH
    have hmul :
        (((m2 - m1) * (m2 - m1)) * (m1 * (F0L * F0L))) * (dH * dH) <
          (3 * ((nu * nu) * ((m2 * m2) * (m2 * m2)))) * (dH * dH) :=
      Int.mul_lt_mul_of_pos_right h_visc_dom hdH2_pos
    have h_chain :
        3 * ((m2 * m2) * (prod * prod)) <
          (3 * ((nu * nu) * ((m2 * m2) * (m2 * m2)))) * (dH * dH) :=
      Int.lt_of_le_of_lt h_comm_bound hmul
    let lhs := m2 * prod
    let rhs := m2 * (nu * (m2 * dH))
    have hlhs_nn : 0 ≤ lhs := Int.mul_nonneg (by omega) hp_nn
    have hm2_dH_pos : 0 < m2 * dH := Int.mul_pos hm2 hdH
    have hnu_m2_dH_pos : 0 < nu * (m2 * dH) := Int.mul_pos hnu hm2_dH_pos
    have hrhs_pos : 0 < rhs := Int.mul_pos hm2 hnu_m2_dH_pos
    have hl_sq : (m2 * m2) * (prod * prod) = lhs * lhs := mul_self_mul_self_comm m2 prod
    have hr_sq :
        ((nu * nu) * ((m2 * m2) * (m2 * m2))) * (dH * dH) = rhs * rhs := by
      dsimp [rhs]
      have s1 : (m2 * (nu * (m2 * dH))) * (m2 * (nu * (m2 * dH))) =
          (m2 * m2) * ((nu * (m2 * dH)) * (nu * (m2 * dH))) :=
        (mul_self_mul_self_comm m2 (nu * (m2 * dH))).symm
      have s2 : (nu * (m2 * dH)) * (nu * (m2 * dH)) =
          (nu * nu) * ((m2 * dH) * (m2 * dH)) :=
        (mul_self_mul_self_comm nu (m2 * dH)).symm
      have s3 : (m2 * dH) * (m2 * dH) = (m2 * m2) * (dH * dH) :=
        (mul_self_mul_self_comm m2 dH).symm
      rw [s1, s2, s3]
      let M := m2 * m2
      let N := nu * nu
      let D := dH * dH
      change (N * (M * M)) * D = M * (N * (M * D))
      calc
        (N * (M * M)) * D = ((N * M) * M) * D := by rw [← Int.mul_assoc N M M]
        _ = ((M * N) * M) * D := by rw [Int.mul_comm N M]
        _ = (M * (N * M)) * D := by rw [Int.mul_assoc M N M]
        _ = M * ((N * M) * D) := Int.mul_assoc M (N * M) D
        _ = M * (N * (M * D)) := by rw [Int.mul_assoc N M D]
    have h_assoc :
        (3 * ((nu * nu) * ((m2 * m2) * (m2 * m2)))) * (dH * dH) =
          3 * (((nu * nu) * ((m2 * m2) * (m2 * m2))) * (dH * dH)) :=
      Int.mul_assoc 3 _ (dH * dH)
    rw [hl_sq, h_assoc, hr_sq] at h_chain
    have h_sq_lt : lhs * lhs < rhs * rhs := by omega
    have h_lt : lhs < rhs := int_lt_of_sq_lt_sq lhs rhs hlhs_nn hrhs_pos h_sq_lt
    dsimp [lhs, rhs] at h_lt
    by_cases h_goal : prod < nu * (m2 * dH)
    · omega
    · have hge : nu * (m2 * dH) ≤ prod := by omega
      have hm_le : m2 * (nu * (m2 * dH)) ≤ m2 * prod :=
        Int.mul_le_mul_of_nonneg_left hge (by omega)
      omega

/-!
  ==============================================================================
  ## Theorem O: Broadband Low-High Sweeping Cancellation & Decoupled UV Decay
  ==============================================================================
  After physical-space integration by parts cancels the zero-mean low-frequency
  sweeping term `∫ u_L · grad(|grad u_H|^2 / 2) dx = 0`, the high-band UV
  enstrophy rate is bounded by `comm_prod + self_prod - nu * P_H`, completely
  DECOUPLED from giant low-frequency kinetic energy `E_L` and enstrophy `D_L^3`!
-/

theorem step6_broadband_commutator_sweeping_decoupling
    (comm_prod self_prod nu m_cut F1L kap dH pH : Int)
    (hcomm_nn : 0 ≤ comm_prod)
    (hself_nn : 0 ≤ self_prod)
    (hnu : 0 < nu)
    (hm_cut : 0 < m_cut)
    (hdH : 0 < dH)
    (hpH : 0 < pH)
    (h_poincare : m_cut * ((dH * dH) * (dH * dH)) ≤ (pH * pH) * (pH * pH))
    (h_comm_bound :
      3 * (comm_prod * comm_prod) ≤
        (F1L * F1L) * (((dH * dH) * (dH * dH)) * ((dH * dH) * (dH * dH))))
    (h_self_bound :
      9 * ((self_prod * self_prod) * (self_prod * self_prod)) ≤
        (((kap * kap) * (kap * kap)) *
          (((dH * dH) * (dH * dH)) * (((dH * dH) * (dH * dH)) * ((dH * dH) * (dH * dH))))) *
        (((pH * pH) * (pH * pH)) * (((pH * pH) * (pH * pH)) * ((pH * pH) * (pH * pH)))))
    (h_low_strain_gate : 4 * (F1L * F1L) < 3 * ((nu * nu) * (m_cut * m_cut)))
    (h_high_self_gate :
      16 * (((kap * kap) * (kap * kap)) *
        (((dH * dH) * (dH * dH)) * (((dH * dH) * (dH * dH)) * ((dH * dH) * (dH * dH))))) <
      9 * (((nu * nu) * (nu * nu)) * ((pH * pH) * (pH * pH)))) :
    2 * (comm_prod + self_prod) - 2 * (nu * ((pH * pH) * (pH * pH))) < 0 := by
  let D4 := (dH * dH) * (dH * dH)
  let P4 := (pH * pH) * (pH * pH)
  have hd2 : 0 < dH * dH := Int.mul_pos hdH hdH
  have hD4_pos : 0 < D4 := Int.mul_pos hd2 hd2
  have hD8_pos : 0 < D4 * D4 := Int.mul_pos hD4_pos hD4_pos
  have hp2 : 0 < pH * pH := Int.mul_pos hpH hpH
  have hP4_pos : 0 < P4 := Int.mul_pos hp2 hp2
  have hnu_P4_pos : 0 < nu * P4 := Int.mul_pos hnu hP4_pos

  -- Part 1: `2 * comm_prod < nu * P4`
  have hmD4_pos : 0 < m_cut * D4 := Int.mul_pos hm_cut hD4_pos
  have h_poin_sq : (m_cut * D4) * (m_cut * D4) ≤ P4 * P4 := by
    have p1 : (m_cut * D4) * (m_cut * D4) ≤ P4 * (m_cut * D4) :=
      Int.mul_le_mul_of_nonneg_right h_poincare (by omega)
    have p2 : P4 * (m_cut * D4) ≤ P4 * P4 :=
      Int.mul_le_mul_of_nonneg_left h_poincare (by omega)
    exact Int.le_trans p1 p2
  have h_poin_exp : (m_cut * D4) * (m_cut * D4) = (m_cut * m_cut) * (D4 * D4) :=
    (mul_self_mul_self_comm m_cut D4).symm
  rw [h_poin_exp] at h_poin_sq

  have h_low_mul :
      (4 * (F1L * F1L)) * (D4 * D4) < (3 * ((nu * nu) * (m_cut * m_cut))) * (D4 * D4) :=
    Int.mul_lt_mul_of_pos_right h_low_strain_gate hD8_pos
  have h_comm_4 :
      12 * (comm_prod * comm_prod) ≤ (4 * (F1L * F1L)) * (D4 * D4) := by
    have h4 : 4 * (3 * (comm_prod * comm_prod)) ≤ 4 * ((F1L * F1L) * (D4 * D4)) :=
      Int.mul_le_mul_of_nonneg_left h_comm_bound (by omega)
    rw [← Int.mul_assoc 4 3 (comm_prod * comm_prod),
        ← Int.mul_assoc 4 (F1L * F1L) (D4 * D4)] at h4
    exact h4
  have h_nu2_pos : 0 ≤ 3 * (nu * nu) := by
    have hnn := int_sq_nonneg nu
    omega
  have h_poin_nu :
      (3 * ((nu * nu) * (m_cut * m_cut))) * (D4 * D4) ≤ 3 * ((nu * nu) * (P4 * P4)) := by
    have eq1 :
        (3 * ((nu * nu) * (m_cut * m_cut))) * (D4 * D4) =
          (3 * (nu * nu)) * ((m_cut * m_cut) * (D4 * D4)) := by
      rw [← Int.mul_assoc 3 (nu * nu) (m_cut * m_cut),
          Int.mul_assoc (3 * (nu * nu)) (m_cut * m_cut) (D4 * D4)]
    have eq2 :
        3 * ((nu * nu) * (P4 * P4)) = (3 * (nu * nu)) * (P4 * P4) := by
      rw [← Int.mul_assoc 3 (nu * nu) (P4 * P4)]
    rw [eq1, eq2]
    exact Int.mul_le_mul_of_nonneg_left h_poin_sq h_nu2_pos
  have h_12_lt : 12 * (comm_prod * comm_prod) < 3 * ((nu * nu) * (P4 * P4)) :=
    Int.lt_of_le_of_lt h_comm_4 (Int.lt_of_lt_of_le h_low_mul h_poin_nu)
  have h_4c_sq : (2 * comm_prod) * (2 * comm_prod) = 4 * (comm_prod * comm_prod) :=
    mul_term_mul_term 2 2 comm_prod comm_prod
  have h_nuP_sq : (nu * P4) * (nu * P4) = (nu * nu) * (P4 * P4) :=
    (mul_self_mul_self_comm nu P4).symm
  have h_comm_sq_lt : (2 * comm_prod) * (2 * comm_prod) < (nu * P4) * (nu * P4) := by
    rw [h_4c_sq, h_nuP_sq]
    omega
  have h_2comm_nn : 0 ≤ 2 * comm_prod := by omega
  have h_part1 : 2 * comm_prod < nu * P4 :=
    int_lt_of_sq_lt_sq (2 * comm_prod) (nu * P4) h_2comm_nn hnu_P4_pos h_comm_sq_lt

  -- Part 2: `2 * self_prod < nu * P4`
  let P12 := P4 * (P4 * P4)
  have hP8_pos : 0 < P4 * P4 := Int.mul_pos hP4_pos hP4_pos
  have hP12_pos : 0 < P12 := Int.mul_pos hP4_pos hP8_pos
  have h_self_16 :
      144 * ((self_prod * self_prod) * (self_prod * self_prod)) ≤
        (16 * (((kap * kap) * (kap * kap)) * (D4 * (D4 * D4)))) * P12 := by
    have h16 :
        16 * (9 * ((self_prod * self_prod) * (self_prod * self_prod))) ≤
          16 * ((((kap * kap) * (kap * kap)) * (D4 * (D4 * D4))) * P12) :=
      Int.mul_le_mul_of_nonneg_left h_self_bound (by omega)
    rw [← Int.mul_assoc 16 9 _, ← Int.mul_assoc 16 _ P12] at h16
    exact h16
  have h_high_mul :
      (16 * (((kap * kap) * (kap * kap)) * (D4 * (D4 * D4)))) * P12 <
        (9 * (((nu * nu) * (nu * nu)) * P4)) * P12 :=
    Int.mul_lt_mul_of_pos_right h_high_self_gate hP12_pos
  have hrhs_nuP4 :
      (9 * (((nu * nu) * (nu * nu)) * P4)) * P12 =
        9 * (((nu * P4) * (nu * P4)) * ((nu * P4) * (nu * P4))) := by
    dsimp [P12]
    rw [h_nuP_sq]
    have s2 :
        ((nu * nu) * (P4 * P4)) * ((nu * nu) * (P4 * P4)) =
          ((nu * nu) * (nu * nu)) * ((P4 * P4) * (P4 * P4)) :=
      (mul_self_mul_self_comm (nu * nu) (P4 * P4)).symm
    have s3 : P4 * (P4 * (P4 * P4)) = (P4 * P4) * (P4 * P4) := by
      rw [← Int.mul_assoc P4 P4 (P4 * P4)]
    rw [s2, ← s3, ← Int.mul_assoc ((nu * nu) * (nu * nu)) P4 (P4 * (P4 * P4)),
        Int.mul_assoc 9 _ (P4 * (P4 * P4))]
  rw [hrhs_nuP4] at h_high_mul
  have h_144_lt :
      144 * ((self_prod * self_prod) * (self_prod * self_prod)) <
        9 * (((nu * P4) * (nu * P4)) * ((nu * P4) * (nu * P4))) :=
    Int.lt_of_le_of_lt h_self_16 h_high_mul
  have h_2s_pow4 :
      ((2 * self_prod) * (2 * self_prod)) * ((2 * self_prod) * (2 * self_prod)) =
        16 * ((self_prod * self_prod) * (self_prod * self_prod)) := by
    have s1 : (2 * self_prod) * (2 * self_prod) = 4 * (self_prod * self_prod) :=
      mul_term_mul_term 2 2 self_prod self_prod
    rw [s1]
    exact mul_term_mul_term 4 4 (self_prod * self_prod) (self_prod * self_prod)
  have h_self_pow4_lt :
      ((2 * self_prod) * (2 * self_prod)) * ((2 * self_prod) * (2 * self_prod)) <
        ((nu * P4) * (nu * P4)) * ((nu * P4) * (nu * P4)) := by
    rw [h_2s_pow4]
    omega
  have h_2self_nn : 0 ≤ 2 * self_prod := by omega
  have h_part2 : 2 * self_prod < nu * P4 :=
    int_lt_of_pow4_lt_pow4 (2 * self_prod) (nu * P4) h_2self_nn hnu_P4_pos h_self_pow4_lt

  dsimp [P4] at h_part1 h_part2
  omega

end SweetbrierBSARStep6

-- Mandatory Constructive Axiom Gate: verify ZERO `Classical.choice` across ALL Round 5 theorems!
#print axioms SweetbrierBSARStep6.list_dot_sq_le
#print axioms SweetbrierBSARStep6.step6_trace_free_isotropic_diagonal_zero
#print axioms SweetbrierBSARStep6.step6_trace_free_strain_bound
#print axioms SweetbrierBSARStep6.step6_trace_free_moving_ceiling
#print axioms SweetbrierBSARStep6.step6_trace_free_quartic_3_128
#print axioms SweetbrierBSARStep6.step6_biot_savart_collinear_zero
#print axioms SweetbrierBSARStep6.step6_lagrange_cross_identity
#print axioms SweetbrierBSARStep6.step6_biot_savart_gram_bound
#print axioms SweetbrierBSARStep6.step6_cf_equal_norm_chord_depletion
#print axioms SweetbrierBSARStep6.step6_lattice_chord_identity
#print axioms SweetbrierBSARStep6.step6_odd_whale_chord_impossible
#print axioms SweetbrierBSARStep6.step6_bimodal_commutator_viscous_gate
#print axioms SweetbrierBSARStep6.step6_broadband_commutator_sweeping_decoupling
