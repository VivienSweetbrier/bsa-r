/-
  Step2ViscousCooldown.lean
  ==============================================================================
  🅱💲🅰-R × Eleven-Entry Bookkeeping — Formal Appendix (Split Sheet #001, 10% Slot)
  Constructive Lean 4 Verification of the Step-2 Moving Viscous Ceiling,
  BCC Invariant Sublattice Dilation, and BSA-R Fourier-Sparsity Cool-Down Gate.

  Architect & Author: Christopher "Topher" Duguay
  Syndicate: One Big Consortium — Split Sheet #001 (GNU AGPLv3)
  Attestation: probabilistic_structural (Modal Box □ Verified, Zero Classical.choice)
  ==============================================================================
-/

namespace SweetbrierBSAR

/--
  Constructive Linearly Ordered Commutative Ring interface (zero reliance on
  `Classical.choice`, `propext`, or external Mathlib downloads; instantiated
  concretely on `Int` below and satisfied by any constructive rational/dyadic/real
  ordered domain).
-/
class ConstructiveOrderedCommRing (R : Type u) extends Add R, Sub R, Mul R, Neg R, LT R, LE R where
  zero : R
  one  : R
  add_comm  : ∀ a b : R, a + b = b + a
  add_assoc : ∀ a b c : R, (a + b) + c = a + (b + c)
  sub_lt_zero_of_lt : ∀ a b : R, a < b → a - b < zero
  mul_comm  : ∀ a b : R, a * b = b * a
  mul_assoc : ∀ a b c : R, (a * b) * c = a * (b * c)
  left_distrib  : ∀ a b c : R, a * (b + c) = a * b + a * c
  right_distrib : ∀ a b c : R, (a + b) * c = a * c + b * c
  lt_irrefl : ∀ a : R, ¬ (a < a)
  lt_trans  : ∀ a b c : R, a < b → b < c → a < c
  lt_of_le_of_lt : ∀ a b c : R, a ≤ b → b < c → a < c
  lt_of_lt_of_le : ∀ a b c : R, a < b → b ≤ c → a < c
  le_trans  : ∀ a b c : R, a ≤ b → b ≤ c → a ≤ c
  le_of_lt  : ∀ a b : R, a < b → a ≤ b
  lt_or_ge  : ∀ a b : R, (a < b) ∨ (b ≤ a)
  mul_pos   : ∀ a b : R, zero < a → zero < b → zero < a * b
  mul_nonneg : ∀ a b : R, zero ≤ a → zero ≤ b → zero ≤ a * b
  mul_le_mul_of_nonneg_left  : ∀ a b c : R, a ≤ b → zero ≤ c → c * a ≤ c * b
  mul_le_mul_of_nonneg_right : ∀ a b c : R, a ≤ b → zero ≤ c → a * c ≤ b * c
  mul_lt_mul_of_pos_left     : ∀ a b c : R, a < b → zero < c → c * a < c * b
  mul_lt_mul_of_pos_right    : ∀ a b c : R, a < b → zero < c → a * c < b * c
  sq_nonneg : ∀ a : R, zero ≤ a * a

section UniversalStep2Theorems

variable {R : Type u} [O : ConstructiveOrderedCommRing R]

/-- Helper: `(a * b) * (a * b) = (a * a) * (b * b)` in any commutative semigroup. -/
theorem mul_self_mul_self_comm (a b : R) : (a * b) * (a * b) = (a * a) * (b * b) := by
  calc
    (a * b) * (a * b) = a * (b * (a * b)) := O.mul_assoc a b (a * b)
    _ = a * ((b * a) * b) := by rw [← O.mul_assoc b a b]
    _ = a * ((a * b) * b) := by rw [O.mul_comm b a]
    _ = a * (a * (b * b)) := by rw [O.mul_assoc a b b]
    _ = (a * a) * (b * b) := by rw [← O.mul_assoc a a (b * b)]

/--
  Constructive Square-Root-Free Order Reflection:
  If `0 ≤ x`, `0 < y`, and `x * x < y * y`, then `x < y` (zero `Classical.choice`).
-/
theorem lt_of_sq_lt_sq (x y : R)
    (hx : O.zero ≤ x) (hy : O.zero < y) (hsq : x * x < y * y) : x < y := by
  cases O.lt_or_ge x y with
  | inl hlt => exact hlt
  | inr hge =>
    have hy0 : O.zero ≤ y := O.le_of_lt O.zero y hy
    have h1 : y * y ≤ x * y := O.mul_le_mul_of_nonneg_right y x y hge hy0
    have h2 : x * y ≤ x * x := O.mul_le_mul_of_nonneg_left y x x hge hx
    have h3 : y * y ≤ x * x := O.le_trans (y * y) (x * y) (x * x) h1 h2
    have h4 : x * x < x * x := O.lt_of_lt_of_le (x * x) (y * y) (x * x) hsq h3
    exact False.elim (O.lt_irrefl (x * x) h4)

/--
  ==============================================================================
  THEOREM A: Universal Step-2 Moving Viscous Ceiling Inequality
  ==============================================================================
  For ANY divergence-free Fourier mode moments `(F0, F1, F2)` satisfying
  weighted Cauchy-Schwarz `F1 * F1 ≤ F0 * F2` and the square-root-free
  Moving Viscous Ceiling bound `(F0 * F0) * F0 < (nu * nu) * F2`
  (equivalent to `‖u‖_{F^0} < ν √(‖u‖_{F^2} / ‖u‖_{F^0}) = ν K_visc(t)`),
  convective vortex stretching `F0 * F1` is strictly dominated by viscous
  dissipation `nu * F2`, forcing `F0 * F1 - nu * F2 < 0`!
-/
theorem step2_moving_viscous_ceiling
    (F0 F1 F2 nu : R)
    (hF0 : O.zero < F0)
    (hF1 : O.zero ≤ F1)
    (hF2 : O.zero < F2)
    (hnu : O.zero < nu)
    (hCS : F1 * F1 ≤ F0 * F2)
    (hCeil : (F0 * F0) * F0 < (nu * nu) * F2) :
    (F0 * F1) - (nu * F2) < O.zero := by
  have hF0_nonneg : O.zero ≤ F0 := O.le_of_lt O.zero F0 hF0
  have hF0_sq_pos : O.zero < F0 * F0 := O.mul_pos F0 F0 hF0 hF0
  have hF0_sq_nonneg : O.zero ≤ F0 * F0 := O.le_of_lt O.zero (F0 * F0) hF0_sq_pos
  have hX_nonneg : O.zero ≤ F0 * F1 := O.mul_nonneg F0 F1 hF0_nonneg hF1
  have hY_pos : O.zero < nu * F2 := O.mul_pos nu F2 hnu hF2
  -- Step 1: (F0 * F1)^2 = F0^2 * F1^2 ≤ F0^2 * (F0 * F2) = F0^3 * F2
  have h_lhs_eq : (F0 * F1) * (F0 * F1) = (F0 * F0) * (F1 * F1) :=
    mul_self_mul_self_comm F0 F1
  have h_step1 : (F0 * F0) * (F1 * F1) ≤ (F0 * F0) * (F0 * F2) :=
    O.mul_le_mul_of_nonneg_left (F1 * F1) (F0 * F2) (F0 * F0) hCS hF0_sq_nonneg
  have h_assoc1 : (F0 * F0) * (F0 * F2) = ((F0 * F0) * F0) * F2 := by
    rw [← O.mul_assoc (F0 * F0) F0 F2]
  -- Step 2: F0^3 * F2 < (nu^2 * F2) * F2 = (nu * F2)^2
  have h_step2 : ((F0 * F0) * F0) * F2 < ((nu * nu) * F2) * F2 :=
    O.mul_lt_mul_of_pos_right ((F0 * F0) * F0) ((nu * nu) * F2) F2 hCeil hF2
  have h_rhs_eq : ((nu * nu) * F2) * F2 = (nu * F2) * (nu * F2) := by
    rw [O.mul_assoc (nu * nu) F2 F2]
    exact Eq.symm (mul_self_mul_self_comm nu F2)
  -- Combine into (F0 * F1)^2 < (nu * F2)^2
  have h_le1 : (F0 * F1) * (F0 * F1) ≤ ((F0 * F0) * F0) * F2 := by
    rw [h_lhs_eq, ← h_assoc1]
    exact h_step1
  have h_lt2 : ((F0 * F0) * F0) * F2 < (nu * F2) * (nu * F2) := by
    rw [← h_rhs_eq]
    exact h_step2
  have h_sq_lt : (F0 * F1) * (F0 * F1) < (nu * F2) * (nu * F2) :=
    O.lt_of_le_of_lt _ _ _ h_le1 h_lt2
  have h_lt : F0 * F1 < nu * F2 :=
    lt_of_sq_lt_sq (F0 * F1) (nu * F2) hX_nonneg hY_pos h_sq_lt
  exact O.sub_lt_zero_of_lt (F0 * F1) (nu * F2) h_lt

/--
  ==============================================================================
  THEOREM B (Spectral Dilation Part): Sublattice Contraction Gate
  ==============================================================================
  Whenever an invariant sublattice enforces `|k| ≥ k_min > 0` (so `k_min * F1 ≤ F2`),
  any flow satisfying `F0 < k_min * nu` immediately obeys `F0 * F1 - nu * F2 < 0`.
-/
theorem step2_sublattice_contraction
    (F0 F1 F2 nu k_min : R)
    (hF1 : O.zero < F1)
    (hnu : O.zero < nu)
    (hFloor : k_min * F1 ≤ F2)
    (hBall  : F0 < k_min * nu) :
    (F0 * F1) - (nu * F2) < O.zero := by
  have hnu_nonneg : O.zero ≤ nu := O.le_of_lt O.zero nu hnu
  have h1 : F0 * F1 < (k_min * nu) * F1 :=
    O.mul_lt_mul_of_pos_right F0 (k_min * nu) F1 hBall hF1
  have h_rearrange : (k_min * nu) * F1 = nu * (k_min * F1) := by
    calc
      (k_min * nu) * F1 = (nu * k_min) * F1 := by rw [O.mul_comm k_min nu]
      _ = nu * (k_min * F1) := O.mul_assoc nu k_min F1
  have h2 : nu * (k_min * F1) ≤ nu * F2 :=
    O.mul_le_mul_of_nonneg_left (k_min * F1) F2 nu hFloor hnu_nonneg
  have h1' : F0 * F1 < nu * (k_min * F1) := by
    rw [← h_rearrange]; exact h1
  have h_lt : F0 * F1 < nu * F2 :=
    O.lt_of_lt_of_le (F0 * F1) (nu * (k_min * F1)) (nu * F2) h1' h2
  exact O.sub_lt_zero_of_lt (F0 * F1) (nu * F2) h_lt

/--
  ==============================================================================
  THEOREM C: The `BSA-R` Fourier-Sparsity Cool-Down Race
  ==============================================================================
  If `N` active Fourier modes at radius `|k| ≥ R_rad` carry Parseval energy `E`
  (`F0^2 ≤ N * E` and `R_rad^2 * F0 ≤ F2`), then the sparsity condition
      `N * E < nu^2 * R_rad^2`
  constructively forces `(F0 * F1) - (nu * F2) < 0`!
-/
theorem bsar_fourier_sparsity_cooldown
    (F0 F1 F2 nu N E R_rad : R)
    (hF0 : O.zero < F0)
    (hF1 : O.zero ≤ F1)
    (hF2 : O.zero < F2)
    (hnu : O.zero < nu)
    (hCS1 : F1 * F1 ≤ F0 * F2)
    (hCS2 : F0 * F0 ≤ N * E)
    (hShell : (R_rad * R_rad) * F0 ≤ F2)
    (hSparse : N * E < (nu * nu) * (R_rad * R_rad)) :
    (F0 * F1) - (nu * F2) < O.zero := by
  have h_f0_sq_lt : F0 * F0 < (nu * nu) * (R_rad * R_rad) :=
    O.lt_of_le_of_lt (F0 * F0) (N * E) ((nu * nu) * (R_rad * R_rad)) hCS2 hSparse
  have h_f0_cube : (F0 * F0) * F0 < ((nu * nu) * (R_rad * R_rad)) * F0 :=
    O.mul_lt_mul_of_pos_right (F0 * F0) ((nu * nu) * (R_rad * R_rad)) F0 h_f0_sq_lt hF0
  have h_assoc : ((nu * nu) * (R_rad * R_rad)) * F0 = (nu * nu) * ((R_rad * R_rad) * F0) :=
    O.mul_assoc (nu * nu) (R_rad * R_rad) F0
  have h_nu2_pos : O.zero < nu * nu := O.mul_pos nu nu hnu hnu
  have h_nu2_nonneg : O.zero ≤ nu * nu := O.le_of_lt O.zero (nu * nu) h_nu2_pos
  have h_shell_scaled : (nu * nu) * ((R_rad * R_rad) * F0) ≤ (nu * nu) * F2 :=
    O.mul_le_mul_of_nonneg_left ((R_rad * R_rad) * F0) F2 (nu * nu) hShell h_nu2_nonneg
  have h_f0_cube' : (F0 * F0) * F0 < (nu * nu) * ((R_rad * R_rad) * F0) := by
    rw [← h_assoc]; exact h_f0_cube
  have hCeil : (F0 * F0) * F0 < (nu * nu) * F2 :=
    O.lt_of_lt_of_le ((F0 * F0) * F0) ((nu * nu) * ((R_rad * R_rad) * F0)) ((nu * nu) * F2) h_f0_cube' h_shell_scaled
  exact step2_moving_viscous_ceiling F0 F1 F2 nu hF0 hF1 hF2 hnu hCS1 hCeil

end UniversalStep2Theorems

/--
  ==============================================================================
  EXACT INTEGER WAVE-LATTICE PROOFS ON `Z^3 \ {0}` (BCC Parity Sublattice)
  ==============================================================================
  Defines `Λ_BCC = (2ℤ + 1)³ ∪ ((2ℤ)³ \ {(0, 0, 0)})`, containing both 3D
  Taylor-Green and 3D Kida-Pelz octahedral flows, and proves constructively:
    1. `bcc_sublattice_closed`: closed under all non-zero triad sums `p + q = k`,
    2. `bcc_spectral_floor_ge_3`: every `k ∈ Λ_BCC` obeys `kx² + ky² + kz² ≥ 3`.
-/
def IsAllOdd3D (kx ky kz : Int) : Prop :=
  (∃ a : Int, kx = 2 * a + 1) ∧ (∃ b : Int, ky = 2 * b + 1) ∧ (∃ c : Int, kz = 2 * c + 1)

def IsNonZeroAllEven3D (kx ky kz : Int) : Prop :=
  (∃ a : Int, kx = 2 * a) ∧ (∃ b : Int, ky = 2 * b) ∧ (∃ c : Int, kz = 2 * c) ∧
  (kx ≠ 0 ∨ ky ≠ 0 ∨ kz ≠ 0)

def InBCCSublattice (kx ky kz : Int) : Prop :=
  IsAllOdd3D kx ky kz ∨ IsNonZeroAllEven3D kx ky kz

theorem odd_sq_ge_one (x a : Int) (hx : x = 2 * a + 1) : 1 ≤ x * x := by
  have hne : x ≠ 0 := by omega
  by_cases hpos : 1 ≤ x
  · exact Int.mul_le_mul hpos hpos (by omega) (by omega)
  · have hneg : 1 ≤ -x := by omega
    have hmul : 1 * 1 ≤ (-x) * (-x) := Int.mul_le_mul hneg hneg (by omega) (by omega)
    have h_eq : (-x) * (-x) = x * x := by
      calc
        (-x) * (-x) = -(x * (-x)) := Int.neg_mul x (-x)
        _ = -(-(x * x)) := by rw [Int.mul_neg x x]
        _ = x * x := Int.neg_neg (x * x)
    rw [h_eq] at hmul
    exact hmul

theorem even_nz_sq_ge_four (x a : Int) (hx : x = 2 * a) (hne : x ≠ 0) : 4 ≤ x * x := by
  have ha : a ≠ 0 := by omega
  by_cases hapos : 1 ≤ a
  · have hx2 : 2 ≤ x := by omega
    exact Int.mul_le_mul hx2 hx2 (by omega) (by omega)
  · have hxneg : 2 ≤ -x := by omega
    have hmul : 2 * 2 ≤ (-x) * (-x) := Int.mul_le_mul hxneg hxneg (by omega) (by omega)
    have h_eq : (-x) * (-x) = x * x := by
      calc
        (-x) * (-x) = -(x * (-x)) := Int.neg_mul x (-x)
        _ = -(-(x * x)) := by rw [Int.mul_neg x x]
        _ = x * x := Int.neg_neg (x * x)
    rw [h_eq] at hmul
    exact hmul

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

/-- Every wavevector in `Λ_BCC` satisfies `|k|² = kx² + ky² + kz² ≥ 3`. -/
theorem bcc_spectral_floor_ge_3 (kx ky kz : Int) (hk : InBCCSublattice kx ky kz) :
    3 ≤ kx * kx + ky * ky + kz * kz := by
  cases hk with
  | inl hodd =>
    rcases hodd with ⟨⟨a, ha⟩, ⟨b, hb⟩, ⟨c, hc⟩⟩
    have hx : 1 ≤ kx * kx := odd_sq_ge_one kx a ha
    have hy : 1 ≤ ky * ky := odd_sq_ge_one ky b hb
    have hz : 1 ≤ kz * kz := odd_sq_ge_one kz c hc
    omega
  | inr heven =>
    rcases heven with ⟨⟨a, ha⟩, ⟨b, hb⟩, ⟨c, hc⟩, hnz⟩
    have hx0 : 0 ≤ kx * kx := int_sq_nonneg kx
    have hy0 : 0 ≤ ky * ky := int_sq_nonneg ky
    have hz0 : 0 ≤ kz * kz := int_sq_nonneg kz
    cases hnz with
    | inl hkx =>
      have hx4 : 4 ≤ kx * kx := even_nz_sq_ge_four kx a ha hkx
      omega
    | inr hyz =>
      cases hyz with
      | inl hky =>
        have hy4 : 4 ≤ ky * ky := even_nz_sq_ge_four ky b hb hky
        omega
      | inr hkz =>
        have hz4 : 4 ≤ kz * kz := even_nz_sq_ge_four kz c hc hkz
        omega

/-- `Λ_BCC` is closed under all non-zero 3D Navier-Stokes triad sums `p + q = k ≠ 0`. -/
theorem bcc_sublattice_closed
    (px py pz qx qy qz : Int)
    (hp : InBCCSublattice px py pz)
    (hq : InBCCSublattice qx qy qz)
    (hnz : px + qx ≠ 0 ∨ py + qy ≠ 0 ∨ pz + qz ≠ 0) :
    InBCCSublattice (px + qx) (py + qy) (pz + qz) := by
  cases hp with
  | inl hp_odd =>
    rcases hp_odd with ⟨⟨pa, hpa⟩, ⟨pb, hpb⟩, ⟨pc, hpc⟩⟩
    cases hq with
    | inl hq_odd =>
      rcases hq_odd with ⟨⟨qa, hqa⟩, ⟨qb, hqb⟩, ⟨qc, hqc⟩⟩
      right
      exact ⟨⟨pa + qa + 1, by omega⟩, ⟨pb + qb + 1, by omega⟩, ⟨pc + qc + 1, by omega⟩, hnz⟩
    | inr hq_even =>
      rcases hq_even with ⟨⟨qa, hqa⟩, ⟨qb, hqb⟩, ⟨qc, hqc⟩, _⟩
      left
      exact ⟨⟨pa + qa, by omega⟩, ⟨pb + qb, by omega⟩, ⟨pc + qc, by omega⟩⟩
  | inr hp_even =>
    rcases hp_even with ⟨⟨pa, hpa⟩, ⟨pb, hpb⟩, ⟨pc, hpc⟩, _⟩
    cases hq with
    | inl hq_odd =>
      rcases hq_odd with ⟨⟨qa, hqa⟩, ⟨qb, hqb⟩, ⟨qc, hqc⟩⟩
      left
      exact ⟨⟨pa + qa, by omega⟩, ⟨pb + qb, by omega⟩, ⟨pc + qc, by omega⟩⟩
    | inr hq_even =>
      rcases hq_even with ⟨⟨qa, hqa⟩, ⟨qb, hqb⟩, ⟨qc, hqc⟩, _⟩
      right
      exact ⟨⟨pa + qa, by omega⟩, ⟨pb + qb, by omega⟩, ⟨pc + qc, by omega⟩, hnz⟩

/-- Non-vacuity witness: concrete instantiation of `ConstructiveOrderedCommRing` on `Int`. -/
instance : ConstructiveOrderedCommRing Int where
  zero := 0
  one  := 1
  add_comm  := Int.add_comm
  add_assoc := Int.add_assoc
  sub_lt_zero_of_lt := by intro a b h; omega
  mul_comm  := Int.mul_comm
  mul_assoc := Int.mul_assoc
  left_distrib  := Int.mul_add
  right_distrib := Int.add_mul
  lt_irrefl := by intro a h; omega
  lt_trans  := by intro a b c h1 h2; omega
  lt_of_le_of_lt := by intro a b c h1 h2; omega
  lt_of_lt_of_le := by intro a b c h1 h2; omega
  le_trans  := by intro a b c h1 h2; omega
  le_of_lt  := by intro a b h; omega
  lt_or_ge  := by
    intro a b
    exact if h : a < b then Or.inl h else Or.inr (by omega)
  mul_pos    := by intro a b ha hb; exact Int.mul_pos ha hb
  mul_nonneg := by intro a b ha hb; exact Int.mul_nonneg ha hb
  mul_le_mul_of_nonneg_left  := by intro a b c h hc; exact Int.mul_le_mul_of_nonneg_left h hc
  mul_le_mul_of_nonneg_right := by intro a b c h hc; exact Int.mul_le_mul_of_nonneg_right h hc
  mul_lt_mul_of_pos_left     := by intro a b c h hc; exact Int.mul_lt_mul_of_pos_left h hc
  mul_lt_mul_of_pos_right    := by intro a b c h hc; exact Int.mul_lt_mul_of_pos_right h hc
  sq_nonneg := int_sq_nonneg

end SweetbrierBSAR

-- Axiom Audit Gate: verify zero `Classical.choice` across all formal proofs!
#print axioms SweetbrierBSAR.step2_moving_viscous_ceiling
#print axioms SweetbrierBSAR.step2_sublattice_contraction
#print axioms SweetbrierBSAR.bsar_fourier_sparsity_cooldown
#print axioms SweetbrierBSAR.bcc_spectral_floor_ge_3
#print axioms SweetbrierBSAR.bcc_sublattice_closed
