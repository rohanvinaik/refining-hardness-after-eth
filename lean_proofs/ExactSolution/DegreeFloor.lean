import ExactSolution.PolynomialAgreement
import ExactSolution.BinomialMode

/-!
# Degree floor under the swap construction's fixing contract

The failure mass is computed from the explicit binomial formula and the
polynomial's agreement set. The external matrix construction enters only in
identifying its unfixed-direction count with `D * swapFailureMass`.
-/

namespace ExactSolution

open Polynomial
open scoped BigOperators

noncomputable def negativeParityMass (Q : ℕ) (p : ℝ) : ℝ :=
  ∑ j ∈ (Finset.range (Q + 1)).filter (fun j : ℕ => (-1 : ℚ) ^ j = -1), binomialMass Q p j

noncomputable def positiveParityMass (Q : ℕ) (p : ℝ) : ℝ :=
  ∑ j ∈ (Finset.range (Q + 1)).filter (fun j : ℕ => (-1 : ℚ) ^ j = 1), binomialMass Q p j

noncomputable def swapFailureMass (f : ℚ[X]) (Q : ℕ) (p : ℝ) : ℝ :=
  ∑ j ∈ (Finset.range (Q + 1)).filter (fun j : ℕ => f.eval (j : ℚ) ≠ (-1 : ℚ) ^ j),
    binomialMass Q p j

theorem signed_binomial_sum (Q : ℕ) (p : ℝ) :
    (∑ j ∈ Finset.range (Q + 1), (-1 : ℝ) ^ j * binomialMass Q p j) =
      (1 - 2 * p) ^ Q := by
  calc
    _ = ∑ j ∈ Finset.range (Q + 1),
        (-p) ^ j * (1 - p) ^ (Q - j) * (Q.choose j : ℝ) := by
      apply Finset.sum_congr rfl
      intro j _
      rw [show -p = (-1 : ℝ) * p by ring, mul_pow]
      unfold binomialMass
      ring
    _ = (-p + (1 - p)) ^ Q := (add_pow (-p) (1 - p) Q).symm
    _ = (1 - 2 * p) ^ Q := by congr 1; ring

theorem parity_mass_sum (Q : ℕ) (p : ℝ) :
    positiveParityMass Q p + negativeParityMass Q p = 1 := by
  unfold positiveParityMass negativeParityMass
  simp only [Finset.sum_filter]
  rw [← Finset.sum_add_distrib]
  calc
    _ = ∑ j ∈ Finset.range (Q + 1), binomialMass Q p j := by
      apply Finset.sum_congr rfl
      intro j _
      rcases alternating_sign_eq_one_or_neg_one j with h | h <;> norm_num [h]
    _ = 1 := Binomial.sum_mass Q p

theorem parity_mass_difference (Q : ℕ) (p : ℝ) :
    positiveParityMass Q p - negativeParityMass Q p = (1 - 2 * p) ^ Q := by
  unfold positiveParityMass negativeParityMass
  simp only [Finset.sum_filter]
  rw [← Finset.sum_sub_distrib]
  calc
    _ = ∑ j ∈ Finset.range (Q + 1), (-1 : ℝ) ^ j * binomialMass Q p j := by
      apply Finset.sum_congr rfl
      intro j _
      rcases alternating_sign_eq_one_or_neg_one j with h | h
      · have hreal : (-1 : ℝ) ^ j = 1 := by exact_mod_cast h
        norm_num [h, hreal]
      · have hreal : (-1 : ℝ) ^ j = -1 := by exact_mod_cast h
        norm_num [h, hreal]
    _ = _ := signed_binomial_sum Q p

theorem parity_mass_lower_bounds {Q : ℕ} {p : ℝ} (hQ : 0 < Q)
    (hp : 1 / 4 ≤ p) (hp' : p ≤ 1 / 2) :
    1 / 4 ≤ negativeParityMass Q p ∧ 1 / 2 ≤ positiveParityMass Q p := by
  have ha0 : 0 ≤ 1 - 2 * p := by linarith
  have ha1 : 1 - 2 * p ≤ 1 := by linarith
  have haHalf : 1 - 2 * p ≤ 1 / 2 := by linarith
  have hpow : (1 - 2 * p) ^ Q ≤ 1 / 2 := by
    calc
      _ ≤ (1 - 2 * p) ^ 1 := pow_le_pow_of_le_one ha0 ha1 hQ
      _ ≤ 1 / 2 := by simpa using haHalf
  have hnonneg : 0 ≤ (1 - 2 * p) ^ Q := pow_nonneg ha0 _
  have hsum := parity_mass_sum Q p
  have hdiff := parity_mass_difference Q p
  constructor <;> linarith

theorem constant_plus_failure (Q : ℕ) (p : ℝ) :
    swapFailureMass (C 1) Q p = negativeParityMass Q p := by
  unfold swapFailureMass negativeParityMass
  simp only [Polynomial.eval_C, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro j _
  rcases alternating_sign_eq_one_or_neg_one j with h | h <;> norm_num [h]

theorem constant_minus_failure (Q : ℕ) (p : ℝ) :
    swapFailureMass (C (-1)) Q p = positiveParityMass Q p := by
  unfold swapFailureMass positiveParityMass
  simp only [Polynomial.eval_C, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro j _
  rcases alternating_sign_eq_one_or_neg_one j with h | h <;> norm_num [h]

theorem agreement_add_failure (f : ℚ[X]) (Q : ℕ) (p : ℝ) :
    (∑ j ∈ parityAgreement f (Finset.range (Q + 1)), binomialMass Q p j) +
      swapFailureMass f Q p = 1 := by
  unfold parityAgreement swapFailureMass
  exact (Finset.sum_filter_add_sum_filter_not _ _ _).trans (Binomial.sum_mass Q p)

theorem swap_failure_lower_bound (f : ℚ[X]) {Q R : ℕ} {p : ℝ}
    (hQ : 0 < Q) (hp : 1 / 4 ≤ p) (hp' : p ≤ 1 / 2)
    (hdegree : f.natDegree < R) (hplus : f ≠ C 1) (hminus : f ≠ C (-1)) :
    1 - ((2 * R - 2 : ℕ) : ℝ) * (2 / Real.sqrt Q) ≤ swapFailureMass f Q p := by
  have hcard := card_parityAgreement_le f (Finset.range (Q + 1)) R hdegree hplus hminus
  have hcardReal : ((parityAgreement f (Finset.range (Q + 1))).card : ℝ) ≤
      ((2 * R - 2 : ℕ) : ℝ) := by exact_mod_cast hcard
  have hmass : (∑ j ∈ parityAgreement f (Finset.range (Q + 1)), binomialMass Q p j) ≤
      ((2 * R - 2 : ℕ) : ℝ) * (2 / Real.sqrt Q) := by
    calc
      _ ≤ ∑ _j ∈ parityAgreement f (Finset.range (Q + 1)), 2 / Real.sqrt Q :=
        Finset.sum_le_sum (fun j _ => binomial_mass_le hQ hp hp' j)
      _ = ((parityAgreement f (Finset.range (Q + 1))).card : ℝ) *
          (2 / Real.sqrt Q) := by simp
      _ ≤ _ := mul_le_mul_of_nonneg_right hcardReal (by positivity)
  have hsum := agreement_add_failure f Q p
  linarith

theorem degree_floor_from_failure (f : ℚ[X]) (r Q R : ℕ) (tau : ℝ)
    (hr : 2 ≤ r) (hQ : 0 < Q) (hdegree : f.natDegree < R) (htau : tau ≤ 1)
    (hbudget : swapFailureMass f Q (((r : ℝ) - 1) / (2 * r)) ≤ tau / (3 * r)) :
    1 + 5 * Real.sqrt Q / 24 ≤ (R : ℝ) := by
  let p : ℝ := ((r : ℝ) - 1) / (2 * r)
  have hrReal : (2 : ℝ) ≤ r := by exact_mod_cast hr
  have hden : 0 < (2 : ℝ) * r := by positivity
  have hp : 1 / 4 ≤ p := by
    dsimp [p]
    apply (le_div_iff₀ hden).mpr
    nlinarith
  have hp' : p ≤ 1 / 2 := by
    dsimp [p]
    apply (div_le_iff₀ hden).mpr
    nlinarith
  have hcap : tau / (3 * (r : ℝ)) ≤ 1 / 6 := by
    apply (div_le_iff₀ (show 0 < (3 : ℝ) * r by positivity)).mpr
    nlinarith
  have hupper : swapFailureMass f Q p ≤ 1 / 6 := hbudget.trans hcap
  have hparity := parity_mass_lower_bounds hQ hp hp'
  have hplus : f ≠ C 1 := by
    intro hf
    rw [hf, constant_plus_failure] at hupper
    linarith [hparity.1]
  have hminus : f ≠ C (-1) := by
    intro hf
    rw [hf, constant_minus_failure] at hupper
    linarith [hparity.2]
  have hlower := swap_failure_lower_bound f hQ hp hp' hdegree hplus hminus
  have hR : 1 ≤ R := by omega
  have hcast : ((2 * R - 2 : ℕ) : ℝ) = 2 * (R : ℝ) - 2 := by
    rw [Nat.cast_sub (by omega), Nat.cast_mul]
    norm_num
  rw [hcast, ← mul_div_assoc] at hlower
  have hratio : 5 / 6 ≤ ((2 * (R : ℝ) - 2) * 2) / Real.sqrt Q := by linarith
  have hsqrt : 0 < Real.sqrt Q := Real.sqrt_pos.mpr (by exact_mod_cast hQ)
  have hscaled := (le_div_iff₀ hsqrt).mp hratio
  nlinarith

/-- A positive scaling factor cancels from the failure-mass budget, giving
the same degree floor as the unscaled bound. -/
theorem swap_degree_floor (f : ℚ[X]) (r Q R : ℕ) (tau D : ℝ)
    (hr : 2 ≤ r) (hQ : 0 < Q) (hD : 0 < D)
    (hdegree : f.natDegree < R) (htau : tau ≤ 1)
    (haux : D * swapFailureMass f Q (((r : ℝ) - 1) / (2 * r)) ≤ D * tau / (3 * r)) :
    1 + 5 * Real.sqrt Q / 24 ≤ (R : ℝ) := by
  apply degree_floor_from_failure f r Q R tau hr hQ hdegree htau
  apply (mul_le_mul_iff_right₀ hD).mp
  simpa only [mul_div_assoc] using haux

noncomputable def selectedWindowMass (Q : ℕ) (p : ℝ) (window : Finset ℕ) : ℝ :=
  ∑ j ∈ (Finset.range (Q + 1)).filter (fun j => j ∉ window), binomialMass Q p j

/-- Measuring every direction outside an interpolation window can overcount
actual unfixed directions; the needed implication is this inequality. -/
theorem swap_failure_le_selected_window (f : ℚ[X]) (Q : ℕ) (p : ℝ)
    (window : Finset ℕ) (hp : 0 ≤ p) (hp' : p ≤ 1)
    (hfixes : ∀ j ∈ window, f.eval (j : ℚ) = (-1 : ℚ) ^ j) :
    swapFailureMass f Q p ≤ selectedWindowMass Q p window := by
  unfold swapFailureMass selectedWindowMass
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro j hj
    obtain ⟨hjrange, hfail⟩ := Finset.mem_filter.mp hj
    exact Finset.mem_filter.mpr ⟨hjrange, fun hjwindow => hfail (hfixes j hjwindow)⟩
  · intro j _ _
    exact Binomial.mass_nonneg hp hp' Q j

end ExactSolution
