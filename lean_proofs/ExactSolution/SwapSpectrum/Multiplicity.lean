import ExactSolution.SwapSpectrum.PairBasis
import ExactSolution.DegreeFloor

/-! Exact multiplicities of the tensor swap signs. -/

namespace ExactSolution.SwapSpectrum

open scoped BigOperators
open Polynomial

def minusCount {r Q : ℕ} (alpha : Fin Q → EigenIndex r) : ℕ :=
  (Finset.univ.filter fun s => (alpha s).isRight).card

theorem minusCount_le {r Q : ℕ} (alpha : Fin Q → EigenIndex r) : minusCount alpha ≤ Q := by
  calc
    minusCount alpha ≤ (Finset.univ : Finset (Fin Q)).card := Finset.card_filter_le _ _
    _ = Q := by simp

def eigenMultiplicity (r Q j : ℕ) : ℕ :=
  Fintype.card {alpha : Fin Q → EigenIndex r // minusCount alpha = j}

theorem sign_generating_polynomial (r Q : ℕ) :
    (∑ alpha : Fin Q → EigenIndex r, (X : ℚ[X]) ^ minusCount alpha) =
      (C (Fintype.card (StrictPair r) : ℚ) * X + C (Fintype.card (PlusIndex r) : ℚ)) ^ Q := by
  have hfactor : (∑ a : EigenIndex r, if a.isRight then (X : ℚ[X]) else 1) =
      C (Fintype.card (StrictPair r) : ℚ) * X + C (Fintype.card (PlusIndex r) : ℚ) := by
    simp only [EigenIndex, Fintype.sum_sum_type, Sum.isRight_inl, Sum.isRight_inr,
      Bool.false_eq_true, if_false, if_true, Finset.sum_const,
      Finset.card_univ, nsmul_eq_mul, mul_one]
    simp only [map_natCast]
    ring
  calc
    (∑ alpha : Fin Q → EigenIndex r, (X : ℚ[X]) ^ minusCount alpha) =
        ∑ alpha : Fin Q → EigenIndex r, ∏ s : Fin Q,
          if (alpha s).isRight then (X : ℚ[X]) else 1 := by
      apply Finset.sum_congr rfl
      intro alpha _
      simp [minusCount, Finset.prod_ite]
    _ = ∏ _s : Fin Q, ∑ a : EigenIndex r, if a.isRight then (X : ℚ[X]) else 1 :=
      (Fintype.prod_sum (fun (_s : Fin Q) (a : EigenIndex r) =>
        if a.isRight then (X : ℚ[X]) else 1)).symm
    _ = _ := by rw [hfactor]; simp

theorem coeff_sign_generating (r Q j : ℕ) :
    (∑ alpha : Fin Q → EigenIndex r, (X : ℚ[X]) ^ minusCount alpha).coeff j =
      (eigenMultiplicity r Q j : ℚ) := by
  rw [Polynomial.finset_sum_coeff]
  simp_rw [Polynomial.coeff_X_pow]
  have hsum := Finset.sum_boole (R := ℚ)
    (fun alpha : Fin Q → EigenIndex r => minusCount alpha = j) Finset.univ
  simpa only [eigenMultiplicity, Fintype.card_subtype, eq_comm] using hsum

private theorem coeff_linear_pow (a b : ℚ) (Q j : ℕ) (hj : j ≤ Q) :
    ((C b * X + C a) ^ Q).coeff j = (Q.choose j : ℚ) * b ^ j * a ^ (Q - j) := by
  have hterm (i : ℕ) : (C b * X) ^ i * (C a) ^ (Q - i) * (Q.choose i : ℚ[X]) =
      C ((Q.choose i : ℚ) * b ^ i * a ^ (Q - i)) * X ^ i := by
    simp only [map_mul, map_pow, map_natCast, mul_pow]
    ring
  rw [add_pow, Polynomial.finset_sum_coeff]
  simp_rw [hterm, Polynomial.coeff_C_mul_X_pow]
  rw [Finset.sum_eq_single j]
  · simp
  · intro i _ hij
    simp [Ne.symm hij]
  · intro hmissing
    exact (hmissing (Finset.mem_range.mpr (by omega))).elim

theorem eigenMultiplicity_eq_choose (r Q j : ℕ) (hj : j ≤ Q) :
    eigenMultiplicity r Q j = Q.choose j * Fintype.card (StrictPair r) ^ j *
      Fintype.card (PlusIndex r) ^ (Q - j) := by
  have h := congrArg (fun p : ℚ[X] => p.coeff j) (sign_generating_polynomial r Q)
  dsimp only at h
  rw [coeff_sign_generating, coeff_linear_pow _ _ Q j hj] at h
  exact_mod_cast h

/-- The exact multiplicity formula includes weights beyond the tensor length. -/
theorem eigenMultiplicity_eq_choose_all (r Q j : ℕ) :
    eigenMultiplicity r Q j = Q.choose j * Fintype.card (StrictPair r) ^ j *
      Fintype.card (PlusIndex r) ^ (Q - j) := by
  by_cases hj : j ≤ Q
  · exact eigenMultiplicity_eq_choose r Q j hj
  · letI : IsEmpty {alpha : Fin Q → EigenIndex r // minusCount alpha = j} :=
      ⟨by
        rintro ⟨alpha, heq⟩
        apply hj
        rw [← heq]
        exact minusCount_le alpha⟩
    simp [eigenMultiplicity, Nat.choose_eq_zero_of_lt (Nat.lt_of_not_ge hj)]

/-- Actual tensor-eigenvector multiplicities normalize to the binomial masses. -/
theorem minusCount_card_normalized (r Q j : ℕ) (hr : 0 < r) (hj : j ≤ Q) :
    (Fintype.card {alpha : Fin Q → EigenIndex r // minusCount alpha = j} : ℝ) =
      (r : ℝ) ^ (2 * Q) * binomialMass Q (((r : ℝ) - 1) / (2 * r)) j := by
  let a : ℝ := Fintype.card (PlusIndex r)
  let b : ℝ := Fintype.card (StrictPair r)
  let p : ℝ := ((r : ℝ) - 1) / (2 * r)
  have hrr : 0 < (r : ℝ) := by exact_mod_cast hr
  have hrel : (r : ℝ) + 2 * b = (r : ℝ) * r := by
    dsimp only [b]
    exact_mod_cast strictPair_card_relation r
  have hplus : a = (r : ℝ) + b := by
    simp [a, b, PlusIndex, Fintype.card_sum]
  have hb : b = (r : ℝ) ^ 2 * p := by
    calc
      b = (r : ℝ) * (r - 1) / 2 := by nlinarith [hrel]
      _ = (r : ℝ) ^ 2 * p := by
        dsimp [p]
        field_simp [hrr.ne']
  have ha : a = (r : ℝ) ^ 2 * (1 - p) := by
    calc
      a = (r : ℝ) + b := hplus
      _ = (r : ℝ) ^ 2 - b := by nlinarith [hrel]
      _ = (r : ℝ) ^ 2 * (1 - p) := by rw [hb]; ring
  have hpow : ((r : ℝ) ^ 2) ^ j * ((r : ℝ) ^ 2) ^ (Q - j) =
      (r : ℝ) ^ (2 * Q) := by
    rw [← pow_add, Nat.add_sub_of_le hj, ← pow_mul]
  have hmul : b ^ j * a ^ (Q - j) =
      (r : ℝ) ^ (2 * Q) * p ^ j * (1 - p) ^ (Q - j) := by
    rw [hb, ha, mul_pow, mul_pow]
    calc
      ((r : ℝ) ^ 2) ^ j * p ^ j *
          (((r : ℝ) ^ 2) ^ (Q - j) * (1 - p) ^ (Q - j)) =
          (((r : ℝ) ^ 2) ^ j * ((r : ℝ) ^ 2) ^ (Q - j)) * p ^ j *
            (1 - p) ^ (Q - j) := by ring
      _ = _ := by rw [hpow]
  change (eigenMultiplicity r Q j : ℝ) = _
  rw [eigenMultiplicity_eq_choose r Q j hj]
  push_cast
  change (Q.choose j : ℝ) * b ^ j * a ^ (Q - j) =
    (r : ℝ) ^ (2 * Q) * binomialMass Q p j
  rw [mul_assoc, hmul]
  unfold binomialMass
  ring

end ExactSolution.SwapSpectrum
