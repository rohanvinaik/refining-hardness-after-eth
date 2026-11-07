import ExactSolution.SwapSpectrum.Operators
import ExactSolution.SwapSpectrum.Multiplicity

namespace ExactSolution.SwapSpectrum

open scoped BigOperators
open Polynomial

theorem signProduct_eq (r Q : ℕ) (alpha : EigenHistory r Q) :
    signProduct alpha = (-1 : ℚ) ^ minusCount alpha := by
  have hs : ∀ s : Fin Q, eigenSign (alpha s) =
      if (alpha s).isRight then (-1 : ℚ) else 1 := by
    intro s
    cases alpha s <;> rfl
  unfold signProduct
  simp_rw [hs]
  rw [Finset.prod_ite]
  simp [minusCount]

theorem weightEigenvalue_eq (r Q : ℕ) (alpha : EigenHistory r Q) :
    weightEigenvalue alpha = (minusCount alpha : ℚ) := by
  have hs : ∀ s : Fin Q, (1 - eigenSign (alpha s)) / 2 =
      if (alpha s).isRight then (1 : ℚ) else 0 := by
    intro s
    cases alpha s <;> norm_num [eigenSign]
  unfold weightEigenvalue
  simp_rw [hs]
  exact Finset.sum_boole _ _

theorem swapM0_tensorBasis_by_count (r Q : ℕ) (f : ℚ[X]) (alpha : EigenHistory r Q) :
    swapM0 r Q f (tensorBasis r Q alpha) =
      ((-1 : ℚ) ^ minusCount alpha * f.eval (minusCount alpha : ℚ)) •
        tensorBasis r Q alpha := by
  rw [swapM0_tensorBasis, signProduct_eq, weightEigenvalue_eq]

theorem swapV0_tensorBasis_by_count (r Q : ℕ) (alpha : EigenHistory r Q) :
    swapV0 r Q (tensorBasis r Q alpha) =
      (-1 : ℚ) ^ minusCount alpha • tensorBasis r Q alpha := by
  rw [swapV0_tensorBasis, signProduct_eq]

theorem swapW0_tensorBasis_by_count (r Q : ℕ) (alpha : EigenHistory r Q) :
    swapW0 r Q (tensorBasis r Q alpha) =
      (minusCount alpha : ℚ) • tensorBasis r Q alpha := by
  rw [swapW0_tensorBasis, weightEigenvalue_eq]

theorem swapPi_commute (r Q : ℕ) (s t : Fin Q) :
    swapPi r Q s * swapPi r Q t = swapPi r Q t * swapPi r Q s := by
  apply (tensorBasis r Q).ext
  intro alpha
  simp only [Module.End.mul_apply, swapPi_tensorBasis, map_smul, smul_smul]
  congr 1
  ring

theorem swapPi_sq (r Q : ℕ) (s : Fin Q) :
    swapPi r Q s * swapPi r Q s = LinearMap.id := by
  apply (tensorBasis r Q).ext
  intro alpha
  simp only [Module.End.mul_apply, swapPi_tensorBasis, map_smul, smul_smul,
    LinearMap.id_apply]
  cases alpha s <;> simp [eigenSign]

theorem sign_mul_fixed_iff (j : ℕ) (x : ℚ) :
    (-1 : ℚ) ^ j * x = 1 ↔ x = (-1 : ℚ) ^ j := by
  have hs : (-1 : ℚ) ^ j * (-1 : ℚ) ^ j = 1 := by
    rw [← mul_pow]
    norm_num
  constructor
  · intro h
    calc
      x = ((-1 : ℚ) ^ j * (-1 : ℚ) ^ j) * x := by rw [hs]; simp
      _ = (-1 : ℚ) ^ j * ((-1 : ℚ) ^ j * x) := by ring
      _ = (-1 : ℚ) ^ j := by rw [h]; ring
  · intro h
    simpa [h] using hs

theorem swap_rank_eq_count (r Q : ℕ) (f : ℚ[X]) :
    Module.finrank ℚ (LinearMap.id - swapM0 r Q f).range =
      (Finset.univ.filter fun alpha : EigenHistory r Q =>
        f.eval (minusCount alpha : ℚ) ≠ (-1 : ℚ) ^ minusCount alpha).card := by
  rw [swap_rank_eq_eigen_history_count]
  congr 1
  ext alpha
  simp only [Finset.mem_filter, Finset.mem_univ, true_and,
    signProduct_eq, weightEigenvalue_eq, ne_eq, sign_mul_fixed_iff]

theorem swap_rank_eq_sum_fiber_card (r Q : ℕ) (f : ℚ[X]) :
    Module.finrank ℚ (LinearMap.id - swapM0 r Q f).range =
      ∑ j ∈ (Finset.range (Q + 1)).filter (fun j : ℕ => f.eval (j : ℚ) ≠ (-1 : ℚ) ^ j),
        Fintype.card {alpha : EigenHistory r Q // minusCount alpha = j} := by
  classical
  rw [swap_rank_eq_count]
  let badAlpha : Finset (EigenHistory r Q) := Finset.univ.filter fun alpha =>
    f.eval (minusCount alpha : ℚ) ≠ (-1 : ℚ) ^ minusCount alpha
  let badWeight : Finset ℕ := (Finset.range (Q + 1)).filter fun j : ℕ =>
    f.eval (j : ℚ) ≠ (-1 : ℚ) ^ j
  have hmap : Set.MapsTo (minusCount (r := r) (Q := Q))
      (badAlpha : Set (EigenHistory r Q)) (badWeight : Set ℕ) := by
    intro alpha halpha
    have ha : f.eval (minusCount alpha : ℚ) ≠ (-1 : ℚ) ^ minusCount alpha :=
      (Finset.mem_filter.mp halpha).2
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by
      have := minusCount_le alpha
      omega), ha⟩
  change badAlpha.card = ∑ j ∈ badWeight, _
  rw [Finset.card_eq_sum_card_fiberwise hmap]
  apply Finset.sum_congr rfl
  intro j hj
  have hjbad : f.eval (j : ℚ) ≠ (-1 : ℚ) ^ j := (Finset.mem_filter.mp hj).2
  rw [Fintype.card_subtype]
  congr 1
  ext alpha
  simp only [badAlpha, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · exact fun h => h.2
  · intro h
    exact ⟨by simpa [h] using hjbad, h⟩

theorem physical_finrank (r Q : ℕ) :
    Module.finrank ℚ (History r Q → ℚ) = r ^ (2 * Q) := by
  simp [History, Pair, ← pow_two, ← pow_mul]

end ExactSolution.SwapSpectrum
