import ExactSolution.MeasurementRank.Basic
import ExactSolution.SwapSpectrum
import ExactSolution.Enumeration

/-!
# Measurements for the concrete swap construction

An arbitrary rational linear measurement map is sufficient for the rank bound.
Its kernel must consist of vectors fixed by the actual coordinate-swap operator.
The proved spectrum identity then supplies the failure mass, and a row budget
gives the polynomial degree floor.
-/

namespace ExactSolution.MeasurementRank

open Polynomial

/-- Every measurement map satisfying the fixing contract must have at least
the actual defect rank of the concrete swap operator. -/
theorem swap_rows_ge_defect_rank (r Q m : ℕ) (f : ℚ[X])
    (C : ((Fin Q → SwapSpectrum.Pair r) → ℚ) →ₗ[ℚ] (Fin m → ℚ))
    (hker : C.ker ≤ (LinearMap.id - SwapSpectrum.swapM0 r Q f).ker) :
    Module.finrank ℚ (LinearMap.id - SwapSpectrum.swapM0 r Q f).range ≤ m := by
  exact measurement_rows_ge_rank C (LinearMap.id - SwapSpectrum.swapM0 r Q f) hker

/-- The exact tensor dimension times the actual parity-failure mass is bounded
by the number of rational measurement rows. -/
theorem swap_failure_mass_le_rows (r Q m : ℕ) (f : ℚ[X]) (hr : 0 < r)
    (C : ((Fin Q → SwapSpectrum.Pair r) → ℚ) →ₗ[ℚ] (Fin m → ℚ))
    (hker : C.ker ≤ (LinearMap.id - SwapSpectrum.swapM0 r Q f).ker) :
    (r : ℝ) ^ (2 * Q) * swapFailureMass f Q (((r : ℝ) - 1) / (2 * r)) ≤ (m : ℝ) := by
  rw [← SwapSpectrum.swap_rank_eq_failure_mass r Q f hr]
  exact_mod_cast swap_rows_ge_defect_rank r Q m f C hker

/-- The same bound stated directly as the fixing condition on zero
measurements. -/
theorem swap_failure_mass_le_rows_of_fixed_kernel (r Q m : ℕ) (f : ℚ[X])
    (hr : 0 < r)
    (C : ((Fin Q → SwapSpectrum.Pair r) → ℚ) →ₗ[ℚ] (Fin m → ℚ))
    (hfixed : ∀ v, C v = 0 → SwapSpectrum.swapM0 r Q f v = v) :
    (r : ℝ) ^ (2 * Q) * swapFailureMass f Q (((r : ℝ) - 1) / (2 * r)) ≤ (m : ℝ) := by
  exact swap_failure_mass_le_rows r Q m f hr C
    ((kernel_defect_iff C (SwapSpectrum.swapM0 r Q f)).mpr hfixed)

/-- An explicit rational matrix is an instance of the same measurement bound. -/
theorem swap_failure_mass_le_matrix_rows (r Q m : ℕ) (f : ℚ[X]) (hr : 0 < r)
    (C : Matrix (Fin m) (Fin Q → SwapSpectrum.Pair r) ℚ)
    (hker : C.mulVecLin.ker ≤ (LinearMap.id - SwapSpectrum.swapM0 r Q f).ker) :
    (r : ℝ) ^ (2 * Q) * swapFailureMass f Q (((r : ℝ) - 1) / (2 * r)) ≤ (m : ℝ) := by
  exact swap_failure_mass_le_rows r Q m f hr C.mulVecLin hker

/-- The concrete linear-measurement contract and row budget imply the degree
floor; the rank-to-failure-mass identity is proved, rather than a premise. -/
theorem swap_measurement_degree_floor (r Q R m : ℕ) (f : ℚ[X]) (tau : ℝ)
    (hr : 2 ≤ r) (hQ : 0 < Q) (hdegree : f.natDegree < R) (htau : tau ≤ 1)
    (C : ((Fin Q → SwapSpectrum.Pair r) → ℚ) →ₗ[ℚ] (Fin m → ℚ))
    (hker : C.ker ≤ (LinearMap.id - SwapSpectrum.swapM0 r Q f).ker)
    (hbudget : (m : ℝ) ≤ (r : ℝ) ^ (2 * Q) * tau / (3 * r)) :
    1 + 5 * Real.sqrt Q / 24 ≤ (R : ℝ) := by
  have hr0 : 0 < r := by omega
  apply swap_degree_floor f r Q R tau ((r : ℝ) ^ (2 * Q)) hr hQ
    (pow_pos (by exact_mod_cast hr0) _) hdegree htau
  exact (swap_failure_mass_le_rows r Q m f hr0 C hker).trans hbudget

/-- Matrix form of the complete measurement-to-degree implication. -/
theorem swap_matrix_degree_floor (r Q R m : ℕ) (f : ℚ[X]) (tau : ℝ)
    (hr : 2 ≤ r) (hQ : 0 < Q) (hdegree : f.natDegree < R) (htau : tau ≤ 1)
    (C : Matrix (Fin m) (Fin Q → SwapSpectrum.Pair r) ℚ)
    (hker : C.mulVecLin.ker ≤ (LinearMap.id - SwapSpectrum.swapM0 r Q f).ker)
    (hbudget : (m : ℝ) ≤ (r : ℝ) ^ (2 * Q) * tau / (3 * r)) :
    1 + 5 * Real.sqrt Q / 24 ≤ (R : ℝ) := by
  exact swap_measurement_degree_floor r Q R m f tau hr hQ hdegree htau
    C.mulVecLin hker hbudget

/-- The actual measurement and dimension budgets imply the complete clipped
enumeration lower bound, including its finite threshold and floor convention. -/
theorem swap_measurement_enumeration_floor (r Q R m n : ℕ) (f : ℚ[X]) (tau M : ℝ)
    (hr : 2 ≤ r) (hQ : 0 < Q) (hn : 65536 ≤ n)
    (hdegree : f.natDegree < R) (htau : tau ≤ 1)
    (C : ((Fin Q → SwapSpectrum.Pair r) → ℚ) →ₗ[ℚ] (Fin m → ℚ))
    (hker : C.ker ≤ (LinearMap.id - SwapSpectrum.swapM0 r Q f).ker)
    (hrows : (m : ℝ) ≤ (r : ℝ) ^ (2 * Q) * tau / (3 * r))
    (hdimension : 12 * ((r : ℝ) ^ (2 * Q)) ^ 2 ≤ M) (hM : M ≤ 3 * (n : ℝ)) :
    (Q : ℝ) ≤ Real.logb 2 (n : ℝ) / 4 ∧
      (2 : ℝ) ^ ((n : ℝ) * Real.logb 2 (Real.logb 2 (n : ℝ)) /
        (4 * Real.sqrt (Real.logb 2 (n : ℝ)))) ≤
          (enumerationCount n (substitutionOrder n R Q) : ℝ) := by
  have hQL := dimension_budget_implies_Q_bound hr rfl hdimension hM
  exact ⟨hQL, enumeration_floor_explicit hn hQ hQL
    (swap_measurement_degree_floor r Q R m f tau hr hQ hdegree htau C hker hrows)⟩

/-- Matrix form of the actual-measurement-to-enumeration implication. -/
theorem swap_matrix_enumeration_floor (r Q R m n : ℕ) (f : ℚ[X]) (tau M : ℝ)
    (hr : 2 ≤ r) (hQ : 0 < Q) (hn : 65536 ≤ n)
    (hdegree : f.natDegree < R) (htau : tau ≤ 1)
    (C : Matrix (Fin m) (Fin Q → SwapSpectrum.Pair r) ℚ)
    (hker : C.mulVecLin.ker ≤ (LinearMap.id - SwapSpectrum.swapM0 r Q f).ker)
    (hrows : (m : ℝ) ≤ (r : ℝ) ^ (2 * Q) * tau / (3 * r))
    (hdimension : 12 * ((r : ℝ) ^ (2 * Q)) ^ 2 ≤ M) (hM : M ≤ 3 * (n : ℝ)) :
    (Q : ℝ) ≤ Real.logb 2 (n : ℝ) / 4 ∧
      (2 : ℝ) ^ ((n : ℝ) * Real.logb 2 (Real.logb 2 (n : ℝ)) /
        (4 * Real.sqrt (Real.logb 2 (n : ℝ)))) ≤
          (enumerationCount n (substitutionOrder n R Q) : ℝ) := by
  exact swap_measurement_enumeration_floor r Q R m n f tau M hr hQ hn hdegree htau
    C.mulVecLin hker hrows hdimension hM

end ExactSolution.MeasurementRank
