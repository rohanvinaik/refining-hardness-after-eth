import ExactSolution.SelectedMeasurements.Rows
import ExactSolution.NearExponential

/-!
# A constructed local measurement application

This formalizes the local `lem:swaps-matrix` construction in OpenAI,
*The Exponential Time Hypothesis is False*, revised 25 October 2026,
section "The matrices M_0 and C^B", at the pinned source revision
<https://github.com/openai/math/blob/42907c9e999cc00d6abe7a50bfc1023250edd1b9/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/build/main_full_version.tex>.

The measurement rows are the actual transposes of all tensor eigenbasis vectors
outside a retained eigenvalue window. Agreement with parity on the window
implies the fixing-kernel contract. The row count is exactly its binomial tail.
The degree and enumeration endpoints below therefore have no abstract kernel
premise. The numerical row and dimension budgets remain explicit.

These are local auxiliary-space measurements. Placement into repeated copies,
variable coordinates, and variable groups is not asserted by this module.
The natural-interval Lagrange instance below is a mathematical representation
by its degree and values; the source's displayed Newton/binomial formula is
not separately formalized. Signed-window clipping is an additional extension.
-/

namespace ExactSolution.SelectedMeasurements

open scoped BigOperators
open Polynomial SwapSpectrum

theorem swapM0_coordinates (r Q : ℕ) (f : ℚ[X]) (v : History r Q → ℚ)
    (alpha : EigenHistory r Q) :
    (tensorBasis r Q).equivFun (swapM0 r Q f v) alpha =
      ((-1 : ℚ) ^ minusCount alpha * f.eval (minusCount alpha : ℚ)) *
        (tensorBasis r Q).equivFun v alpha := by
  have h := congrFun (congrArg (fun T : Module.End ℚ (EigenHistory r Q → ℚ) =>
    T ((tensorBasis r Q).equivFun v)) (swapM0_diagonalization r Q f)) alpha
  simpa only [LinearEquiv.conj_apply, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.symm_apply_apply, MeasurementRank.diagEnd_apply,
    signProduct_eq, weightEigenvalue_eq] using h

theorem dualMeasurement_zero_iff (r Q : ℕ) (window : Finset ℕ)
    (v : History r Q → ℚ) :
    dualMeasurement r Q window v = 0 ↔
      ∀ alpha : EigenHistory r Q, minusCount alpha ∉ window →
        (tensorBasis r Q).equivFun v alpha = 0 := by
  constructor
  · intro h alpha ha
    have hi := congrFun h (rowEquiv r Q window ⟨alpha, ha⟩)
    simpa [dualMeasurement] using hi
  · intro h
    ext i
    exact h _ ((rowEquiv r Q window).symm i).property

/-- Agreement on the retained eigenvalues makes every vector with zero
selected transpose measurements fixed by the concrete swap operator. -/
theorem measurement_fixed (r Q : ℕ) (window : Finset ℕ) (f : ℚ[X])
    (hagrees : ∀ j ∈ window, f.eval (j : ℚ) = (-1 : ℚ) ^ j)
    (v : History r Q → ℚ) (hzero : measurement r Q window v = 0) :
    swapM0 r Q f v = v := by
  have hdual : dualMeasurement r Q window v = 0 := by
    change v ∈ (dualMeasurement r Q window).ker
    rw [← measurement_ker_eq_dual]
    exact hzero
  have hv := (dualMeasurement_zero_iff r Q window v).mp hdual
  apply (tensorBasis r Q).equivFun.injective
  ext alpha
  rw [swapM0_coordinates]
  by_cases ha : minusCount alpha ∈ window
  · rw [(sign_mul_fixed_iff _ _).mpr (hagrees _ ha), one_mul]
  · rw [hv alpha ha, mul_zero]

theorem measurement_fixing_kernel (r Q : ℕ) (window : Finset ℕ) (f : ℚ[X])
    (hagrees : ∀ j ∈ window, f.eval (j : ℚ) = (-1 : ℚ) ^ j) :
    (measurement r Q window).ker ≤ (LinearMap.id - swapM0 r Q f).ker :=
  (MeasurementRank.kernel_defect_iff _ _).mpr
    (measurement_fixed r Q window f hagrees)

/-- The literal matrix of the local transpose measurements. -/
noncomputable def measurementMatrix (r Q : ℕ) (window : Finset ℕ) :
    Matrix (Fin (rowCount r Q window)) (History r Q) ℚ :=
  fun i h => tensorBasis r Q ((rowEquiv r Q window).symm i).val h

theorem measurementMatrix_mulVecLin (r Q : ℕ) (window : Finset ℕ) :
    (measurementMatrix r Q window).mulVecLin = measurement r Q window := by
  ext v i
  rfl

theorem measurementMatrix_values (r Q : ℕ) (window : Finset ℕ)
    (i : Fin (rowCount r Q window)) (h : History r Q) :
    measurementMatrix r Q window i h = 0 ∨
      measurementMatrix r Q window i h = 1 ∨
      measurementMatrix r Q window i h = -1 :=
  tensorBasis_values r Q _ h

theorem measurementMatrix_integral (r Q : ℕ) (window : Finset ℕ)
    (i : Fin (rowCount r Q window)) (h : History r Q) :
    ∃ z : ℤ, -1 ≤ z ∧ z ≤ 1 ∧ (z : ℚ) = measurementMatrix r Q window i h :=
  tensorBasis_integral r Q _ h

/-- An integer matrix whose coefficientwise rational cast is the constructed
physical measurement matrix. -/
noncomputable def integerMeasurementMatrix (r Q : ℕ) (window : Finset ℕ) :
    Matrix (Fin (rowCount r Q window)) (History r Q) ℤ :=
  fun i h => (measurementMatrix r Q window i h).num

theorem integerMeasurementMatrix_cast (r Q : ℕ) (window : Finset ℕ)
    (i : Fin (rowCount r Q window)) (h : History r Q) :
    (integerMeasurementMatrix r Q window i h : ℚ) = measurementMatrix r Q window i h := by
  rcases measurementMatrix_values r Q window i h with hz | hz | hz
  all_goals simp [integerMeasurementMatrix, hz]

theorem measurementMatrix_l1_le (r Q : ℕ) (window : Finset ℕ)
    (i : Fin (rowCount r Q window)) :
    (∑ h, |measurementMatrix r Q window i h|) ≤ (r : ℚ) ^ (2 * Q) :=
  tensorBasis_l1_le r Q _

theorem integerMeasurementMatrix_l1_le (r Q : ℕ) (window : Finset ℕ)
    (i : Fin (rowCount r Q window)) :
    (∑ h, |integerMeasurementMatrix r Q window i h|) ≤ (r : ℤ) ^ (2 * Q) := by
  have h := measurementMatrix_l1_le r Q window i
  simp_rw [← integerMeasurementMatrix_cast r Q window i] at h
  exact_mod_cast h

theorem rowCount_eq_sum_multiplicity (r Q : ℕ) (window : Finset ℕ) :
    rowCount r Q window =
      ∑ j ∈ (Finset.range (Q + 1)).filter (fun j => j ∉ window),
        eigenMultiplicity r Q j := by
  classical
  unfold rowCount
  rw [Fintype.card_subtype]
  let outsideAlpha : Finset (EigenHistory r Q) :=
    Finset.univ.filter fun alpha => minusCount alpha ∉ window
  let outsideWeight : Finset ℕ := (Finset.range (Q + 1)).filter fun j => j ∉ window
  have hmap : Set.MapsTo (minusCount (r := r) (Q := Q))
      (outsideAlpha : Set (EigenHistory r Q)) (outsideWeight : Set ℕ) := by
    intro alpha ha
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by
      have := minusCount_le alpha
      omega), (Finset.mem_filter.mp ha).2⟩
  change outsideAlpha.card = ∑ j ∈ outsideWeight, _
  rw [Finset.card_eq_sum_card_fiberwise hmap]
  apply Finset.sum_congr rfl
  intro j hj
  have hjoutside : j ∉ window := (Finset.mem_filter.mp hj).2
  rw [eigenMultiplicity, Fintype.card_subtype]
  congr 1
  ext alpha
  simp only [outsideAlpha, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · exact fun h => h.2
  · intro h
    exact ⟨by simpa [h] using hjoutside, h⟩

theorem rowCount_eq_sum_choose (r Q : ℕ) (window : Finset ℕ) :
    rowCount r Q window =
      ∑ j ∈ (Finset.range (Q + 1)).filter (fun j => j ∉ window),
        Q.choose j * (r * (r - 1) / 2) ^ j * (r * (r + 1) / 2) ^ (Q - j) := by
  rw [rowCount_eq_sum_multiplicity]
  simp_rw [eigenMultiplicity_eq_choose_all, minusIndex_card, plusIndex_card]

noncomputable def outsideWindowMass (Q : ℕ) (p : ℝ) (window : Finset ℕ) : ℝ :=
  ∑ j ∈ (Finset.range (Q + 1)).filter (fun j => j ∉ window), binomialMass Q p j

/-- Clipping an original signed-integer window to the actual spectrum. -/
def retainedSignedWindow (Q : ℕ) (window : Finset ℤ) : Finset ℕ :=
  (Finset.range (Q + 1)).filter fun j => (j : ℤ) ∈ window

theorem agreement_on_retainedSignedWindow (Q : ℕ) (window : Finset ℤ) (f : ℚ[X])
    (hagrees : ∀ j ∈ window, f.eval (j : ℚ) = (-1 : ℚ) ^ j) :
    ∀ j ∈ retainedSignedWindow Q window, f.eval (j : ℚ) = (-1 : ℚ) ^ j := by
  intro j hj
  have h := hagrees (j : ℤ) (Finset.mem_filter.mp hj).2
  simpa using h

theorem outsideWindowMass_retainedSignedWindow (Q : ℕ) (p : ℝ) (window : Finset ℤ) :
    outsideWindowMass Q p (retainedSignedWindow Q window) =
      ∑ j ∈ (Finset.range (Q + 1)).filter (fun j : ℕ => (j : ℤ) ∉ window),
        binomialMass Q p j := by
  unfold outsideWindowMass
  congr 1
  ext j
  simp [retainedSignedWindow]
  tauto

/-- Exact row count, normalized by the actual physical dimension. -/
theorem rowCount_eq_dimension_mul_tail (r Q : ℕ) (window : Finset ℕ) (hr : 0 < r) :
    (rowCount r Q window : ℝ) = (r : ℝ) ^ (2 * Q) *
      outsideWindowMass Q (((r : ℝ) - 1) / (2 * r)) window := by
  rw [rowCount_eq_sum_multiplicity, Nat.cast_sum]
  unfold outsideWindowMass
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  exact minusCount_card_normalized r Q j hr
    (Nat.lt_succ_iff.mp (Finset.mem_range.mp (Finset.mem_filter.mp hj).1))

theorem row_budget_of_tail (r Q : ℕ) (window : Finset ℕ) (tau : ℝ) (hr : 0 < r)
    (htail : outsideWindowMass Q (((r : ℝ) - 1) / (2 * r)) window ≤ tau / (3 * r)) :
    (rowCount r Q window : ℝ) ≤ (r : ℝ) ^ (2 * Q) * tau / (3 * r) := by
  rw [rowCount_eq_dimension_mul_tail r Q window hr]
  simpa only [mul_div_assoc] using
    mul_le_mul_of_nonneg_left htail (pow_nonneg (by exact_mod_cast hr.le) _)

/-- Numerical bookkeeping for `h` copies and `r` group restrictions retaining
all rows. This does not assert the external placement or restriction maps. -/
theorem placed_row_count_bound (r h m n : ℕ) (D tau M : ℝ)
    (hr : 0 < r) (htau : 0 ≤ tau)
    (hlocal : (m : ℝ) ≤ D * tau / (3 * r))
    (hcopies : (h : ℝ) * D ≤ 2 * M) (hM : M ≤ 3 * (n : ℝ)) :
    ((r * h * m : ℕ) : ℝ) ≤ 2 * tau * (n : ℝ) := by
  have hrpos : 0 < (r : ℝ) := by exact_mod_cast hr
  have hlocal' := (le_div_iff₀ (by positivity : 0 < 3 * (r : ℝ))).mp hlocal
  have hscaled := mul_le_mul_of_nonneg_left hlocal' (Nat.cast_nonneg h : (0 : ℝ) ≤ h)
  have hcopies' := mul_le_mul_of_nonneg_right hcopies htau
  have hM' := mul_le_mul_of_nonneg_right hM htau
  push_cast
  nlinarith

/-- A local source-style measurement application: no abstract kernel premise
is supplied. Agreement on the window and its tail budget suffice. -/
theorem selected_measurement_degree_floor (r Q R : ℕ) (window : Finset ℕ)
    (f : ℚ[X]) (tau : ℝ) (hr : 2 ≤ r) (hQ : 0 < Q)
    (hdegree : f.natDegree < R) (htau : tau ≤ 1)
    (hagrees : ∀ j ∈ window, f.eval (j : ℚ) = (-1 : ℚ) ^ j)
    (htail : outsideWindowMass Q (((r : ℝ) - 1) / (2 * r)) window ≤ tau / (3 * r)) :
    1 + 5 * Real.sqrt Q / 24 ≤ (R : ℝ) := by
  exact MeasurementRank.swap_measurement_degree_floor r Q R (rowCount r Q window)
    f tau hr hQ hdegree htau (measurement r Q window)
    (measurement_fixing_kernel r Q window f hagrees)
    (row_budget_of_tail r Q window tau (by omega) htail)

theorem selected_measurement_enumeration_floor (r Q R n : ℕ) (window : Finset ℕ)
    (f : ℚ[X]) (tau M : ℝ) (hr : 2 ≤ r) (hQ : 0 < Q) (hn : 65536 ≤ n)
    (hdegree : f.natDegree < R) (htau : tau ≤ 1)
    (hagrees : ∀ j ∈ window, f.eval (j : ℚ) = (-1 : ℚ) ^ j)
    (htail : outsideWindowMass Q (((r : ℝ) - 1) / (2 * r)) window ≤ tau / (3 * r))
    (hdimension : 12 * ((r : ℝ) ^ (2 * Q)) ^ 2 ≤ M) (hM : M ≤ 3 * (n : ℝ)) :
    (Q : ℝ) ≤ Real.logb 2 (n : ℝ) / 4 ∧
      (2 : ℝ) ^ ((n : ℝ) * Real.logb 2 (Real.logb 2 (n : ℝ)) /
        (4 * Real.sqrt (Real.logb 2 (n : ℝ)))) ≤
          (enumerationCount n (substitutionOrder n R Q) : ℝ) := by
  exact MeasurementRank.swap_measurement_enumeration_floor r Q R (rowCount r Q window)
    n f tau M hr hQ hn hdegree htau (measurement r Q window)
    (measurement_fixing_kernel r Q window f hagrees)
    (row_budget_of_tail r Q window tau (by omega) htail) hdimension hM

/-- The eventual threshold is uniform in the window and its interpolating
polynomial, as well as all numerical construction parameters. -/
theorem selected_measurement_near_exponential (eps : ℝ) (heps : 0 < eps) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ r Q R : ℕ, ∀ window : Finset ℕ, ∀ f : ℚ[X], ∀ tau M : ℝ,
      2 ≤ r → 0 < Q → f.natDegree < R → tau ≤ 1 →
      (∀ j ∈ window, f.eval (j : ℚ) = (-1 : ℚ) ^ j) →
      outsideWindowMass Q (((r : ℝ) - 1) / (2 * r)) window ≤ tau / (3 * r) →
      12 * ((r : ℝ) ^ (2 * Q)) ^ 2 ≤ M → M ≤ 3 * (n : ℝ) →
      (2 : ℝ) ^ ((n : ℝ) ^ (1 - eps)) ≤
        (enumerationCount n (substitutionOrder n R Q) : ℝ) := by
  obtain ⟨N, hN⟩ := swap_measurement_near_exponential eps heps
  refine ⟨N, ?_⟩
  intro n hn r Q R window f tau M hr hQ hdegree htau hagrees htail hdimension hM
  exact hN n hn r Q R (rowCount r Q window) f tau M (measurement r Q window)
    hr hQ hdegree htau (measurement_fixing_kernel r Q window f hagrees)
    (row_budget_of_tail r Q window tau (by omega) htail) hdimension hM

/-- An original signed window may extend outside the spectrum. Only its
retained nonnegative eigenvalues determine which physical rows are selected. -/
theorem signed_window_measurement_degree_floor (r Q R : ℕ) (window : Finset ℤ)
    (f : ℚ[X]) (tau : ℝ) (hr : 2 ≤ r) (hQ : 0 < Q)
    (hdegree : f.natDegree < R) (htau : tau ≤ 1)
    (hagrees : ∀ j ∈ window, f.eval (j : ℚ) = (-1 : ℚ) ^ j)
    (htail : outsideWindowMass Q (((r : ℝ) - 1) / (2 * r))
      (retainedSignedWindow Q window) ≤ tau / (3 * r)) :
    1 + 5 * Real.sqrt Q / 24 ≤ (R : ℝ) :=
  selected_measurement_degree_floor r Q R (retainedSignedWindow Q window) f tau
    hr hQ hdegree htau (agreement_on_retainedSignedWindow Q window f hagrees) htail

theorem signed_window_measurement_enumeration_floor (r Q R n : ℕ)
    (window : Finset ℤ) (f : ℚ[X]) (tau M : ℝ)
    (hr : 2 ≤ r) (hQ : 0 < Q) (hn : 65536 ≤ n)
    (hdegree : f.natDegree < R) (htau : tau ≤ 1)
    (hagrees : ∀ j ∈ window, f.eval (j : ℚ) = (-1 : ℚ) ^ j)
    (htail : outsideWindowMass Q (((r : ℝ) - 1) / (2 * r))
      (retainedSignedWindow Q window) ≤ tau / (3 * r))
    (hdimension : 12 * ((r : ℝ) ^ (2 * Q)) ^ 2 ≤ M) (hM : M ≤ 3 * (n : ℝ)) :
    (Q : ℝ) ≤ Real.logb 2 (n : ℝ) / 4 ∧
      (2 : ℝ) ^ ((n : ℝ) * Real.logb 2 (Real.logb 2 (n : ℝ)) /
        (4 * Real.sqrt (Real.logb 2 (n : ℝ)))) ≤
          (enumerationCount n (substitutionOrder n R Q) : ℝ) :=
  selected_measurement_enumeration_floor r Q R n (retainedSignedWindow Q window)
    f tau M hr hQ hn hdegree htau (agreement_on_retainedSignedWindow Q window f hagrees)
    htail hdimension hM

theorem signed_window_measurement_near_exponential (eps : ℝ) (heps : 0 < eps) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ r Q R : ℕ, ∀ window : Finset ℤ, ∀ f : ℚ[X], ∀ tau M : ℝ,
      2 ≤ r → 0 < Q → f.natDegree < R → tau ≤ 1 →
      (∀ j ∈ window, f.eval (j : ℚ) = (-1 : ℚ) ^ j) →
      outsideWindowMass Q (((r : ℝ) - 1) / (2 * r)) (retainedSignedWindow Q window) ≤
        tau / (3 * r) →
      12 * ((r : ℝ) ^ (2 * Q)) ^ 2 ≤ M → M ≤ 3 * (n : ℝ) →
      (2 : ℝ) ^ ((n : ℝ) ^ (1 - eps)) ≤
        (enumerationCount n (substitutionOrder n R Q) : ℝ) := by
  obtain ⟨N, hN⟩ := selected_measurement_near_exponential eps heps
  refine ⟨N, ?_⟩
  intro n hn r Q R window f tau M hr hQ hdegree htau hagrees htail hdimension hM
  exact hN n hn r Q R (retainedSignedWindow Q window) f tau M hr hQ hdegree htau
    (agreement_on_retainedSignedWindow Q window f hagrees) htail hdimension hM

/-- A separate concrete Lagrange instance. Equality with another construction
requires the degree and value hypotheses of `eq_parityInterpolant`; no
verbatim closed Newton/binomial formula is asserted here. -/
noncomputable def parityInterpolant (window : Finset ℕ) : ℚ[X] :=
  Lagrange.interpolate window (fun j : ℕ => (j : ℚ)) (fun j => (-1 : ℚ) ^ j)

theorem parityInterpolant_agrees (window : Finset ℕ) (j : ℕ) (hj : j ∈ window) :
    (parityInterpolant window).eval (j : ℚ) = (-1 : ℚ) ^ j :=
  Lagrange.eval_interpolate_at_node _ (Nat.cast_injective.injOn) hj

theorem parityInterpolant_ne_zero (window : Finset ℕ) (hne : window.Nonempty) :
    parityInterpolant window ≠ 0 := by
  obtain ⟨j, hj⟩ := hne
  intro hz
  have h := parityInterpolant_agrees window j hj
  rw [hz, Polynomial.eval_zero] at h
  exact (pow_ne_zero j (by norm_num : (-1 : ℚ) ≠ 0)) h.symm

theorem parityInterpolant_natDegree_lt (window : Finset ℕ) (hne : window.Nonempty) :
    (parityInterpolant window).natDegree < window.card := by
  apply (Polynomial.natDegree_lt_iff_degree_lt (parityInterpolant_ne_zero window hne)).mpr
  exact Lagrange.degree_interpolate_lt _ (Nat.cast_injective.injOn)

/-- Uniqueness identifies any other degree-bounded parity interpolant,
including a closed-form construction, with this actual polynomial. -/
theorem eq_parityInterpolant (window : Finset ℕ) (f : ℚ[X])
    (hdegree : f.degree < (window.card : WithBot ℕ))
    (hagrees : ∀ j ∈ window, f.eval (j : ℚ) = (-1 : ℚ) ^ j) :
    f = parityInterpolant window :=
  Lagrange.eq_interpolate_of_eval_eq _ Nat.cast_injective.injOn hdegree hagrees

def intervalWindow (A R : ℕ) : Finset ℕ := Finset.Ico A (A + R)

theorem intervalWindow_card (A R : ℕ) : (intervalWindow A R).card = R := by
  simp [intervalWindow]

theorem intervalWindow_nonempty (A R : ℕ) (hR : 0 < R) :
    (intervalWindow A R).Nonempty := by
  exact ⟨A, Finset.mem_Ico.mpr ⟨le_rfl, by omega⟩⟩

/-- The explicit interval interpolant needs no supplied polynomial or
agreement premise in the local measurement application. -/
theorem interval_measurement_degree_floor (r Q A R : ℕ) (tau : ℝ)
    (hr : 2 ≤ r) (hQ : 0 < Q) (hR : 0 < R) (htau : tau ≤ 1)
    (htail : outsideWindowMass Q (((r : ℝ) - 1) / (2 * r)) (intervalWindow A R) ≤
      tau / (3 * r)) :
    1 + 5 * Real.sqrt Q / 24 ≤ (R : ℝ) := by
  have hd := parityInterpolant_natDegree_lt (intervalWindow A R)
    (intervalWindow_nonempty A R hR)
  rw [intervalWindow_card] at hd
  exact selected_measurement_degree_floor r Q R (intervalWindow A R)
    (parityInterpolant (intervalWindow A R)) tau hr hQ hd htau
    (parityInterpolant_agrees _) htail

theorem interval_measurement_enumeration_floor (r Q A R n : ℕ) (tau M : ℝ)
    (hr : 2 ≤ r) (hQ : 0 < Q) (hR : 0 < R) (hn : 65536 ≤ n) (htau : tau ≤ 1)
    (htail : outsideWindowMass Q (((r : ℝ) - 1) / (2 * r)) (intervalWindow A R) ≤
      tau / (3 * r))
    (hdimension : 12 * ((r : ℝ) ^ (2 * Q)) ^ 2 ≤ M) (hM : M ≤ 3 * (n : ℝ)) :
    (Q : ℝ) ≤ Real.logb 2 (n : ℝ) / 4 ∧
      (2 : ℝ) ^ ((n : ℝ) * Real.logb 2 (Real.logb 2 (n : ℝ)) /
        (4 * Real.sqrt (Real.logb 2 (n : ℝ)))) ≤
          (enumerationCount n (substitutionOrder n R Q) : ℝ) := by
  have hd := parityInterpolant_natDegree_lt (intervalWindow A R)
    (intervalWindow_nonempty A R hR)
  rw [intervalWindow_card] at hd
  exact selected_measurement_enumeration_floor r Q R n (intervalWindow A R)
    (parityInterpolant (intervalWindow A R)) tau M hr hQ hn hd htau
    (parityInterpolant_agrees _) htail hdimension hM

theorem interval_measurement_near_exponential (eps : ℝ) (heps : 0 < eps) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ r Q A R : ℕ, ∀ tau M : ℝ,
      2 ≤ r → 0 < Q → 0 < R → tau ≤ 1 →
      outsideWindowMass Q (((r : ℝ) - 1) / (2 * r)) (intervalWindow A R) ≤
        tau / (3 * r) →
      12 * ((r : ℝ) ^ (2 * Q)) ^ 2 ≤ M → M ≤ 3 * (n : ℝ) →
      (2 : ℝ) ^ ((n : ℝ) ^ (1 - eps)) ≤
        (enumerationCount n (substitutionOrder n R Q) : ℝ) := by
  obtain ⟨N, hN⟩ := selected_measurement_near_exponential eps heps
  refine ⟨N, ?_⟩
  intro n hn r Q A R tau M hr hQ hR htau htail hdimension hM
  have hd := parityInterpolant_natDegree_lt (intervalWindow A R)
    (intervalWindow_nonempty A R hR)
  rw [intervalWindow_card] at hd
  exact hN n hn r Q R (intervalWindow A R) (parityInterpolant (intervalWindow A R))
    tau M hr hQ hd htau (parityInterpolant_agrees _) htail hdimension hM

end ExactSolution.SelectedMeasurements
