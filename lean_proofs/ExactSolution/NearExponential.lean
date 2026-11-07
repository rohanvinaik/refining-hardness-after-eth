import ExactSolution.MeasurementRank
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Power-index consequences for the specified substitution enumeration

The analytic comparison below turns the existing explicit enumeration floor
into a bound with exponent `n^(1-eps)`, for every positive real `eps`.
The application endpoint retains the actual measurement map, fixing contract,
and row and dimension budgets. It is a statement about this enumeration family.
-/

namespace ExactSolution

open Filter
open scoped Topology BigOperators
open Polynomial

theorem four_logTwo_eventually_le_rpow (eps : ℝ) (heps : 0 < eps) :
    ∀ᶠ n : ℕ in atTop, 4 * Real.logb 2 (n : ℝ) ≤ (n : ℝ) ^ eps := by
  have hlog := (isLittleO_log_rpow_atTop heps).tendsto_div_nhds_zero
  have hscaled : Tendsto (fun x : ℝ => 4 * Real.logb 2 x / x ^ eps) atTop (𝓝 0) := by
    convert hlog.const_mul (4 / Real.log 2) using 1
    · ext x
      simp only [Real.logb]
      ring
    · simp
  have hsmall := (hscaled.comp tendsto_natCast_atTop_atTop).eventually
    (eventually_lt_nhds (show (0 : ℝ) < 1 by norm_num))
  filter_upwards [hsmall, eventually_ge_atTop (1 : ℕ)] with n hn hn1
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hpowpos := Real.rpow_pos_of_pos hnpos eps
  exact le_of_lt (by simpa using (div_lt_iff₀ hpowpos).mp hn)

/-- The explicit enumeration exponent eventually dominates every fixed
power `n^(1-eps)` with positive real `eps`. -/
theorem enumeration_exponent_eventually_ge_power (eps : ℝ) (heps : 0 < eps) :
    ∀ᶠ n : ℕ in atTop,
      (n : ℝ) ^ (1 - eps) ≤
        (n : ℝ) * Real.logb 2 (Real.logb 2 (n : ℝ)) /
          (4 * Real.sqrt (Real.logb 2 (n : ℝ))) := by
  filter_upwards [four_logTwo_eventually_le_rpow eps heps,
    eventually_ge_atTop (65536 : ℕ)] with n hpower hn
  let L : ℝ := Real.logb 2 (n : ℝ)
  obtain ⟨hL, _⟩ := logTwo_bounds hn
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hLpos : 0 < L := by dsimp [L]; linarith
  have hsqrtpos : 0 < Real.sqrt L := Real.sqrt_pos.mpr hLpos
  have hsqrt : Real.sqrt L ≤ L := by
    have hsquare := Real.sq_sqrt hLpos.le
    have hnonneg := Real.sqrt_nonneg L
    dsimp [L] at *
    nlinarith
  have hloglog : 1 ≤ Real.logb 2 L := by
    apply (Real.le_logb_iff_rpow_le (by norm_num : (1 : ℝ) < 2) hLpos).mpr
    norm_num
    dsimp [L]
    linarith
  calc
    (n : ℝ) ^ (1 - eps) = (n : ℝ) / (n : ℝ) ^ eps := by
      rw [Real.rpow_sub hnpos, Real.rpow_one]
    _ ≤ (n : ℝ) / (4 * L) :=
      div_le_div_of_nonneg_left hnpos.le (by positivity) hpower
    _ ≤ (n : ℝ) * Real.logb 2 L / (4 * Real.sqrt L) := by
      apply (div_le_div_iff₀ (by positivity : 0 < 4 * L) (by positivity)).mpr
      calc
        (n : ℝ) * (4 * Real.sqrt L) ≤ (n : ℝ) * (4 * L) := by gcongr
        _ ≤ ((n : ℝ) * Real.logb 2 L) * (4 * L) :=
          mul_le_mul_of_nonneg_right (le_mul_of_one_le_right hnpos.le hloglog) (by positivity)

/-- The actual measurement and dimension contracts force the power-index
lower bound uniformly in every permitted polynomial and measurement map. -/
theorem swap_measurement_near_exponential_eventually (eps : ℝ) (heps : 0 < eps) :
    ∀ᶠ n : ℕ in atTop, ∀ r Q R m : ℕ, ∀ f : ℚ[X], ∀ tau M : ℝ,
      ∀ C : ((Fin Q → SwapSpectrum.Pair r) → ℚ) →ₗ[ℚ] (Fin m → ℚ),
      2 ≤ r → 0 < Q → f.natDegree < R → tau ≤ 1 →
      C.ker ≤ (LinearMap.id - SwapSpectrum.swapM0 r Q f).ker →
      (m : ℝ) ≤ (r : ℝ) ^ (2 * Q) * tau / (3 * r) →
      12 * ((r : ℝ) ^ (2 * Q)) ^ 2 ≤ M → M ≤ 3 * (n : ℝ) →
      (2 : ℝ) ^ ((n : ℝ) ^ (1 - eps)) ≤
        (enumerationCount n (substitutionOrder n R Q) : ℝ) := by
  filter_upwards [enumeration_exponent_eventually_ge_power eps heps,
    eventually_ge_atTop (65536 : ℕ)] with n hpower hn
  intro r Q R m f tau M C hr hQ hdegree htau hker hrows hdimension hM
  have hfloor := MeasurementRank.swap_measurement_enumeration_floor
    r Q R m n f tau M hr hQ hn hdegree htau C hker hrows hdimension hM
  exact (Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hpower).trans hfloor.2

/-- An existential-threshold form of the preceding eventual theorem. -/
theorem swap_measurement_near_exponential (eps : ℝ) (heps : 0 < eps) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ r Q R m : ℕ, ∀ f : ℚ[X], ∀ tau M : ℝ,
      ∀ C : ((Fin Q → SwapSpectrum.Pair r) → ℚ) →ₗ[ℚ] (Fin m → ℚ),
      2 ≤ r → 0 < Q → f.natDegree < R → tau ≤ 1 →
      C.ker ≤ (LinearMap.id - SwapSpectrum.swapM0 r Q f).ker →
      (m : ℝ) ≤ (r : ℝ) ^ (2 * Q) * tau / (3 * r) →
      12 * ((r : ℝ) ^ (2 * Q)) ^ 2 ≤ M → M ≤ 3 * (n : ℝ) →
      (2 : ℝ) ^ ((n : ℝ) ^ (1 - eps)) ≤
        (enumerationCount n (substitutionOrder n R Q) : ℝ) :=
  eventually_atTop.mp (swap_measurement_near_exponential_eventually eps heps)

/-- Clipping never increases the complete ternary substitution count. -/
theorem enumerationCount_le_three_pow (n q : ℕ) : enumerationCount n q ≤ 3 ^ n := by
  unfold enumerationCount
  calc
    (∑ j ∈ Finset.range (min q n + 1), 2 ^ j * n.choose j) ≤
        ∑ j ∈ Finset.range (n + 1), 2 ^ j * n.choose j := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · exact Finset.range_mono (by omega)
      · intro j _ _
        exact Nat.zero_le _
    _ = 3 ^ n := by simpa using (add_pow (2 : ℕ) 1 n).symm

end ExactSolution
