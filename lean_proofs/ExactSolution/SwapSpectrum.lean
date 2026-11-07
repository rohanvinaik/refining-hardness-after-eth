import ExactSolution.SwapSpectrum.Values

/-!
# The concrete swap-matrix rank identity

The coordinate operators act on functions on `([r] × [r])^Q`. The explicit
rational change of basis, the actual swap actions, and the finite multiplicity
calculation are established in the imported modules. The defect rank is exactly
the total dimension of the weight spaces where the polynomial misses parity.
-/

namespace ExactSolution.SwapSpectrum

open scoped BigOperators
open Polynomial

theorem swap_rank_eq_failure_mass (r Q : ℕ) (f : ℚ[X]) (hr : 0 < r) :
    (Module.finrank ℚ (LinearMap.id - swapM0 r Q f).range : ℝ) =
      (r : ℝ) ^ (2 * Q) *
        ExactSolution.swapFailureMass f Q (((r : ℝ) - 1) / (2 * r)) := by
  rw [swap_rank_eq_sum_fiber_card, Nat.cast_sum]
  unfold ExactSolution.swapFailureMass
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  exact minusCount_card_normalized r Q j hr
    (Nat.lt_succ_iff.mp (Finset.mem_range.mp (Finset.mem_filter.mp hj).1))

end ExactSolution.SwapSpectrum
