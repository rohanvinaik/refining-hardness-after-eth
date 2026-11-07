import ExactSolution.SwapSpectrum

/-!
# Selected transpose eigenbasis measurements

The local measurement rows are the transposes of the tensor swap eigenvectors
whose antisymmetric counts lie outside a retained window.  The normalized dual
coordinates are also constructed, and the two maps have the same kernel.
-/

namespace ExactSolution.SelectedMeasurements

open scoped BigOperators
open SwapSpectrum

private theorem strictPair_ne_swap {r : ℕ} (p q : StrictPair r) :
    p.val ≠ q.val.swap := by
  intro h
  have h₁ := congrArg Prod.fst h
  have h₂ := congrArg Prod.snd h
  have hp := p.property
  have hq := q.property
  simp only [Prod.fst_swap, Prod.snd_swap] at h₁ h₂
  omega

private theorem strictPair_ne_diag {r : ℕ} (p : StrictPair r) (a : Fin r) :
    p.val ≠ (a, a) := by
  intro h
  have hp := p.property
  rw [h] at hp
  exact (lt_irrefl _ hp)

private theorem strictPair_swap_ne_diag {r : ℕ} (p : StrictPair r) (a : Fin r) :
    p.val.swap ≠ (a, a) := by
  intro h
  apply strictPair_ne_diag p a
  simpa using congrArg Prod.swap h

private def pairVector {r : ℕ} : EigenIndex r → (Pair r → ℚ)
  | .inl (.inl a) => Pi.single (a, a) 1
  | .inl (.inr p) => Pi.single p.val 1 + Pi.single p.val.swap 1
  | .inr p => Pi.single p.val 1 - Pi.single p.val.swap 1

private theorem pairVector_coordinates {r : ℕ} (k : EigenIndex r) :
    pairEquiv r (pairVector k) = Pi.single k 1 := by
  ext l
  rcases k with (a | p) | p <;> rcases l with (b | q) | q
  all_goals
    simp [pairVector, pairTo, Pi.single_apply, strictPair_ne_swap,
      strictPair_ne_diag, Ne.symm (strictPair_ne_diag _ _),
      strictPair_swap_ne_diag, Ne.symm (strictPair_swap_ne_diag _ _),
      Prod.swap_inj, Subtype.val_inj]

private theorem pairBasis_eq_pairVector {r : ℕ} (k : EigenIndex r) :
    pairBasis r k = pairVector k := by
  apply (pairEquiv r).injective
  rw [pairEquiv_pairBasis, pairVector_coordinates]

def pairNorm {r : ℕ} : EigenIndex r → ℚ
  | .inl (.inl _) => 1
  | .inl (.inr _) => 2
  | .inr _ => 2

theorem pairNorm_pos {r : ℕ} (k : EigenIndex r) : 0 < pairNorm k := by
  rcases k with (_ | _) | _ <;> norm_num [pairNorm]

theorem pairBasis_dot (r : ℕ) (k : EigenIndex r) (v : Pair r → ℚ) :
    (∑ p, pairBasis r k p * v p) = pairNorm k * pairEquiv r v k := by
  rw [pairBasis_eq_pairVector]
  rcases k with (a | p) | p
  · change Pi.single (a, a) 1 ⬝ᵥ v = _
    rw [single_dotProduct]
    simp [pairNorm, pairTo]
  · change (Pi.single p.val 1 + Pi.single p.val.swap 1) ⬝ᵥ v = _
    rw [add_dotProduct, single_dotProduct, single_dotProduct]
    simp only [pairNorm, pairEquiv_apply, pairTo]
    ring
  · change (Pi.single p.val 1 - Pi.single p.val.swap 1) ⬝ᵥ v = _
    rw [sub_dotProduct, single_dotProduct, single_dotProduct]
    simp only [pairNorm, pairEquiv_apply, pairTo]
    ring

theorem pairBasis_values (r : ℕ) (k : EigenIndex r) (x : Pair r) :
    pairBasis r k x = 0 ∨ pairBasis r k x = 1 ∨ pairBasis r k x = -1 := by
  rw [pairBasis_eq_pairVector]
  rcases k with (a | p) | p
  · by_cases hx : x = (a, a) <;> simp [pairVector, Pi.single_apply, hx]
  · have hp := strictPair_ne_swap p p
    by_cases hx : x = p.val
    · subst x
      simp [pairVector, hp]
    · by_cases hx' : x = p.val.swap
      · subst x
        simp [pairVector, Ne.symm hp]
      · simp [pairVector, hx, hx']
  · have hp := strictPair_ne_swap p p
    by_cases hx : x = p.val
    · subst x
      simp [pairVector, hp]
    · by_cases hx' : x = p.val.swap
      · subst x
        simp [pairVector, Ne.symm hp]
      · simp [pairVector, hx, hx']

theorem tensorBasis_values (r Q : ℕ) (alpha : EigenHistory r Q) (h : History r Q) :
    tensorBasis r Q alpha h = 0 ∨ tensorBasis r Q alpha h = 1 ∨
      tensorBasis r Q alpha h = -1 := by
  rw [tensorBasis_apply]
  have hprod (s : Finset (Fin Q)) :
      (∏ i ∈ s, pairBasis r (alpha i) (h i)) = 0 ∨
      (∏ i ∈ s, pairBasis r (alpha i) (h i)) = 1 ∨
      (∏ i ∈ s, pairBasis r (alpha i) (h i)) = -1 := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert i s hi ih =>
      rw [Finset.prod_insert hi]
      rcases pairBasis_values r (alpha i) (h i) with hv | hv | hv
      all_goals rw [hv]
      all_goals rcases ih with hs | hs | hs <;> rw [hs] <;> norm_num
  exact hprod Finset.univ

theorem tensorBasis_integral (r Q : ℕ) (alpha : EigenHistory r Q) (h : History r Q) :
    ∃ z : ℤ, -1 ≤ z ∧ z ≤ 1 ∧ (z : ℚ) = tensorBasis r Q alpha h := by
  rcases tensorBasis_values r Q alpha h with hz | hz | hz
  · exact ⟨0, by norm_num, by norm_num, by simpa using hz.symm⟩
  · exact ⟨1, by norm_num, by norm_num, by simpa using hz.symm⟩
  · exact ⟨-1, by norm_num, by norm_num, by simpa using hz.symm⟩

theorem tensorBasis_l1_le (r Q : ℕ) (alpha : EigenHistory r Q) :
    (∑ h, |tensorBasis r Q alpha h|) ≤ (r : ℚ) ^ (2 * Q) := by
  calc
    (∑ h, |tensorBasis r Q alpha h|) ≤ ∑ _h : History r Q, (1 : ℚ) := by
      apply Finset.sum_le_sum
      intro h _
      rcases tensorBasis_values r Q alpha h with hz | hz | hz <;> rw [hz] <;> norm_num
    _ = (r : ℚ) ^ (2 * Q) := by simp [History, Pair, ← pow_two, ← pow_mul]

def tensorNorm {r Q : ℕ} (alpha : EigenHistory r Q) : ℚ :=
  ∏ s, pairNorm (alpha s)

theorem tensorNorm_pos {r Q : ℕ} (alpha : EigenHistory r Q) :
    0 < tensorNorm alpha := Finset.prod_pos fun _ _ => pairNorm_pos _

theorem tensorBasis_orthogonal (r Q : ℕ) (alpha beta : EigenHistory r Q) :
    (∑ h, tensorBasis r Q alpha h * tensorBasis r Q beta h) =
      if alpha = beta then tensorNorm alpha else 0 := by
  simp_rw [tensorBasis_apply, ← Finset.prod_mul_distrib]
  rw [← Fintype.prod_sum (fun s : Fin Q => fun p : Pair r =>
    pairBasis r (alpha s) p * pairBasis r (beta s) p)]
  simp_rw [pairBasis_dot, pairEquiv_pairBasis, Pi.single_apply]
  by_cases hab : alpha = beta
  · subst beta
    simp [tensorNorm]
  · have hdiff : ∃ s, beta s ≠ alpha s := by
      by_contra h
      push_neg at h
      exact hab (funext fun s => (h s).symm)
    obtain ⟨s, hs⟩ := hdiff
    rw [if_neg hab]
    exact Finset.prod_eq_zero (Finset.mem_univ s) (by simp [Ne.symm hs])

theorem tensorBasis_dot_coordinates (r Q : ℕ) (alpha : EigenHistory r Q)
    (v : History r Q → ℚ) :
    (∑ h, tensorBasis r Q alpha h * v h) =
      tensorNorm alpha * (tensorBasis r Q).equivFun v alpha := by
  conv_lhs => rw [← (tensorBasis r Q).sum_equivFun v]
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  have hterm (beta : EigenHistory r Q) :
      (∑ h, tensorBasis r Q alpha h *
          ((tensorBasis r Q).equivFun v beta * tensorBasis r Q beta h)) =
        (tensorBasis r Q).equivFun v beta *
          (if alpha = beta then tensorNorm alpha else 0) := by
    rw [← tensorBasis_orthogonal]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro h _
    ring
  simp_rw [hterm]
  simp [mul_comm]

abbrev RowIndex (r Q : ℕ) (window : Finset ℕ) :=
  {alpha : EigenHistory r Q // minusCount alpha ∉ window}

noncomputable def rowCount (r Q : ℕ) (window : Finset ℕ) : ℕ :=
  Fintype.card (RowIndex r Q window)

noncomputable def rowEquiv (r Q : ℕ) (window : Finset ℕ) :
    RowIndex r Q window ≃ Fin (rowCount r Q window) := Fintype.equivFin _

/-- The literal source-style row: the transpose of the selected eigenvector. -/
noncomputable def measurement (r Q : ℕ) (window : Finset ℕ) :
    (History r Q → ℚ) →ₗ[ℚ] (Fin (rowCount r Q window) → ℚ) where
  toFun v i := ∑ h, tensorBasis r Q ((rowEquiv r Q window).symm i).val h * v h
  map_add' v w := by ext i; simp [Finset.sum_add_distrib, mul_add]
  map_smul' c v := by ext i; simp [Finset.mul_sum, mul_left_comm]

/-- The selected normalized dual coordinates of the same eigenbasis. -/
noncomputable def dualMeasurement (r Q : ℕ) (window : Finset ℕ) :
    (History r Q → ℚ) →ₗ[ℚ] (Fin (rowCount r Q window) → ℚ) where
  toFun v i := (tensorBasis r Q).equivFun v ((rowEquiv r Q window).symm i).val
  map_add' v w := by ext i; simp
  map_smul' c v := by ext i; simp

theorem measurement_eq_scaled_dual (r Q : ℕ) (window : Finset ℕ)
    (v : History r Q → ℚ) (i : Fin (rowCount r Q window)) :
    measurement r Q window v i =
      tensorNorm ((rowEquiv r Q window).symm i).val * dualMeasurement r Q window v i :=
  tensorBasis_dot_coordinates r Q _ v

theorem measurement_ker_eq_dual (r Q : ℕ) (window : Finset ℕ) :
    (measurement r Q window).ker = (dualMeasurement r Q window).ker := by
  ext v
  simp only [LinearMap.mem_ker, funext_iff, Pi.zero_apply]
  constructor
  · intro h i
    have hi := h i
    rw [measurement_eq_scaled_dual] at hi
    exact (mul_eq_zero.mp hi).resolve_left (ne_of_gt (tensorNorm_pos _))
  · intro h i
    rw [measurement_eq_scaled_dual, h i, mul_zero]

end ExactSolution.SelectedMeasurements
