import Mathlib

/-!
# A rational eigenbasis for the actual ordered-pair swap

Diagonal positions and symmetric/antisymmetric combinations of distinct
positions form a basis. The change of coordinates and its inverse are given
explicitly; no spectral assertion is assumed.
-/

namespace ExactSolution.SwapSpectrum

abbrev Pair (r : ℕ) := Fin r × Fin r
abbrev StrictPair (r : ℕ) := {p : Pair r // p.1 < p.2}
abbrev PlusIndex (r : ℕ) := Fin r ⊕ StrictPair r
abbrev EigenIndex (r : ℕ) := PlusIndex r ⊕ StrictPair r

def eigenSign {r : ℕ} : EigenIndex r → ℚ
  | .inl _ => 1
  | .inr _ => -1

def pairTo {r : ℕ} (x : Pair r → ℚ) : EigenIndex r → ℚ
  | .inl (.inl a) => x (a, a)
  | .inl (.inr p) => (x p.val + x p.val.swap) / 2
  | .inr p => (x p.val - x p.val.swap) / 2

def pairFrom {r : ℕ} (y : EigenIndex r → ℚ) (p : Pair r) : ℚ :=
  if hab : p.1 = p.2 then y (.inl (.inl p.1))
  else if hlt : p.1 < p.2 then
    y (.inl (.inr ⟨p, hlt⟩)) + y (.inr ⟨p, hlt⟩)
  else
    let q : StrictPair r := ⟨p.swap, lt_of_le_of_ne (le_of_not_gt hlt) (Ne.symm hab)⟩
    y (.inl (.inr q)) - y (.inr q)

noncomputable def pairEquiv (r : ℕ) : (Pair r → ℚ) ≃ₗ[ℚ] (EigenIndex r → ℚ) where
  toFun := pairTo
  invFun := pairFrom
  left_inv := by
    intro x
    funext p
    rcases p with ⟨a, b⟩
    by_cases hab : a = b
    · subst b
      simp [pairFrom, pairTo]
    · by_cases hlt : a < b
      · simp [pairFrom, pairTo, hab, hlt]
        ring
      · simp [pairFrom, pairTo, hab, hlt]
        ring
  right_inv := by
    intro y
    funext k
    rcases k with (a | ⟨⟨a, b⟩, hlt⟩) | ⟨⟨a, b⟩, hlt⟩
    · simp [pairTo, pairFrom]
    · have hab : a ≠ b := ne_of_lt hlt
      have hba : b ≠ a := Ne.symm hab
      simp [pairTo, pairFrom, hab, hba, hlt, not_lt_of_ge hlt.le]
    · have hab : a ≠ b := ne_of_lt hlt
      have hba : b ≠ a := Ne.symm hab
      simp [pairTo, pairFrom, hab, hba, hlt, not_lt_of_ge hlt.le]
  map_add' := by
    intro x y
    funext k
    rcases k with (a | p) | p <;> simp [pairTo] <;> ring
  map_smul' := by
    intro c x
    funext k
    rcases k with (a | p) | p <;> simp [pairTo, smul_eq_mul] <;> ring

@[simp] theorem pairEquiv_apply (r : ℕ) (x : Pair r → ℚ) (k : EigenIndex r) :
    pairEquiv r x k = pairTo x k := rfl

noncomputable def pairSwap (r : ℕ) : Module.End ℚ (Pair r → ℚ) where
  toFun x := fun p => x p.swap
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem pairEquiv_swap (r : ℕ) (x : Pair r → ℚ) (k : EigenIndex r) :
    pairEquiv r (pairSwap r x) k = eigenSign k * pairEquiv r x k := by
  rcases k with (a | p) | p <;> simp [pairTo, pairSwap, eigenSign] <;> ring

noncomputable def pairBasis (r : ℕ) : Module.Basis (EigenIndex r) ℚ (Pair r → ℚ) :=
  (Pi.basisFun ℚ (EigenIndex r)).map (pairEquiv r).symm

@[simp] theorem pairEquiv_pairBasis (r : ℕ) (k : EigenIndex r) :
    pairEquiv r (pairBasis r k) = Pi.single k 1 := by
  simp [pairBasis]

theorem pairBasis_eigen (r : ℕ) (k : EigenIndex r) :
    pairSwap r (pairBasis r k) = eigenSign k • pairBasis r k := by
  apply (pairEquiv r).injective
  ext l
  rw [pairEquiv_swap, map_smul, pairEquiv_pairBasis]
  by_cases hl : l = k
  · subst l
    simp
  · simp [hl]

theorem eigenIndex_card (r : ℕ) : Fintype.card (EigenIndex r) = r * r := by
  have h := Module.finrank_eq_card_basis (pairBasis r)
  rw [Module.finrank_pi] at h
  simpa [Pair] using h.symm

theorem strictPair_card_relation (r : ℕ) :
    r + 2 * Fintype.card (StrictPair r) = r * r := by
  have h := eigenIndex_card r
  simp only [EigenIndex, PlusIndex, Fintype.card_sum, Fintype.card_fin] at h
  omega

theorem minusIndex_card (r : ℕ) : Fintype.card (StrictPair r) = r * (r - 1) / 2 := by
  have h := strictPair_card_relation r
  have he : r * (r - 1) = 2 * Fintype.card (StrictPair r) := by
    rw [Nat.mul_sub_left_distrib, Nat.mul_one]
    omega
  rw [he]
  omega

theorem plusIndex_card (r : ℕ) : Fintype.card (PlusIndex r) = r * (r + 1) / 2 := by
  have h := strictPair_card_relation r
  have he : r * (r + 1) = 2 * (r + Fintype.card (StrictPair r)) := by nlinarith
  simp only [PlusIndex, Fintype.card_sum, Fintype.card_fin]
  rw [he]
  omega

end ExactSolution.SwapSpectrum
