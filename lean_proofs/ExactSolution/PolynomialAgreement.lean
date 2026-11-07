import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Tactic

/-!
# Polynomial agreement with alternating signs

This module formalizes the algebraic part of the swap-construction degree
floor. It does not formalize the binomial distribution, the mode bound, or the
translation from the auxiliary matrix construction to a probability of failure.

All conclusions below follow from polynomial root counting. In particular,
no bound on the agreement set is assumed as a hypothesis.
-/

namespace ExactSolution

open Polynomial

/-- Indices in a finite set where a rational polynomial has the required
alternating sign. -/
def parityAgreement (f : ℚ[X]) (s : Finset ℕ) : Finset ℕ :=
  s.filter fun j : ℕ => f.eval (j : ℚ) = (-1 : ℚ) ^ j

/-- A polynomial distinct from the constant `a` takes the value `a` at no
more than its degree many distinct natural-number arguments. -/
theorem card_constant_agreement_le_natDegree (f : ℚ[X]) (s : Finset ℕ)
    (a : ℚ) (hconstant : f ≠ C a) :
    (s.filter fun j : ℕ => f.eval (j : ℚ) = a).card ≤ f.natDegree := by
  classical
  let t := s.filter fun j : ℕ => f.eval (j : ℚ) = a
  have hcast : Function.Injective (fun j : ℕ => (j : ℚ)) := Nat.cast_injective
  have hroots : t.image (fun j : ℕ => (j : ℚ)) ⊆ (f - C a).roots.toFinset := by
    intro x hx
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hx
    apply Multiset.mem_toFinset.mpr
    exact Polynomial.mem_roots_sub_C'.mpr ⟨hconstant, (Finset.mem_filter.mp hj).2⟩
  have hdegree : (f - C a).natDegree ≤ f.natDegree := by
    simp
  calc
    t.card = (t.image (fun j : ℕ => (j : ℚ))).card :=
      (Finset.card_image_of_injective t hcast).symm
    _ ≤ (f - C a).roots.toFinset.card := Finset.card_le_card hroots
    _ ≤ (f - C a).roots.card := Multiset.toFinset_card_le _
    _ ≤ (f - C a).natDegree := Polynomial.card_roots' _
    _ ≤ f.natDegree := hdegree

/-- Every integer power of `-1` is one of the two possible signs. -/
theorem alternating_sign_eq_one_or_neg_one (j : ℕ) :
    (-1 : ℚ) ^ j = 1 ∨ (-1 : ℚ) ^ j = -1 := by
  induction j with
  | zero => simp
  | succ j ih =>
      rcases ih with h | h
      · right
        simp [pow_succ, h]
      · left
        simp [pow_succ, h]

/-- Outside the two constant polynomials, agreement with alternating signs
has cardinality at most twice the polynomial's degree. The finite index set
is arbitrary; it need not be an interval. -/
theorem card_parityAgreement_le_twice_natDegree (f : ℚ[X]) (s : Finset ℕ)
    (hplus : f ≠ C 1) (hminus : f ≠ C (-1)) :
    (parityAgreement f s).card ≤ 2 * f.natDegree := by
  classical
  have hcover : parityAgreement f s ⊆
      (s.filter fun j : ℕ => f.eval (j : ℚ) = 1) ∪
        (s.filter fun j : ℕ => f.eval (j : ℚ) = -1) := by
    intro j hj
    obtain ⟨hjs, hjeval⟩ := Finset.mem_filter.mp hj
    rcases alternating_sign_eq_one_or_neg_one j with h | h
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hjs, hjeval.trans h⟩)
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hjs, hjeval.trans h⟩)
  calc
    (parityAgreement f s).card ≤
        ((s.filter fun j : ℕ => f.eval (j : ℚ) = 1) ∪
          (s.filter fun j : ℕ => f.eval (j : ℚ) = -1)).card :=
      Finset.card_le_card hcover
    _ ≤ (s.filter fun j : ℕ => f.eval (j : ℚ) = 1).card +
        (s.filter fun j : ℕ => f.eval (j : ℚ) = -1).card :=
      Finset.card_union_le _ _
    _ ≤ f.natDegree + f.natDegree := Nat.add_le_add
      (card_constant_agreement_le_natDegree f s 1 hplus)
      (card_constant_agreement_le_natDegree f s (-1) hminus)
    _ = 2 * f.natDegree := by omega

/-- Algebraic agreement bound used in the degree floor: if `deg f < R`
and `f` is neither constant sign, there are at most `2R - 2` agreements.
Using `natDegree` makes the positive degree-budget convention explicit. -/
theorem card_parityAgreement_le (f : ℚ[X]) (s : Finset ℕ) (R : ℕ)
    (hdegree : f.natDegree < R) (hplus : f ≠ C 1) (hminus : f ≠ C (-1)) :
    (parityAgreement f s).card ≤ 2 * R - 2 := by
  have h := card_parityAgreement_le_twice_natDegree f s hplus hminus
  omega

/-- The finite-support form for the possible swap-odd counts `0,...,Q`.
The exceptional constant cases are retained, rather than silently excluded. -/
theorem swap_agreement_dichotomy (f : ℚ[X]) (Q R : ℕ)
    (hdegree : f.natDegree < R) :
    f = C 1 ∨ f = C (-1) ∨
      (parityAgreement f (Finset.range (Q + 1))).card ≤ 2 * R - 2 := by
  by_cases hplus : f = C 1
  · exact Or.inl hplus
  by_cases hminus : f = C (-1)
  · exact Or.inr (Or.inl hminus)
  exact Or.inr (Or.inr (card_parityAgreement_le f _ R hdegree hplus hminus))

end ExactSolution
