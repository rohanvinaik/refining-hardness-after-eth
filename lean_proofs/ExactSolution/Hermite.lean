import Mathlib.Algebra.Polynomial.Taylor
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Tactic

/-!
# Initial Taylor jets and the Hermite degree threshold

Nodes are a finite set of rational numbers, so distinctness is built into their
representation. The jet at a node consists of actual coefficients of
`Polynomial.taylor`, not an abstract oracle or an assumed uniqueness contract.

The vanishing product records the multiplicity requested at each node. Its
divisibility characterization gives uniqueness above the degree budget. Adding
it gives an explicit ambiguity within the degree budget; nonzero nodes ensure
that this ambiguity changes the value at zero.
-/

namespace ExactSolution

open Polynomial
open scoped BigOperators

/-- Equality of the initial `J t` Taylor coefficients at every observed node. -/
def TaylorJetsEqual (nodes : Finset ℚ) (J : ℚ → ℕ) (f g : ℚ[X]) : Prop :=
  ∀ t ∈ nodes, ∀ k < J t,
    (taylor t f).coeff k = (taylor t g).coeff k

/-- The polynomial vanishing to the requested multiplicity at every node. -/
noncomputable def hermiteVanishing (nodes : Finset ℚ) (J : ℚ → ℕ) : ℚ[X] :=
  ∏ t ∈ nodes, (X - C t) ^ J t

/-- Initial Taylor coefficients vanish exactly when the corresponding power
of the node's linear factor divides the polynomial. -/
theorem pow_X_sub_C_dvd_iff_initialTaylor_zero (f : ℚ[X]) (t : ℚ) (J : ℕ) :
    (X - C t) ^ J ∣ f ↔ ∀ k < J, (taylor t f).coeff k = 0 := by
  constructor
  · rintro ⟨q, rfl⟩
    apply Polynomial.X_pow_dvd_iff.mp
    have hshift : taylor t (X - C t : ℚ[X]) = X := by simp
    rw [Polynomial.taylor_mul, Polynomial.taylor_pow, hshift]
    exact dvd_mul_right _ _
  · intro hcoeff
    obtain ⟨q, hq⟩ := Polynomial.X_pow_dvd_iff.mpr hcoeff
    refine ⟨taylor (-t) q, ?_⟩
    have htranslated := congrArg (taylor (-t)) hq
    simpa [Polynomial.taylor_taylor, Polynomial.taylor_mul,
      Polynomial.taylor_pow, sub_eq_add_neg] using htranslated

/-- The vanishing product is nonzero, including for an empty node set. -/
theorem hermiteVanishing_ne_zero (nodes : Finset ℚ) (J : ℚ → ℕ) :
    hermiteVanishing nodes J ≠ 0 := by
  unfold hermiteVanishing
  exact Finset.prod_ne_zero_iff.mpr fun t _ =>
    pow_ne_zero _ (Polynomial.X_sub_C_ne_zero t)

/-- Its degree is precisely the total number of observed scalar coefficients. -/
theorem natDegree_hermiteVanishing (nodes : Finset ℚ) (J : ℚ → ℕ) :
    (hermiteVanishing nodes J).natDegree = ∑ t ∈ nodes, J t := by
  unfold hermiteVanishing
  rw [Polynomial.natDegree_prod]
  · simp
  · intro t _
    exact pow_ne_zero _ (Polynomial.X_sub_C_ne_zero t)

/-- Each requested node factor divides the full vanishing product. -/
theorem node_power_dvd_hermiteVanishing (nodes : Finset ℚ) (J : ℚ → ℕ)
    {t : ℚ} (ht : t ∈ nodes) :
    (X - C t) ^ J t ∣ hermiteVanishing nodes J := by
  exact Finset.dvd_prod_of_mem (fun u : ℚ => (X - C u) ^ J u) ht

/-- Adding the vanishing product leaves every requested Taylor coefficient
unchanged. -/
theorem taylorJetsEqual_add_hermiteVanishing (nodes : Finset ℚ) (J : ℚ → ℕ)
    (f : ℚ[X]) : TaylorJetsEqual nodes J f (f + hermiteVanishing nodes J) := by
  intro t ht k hk
  have hzero := (pow_X_sub_C_dvd_iff_initialTaylor_zero
    (hermiteVanishing nodes J) t (J t)).mp
    (node_power_dvd_hermiteVanishing nodes J ht) k hk
  simp only [map_add, Polynomial.coeff_add, hzero, add_zero]

/-- With no node at zero, the vanishing product has nonzero value at zero. -/
theorem eval_zero_hermiteVanishing_ne_zero (nodes : Finset ℚ) (J : ℚ → ℕ)
    (hnodes : ∀ t ∈ nodes, t ≠ 0) :
    (hermiteVanishing nodes J).eval 0 ≠ 0 := by
  unfold hermiteVanishing
  simp only [Polynomial.eval_prod, Polynomial.eval_pow, Polynomial.eval_sub,
    Polynomial.eval_X, Polynomial.eval_C, zero_sub]
  exact Finset.prod_ne_zero_iff.mpr fun t ht =>
    pow_ne_zero _ (neg_ne_zero.mpr (hnodes t ht))

/-- The perturbation changes the task value `f(0)`, not only the polynomial. -/
theorem eval_zero_add_hermiteVanishing_ne (nodes : Finset ℚ) (J : ℚ → ℕ)
    (f : ℚ[X]) (hnodes : ∀ t ∈ nodes, t ≠ 0) :
    (f + hermiteVanishing nodes J).eval 0 ≠ f.eval 0 := by
  simpa only [Polynomial.eval_add, ne_eq, add_eq_left] using
    eval_zero_hermiteVanishing_ne_zero nodes J hnodes

/-- Equal initial Taylor jets force the complete vanishing product to divide
the polynomial difference. Distinct nodes supply coprime linear factors. -/
theorem hermiteVanishing_dvd_sub_of_taylorJetsEqual (nodes : Finset ℚ)
    (J : ℚ → ℕ) (f g : ℚ[X]) (hjets : TaylorJetsEqual nodes J f g) :
    hermiteVanishing nodes J ∣ f - g := by
  apply Finset.prod_dvd_of_coprime
  · intro t _ u _ htu
    exact (Polynomial.pairwise_coprime_X_sub_C (Function.injective_id) htu).pow
  · intro t ht
    apply (pow_X_sub_C_dvd_iff_initialTaylor_zero (f - g) t (J t)).mpr
    intro k hk
    simp only [map_sub, Polynomial.coeff_sub, sub_eq_zero]
    exact hjets t ht k hk

/-- Hermite sufficiency: more scalar coefficients than the ambient degree
budget determine the entire rational polynomial. -/
theorem hermite_unique (nodes : Finset ℚ) (J : ℚ → ℕ) (d : ℕ)
    (f g : ℚ[X]) (hf : f.natDegree ≤ d) (hg : g.natDegree ≤ d)
    (hcount : d < ∑ t ∈ nodes, J t) (hjets : TaylorJetsEqual nodes J f g) :
    f = g := by
  apply sub_eq_zero.mp
  by_contra hnonzero
  have hdiv := hermiteVanishing_dvd_sub_of_taylorJetsEqual nodes J f g hjets
  have hlower := Polynomial.natDegree_le_of_dvd hdiv hnonzero
  have hupper : (f - g).natDegree ≤ d :=
    (Polynomial.natDegree_sub_le f g).trans (max_le hf hg)
  rw [natDegree_hermiteVanishing] at hlower
  omega

/-- Hermite necessity for the ambient bounded-degree class: if the total
multiplicity fits the budget and nodes are nonzero, every target has another
admissible polynomial with the same jets and a different value at zero. -/
theorem hermite_nonunique (nodes : Finset ℚ) (J : ℚ → ℕ) (d : ℕ)
    (f : ℚ[X]) (hf : f.natDegree ≤ d)
    (hcount : (∑ t ∈ nodes, J t) ≤ d)
    (hnodes : ∀ t ∈ nodes, t ≠ 0) :
    ∃ g : ℚ[X], g.natDegree ≤ d ∧ TaylorJetsEqual nodes J f g ∧
      g.eval 0 ≠ f.eval 0 := by
  refine ⟨f + hermiteVanishing nodes J, ?_,
    taylorJetsEqual_add_hermiteVanishing nodes J f,
    eval_zero_add_hermiteVanishing_ne nodes J f hnodes⟩
  apply (Polynomial.natDegree_add_le _ _).trans
  apply max_le hf
  simpa only [natDegree_hermiteVanishing] using hcount

/-- For nonzero nodes, the scalar-count threshold is also necessary and
sufficient for determining just the task value at zero throughout the ambient
bounded-degree class. -/
theorem hermite_value_at_zero_determined_iff (nodes : Finset ℚ) (J : ℚ → ℕ)
    (d : ℕ) (hnodes : ∀ t ∈ nodes, t ≠ 0) :
    (∀ f g : ℚ[X], f.natDegree ≤ d → g.natDegree ≤ d →
      TaylorJetsEqual nodes J f g → f.eval 0 = g.eval 0) ↔
      d < ∑ t ∈ nodes, J t := by
  constructor
  · intro hdetermined
    by_contra hcount
    have hcount' : (∑ t ∈ nodes, J t) ≤ d := Nat.le_of_not_gt hcount
    obtain ⟨g, hg, hjets, hne⟩ := hermite_nonunique nodes J d 0
      (by simp) hcount' hnodes
    exact hne (hdetermined 0 g (by simp) hg hjets).symm
  · intro hcount f g hf hg hjets
    rw [hermite_unique nodes J d f g hf hg hcount hjets]

end ExactSolution
