import ExactSolution.Composition

/-!
# Cost-preserving observation simulation

Every simulated observation is decoded from a specified finite set of source
observations. The decoder is a function on the actual answer vector. Taking
the union of these source sets transports a certificate; nonnegative costs
bound the union by the summed simulation charges.
-/

namespace ExactSolution

open scoped BigOperators

section Simulation

variable {C E A Y C' E' A' : Type*} [DecidableEq E]

def simulatedCertificate (simulation : E' → Finset E) (T : Finset E') : Finset E :=
  T.biUnion simulation

/-- A new certificate transports through actual finite observation decoders.
Task preservation and admissibility preservation are explicit hypotheses. -/
theorem simulation_certificate
    {admissible : Set C} {observe : E → C → A} {task : C → Y} {target : C}
    {admissible' : Set C'} {observe' : E' → C' → A'} {task' : C' → Y}
    (representation : C → C') (simulation : E' → Finset E)
    (decode : ∀ e', ({e : E // e ∈ simulation e'} → A) → A')
    (htarget : target ∈ admissible)
    (hrepresentation : ∀ g ∈ admissible, representation g ∈ admissible')
    (htask : ∀ g ∈ admissible, task' (representation g) = task g)
    (hsimulation : ∀ e' g, g ∈ admissible →
      observe' e' (representation g) = decode e' (fun e => observe e.1 g))
    (T' : Finset E')
    (hcertificate : IsCertificate admissible' observe' task' (representation target) T') :
    IsCertificate admissible observe task target (simulatedCertificate simulation T') := by
  intro g hg hagree
  have hnew : AgreesOn observe' T' (representation target) (representation g) := by
    intro e' he'
    have hvectors : (fun e : {e : E // e ∈ simulation e'} => observe e.1 g) =
        (fun e : {e : E // e ∈ simulation e'} => observe e.1 target) := by
      funext e
      exact hagree e.1 (Finset.mem_biUnion.mpr ⟨e', he', e.2⟩)
    rw [hsimulation e' g hg, hsimulation e' target htarget, hvectors]
  calc
    task g = task' (representation g) := (htask g hg).symm
    _ = task' (representation target) :=
      hcertificate (representation g) (hrepresentation g hg) hnew
    _ = task target := htask target htarget

/-- The finite union of simulations costs no more than their summed charges. -/
theorem simulation_certificate_cost_bound
    (simulation : E' → Finset E) (cost : E → ENNReal) (cost' : E' → ENNReal)
    (K : ENNReal) (T' : Finset E')
    (hcharges : ∀ e' ∈ T', (∑ e ∈ simulation e', cost e) ≤ K * cost' e') :
    (∑ e ∈ simulatedCertificate simulation T', cost e) ≤
      K * ∑ e' ∈ T', cost' e' := by
  calc
    _ ≤ ∑ e' ∈ T', ∑ e ∈ simulation e', cost e :=
      sum_biUnion_cost_le T' simulation cost
    _ ≤ ∑ e' ∈ T', K * cost' e' := Finset.sum_le_sum hcharges
    _ = _ := (Finset.mul_sum _ _ _).symm

/-- Cost-preserving finite simulations bound weighted certificate complexity.
Finite new observation families provide an attained new optimum.
If no new certificate exists, its complexity is infinity and `K ≠ 0` makes
the bound immediate. Finite positive real factors are included. -/
theorem weighted_observation_simulation [Fintype E']
    {admissible : Set C} {observe : E → C → A} {task : C → Y} {target : C}
    {admissible' : Set C'} {observe' : E' → C' → A'} {task' : C' → Y}
    (representation : C → C') (simulation : E' → Finset E)
    (decode : ∀ e', ({e : E // e ∈ simulation e'} → A) → A')
    (cost : E → ENNReal) (cost' : E' → ENNReal) (K : ENNReal) (hK : K ≠ 0)
    (htarget : target ∈ admissible)
    (hrepresentation : ∀ g ∈ admissible, representation g ∈ admissible')
    (htask : ∀ g ∈ admissible, task' (representation g) = task g)
    (hsimulation : ∀ e' g, g ∈ admissible →
      observe' e' (representation g) = decode e' (fun e => observe e.1 g))
    (hcharges : ∀ e', (∑ e ∈ simulation e', cost e) ≤ K * cost' e') :
    weightedCertificateComplexity admissible observe task target cost ≤
      K * weightedCertificateComplexity admissible' observe' task'
        (representation target) cost' := by
  classical
  by_cases hexists : ∃ T',
      IsCertificate admissible' observe' task' (representation target) T'
  · obtain ⟨T', hT', hcost'⟩ := weighted_complexity_attained (cost := cost') hexists
    have hsource := simulation_certificate representation simulation decode htarget
      hrepresentation htask hsimulation T' hT'
    calc
      _ ≤ ∑ e ∈ simulatedCertificate simulation T', cost e :=
        weighted_complexity_le_cost hsource
      _ ≤ K * ∑ e' ∈ T', cost' e' :=
        simulation_certificate_cost_bound simulation cost cost' K T'
          (fun e' _ => hcharges e')
      _ = _ := by rw [hcost']
  · have htop : weightedCertificateComplexity admissible' observe' task'
        (representation target) cost' = ⊤ := by
      unfold weightedCertificateComplexity
      have hempty : {k | ∃ T' : Finset E',
          IsCertificate admissible' observe' task' (representation target) T' ∧
            (∑ e' ∈ T', cost' e') = k} = ∅ := by
        ext k
        simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
        rintro ⟨T', hT', _⟩
        exact hexists ⟨T', hT'⟩
      rw [hempty]
      exact sInf_empty
    rw [htop, ENNReal.mul_top hK]
    exact le_top

end Simulation

end ExactSolution
