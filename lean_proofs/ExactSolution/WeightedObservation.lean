import ExactSolution.Observation

/-!
# Weighted observation certificates

Extended nonnegative costs include the manuscripts' finite positive costs and
make impossibility expressible as infinity. The available observation family
is finite whenever attainment is asserted.
-/

namespace ExactSolution

open scoped ENNReal BigOperators

noncomputable def weightedCertificateComplexity {C E A Y : Type*}
    (admissible : Set C) (observe : E → C → A) (task : C → Y)
    (target : C) (cost : E → ℝ≥0∞) : ℝ≥0∞ :=
  sInf {k | ∃ T : Finset E, IsCertificate admissible observe task target T ∧
    (∑ e ∈ T, cost e) = k}

theorem weighted_complexity_le_cost {C E A Y : Type*}
    {admissible : Set C} {observe : E → C → A} {task : C → Y}
    {target : C} {cost : E → ℝ≥0∞} {T : Finset E}
    (hT : IsCertificate admissible observe task target T) :
    weightedCertificateComplexity admissible observe task target cost ≤ ∑ e ∈ T, cost e := by
  exact sInf_le ⟨T, hT, rfl⟩

theorem le_weighted_complexity {C E A Y : Type*}
    {admissible : Set C} {observe : E → C → A} {task : C → Y}
    {target : C} {cost : E → ℝ≥0∞} {m : ℝ≥0∞}
    (hm : ∀ T : Finset E, IsCertificate admissible observe task target T →
      m ≤ ∑ e ∈ T, cost e) :
    m ≤ weightedCertificateComplexity admissible observe task target cost := by
  apply le_sInf
  rintro k ⟨T, hT, rfl⟩
  exact hm T hT

theorem weighted_complexity_attained {C E A Y : Type*} [Fintype E]
    {admissible : Set C} {observe : E → C → A} {task : C → Y}
    {target : C} {cost : E → ℝ≥0∞}
    (hexists : ∃ T : Finset E, IsCertificate admissible observe task target T) :
    ∃ T : Finset E, IsCertificate admissible observe task target T ∧
      (∑ e ∈ T, cost e) =
        weightedCertificateComplexity admissible observe task target cost := by
  classical
  let certificates := Finset.univ.filter
    (fun T : Finset E => IsCertificate admissible observe task target T)
  let charge := fun T : Finset E => ∑ e ∈ T, cost e
  have hnonempty : certificates.Nonempty := by
    obtain ⟨T, hT⟩ := hexists
    exact ⟨T, Finset.mem_filter.mpr ⟨Finset.mem_univ T, hT⟩⟩
  obtain ⟨T, hT, hmin⟩ := certificates.exists_min_image charge hnonempty
  have hcertificate : IsCertificate admissible observe task target T :=
    (Finset.mem_filter.mp hT).2
  refine ⟨T, hcertificate, le_antisymm ?_ (weighted_complexity_le_cost hcertificate)⟩
  apply le_weighted_complexity
  intro S hS
  exact hmin S (Finset.mem_filter.mpr ⟨Finset.mem_univ S, hS⟩)

end ExactSolution
