import ExactSolution.Observation

/-!
# Distinguishability capacity

Finite witnesses are covered by observations on which they disagree with the
target. The certificate supplies the covering property; the capacity premise
then bounds the number of witnesses any one observation can remove.
-/

namespace ExactSolution

theorem cover_capacity {α β : Type*} [DecidableEq α] [DecidableEq β]
    (W : Finset α) (T : Finset β) (K : β → Finset α)
    (r : ℕ) (hcover : W ⊆ T.biUnion K)
    (hcap : ∀ e ∈ T, (K e).card ≤ r) :
    W.card ≤ T.card * r := by
  calc
    W.card ≤ (T.biUnion K).card := Finset.card_le_card hcover
    _ ≤ ∑ e ∈ T, (K e).card := Finset.card_biUnion_le
    _ ≤ ∑ _e ∈ T, r := Finset.sum_le_sum hcap
    _ = T.card * r := by simp

noncomputable def disagreementWitnesses {C E A : Type*}
    (observe : E → C → A) (target : C) (W : Finset C) (e : E) : Finset C := by
  classical
  exact W.filter fun g => observe e g ≠ observe e target

theorem certificate_covers_witnesses {C E A Y : Type*} [DecidableEq C] [DecidableEq E]
    {admissible : Set C} {observe : E → C → A} {task : C → Y} {target : C}
    (W : Finset C) (T : Finset E)
    (hwitnesses : ∀ g ∈ W, g ∈ admissible ∧ task g ≠ task target)
    (hcertificate : IsCertificate admissible observe task target T) :
    W ⊆ T.biUnion (disagreementWitnesses observe target W) := by
  classical
  intro g hg
  by_contra hmissing
  have hagree : AgreesOn observe T target g := by
    intro e he
    by_contra hdifferent
    apply hmissing
    apply Finset.mem_biUnion.mpr
    refine ⟨e, he, ?_⟩
    simp only [disagreementWitnesses, Finset.mem_filter]
    exact ⟨hg, hdifferent⟩
  exact (hwitnesses g hg).2 (hcertificate g (hwitnesses g hg).1 hagree)

/-- Witness coverage in the integer form `M ≤ s*r`, before dividing
by the positive capacity `r`. Capacity zero is covered without division. -/
theorem distinguishability_capacity_bound {C E A Y : Type*}
    [DecidableEq C] [DecidableEq E]
    {admissible : Set C} {observe : E → C → A} {task : C → Y} {target : C}
    (W : Finset C) (T : Finset E) (r : ℕ)
    (hwitnesses : ∀ g ∈ W, g ∈ admissible ∧ task g ≠ task target)
    (hcertificate : IsCertificate admissible observe task target T)
    (hcapacity : ∀ e ∈ T, (disagreementWitnesses observe target W e).card ≤ r) :
    W.card ≤ T.card * r := by
  exact cover_capacity W T _ r
    (certificate_covers_witnesses W T hwitnesses hcertificate) hcapacity

theorem distinguishability_ceiling_bound {C E A Y : Type*}
    [DecidableEq C] [DecidableEq E]
    {admissible : Set C} {observe : E → C → A} {task : C → Y} {target : C}
    (W : Finset C) (T : Finset E) (r : ℕ) (hr : 0 < r)
    (hwitnesses : ∀ g ∈ W, g ∈ admissible ∧ task g ≠ task target)
    (hcertificate : IsCertificate admissible observe task target T)
    (hcapacity : ∀ e ∈ T, (disagreementWitnesses observe target W e).card ≤ r) :
    ⌈(W.card : ℝ) / r⌉₊ ≤ T.card := by
  rw [Nat.ceil_le]
  apply (div_le_iff₀ (show 0 < (r : ℝ) by exact_mod_cast hr)).mpr
  exact_mod_cast distinguishability_capacity_bound W T r hwitnesses hcertificate hcapacity

theorem distinguishability_complexity_lower {C E A Y : Type*}
    [DecidableEq C] [DecidableEq E]
    {admissible : Set C} {observe : E → C → A} {task : C → Y} {target : C}
    (W : Finset C) (r : ℕ) (hr : 0 < r)
    (hwitnesses : ∀ g ∈ W, g ∈ admissible ∧ task g ≠ task target)
    (hcapacity : ∀ e, (disagreementWitnesses observe target W e).card ≤ r) :
    (⌈(W.card : ℝ) / r⌉₊ : WithTop ℕ) ≤
      certificateComplexity admissible observe task target := by
  apply le_complexity
  intro T hT
  exact_mod_cast distinguishability_ceiling_bound W T r hr hwitnesses hT
    (fun e _ => hcapacity e)

end ExactSolution
