import Mathlib

/-!
# Task-relative observation certificates

A finite set of observations certifies a task when every agreeing admissible
object has the target's task value. Certificate complexity is the infimum of
the cardinalities of such sets, with infinity when no finite certificate exists.
The operational transcript model is in `ExactSolution.Transcript`; neither
module identifies certificate size with the cost of discovering a certificate.
-/

namespace ExactSolution

def AgreesOn {C E A : Type*} (observe : E → C → A)
    (T : Finset E) (f g : C) : Prop :=
  ∀ e ∈ T, observe e g = observe e f

def IsCertificate {C E A Y : Type*} (admissible : Set C)
    (observe : E → C → A) (task : C → Y) (target : C) (T : Finset E) : Prop :=
  ∀ g ∈ admissible, AgreesOn observe T target g → task g = task target

theorem agreesOn_mono {C E A : Type*} {observe : E → C → A}
    {S T : Finset E} {f g : C} (hST : S ⊆ T)
    (h : AgreesOn observe T f g) : AgreesOn observe S f g := by
  intro e he
  exact h e (hST he)

theorem certificate_mono {C E A Y : Type*} {admissible : Set C}
    {observe : E → C → A} {task : C → Y} {target : C}
    {S T : Finset E} (hS : IsCertificate admissible observe task target S)
    (hST : S ⊆ T) : IsCertificate admissible observe task target T := by
  intro g hg h
  exact hS g hg (agreesOn_mono hST h)

theorem full_point_certificate {X A Y : Type*} [Fintype X]
    (admissible : Set (X → A)) (task : (X → A) → Y) (target : X → A) :
    IsCertificate admissible (fun x f => f x) task target Finset.univ := by
  intro g _ h
  have hgf : g = target := funext (fun x => h x (Finset.mem_univ x))
  exact congrArg task hgf

/-- The infimum is top precisely when the set of finite certificates is empty. -/
noncomputable def certificateComplexity {C E A Y : Type*} (admissible : Set C)
    (observe : E → C → A) (task : C → Y) (target : C) : WithTop ℕ :=
  sInf {k | ∃ T : Finset E,
    IsCertificate admissible observe task target T ∧ (T.card : WithTop ℕ) = k}

theorem complexity_le_card {C E A Y : Type*} {admissible : Set C}
    {observe : E → C → A} {task : C → Y} {target : C} {T : Finset E}
    (hT : IsCertificate admissible observe task target T) :
    certificateComplexity admissible observe task target ≤ (T.card : WithTop ℕ) := by
  exact sInf_le ⟨T, hT, rfl⟩

theorem le_complexity {C E A Y : Type*} {admissible : Set C}
    {observe : E → C → A} {task : C → Y} {target : C} {m : WithTop ℕ}
    (hm : ∀ T : Finset E, IsCertificate admissible observe task target T →
      m ≤ (T.card : WithTop ℕ)) :
    m ≤ certificateComplexity admissible observe task target := by
  apply le_sInf
  rintro k ⟨T, hT, rfl⟩
  exact hm T hT

theorem explicit_input_ceiling {L : ℕ} {Y : Type*}
    (admissible : Set (Fin L → Bool)) (task : (Fin L → Bool) → Y)
    (target : Fin L → Bool) :
    certificateComplexity admissible (fun i x => x i) task target ≤ (L : WithTop ℕ) := by
  simpa using complexity_le_card (full_point_certificate admissible task target)

end ExactSolution
