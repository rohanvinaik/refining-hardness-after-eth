import ExactSolution.Observability

/-!
# Deterministic terminating transcripts

The policy receives only the previous query/answer pairs. It may continue
forever on some inputs: `Executes` asserts only a particular finite terminating
execution. No source identity or future answers enter the policy.
-/

namespace ExactSolution

def transcriptQueries {E A : Type*} [DecidableEq E]
    (transcript : List (E × A)) : Finset E :=
  (transcript.map Prod.fst).toFinset

inductive Executes {C E A Y : Type*} (observe : E → C → A)
    (policy : List (E × A) → E ⊕ Y) (target : C) :
    List (E × A) → List (E × A) → Y → Prop where
  | stop {history : List (E × A)} {result : Y}
      (halt : policy history = Sum.inr result) :
      Executes observe policy target history [] result
  | step {history tail : List (E × A)} {e : E} {result : Y}
      (ask : policy history = Sum.inl e)
      (rest : Executes observe policy target
        (history ++ [(e, observe e target)]) tail result) :
      Executes observe policy target history ((e, observe e target) :: tail) result

theorem Executes.replay {C E A Y : Type*} [DecidableEq E]
    {observe : E → C → A} {policy : List (E × A) → E ⊕ Y}
    {f g : C} {history transcript : List (E × A)} {result : Y}
    (execution : Executes observe policy f history transcript result)
    (agree : AgreesOn observe (transcriptQueries transcript) f g) :
    Executes observe policy g history transcript result := by
  induction execution with
  | stop halt => exact Executes.stop halt
  | @step history tail e result ask rest ih =>
      have he : observe e g = observe e f := agree e (by simp [transcriptQueries])
      have htail : AgreesOn observe (transcriptQueries tail) f g := by
        intro e' he'
        exact agree e' (by simpa [transcriptQueries] using Or.inr he')
      have hrest := ih htail
      have hrest' : Executes observe policy g
          (history ++ [(e, observe e g)]) tail result := by
        simpa [he] using hrest
      have hstep : Executes observe policy g history
          ((e, observe e g) :: tail) result := Executes.step ask hrest'
      simpa [he] using hstep

/-- The observations in a terminating, globally correct run
certify its task at the target. Correctness is required on all admissible
objects, but termination is required only for the displayed execution. -/
theorem transcript_certificate {C E A Y : Type*} [DecidableEq E]
    (observe : E → C → A) (policy : List (E × A) → E ⊕ Y)
    (admissible : Set C) (task : C → Y)
    (correct : ∀ f ∈ admissible, ∀ transcript result,
      Executes observe policy f [] transcript result → result = task f)
    {target : C} (htarget : target ∈ admissible)
    {transcript : List (E × A)} {result : Y}
    (execution : Executes observe policy target [] transcript result) :
    IsCertificate admissible observe task target (transcriptQueries transcript) := by
  intro g hg agree
  calc
    task g = result := (correct g hg transcript result (execution.replay agree)).symm
    _ = task target := correct target htarget transcript result execution

theorem transcript_query_lower_bound {C E A Y : Type*} [DecidableEq E]
    (observe : E → C → A) (policy : List (E × A) → E ⊕ Y)
    (admissible : Set C) (task : C → Y)
    (correct : ∀ f ∈ admissible, ∀ transcript result,
      Executes observe policy f [] transcript result → result = task f)
    {target : C} (htarget : target ∈ admissible)
    {transcript : List (E × A)} {result : Y}
    (execution : Executes observe policy target [] transcript result) :
    certificateComplexity admissible observe task target ≤
      (transcript.length : WithTop ℕ) := by
  have hc := complexity_le_card
    (transcript_certificate observe policy admissible task correct htarget execution)
  have hlength : (transcriptQueries transcript).card ≤ transcript.length := by
    simpa [transcriptQueries] using List.toFinset_card_le (transcript.map Prod.fst)
  exact hc.trans (by exact_mod_cast hlength)

/-- In the operational model, a task-changing indistinguishable
alternative rules out termination of a globally correct policy at this target. -/
theorem ambiguity_precludes_termination {C E A Y : Type*} [DecidableEq E]
    (observe : E → C → A) (policy : List (E × A) → E ⊕ Y)
    (admissible : Set C) (task : C → Y)
    (correct : ∀ f ∈ admissible, ∀ transcript result,
      Executes observe policy f [] transcript result → result = task f)
    {target other : C} (htarget : target ∈ admissible) (hother : other ∈ admissible)
    (hobservations : observationVector observe target = observationVector observe other)
    (htask : task other ≠ task target)
    {transcript : List (E × A)} {result : Y} :
    ¬ Executes observe policy target [] transcript result := by
  intro execution
  exact indistinguishable_no_certificate hother hobservations htask _
    (transcript_certificate observe policy admissible task correct htarget execution)

end ExactSolution
