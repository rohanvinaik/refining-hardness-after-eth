import ExactSolution.Discovery

/-!
# An operational read-all strategy

The tree accumulates observed bits in an initially zero function.  The task
is applied only to the reconstructed function at a terminal node.  No source
identity is supplied to the policy.
-/

namespace ExactSolution.ReadAll

open Discovery

variable {X Y : Type*} [DecidableEq X]

def tree (acquired : X → Bool) : List X → SearchTree X
  | [] => .answer acquired
  | x :: rest => .query x (fun value => tree (Function.update acquired x value) rest)

theorem tree_run_apply (acquired f : X → Bool) (points : List X) (x : X) :
    (tree acquired points).run f x = if x ∈ points then f x else acquired x := by
  induction points generalizing acquired with
  | nil => simp [tree, SearchTree.run]
  | cons a rest ih =>
    simp only [tree, SearchTree.run]
    rw [ih]
    by_cases hx : x = a <;> by_cases hr : x ∈ rest <;>
      simp [hx, hr, Function.update_apply]

theorem tree_trace_length (acquired f : X → Bool) (points : List X) :
    ((tree acquired points).trace f).length = points.length := by
  induction points generalizing acquired with
  | nil => rfl
  | cons x rest ih => simp [tree, SearchTree.trace, ih]

def mapPolicy (task : (X → Bool) → Y) (policy : Policy X)
    (history : List (X × Bool)) : X ⊕ Y := Sum.map id task (policy history)

omit [DecidableEq X] in
theorem map_execution (task : (X → Bool) → Y) {policy : Policy X}
    {f : X → Bool} {history transcript : List (X × Bool)} {result : X → Bool}
    (execution : Executes observe policy f history transcript result) :
    Executes observe (mapPolicy task policy) f history transcript (task result) := by
  induction execution with
  | stop halt => exact Executes.stop (by simp [mapPolicy, halt])
  | step ask rest ih => exact Executes.step (by simp [mapPolicy, ask]) ih

theorem finite_read_all [Fintype X] (task : (X → Bool) → Y) :
    ∃ policy : List (X × Bool) → X ⊕ Y,
      (∀ f, ∃ transcript, Executes observe policy f [] transcript (task f) ∧
        transcript.length = Fintype.card X) ∧
      (∀ f transcript result, Executes observe policy f [] transcript result →
        result = task f ∧ transcript.length = Fintype.card X) := by
  classical
  let points : List X := (Finset.univ : Finset X).toList
  let root := tree (fun _ : X => false) points
  let policy := mapPolicy task root.policy
  have hc (f : X → Bool) : Executes observe policy f [] (root.trace f) (task f) := by
    have h := root.execution root f [] (by simp [SearchTree.advance])
    have hr : root.run f = f := by
      funext x
      simpa [root, points] using tree_run_apply (fun _ : X => false) f points x
    have hm := map_execution task h
    simpa only [hr] using hm
  have hl (f : X → Bool) : (root.trace f).length = Fintype.card X := by
    simpa [root, points] using tree_trace_length (fun _ : X => false) f points
  refine ⟨policy, ?_, ?_⟩
  · intro f
    exact ⟨root.trace f, hc f, hl f⟩
  · intro f transcript result execution
    obtain ⟨ht, hr⟩ := execution_unique execution (hc f)
    exact ⟨hr, by simpa [ht] using hl f⟩

end ExactSolution.ReadAll

namespace ExactSolution

/-- A correct deterministic read-all policy for an arbitrary task on `L` bits.
Every execution makes exactly `L` bit queries, including `L = 0`. -/
theorem read_all_operational {L : ℕ} {Y : Type*}
    (task : (Fin L → Bool) → Y) :
    ∃ policy : List (Fin L × Bool) → Fin L ⊕ Y,
      (∀ f, ∃ transcript, Executes (fun x f => f x) policy f [] transcript (task f) ∧
        transcript.length = L) ∧
      (∀ f transcript result, Executes (fun x f => f x) policy f [] transcript result →
        result = task f ∧ transcript.length = L) := by
  simpa [Discovery.observe] using ReadAll.finite_read_all task

end ExactSolution
