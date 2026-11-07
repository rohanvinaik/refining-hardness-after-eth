import ExactSolution.Transcript

/-!
# Teaching a singleton and discovering its location

The admissible objects are exactly the singleton indicators on a finite
domain.  Lower bounds quantify over arbitrary deterministic history policies
and use the operational `Executes` relation.
-/

namespace ExactSolution.Discovery

variable {X : Type*} [DecidableEq X]

def singleton (a : X) : X → Bool := fun x => decide (x = a)

def admissible : Set (X → Bool) := {f | ∃ a, f = singleton a}

def observe (x : X) (f : X → Bool) : Bool := f x

abbrev Policy (X : Type*) := List (X × Bool) → X ⊕ (X → Bool)

def Correct (policy : Policy X) : Prop :=
  ∀ a transcript result,
    Executes observe policy (singleton a) [] transcript result → result = singleton a

def Terminates (policy : Policy X) : Prop :=
  ∀ a, ∃ transcript result, Executes observe policy (singleton a) [] transcript result

theorem singleton_injective : Function.Injective (singleton : X → X → Bool) := by
  intro a b h
  have hx := congrFun h a
  simpa [singleton] using hx.symm

theorem positive_certificate (a : X) :
    IsCertificate (admissible : Set (X → Bool)) observe id (singleton a) {a} := by
  intro f hf h
  obtain ⟨b, rfl⟩ := hf
  have hx := h a (Finset.mem_singleton_self a)
  have hab : a = b := by simpa [observe, singleton] using hx
  subst b
  rfl

theorem empty_not_certificate [Fintype X] (hN : 2 ≤ Fintype.card X) (a : X) :
    ¬ IsCertificate (admissible : Set (X → Bool)) observe id (singleton a) ∅ := by
  letI : Nontrivial X := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  obtain ⟨b, hba⟩ := exists_ne a
  intro h
  have heq := h (singleton b) ⟨b, rfl⟩ (by simp [AgreesOn])
  exact hba (singleton_injective heq)

theorem singleton_certificate_complexity [Fintype X] (hN : 2 ≤ Fintype.card X) (a : X) :
    certificateComplexity (admissible : Set (X → Bool)) observe id (singleton a) = 1 := by
  apply le_antisymm
  · simpa using complexity_le_card (positive_certificate a)
  · apply le_complexity
    intro T hT
    have hn : T.Nonempty := by
      by_contra hn
      have he : T = ∅ := Finset.not_nonempty_iff_eq_empty.mp hn
      subst T
      exact empty_not_certificate hN a hT
    exact_mod_cast Finset.one_le_card.mpr hn

inductive NegativePrefix (policy : Policy X) : List (X × Bool) → List (X × Bool) → Prop where
  | nil {history} : NegativePrefix policy history []
  | step {history tail} {e : X}
      (ask : policy history = Sum.inl e)
      (rest : NegativePrefix policy (history ++ [(e, false)]) tail) :
      NegativePrefix policy history ((e, false) :: tail)

omit [DecidableEq X] in
theorem NegativePrefix.snoc {policy : Policy X} {history pre : List (X × Bool)}
    (run : NegativePrefix policy history pre) {e : X}
    (ask : policy (history ++ pre) = Sum.inl e) :
    NegativePrefix policy history (pre ++ [(e, false)]) := by
  induction run with
  | nil =>
    simpa using NegativePrefix.step (by simpa using ask) NegativePrefix.nil
  | @step history tail e' ask' rest ih =>
    apply NegativePrefix.step ask'
    apply ih
    simpa [List.append_assoc] using ask

private theorem missing_cons {a e : X} {tail : List (X × Bool)} :
    a ∉ transcriptQueries ((e, false) :: tail) → a ≠ e ∧ a ∉ transcriptQueries tail := by
  simp [transcriptQueries]

theorem NegativePrefix.stopped_execution {policy : Policy X}
    {history pre : List (X × Bool)} (run : NegativePrefix policy history pre)
    {a : X} (ha : a ∉ transcriptQueries pre) {result : X → Bool}
    (halt : policy (history ++ pre) = Sum.inr result) :
    Executes observe policy (singleton a) history pre result := by
  induction run with
  | nil => exact Executes.stop (by simpa using halt)
  | @step history tail e ask rest ih =>
    obtain ⟨hae, hat⟩ := missing_cons ha
    have he : observe e (singleton a) = false := by
      simp [observe, singleton, Ne.symm hae]
    have hr := ih hat (by simpa [List.append_assoc] using halt)
    have hr' : Executes observe policy (singleton a)
        (history ++ [(e, observe e (singleton a))]) tail result := by simpa [he] using hr
    simpa [he] using Executes.step ask hr'

theorem NegativePrefix.length_le {policy : Policy X}
    {history pre : List (X × Bool)} (run : NegativePrefix policy history pre)
    {a : X} (ha : a ∉ transcriptQueries pre) {transcript : List (X × Bool)}
    {result : X → Bool} (execution : Executes observe policy (singleton a) history transcript result) :
    pre.length ≤ transcript.length := by
  induction run generalizing transcript result with
  | nil => simp
  | @step history tail e ask rest ih =>
    obtain ⟨hae, hat⟩ := missing_cons ha
    cases execution with
    | stop halt => simp [ask] at halt
    | @step _ tail' e' _ ask' rest' =>
      have hee : e' = e := Sum.inl.inj (ask'.symm.trans ask)
      subst e'
      have he : observe e (singleton a) = false := by
        simp [observe, singleton, Ne.symm hae]
      have hr : Executes observe policy (singleton a)
          (history ++ [(e, false)]) tail' result := by simpa [he] using rest'
      simpa using Nat.succ_le_succ (ih hat hr)

private theorem query_card_le (pre : List (X × Bool)) :
    (transcriptQueries pre).card ≤ pre.length := by
  simpa [transcriptQueries] using List.toFinset_card_le (pre.map Prod.fst)

theorem negative_stop_card_lower [Fintype X] {policy : Policy X} (correct : Correct policy)
    {pre : List (X × Bool)} (run : NegativePrefix policy [] pre)
    {result : X → Bool} (halt : policy pre = Sum.inr result) :
    Fintype.card X - 1 ≤ (transcriptQueries pre).card := by
  by_contra h
  have hsmall : (transcriptQueries pre).card < Fintype.card X - 1 := by omega
  have hcomp : 1 < (transcriptQueries pre)ᶜ.card := by
    rw [Finset.card_compl]
    omega
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp hcomp
  have ha' : a ∉ transcriptQueries pre := by simpa using ha
  have hb' : b ∉ transcriptQueries pre := by simpa using hb
  have ea := run.stopped_execution ha' (by simpa using halt)
  have eb := run.stopped_execution hb' (by simpa using halt)
  have hea := correct a pre result ea
  have heb := correct b pre result eb
  exact hab (singleton_injective (hea.symm.trans heb))

theorem negative_prefix_exists [Fintype X] {policy : Policy X} (correct : Correct policy)
    (k : ℕ) (hk : k ≤ Fintype.card X - 1) :
    ∃ pre : List (X × Bool), NegativePrefix policy [] pre ∧ pre.length = k := by
  induction k with
  | zero => exact ⟨[], NegativePrefix.nil, rfl⟩
  | succ k ih =>
    obtain ⟨pre, run, hlen⟩ := ih (by omega)
    cases hpolicy : policy pre with
    | inl e =>
      refine ⟨pre ++ [(e, false)], ?_, ?_⟩
      · exact run.snoc (by simpa using hpolicy)
      · simp [hlen]
    | inr result =>
      have hcard := negative_stop_card_lower correct run hpolicy
      have hlength := query_card_le pre
      omega

/-- The all-negative path need not terminate.  Its finite pre is realized
on an unqueried singleton, whose actual termination is supplied separately. -/
theorem worst_case_lower [Fintype X] {policy : Policy X} (hN : 2 ≤ Fintype.card X)
    (correct : Correct policy) (terminates : Terminates policy) :
    ∃ a transcript result,
      Executes observe policy (singleton a) [] transcript result ∧
        Fintype.card X - 1 ≤ transcript.length := by
  obtain ⟨pre, run, hlen⟩ := negative_prefix_exists correct (Fintype.card X - 1) le_rfl
  have hcomp : 0 < (transcriptQueries pre)ᶜ.card := by
    rw [Finset.card_compl]
    have hc := query_card_le pre
    omega
  obtain ⟨a, ha⟩ := Finset.card_pos.mp hcomp
  have ha' : a ∉ transcriptQueries pre := by simpa using ha
  obtain ⟨transcript, result, execution⟩ := terminates a
  exact ⟨a, transcript, result, execution, by simpa [hlen] using run.length_le ha' execution⟩

omit [DecidableEq X] in
theorem execution_unique {Y : Type*} {policy : List (X × Bool) → X ⊕ Y}
    {f : X → Bool} {history : List (X × Bool)}
    {first second : List (X × Bool)} {r s : Y}
    (one : Executes observe policy f history first r)
    (two : Executes observe policy f history second s) : first = second ∧ r = s := by
  induction one generalizing second s with
  | stop halt =>
    cases two with
    | stop halt' =>
      exact ⟨rfl, Sum.inr.inj (halt.symm.trans halt')⟩
    | step ask rest => simp [halt] at ask
  | @step history tail e result ask rest ih =>
    cases two with
    | stop halt => simp [ask] at halt
    | @step _ tail' e' result' ask' rest' =>
      have he : e' = e := Sum.inl.inj (ask'.symm.trans ask)
      subst e'
      obtain ⟨ht, hr⟩ := ih rest'
      exact ⟨by simp [ht], hr⟩

inductive SearchTree (X : Type*) where
  | answer : (X → Bool) → SearchTree X
  | query : X → (Bool → SearchTree X) → SearchTree X

def SearchTree.run : SearchTree X → (X → Bool) → (X → Bool)
  | .answer result, _ => result
  | .query e next, f => (next (f e)).run f

def SearchTree.trace : SearchTree X → (X → Bool) → List (X × Bool)
  | .answer _, _ => []
  | .query e next, f => (e, f e) :: (next (f e)).trace f

def SearchTree.advance (tree : SearchTree X) : List (X × Bool) → SearchTree X
  | [] => tree
  | (_, value) :: rest => match tree with
    | .answer result => .answer result
    | .query _ next => (next value).advance rest

def SearchTree.policy (root : SearchTree X) (history : List (X × Bool)) : X ⊕ (X → Bool) :=
  match root.advance history with
  | .answer result => Sum.inr result
  | .query e _ => Sum.inl e

omit [DecidableEq X] in
theorem SearchTree.advance_append (tree : SearchTree X) (first second : List (X × Bool)) :
    tree.advance (first ++ second) = (tree.advance first).advance second := by
  induction first generalizing tree with
  | nil => simp [advance]
  | cons pair rest ih =>
    cases tree with
    | answer result => cases second <;> simp [advance]
    | query e next => simpa [advance] using ih (tree := next pair.2)

omit [DecidableEq X] in
theorem SearchTree.execution (root current : SearchTree X) (f : X → Bool)
    (history : List (X × Bool)) (hcurrent : root.advance history = current) :
    Executes observe root.policy f history (current.trace f) (current.run f) := by
  induction current generalizing history with
  | answer result =>
    simpa [trace, run] using
      (Executes.stop (show root.policy history = Sum.inr result by simp [policy, hcurrent]) :
        Executes observe root.policy f history [] result)
  | query e next ih =>
    have hnext : root.advance (history ++ [(e, f e)]) = next (f e) := by
      rw [advance_append, hcurrent]
      simp [advance]
    have hr := ih (f e) (history ++ [(e, f e)]) hnext
    simpa [trace, run, observe] using
      Executes.step (show root.policy history = Sum.inl e by simp [policy, hcurrent]) hr

def searchTree (fallback : X) : List X → SearchTree X
  | [] => .answer (singleton fallback)
  | [a] => .answer (singleton a)
  | a :: b :: rest => .query a (fun yes =>
      if yes then .answer (singleton a) else searchTree fallback (b :: rest))

theorem searchTree_run (fallback a : X) (points : List X) (ha : a ∈ points) :
    (searchTree fallback points).run (singleton a) = singleton a := by
  induction points with
  | nil => simp at ha
  | cons x xs ih =>
    cases xs with
    | nil =>
      have he : a = x := by simpa using ha
      subst x
      rfl
    | cons y ys =>
      by_cases hax : a = x
      · subst x
        simp [searchTree, SearchTree.run, singleton]
      · have hat : a ∈ y :: ys := (List.mem_cons.mp ha).resolve_left hax
        simpa [searchTree, SearchTree.run, singleton, Ne.symm hax] using ih hat

theorem searchTree_trace_length (fallback : X) (points : List X) (f : X → Bool) :
    ((searchTree fallback points).trace f).length ≤ points.length - 1 := by
  induction points with
  | nil => simp [searchTree, SearchTree.trace]
  | cons x xs ih =>
    cases xs with
    | nil => simp [searchTree, SearchTree.trace]
    | cons y ys =>
      cases he : f x with
      | false =>
        simpa [searchTree, SearchTree.trace, he] using Nat.succ_le_succ ih
      | true => simp [searchTree, SearchTree.trace, he]

theorem worst_case_upper [Fintype X] (hN : 2 ≤ Fintype.card X) :
    ∃ policy : Policy X, Correct policy ∧ Terminates policy ∧
      ∀ a transcript result, Executes observe policy (singleton a) [] transcript result →
        transcript.length ≤ Fintype.card X - 1 := by
  classical
  letI : Nonempty X := Fintype.card_pos_iff.mp (by omega)
  let fallback : X := Classical.choice inferInstance
  let points : List X := (Finset.univ : Finset X).toList
  let tree := searchTree fallback points
  have hc (a : X) : Executes observe tree.policy (singleton a) []
      (tree.trace (singleton a)) (singleton a) := by
    have h := tree.execution tree (singleton a) [] (by simp [SearchTree.advance])
    have ha : a ∈ points := by simp [points]
    have hr : tree.run (singleton a) = singleton a := searchTree_run fallback a points ha
    simpa only [hr] using h
  have hl (a : X) : (tree.trace (singleton a)).length ≤ Fintype.card X - 1 := by
    simpa [tree, points] using searchTree_trace_length fallback points (singleton a)
  refine ⟨tree.policy, ?_, ?_, ?_⟩
  · intro a transcript result execution
    exact (execution_unique execution (hc a)).2
  · intro a
    exact ⟨tree.trace (singleton a), singleton a, hc a⟩
  · intro a transcript result execution
    have he := (execution_unique execution (hc a)).1
    simpa [he] using hl a

/-- There is a correct terminating policy with worst-case exactly `N - 1`,
and no correct policy terminating on every singleton has a smaller bound. -/
theorem optimal_worst_case [Fintype X] (hN : 2 ≤ Fintype.card X) :
    (∀ policy : Policy X, Correct policy → Terminates policy →
      ∃ a transcript result, Executes observe policy (singleton a) [] transcript result ∧
        Fintype.card X - 1 ≤ transcript.length) ∧
    (∃ policy : Policy X, Correct policy ∧ Terminates policy ∧
      (∀ a transcript result, Executes observe policy (singleton a) [] transcript result →
        transcript.length ≤ Fintype.card X - 1) ∧
      ∃ a transcript result, Executes observe policy (singleton a) [] transcript result ∧
        transcript.length = Fintype.card X - 1) := by
  constructor
  · intro policy hc ht
    exact worst_case_lower hN hc ht
  · obtain ⟨policy, hc, ht, hupper⟩ := worst_case_upper hN
    obtain ⟨a, transcript, result, execution, hlower⟩ := worst_case_lower hN hc ht
    exact ⟨policy, hc, ht, hupper, a, transcript, result, execution,
      le_antisymm (hupper a transcript result execution) hlower⟩

end ExactSolution.Discovery
