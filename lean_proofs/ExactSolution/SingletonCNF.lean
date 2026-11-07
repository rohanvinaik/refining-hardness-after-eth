import ExactSolution.Observation

/-!
# Point certificates inside the semantic k-CNF class

Clauses below are actual finite lists of signed Boolean literals.  Class
membership is expressibility by such a formula; it does not assume any
certificate conclusion.  Singleton targets, the zero function, and every
two-point competitor are constructed in this syntax.
-/

namespace ExactSolution.SingletonCNF

abbrev Assignment (n : ℕ) := Fin n → Bool
abbrev BooleanFunction (n : ℕ) := Assignment n → Bool

structure Literal (n : ℕ) where
  index : Fin n
  value : Bool
  deriving DecidableEq

abbrev Clause (n : ℕ) := List (Literal n)
abbrev Formula (n : ℕ) := List (Clause n)

def Clause.Holds {n : ℕ} (c : Clause n) (x : Assignment n) : Prop :=
  ∃ l ∈ c, x l.index = l.value

def Formula.Holds {n : ℕ} (F : Formula n) (x : Assignment n) : Prop :=
  ∀ c ∈ F, Clause.Holds c x

def Expressible {n : ℕ} (k : ℕ) (f : BooleanFunction n) : Prop :=
  ∃ F : Formula n,
    (∀ c ∈ F, c.length ≤ k) ∧ ∀ x, Formula.Holds F x ↔ f x = true

def admissible (n k : ℕ) : Set (BooleanFunction n) := {f | Expressible k f}

noncomputable section

def singleton {n : ℕ} (a : Assignment n) : BooleanFunction n := by
  classical
  exact fun x => decide (x = a)

def twoPoint {n : ℕ} (a b : Assignment n) : BooleanFunction n := by
  classical
  exact fun x => decide (x = a ∨ x = b)

def zero {n : ℕ} : BooleanFunction n := fun _ => false

@[simp] theorem singleton_true {n : ℕ} (a x : Assignment n) :
    singleton a x = true ↔ x = a := by
  classical
  simp [singleton]

@[simp] theorem twoPoint_true {n : ℕ} (a b x : Assignment n) :
    twoPoint a b x = true ↔ x = a ∨ x = b := by
  classical
  simp [twoPoint]

private theorem bool_eq_not_iff_ne (u v : Bool) : u = !v ↔ u ≠ v := by
  cases u <;> cases v <;> decide

private theorem bool_eq_of_ne_of_ne {u v w : Bool}
    (hvw : v ≠ w) (huv : u ≠ v) : u = w := by
  cases u <;> cases v <;> cases w <;> simp_all

def singletonFormula {n : ℕ} (a : Assignment n) : Formula n :=
  List.ofFn (fun i : Fin n => [⟨i, a i⟩])

theorem singletonFormula_holds {n : ℕ} (a x : Assignment n) :
    Formula.Holds (singletonFormula a) x ↔ x = a := by
  constructor
  · intro h
    funext i
    have hi := h [⟨i, a i⟩] (List.mem_ofFn.mpr ⟨i, rfl⟩)
    simpa [Clause.Holds] using hi
  · rintro rfl c hc
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hc
    simp [Clause.Holds]

theorem singleton_expressible {n k : ℕ} (a : Assignment n) (hk : 1 ≤ k) :
    Expressible k (singleton a) := by
  refine ⟨singletonFormula a, ?_, ?_⟩
  · intro c hc
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hc
    simpa using hk
  · intro x
    rw [singletonFormula_holds, singleton_true]

theorem singletonFormula_length {n : ℕ} (a : Assignment n) :
    (singletonFormula a).length = n := by simp [singletonFormula]

theorem zero_expressible (n k : ℕ) : Expressible k (zero : BooleanFunction n) := by
  refine ⟨[[]], ?_, ?_⟩
  · simp
  · intro x
    simp [Formula.Holds, Clause.Holds, zero]

private def firstClause {n : ℕ} (a b : Assignment n) (p i : Fin n) : Clause n :=
  if a i = b i then [⟨i, a i⟩] else [⟨i, !(a i)⟩, ⟨p, a p⟩]

private def secondClause {n : ℕ} (a b : Assignment n) (p i : Fin n) : Clause n :=
  if a i = b i then [⟨i, a i⟩] else [⟨i, a i⟩, ⟨p, !(a p)⟩]

def twoPointFormula {n : ℕ} (a b : Assignment n) (p : Fin n) : Formula n :=
  List.ofFn (firstClause a b p) ++ List.ofFn (secondClause a b p)

theorem twoPointFormula_length {n : ℕ} (a b : Assignment n) (p : Fin n) :
    (twoPointFormula a b p).length = 2 * n := by
  simp [twoPointFormula, two_mul]

theorem twoPointFormula_width {n : ℕ} (a b : Assignment n) (p : Fin n)
    (c : Clause n) (hc : c ∈ twoPointFormula a b p) : c.length ≤ 2 := by
  rcases List.mem_append.mp hc with hc | hc
  · obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hc
    simp [firstClause]
    split <;> simp
  · obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hc
    simp [secondClause]
    split <;> simp

theorem twoPointFormula_holds {n : ℕ} (a b x : Assignment n) (p : Fin n)
    (hp : a p ≠ b p) :
    Formula.Holds (twoPointFormula a b p) x ↔ x = a ∨ x = b := by
  constructor
  · intro h
    have hfirst (i : Fin n) : Clause.Holds (firstClause a b p i) x :=
      h _ (List.mem_append.mpr (Or.inl (List.mem_ofFn.mpr ⟨i, rfl⟩)))
    have hsecond (i : Fin n) : Clause.Holds (secondClause a b p i) x :=
      h _ (List.mem_append.mpr (Or.inr (List.mem_ofFn.mpr ⟨i, rfl⟩)))
    by_cases hx : x p = a p
    · left
      funext i
      have hi := hsecond i
      by_cases hab : a i = b i
      · simpa [secondClause, hab, Clause.Holds] using hi
      · simpa [secondClause, hab, Clause.Holds, bool_eq_not_iff_ne, hx] using hi
    · right
      funext i
      have hi := hfirst i
      by_cases hab : a i = b i
      · have hai : x i = a i := by simpa [firstClause, hab, Clause.Holds] using hi
        exact hai.trans hab
      · have hne : x i ≠ a i := by
          simpa [firstClause, hab, Clause.Holds, bool_eq_not_iff_ne, hx] using hi
        exact bool_eq_of_ne_of_ne hab hne
  · intro hx
    rcases hx with hxa | hxb
    · subst x
      intro c hc
      rcases List.mem_append.mp hc with hc | hc
      · obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hc
        by_cases hab : a i = b i <;> simp [firstClause, hab, Clause.Holds]
      · obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hc
        by_cases hab : a i = b i <;> simp [secondClause, hab, Clause.Holds]
    · subst x
      intro c hc
      rcases List.mem_append.mp hc with hc | hc
      · obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hc
        by_cases hab : a i = b i
        · simp [firstClause, hab, Clause.Holds]
        · simp [firstClause, hab, Clause.Holds, bool_eq_not_iff_ne, Ne.symm hab]
      · obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hc
        by_cases hab : a i = b i
        · simp [secondClause, hab, Clause.Holds]
        · simp [secondClause, hab, Clause.Holds, bool_eq_not_iff_ne, Ne.symm hp]

theorem twoPoint_expressible {n k : ℕ} (a b : Assignment n)
    (hab : a ≠ b) (hk : 2 ≤ k) : Expressible k (twoPoint a b) := by
  classical
  obtain ⟨p, hp⟩ := Function.ne_iff.mp hab
  refine ⟨twoPointFormula a b p, ?_, ?_⟩
  · intro c hc
    exact (twoPointFormula_width a b p c hc).trans hk
  · intro x
    rw [twoPointFormula_holds a b x p hp, twoPoint_true]

theorem twoPoint_has_linear_formula {n : ℕ} (a b : Assignment n) (hab : a ≠ b) :
    ∃ F : Formula n, F.length ≤ 2 * n ∧ (∀ c ∈ F, c.length ≤ 2) ∧
      ∀ x, Formula.Holds F x ↔ x = a ∨ x = b := by
  classical
  obtain ⟨p, hp⟩ := Function.ne_iff.mp hab
  refine ⟨twoPointFormula a b p, ?_, ?_, ?_⟩
  · exact (twoPointFormula_length a b p).le
  · exact twoPointFormula_width a b p
  · intro x
    exact twoPointFormula_holds a b x p hp

def solutionCount {n : ℕ} (f : BooleanFunction n) : ℕ :=
  (Finset.univ.filter (fun x => f x = true)).card

@[simp] theorem solutionCount_singleton {n : ℕ} (a : Assignment n) :
    solutionCount (singleton a) = 1 := by
  classical
  have hs : (Finset.univ.filter (fun x => singleton a x = true)) = {a} := by
    ext x
    simp
  unfold solutionCount
  rw [hs]
  simp

@[simp] theorem solutionCount_zero (n : ℕ) :
    solutionCount (zero : BooleanFunction n) = 0 := by simp [solutionCount, zero]

theorem solutionCount_twoPoint {n : ℕ} (a b : Assignment n) (hab : a ≠ b) :
    solutionCount (twoPoint a b) = 2 := by
  classical
  have hs : (Finset.univ.filter (fun x => twoPoint a b x = true)) = {a, b} := by
    ext x
    simp
  unfold solutionCount
  rw [hs]
  simp [hab]

def pointObserve {n : ℕ} (x : Assignment n) (f : BooleanFunction n) : Bool := f x

private theorem agrees_zero_of_missing {n : ℕ} (a : Assignment n)
    (T : Finset (Assignment n)) (ha : a ∉ T) :
    AgreesOn pointObserve T (singleton a) zero := by
  intro x hx
  have hxa : x ≠ a := fun h => ha (h ▸ hx)
  simp [pointObserve, zero, singleton, hxa]

private theorem agrees_twoPoint_of_missing {n : ℕ} (a b : Assignment n)
    (T : Finset (Assignment n)) (hb : b ∉ T) :
    AgreesOn pointObserve T (singleton a) (twoPoint a b) := by
  classical
  intro x hx
  have hxb : x ≠ b := fun h => hb (h ▸ hx)
  by_cases hxa : x = a <;> simp [pointObserve, singleton, twoPoint, hxb, hxa]

theorem identity_certificate_eq_univ {n k : ℕ} (a : Assignment n) (hk : 2 ≤ k)
    (T : Finset (Assignment n))
    (hT : IsCertificate (admissible n k) pointObserve id (singleton a) T) :
    T = Finset.univ := by
  classical
  apply Finset.eq_univ_of_forall
  intro b
  by_contra hb
  by_cases hba : b = a
  · subst b
    have h := hT zero (zero_expressible n k) (agrees_zero_of_missing a T hb)
    have hat := congrFun h a
    simp [zero, singleton] at hat
  · have h := hT (twoPoint a b) (twoPoint_expressible a b (Ne.symm hba) hk)
      (agrees_twoPoint_of_missing a b T hb)
    have hbt := congrFun h b
    simp [twoPoint, singleton, hba] at hbt

theorem count_certificate_eq_univ {n k : ℕ} (a : Assignment n) (hk : 2 ≤ k)
    (T : Finset (Assignment n))
    (hT : IsCertificate (admissible n k) pointObserve solutionCount (singleton a) T) :
    T = Finset.univ := by
  classical
  apply Finset.eq_univ_of_forall
  intro b
  by_contra hb
  by_cases hba : b = a
  · subst b
    have h := hT zero (zero_expressible n k) (agrees_zero_of_missing a T hb)
    simp at h
  · have h := hT (twoPoint a b) (twoPoint_expressible a b (Ne.symm hba) hk)
      (agrees_twoPoint_of_missing a b T hb)
    rw [solutionCount_twoPoint a b (Ne.symm hba), solutionCount_singleton] at h
    omega

theorem univ_certificate {n k : ℕ} {Y : Type*} (task : BooleanFunction n → Y)
    (target : BooleanFunction n) :
    IsCertificate (admissible n k) pointObserve task target Finset.univ := by
  intro g _ h
  apply congrArg task
  funext x
  exact h x (Finset.mem_univ x)

theorem assignment_card (n : ℕ) : Fintype.card (Assignment n) = 2 ^ n := by
  simp [Assignment]

theorem identity_certificate_card {n k : ℕ} (a : Assignment n) (hk : 2 ≤ k)
    (T : Finset (Assignment n))
    (hT : IsCertificate (admissible n k) pointObserve id (singleton a) T) :
    T.card = 2 ^ n := by
  rw [identity_certificate_eq_univ a hk T hT, Finset.card_univ, assignment_card]

theorem count_certificate_card {n k : ℕ} (a : Assignment n) (hk : 2 ≤ k)
    (T : Finset (Assignment n))
    (hT : IsCertificate (admissible n k) pointObserve solutionCount (singleton a) T) :
    T.card = 2 ^ n := by
  rw [count_certificate_eq_univ a hk T hT, Finset.card_univ, assignment_card]

def Satisfiable {n : ℕ} (f : BooleanFunction n) : Prop := ∃ x, f x = true

theorem singleton_sat_certificate {n k : ℕ} (a : Assignment n) :
    IsCertificate (admissible n k) pointObserve Satisfiable (singleton a) {a} := by
  intro g _ h
  apply propext
  constructor
  · intro _
    exact ⟨a, by simp⟩
  · intro _
    refine ⟨a, ?_⟩
    have ha := h a (Finset.mem_singleton_self a)
    simpa [pointObserve, singleton] using ha

theorem empty_not_sat_certificate {n k : ℕ} (a : Assignment n) :
    ¬ IsCertificate (admissible n k) pointObserve Satisfiable (singleton a) ∅ := by
  intro h
  have heq := h zero (zero_expressible n k) (by simp [AgreesOn])
  have hsat : Satisfiable (singleton a) := ⟨a, by simp⟩
  have hzero : Satisfiable (zero : BooleanFunction n) := heq.symm ▸ hsat
  simp [Satisfiable, zero] at hzero

theorem singleton_identity_complexity {n k : ℕ} (a : Assignment n) (hk : 2 ≤ k) :
    certificateComplexity (admissible n k) pointObserve id (singleton a) =
      ((2 ^ n : ℕ) : WithTop ℕ) := by
  apply le_antisymm
  · have h := complexity_le_card (univ_certificate (k := k) id (singleton a))
    simpa [assignment_card] using h
  · apply le_complexity
    intro T hT
    rw [identity_certificate_card a hk T hT]

theorem singleton_count_complexity {n k : ℕ} (a : Assignment n) (hk : 2 ≤ k) :
    certificateComplexity (admissible n k) pointObserve solutionCount (singleton a) =
      ((2 ^ n : ℕ) : WithTop ℕ) := by
  apply le_antisymm
  · have h := complexity_le_card (univ_certificate (k := k) solutionCount (singleton a))
    simpa [assignment_card] using h
  · apply le_complexity
    intro T hT
    rw [count_certificate_card a hk T hT]

theorem singleton_sat_complexity {n k : ℕ} (a : Assignment n) :
    certificateComplexity (admissible n k) pointObserve Satisfiable (singleton a) = 1 := by
  apply le_antisymm
  · simpa using complexity_le_card (singleton_sat_certificate (k := k) a)
  · apply le_complexity
    intro T hT
    have hne : T.Nonempty := by
      by_contra h
      have he : T = ∅ := Finset.not_nonempty_iff_eq_empty.mp h
      subst T
      exact empty_not_sat_certificate a hT
    exact_mod_cast Finset.one_le_card.mpr hne

end

end ExactSolution.SingletonCNF
