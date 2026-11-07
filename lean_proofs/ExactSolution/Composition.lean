import ExactSolution.WeightedObservation

/-!
# Local products, interactions, and interfaces

The local-product model has a genuinely full product of admissible component
objects, a tuple task, and tagged local observations. Observation answers are
also tagged, so components may have different answer types.
-/

namespace ExactSolution

open scoped BigOperators

/-- Nonnegative costs make overlap in a union reduce its total charge. -/
theorem sum_union_cost_le {E : Type*} [DecidableEq E]
    (S T : Finset E) (cost : E → ENNReal) :
    (∑ e ∈ S ∪ T, cost e) ≤ (∑ e ∈ S, cost e) + ∑ e ∈ T, cost e := by
  calc
    (∑ e ∈ S ∪ T, cost e) ≤
        (∑ e ∈ S ∪ T, cost e) + ∑ e ∈ S ∩ T, cost e := le_self_add
    _ = (∑ e ∈ S, cost e) + ∑ e ∈ T, cost e := Finset.sum_union_inter

/-- The same cost inequality for a finite union of simulation or lift sets. -/
theorem sum_biUnion_cost_le {E F : Type*} [DecidableEq E]
    (T : Finset F) (S : F → Finset E) (cost : E → ENNReal) :
    (∑ e ∈ T.biUnion S, cost e) ≤ ∑ f ∈ T, ∑ e ∈ S f, cost e := by
  classical
  induction T using Finset.induction_on with
  | empty => simp
  | @insert f T hf ih =>
      simpa only [Finset.biUnion_insert, Finset.sum_insert hf] using
        (sum_union_cost_le (S f) (T.biUnion S) cost).trans (add_le_add le_rfl ih)

section LocalProduct

variable {I : Type*} {C E A Y : I → Type*}

def productAdmissible (admissible : ∀ i, Set (C i)) : Set (∀ i, C i) :=
  fun f => ∀ i, f i ∈ admissible i

def productTask (task : ∀ i, C i → Y i) (f : ∀ i, C i) : ∀ i, Y i :=
  fun i => task i (f i)

def taggedLocalObserve (observe : ∀ i, E i → C i → A i)
    (e : Sigma E) (f : ∀ i, C i) : Sigma A :=
  ⟨e.1, observe e.1 e.2 (f e.1)⟩

variable [Fintype I] [DecidableEq I] [∀ i, Fintype (E i)]
  [∀ i, DecidableEq (E i)]

/-- The local queries with tag `i` appearing in a composite certificate. -/
def localProjection (T : Finset (Sigma E)) (i : I) : Finset (E i) :=
  Finset.univ.filter fun e => Sigma.mk i e ∈ T

theorem localProjection_reassemble (T : Finset (Sigma E)) :
    Finset.univ.sigma (localProjection T) = T := by
  ext ⟨i, e⟩
  simp [localProjection]

theorem localProjection_sigma (T : ∀ i, Finset (E i)) (i : I) :
    localProjection (Finset.univ.sigma T) i = T i := by
  ext e
  simp [localProjection]

omit [Fintype I] in
/-- The full product and locality assumptions force every component projection
to certify its component task; conversely those local certificates suffice. -/
theorem product_certificate_iff
    (admissible : ∀ i, Set (C i)) (observe : ∀ i, E i → C i → A i)
    (task : ∀ i, C i → Y i) (target : ∀ i, C i)
    (htarget : ∀ i, target i ∈ admissible i) (T : Finset (Sigma E)) :
    IsCertificate (productAdmissible admissible) (taggedLocalObserve observe)
      (productTask task) target T ↔
      ∀ i, IsCertificate (admissible i) (observe i) (task i) (target i)
        (localProjection T i) := by
  constructor
  · intro hcertificate i g hg hagree
    let replacement := Function.update target i g
    have hreplacement : replacement ∈ productAdmissible admissible := by
      intro j
      by_cases hji : j = i
      · subst j
        simpa [replacement, Function.update] using hg
      · simpa [replacement, Function.update, hji] using htarget j
    have hglobal : AgreesOn (taggedLocalObserve observe) T target replacement := by
      intro e he
      obtain ⟨j, e⟩ := e
      by_cases hji : j = i
      · subst j
        have hlocal : e ∈ localProjection T i := by
          simpa [localProjection] using he
        have hvalue := hagree e hlocal
        simpa [taggedLocalObserve, replacement, Function.update] using
          congrArg (Sigma.mk i) hvalue
      · simp [taggedLocalObserve, replacement, hji]
    have htuple := hcertificate replacement hreplacement hglobal
    have hcomponent := congrFun htuple i
    simpa [productTask, replacement, Function.update] using hcomponent
  · intro hlocal g hg hagree
    funext i
    apply hlocal i (g i) (hg i)
    intro e he
    have htag : Sigma.mk i e ∈ T := by
      simpa [localProjection] using he
    have hvalue := hagree (Sigma.mk i e) htag
    simpa [taggedLocalObserve] using hvalue

/-- Tagged query costs decompose exactly, with no overlap between tags. -/
theorem sum_tagged_local_cost (cost : ∀ i, E i → ENNReal)
    (T : Finset (Sigma E)) :
    (∑ e ∈ T, cost e.1 e.2) =
      ∑ i, ∑ e ∈ localProjection T i, cost i e := by
  calc
    (∑ e ∈ T, cost e.1 e.2) =
        ∑ e ∈ Finset.univ.sigma (localProjection T), cost e.1 e.2 := by
      rw [localProjection_reassemble]
    _ = ∑ i, ∑ e ∈ localProjection T i, cost i e :=
      Finset.sum_sigma _ _ _

/-- Weighted product additivity. The full product, tuple task, tagged local
observations, and target admissibility appear explicitly. Finite observation
families ensure that the component cost minima are attained. -/
theorem weighted_product_additivity
    (admissible : ∀ i, Set (C i)) (observe : ∀ i, E i → C i → A i)
    (task : ∀ i, C i → Y i) (target : ∀ i, C i)
    (cost : ∀ i, E i → ENNReal)
    (htarget : ∀ i, target i ∈ admissible i)
    (hcertificates : ∀ i, ∃ T : Finset (E i),
      IsCertificate (admissible i) (observe i) (task i) (target i) T) :
    weightedCertificateComplexity (productAdmissible admissible)
      (taggedLocalObserve observe) (productTask task) target
      (fun e : Sigma E => cost e.1 e.2) =
      ∑ i, weightedCertificateComplexity (admissible i) (observe i)
        (task i) (target i) (cost i) := by
  classical
  apply le_antisymm
  · have hmin : ∀ i, ∃ T : Finset (E i),
        IsCertificate (admissible i) (observe i) (task i) (target i) T ∧
        (∑ e ∈ T, cost i e) = weightedCertificateComplexity
          (admissible i) (observe i) (task i) (target i) (cost i) :=
      fun i => weighted_complexity_attained (hcertificates i)
    choose T hT hcost using hmin
    have hcomposite : IsCertificate (productAdmissible admissible)
        (taggedLocalObserve observe) (productTask task) target
        (Finset.univ.sigma T) := by
      apply (product_certificate_iff admissible observe task target htarget _).mpr
      intro i
      simpa only [localProjection_sigma] using hT i
    calc
      _ ≤ ∑ e ∈ Finset.univ.sigma T, cost e.1 e.2 :=
        weighted_complexity_le_cost hcomposite
      _ = ∑ i, ∑ e ∈ T i, cost i e := Finset.sum_sigma _ _ _
      _ = _ := Finset.sum_congr rfl fun i _ => hcost i
  · apply le_weighted_complexity
    intro T hT
    have hlocal := (product_certificate_iff admissible observe task target htarget T).mp hT
    calc
      (∑ i, weightedCertificateComplexity (admissible i) (observe i)
          (task i) (target i) (cost i)) ≤
          ∑ i, ∑ e ∈ localProjection T i, cost i e :=
        Finset.sum_le_sum fun i _ => weighted_complexity_le_cost (hlocal i)
      _ = ∑ e ∈ T, cost e.1 e.2 := (sum_tagged_local_cost cost T).symm

end LocalProduct

section Interaction

variable {X : Type*} [Fintype X] [DecidableEq X]

def interactionIndicator (x : X) (y : X) : Bool := decide (y = x)

def interactionAdmissible (X : Type*) [DecidableEq X] : Set (X → Bool) :=
  fun f => f = (fun _ => false) ∨ ∃ x, f = interactionIndicator x

/-- Every point is forced when its singleton competitor changes the task. -/
theorem interaction_certificate_iff_full {Y : Type*} (task : (X → Bool) → Y)
    (hchanges : ∀ x, task (interactionIndicator x) ≠ task (fun _ => false))
    (T : Finset X) :
    IsCertificate (interactionAdmissible X) (fun x f => f x) task
      (fun _ => false) T ↔ T = Finset.univ := by
  constructor
  · intro hcertificate
    apply Finset.eq_univ_of_forall
    intro x
    by_contra hx
    have hagree : AgreesOn (fun x f => f x) T
        (fun _ => false) (interactionIndicator x) := by
      intro y hy
      have hyx : y ≠ x := by
        intro h
        subst y
        exact hx hy
      simp [interactionIndicator, hyx]
    exact hchanges x
      (hcertificate (interactionIndicator x) (Or.inr ⟨x, rfl⟩) hagree)
  · rintro rfl
    exact full_point_certificate _ _ _

/-- The zero target's exact query-certificate cost is the domain size for any
task changed by every singleton. -/
theorem interaction_complexity_eq_card {Y : Type*} (task : (X → Bool) → Y)
    (hchanges : ∀ x, task (interactionIndicator x) ≠ task (fun _ => false)) :
    certificateComplexity (interactionAdmissible X) (fun x f => f x) task
      (fun _ => false) = (Fintype.card X : WithTop ℕ) := by
  apply le_antisymm
  · simpa using complexity_le_card
      (full_point_certificate (interactionAdmissible X) task (fun _ => false))
  · apply le_complexity
    intro T hT
    rw [(interaction_certificate_iff_full task hchanges T).mp hT]
    simp

theorem interaction_identity_complexity :
    certificateComplexity (interactionAdmissible X) (fun x f => f x) id
      (fun _ => false) = (Fintype.card X : WithTop ℕ) := by
  apply interaction_complexity_eq_card
  intro x h
  have hx := congrFun h x
  simp [interactionIndicator] at hx

def interactionAnyPositive (f : X → Bool) : Prop := ∃ x, f x = true

theorem interaction_existence_complexity :
    certificateComplexity (interactionAdmissible X) (fun x f => f x)
      interactionAnyPositive (fun _ => false) = (Fintype.card X : WithTop ℕ) := by
  apply interaction_complexity_eq_card
  intro x
  simp [interactionAnyPositive, interactionIndicator]

def interactionPositiveCount (f : X → Bool) : ℕ :=
  (Finset.univ.filter fun x => f x = true).card

theorem interaction_counting_complexity :
    certificateComplexity (interactionAdmissible X) (fun x f => f x)
      interactionPositiveCount (fun _ => false) = (Fintype.card X : WithTop ℕ) := by
  apply interaction_complexity_eq_card
  intro x
  have hsupport : (Finset.univ.filter fun y => interactionIndicator x y = true) = {x} := by
    ext y
    simp [interactionIndicator]
  simp [interactionPositiveCount, hsupport]

/-- The interaction-domain instance has `p*q` forced point observations. -/
theorem pairwise_interaction_identity_complexity (p q : ℕ) :
    certificateComplexity (interactionAdmissible (Fin p × Fin q))
      (fun x f => f x) id (fun _ => false) = ((p * q : ℕ) : WithTop ℕ) := by
  simpa using (interaction_identity_complexity (X := Fin p × Fin q))

end Interaction

section Interfaces

variable {C E A Y : Type*} [DecidableEq E]

/-- A set of admissible observations distinguishes every listed alternative
from the target. No observation-lifting assertion is built into this definition. -/
def CoversAlternatives (observe : E → C → A) (target : C)
    (alternatives : Set C) (T : Finset E) : Prop :=
  ∀ g ∈ alternatives, ∃ e ∈ T, observe e g ≠ observe e target

omit [DecidableEq E] in
theorem interface_certificate_iff_covers {observe : E → C → A}
    {task : C → Y} {target : C} {alternatives : Set C} (T : Finset E)
    (hdifferent : ∀ g ∈ alternatives, task g ≠ task target) :
    IsCertificate alternatives observe task target T ↔
      CoversAlternatives observe target alternatives T := by
  classical
  constructor
  · intro hcertificate g hg
    by_contra hmissing
    apply hdifferent g hg (hcertificate g hg ?_)
    intro e he
    by_contra hdiff
    exact hmissing ⟨e, he, hdiff⟩
  · intro hcover g hg hagree
    obtain ⟨e, he, hd⟩ := hcover g hg
    exact False.elim (hd (hagree e he))

/-- The minimum cost of covering the specified interface alternatives. -/
noncomputable def interfaceCoverComplexity (observe : E → C → A) (target : C)
    (UI : Set C) (cost : E → ENNReal) : ENNReal :=
  sInf {k | ∃ T : Finset E, CoversAlternatives observe target UI T ∧
    (∑ e ∈ T, cost e) = k}

omit [DecidableEq E] in
theorem interfaceCoverComplexity_eq_weighted
    (observe : E → C → A) (task : C → Y) (target : C)
    (UI : Set C) (cost : E → ENNReal)
    (hdifferent : ∀ g ∈ UI, task g ≠ task target) :
    interfaceCoverComplexity observe target UI cost =
      weightedCertificateComplexity UI observe task target cost := by
  unfold interfaceCoverComplexity weightedCertificateComplexity
  congr 1
  ext k
  constructor
  · rintro ⟨T, hcover, hcost⟩
    exact ⟨T, (interface_certificate_iff_covers T hdifferent).mpr hcover, hcost⟩
  · rintro ⟨T, hcertificate, hcost⟩
    exact ⟨T, (interface_certificate_iff_covers T hdifferent).mp hcertificate, hcost⟩

/-- Actual covers of the component and interface alternatives give a
composite certificate, with total cost bounded by the sum of their costs. -/
theorem lifted_interface_cover_bound
    {admissible : Set C} {observe : E → C → A} {task : C → Y} {target : C}
    (UA UB UI : Set C) (TA TB TI : Finset E) (cost : E → ENNReal)
    (hpartition : ∀ g ∈ admissible, task g ≠ task target →
      g ∈ UA ∨ g ∈ UB ∨ g ∈ UI)
    (hA : CoversAlternatives observe target UA TA)
    (hB : CoversAlternatives observe target UB TB)
    (hI : CoversAlternatives observe target UI TI) :
    weightedCertificateComplexity admissible observe task target cost ≤
      (∑ e ∈ TA, cost e) + (∑ e ∈ TB, cost e) + ∑ e ∈ TI, cost e := by
  have hcertificate : IsCertificate admissible observe task target ((TA ∪ TB) ∪ TI) := by
    intro g hg hagree
    by_contra hdifferent
    rcases hpartition g hg hdifferent with hgA | hgB | hgI
    · obtain ⟨e, he, hd⟩ := hA g hgA
      exact hd (hagree e (Finset.mem_union_left _ (Finset.mem_union_left _ he)))
    · obtain ⟨e, he, hd⟩ := hB g hgB
      exact hd (hagree e (Finset.mem_union_left _ (Finset.mem_union_right _ he)))
    · obtain ⟨e, he, hd⟩ := hI g hgI
      exact hd (hagree e (Finset.mem_union_right _ he))
  calc
    _ ≤ ∑ e ∈ (TA ∪ TB) ∪ TI, cost e := weighted_complexity_le_cost hcertificate
    _ ≤ (∑ e ∈ TA ∪ TB, cost e) + ∑ e ∈ TI, cost e :=
      sum_union_cost_le _ _ _
    _ ≤ _ := add_le_add (sum_union_cost_le TA TB cost) le_rfl

/-- Component optima and the minimum interface-cover cost bound the composite
optimum under cost-preserving lifts. The lifting hypotheses cover the corresponding global
alternatives and explicitly preserve each finite certificate's cost bound. -/
theorem weighted_lifted_interface_bound
    {CA EA AA YA CB EB AB YB : Type*}
    [Fintype E] [Fintype EA] [Fintype EB]
    {admissible : Set C} {observe : E → C → A} {task : C → Y} {target : C}
    (admissibleA : Set CA) (observeA : EA → CA → AA) (taskA : CA → YA)
    (targetA : CA) (costA : EA → ENNReal)
    (admissibleB : Set CB) (observeB : EB → CB → AB) (taskB : CB → YB)
    (targetB : CB) (costB : EB → ENNReal)
    (UA UB UI : Set C) (cost : E → ENNReal)
    (liftA : Finset EA → Finset E) (liftB : Finset EB → Finset E)
    (hpartition : ∀ g ∈ admissible, task g ≠ task target →
      g ∈ UA ∨ g ∈ UB ∨ g ∈ UI)
    (hUI : ∀ g ∈ UI, task g ≠ task target)
    (hliftA : ∀ T, IsCertificate admissibleA observeA taskA targetA T →
      CoversAlternatives observe target UA (liftA T) ∧
        (∑ e ∈ liftA T, cost e) ≤ ∑ e ∈ T, costA e)
    (hliftB : ∀ T, IsCertificate admissibleB observeB taskB targetB T →
      CoversAlternatives observe target UB (liftB T) ∧
        (∑ e ∈ liftB T, cost e) ≤ ∑ e ∈ T, costB e)
    (hcertificateA : ∃ T, IsCertificate admissibleA observeA taskA targetA T)
    (hcertificateB : ∃ T, IsCertificate admissibleB observeB taskB targetB T)
    (hinterface : ∃ T, CoversAlternatives observe target UI T) :
    weightedCertificateComplexity admissible observe task target cost ≤
      weightedCertificateComplexity admissibleA observeA taskA targetA costA +
      weightedCertificateComplexity admissibleB observeB taskB targetB costB +
      interfaceCoverComplexity observe target UI cost := by
  classical
  obtain ⟨TA, hTA, hcostA⟩ := weighted_complexity_attained (cost := costA) hcertificateA
  obtain ⟨TB, hTB, hcostB⟩ := weighted_complexity_attained (cost := costB) hcertificateB
  have hinterface' : ∃ T, IsCertificate UI observe task target T := by
    obtain ⟨T, hT⟩ := hinterface
    exact ⟨T, (interface_certificate_iff_covers T hUI).mpr hT⟩
  obtain ⟨TI, hTI, hcostI⟩ := weighted_complexity_attained (cost := cost) hinterface'
  have hcoverI := (interface_certificate_iff_covers TI hUI).mp hTI
  have hA := hliftA TA hTA
  have hB := hliftB TB hTB
  calc
    _ ≤ (∑ e ∈ liftA TA, cost e) + (∑ e ∈ liftB TB, cost e) +
        ∑ e ∈ TI, cost e :=
      lifted_interface_cover_bound UA UB UI _ _ _ cost hpartition hA.1 hB.1 hcoverI
    _ ≤ (∑ e ∈ TA, costA e) + (∑ e ∈ TB, costB e) + ∑ e ∈ TI, cost e :=
      add_le_add (add_le_add hA.2 hB.2) le_rfl
    _ = _ := by
      rw [hcostA, hcostB, hcostI,
        interfaceCoverComplexity_eq_weighted observe task target UI cost hUI]

end Interfaces

/-- Enlarging the admissible comparison class can only increase certificate
complexity, since every certificate for the larger class also serves the smaller. -/
theorem complexity_mono_admissible {C E A Y : Type*}
    {smaller larger : Set C} {observe : E → C → A} {task : C → Y} {target : C}
    (hsubset : smaller ⊆ larger) :
    certificateComplexity smaller observe task target ≤
      certificateComplexity larger observe task target := by
  apply le_complexity
  intro T hT
  apply complexity_le_card
  intro g hg hagree
  exact hT g (hsubset hg) hagree

section InteractionSupersets

variable {X : Type*} [Fintype X] [DecidableEq X]

/-- The interaction lower bound is unchanged for any Boolean function class
containing zero and every singleton, including larger comparison classes. -/
theorem interaction_complexity_eq_card_of_contains {Y : Type*}
    (admissible : Set (X → Bool)) (task : (X → Bool) → Y)
    (hzero : (fun _ => false) ∈ admissible)
    (hsingletons : ∀ x, interactionIndicator x ∈ admissible)
    (hchanges : ∀ x, task (interactionIndicator x) ≠ task (fun _ => false)) :
    certificateComplexity admissible (fun x f => f x) task (fun _ => false) =
      (Fintype.card X : WithTop ℕ) := by
  apply le_antisymm
  · simpa using complexity_le_card (full_point_certificate admissible task (fun _ => false))
  · calc
      (Fintype.card X : WithTop ℕ) = certificateComplexity (interactionAdmissible X)
          (fun x f => f x) task (fun _ => false) :=
        (interaction_complexity_eq_card task hchanges).symm
      _ ≤ _ := complexity_mono_admissible (by
        intro f hf
        rcases hf with rfl | ⟨x, rfl⟩
        · exact hzero
        · exact hsingletons x)

theorem interaction_identity_complexity_of_contains
    (admissible : Set (X → Bool)) (hzero : (fun _ => false) ∈ admissible)
    (hsingletons : ∀ x, interactionIndicator x ∈ admissible) :
    certificateComplexity admissible (fun x f => f x) id (fun _ => false) =
      (Fintype.card X : WithTop ℕ) := by
  apply interaction_complexity_eq_card_of_contains admissible id hzero hsingletons
  intro x h
  have hx := congrFun h x
  simp [interactionIndicator] at hx

theorem interaction_existence_complexity_of_contains
    (admissible : Set (X → Bool)) (hzero : (fun _ => false) ∈ admissible)
    (hsingletons : ∀ x, interactionIndicator x ∈ admissible) :
    certificateComplexity admissible (fun x f => f x) interactionAnyPositive
      (fun _ => false) = (Fintype.card X : WithTop ℕ) := by
  apply interaction_complexity_eq_card_of_contains admissible _ hzero hsingletons
  intro x
  simp [interactionAnyPositive, interactionIndicator]

theorem interaction_counting_complexity_of_contains
    (admissible : Set (X → Bool)) (hzero : (fun _ => false) ∈ admissible)
    (hsingletons : ∀ x, interactionIndicator x ∈ admissible) :
    certificateComplexity admissible (fun x f => f x) interactionPositiveCount
      (fun _ => false) = (Fintype.card X : WithTop ℕ) := by
  apply interaction_complexity_eq_card_of_contains admissible _ hzero hsingletons
  intro x
  have hsupport : (Finset.univ.filter fun y => interactionIndicator x y = true) = {x} := by
    ext y
    simp [interactionIndicator]
  simp [interactionPositiveCount, hsupport]

end InteractionSupersets

theorem pairwise_interaction_identity_complexity_of_contains (p q : ℕ)
    (admissible : Set ((Fin p × Fin q) → Bool))
    (hzero : (fun _ => false) ∈ admissible)
    (hsingletons : ∀ x, interactionIndicator x ∈ admissible) :
    certificateComplexity admissible (fun x f => f x) id (fun _ => false) =
      ((p * q : ℕ) : WithTop ℕ) := by
  simpa using interaction_identity_complexity_of_contains admissible hzero hsingletons

theorem pairwise_interaction_existence_complexity_of_contains (p q : ℕ)
    (admissible : Set ((Fin p × Fin q) → Bool))
    (hzero : (fun _ => false) ∈ admissible)
    (hsingletons : ∀ x, interactionIndicator x ∈ admissible) :
    certificateComplexity admissible (fun x f => f x) interactionAnyPositive
      (fun _ => false) = ((p * q : ℕ) : WithTop ℕ) := by
  simpa using interaction_existence_complexity_of_contains admissible hzero hsingletons

theorem pairwise_interaction_counting_complexity_of_contains (p q : ℕ)
    (admissible : Set ((Fin p × Fin q) → Bool))
    (hzero : (fun _ => false) ∈ admissible)
    (hsingletons : ∀ x, interactionIndicator x ∈ admissible) :
    certificateComplexity admissible (fun x f => f x) interactionPositiveCount
      (fun _ => false) = ((p * q : ℕ) : WithTop ℕ) := by
  simpa using interaction_counting_complexity_of_contains admissible hzero hsingletons

end ExactSolution
