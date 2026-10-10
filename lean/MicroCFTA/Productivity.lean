import MicroCFTA.Language

/-!
# Finite graph closure and guarded productivity

The minimizer's `unconstrainedBelow` repair checks a representative transition
and every transition reachable below its children. This module proves that
this check restores the implication from structural runs to accepted runs.

The executable graph algorithms use a complete finite list of states and
Boolean state sets. They iterate to a fixed point within the list's length.
The Haskell implementation uses maps and sets and stops on equality instead.
A sound metadata predicate represents the syntactic `noConstraint` check.
The below-check and productivity premises use the same automaton snapshot.
Haskell checks the intermediate table and later checks productivity after the
whole schedule. Preservation across those snapshots remains a separate proof.
No solver, guard equivalence procedure, or complete minimization schedule is
assumed to have been verified.
-/

namespace MicroCFTA.Productivity
open MicroCFTA.Language

/-- Inclusion of Boolean state sets. -/
def Included (left right : State → Bool) : Prop :=
  ∀ state, left state = true → right state = true

/-- A graph operator preserves inclusion. -/
def Monotone (step : (State → Bool) → State → Bool) : Prop :=
  ∀ left right, Included left right → Included (step left) (step right)

/-- Iterate a graph operator without inspecting terms. -/
def iterate (step : (State → Bool) → State → Bool) (initial : State → Bool) :
    Nat → State → Bool
  | 0 => initial
  | fuel + 1 => step (iterate step initial fuel)

/-- A monotone operator produces an ascending chain from an ascending first step. -/
theorem iterate_ascending (step : (State → Bool) → State → Bool)
    (initial : State → Bool) (monotone : Monotone step)
    (first : Included initial (step initial)) (fuel : Nat) :
    Included (iterate step initial fuel) (iterate step initial (fuel + 1)) := by
  induction fuel with
  | zero => exact first
  | succ fuel ih => exact monotone _ _ ih

/-- Iteration stays inside every closed state set that contains its initial set. -/
theorem iterate_below_closed (step : (State → Bool) → State → Bool)
    (initial invariant : State → Bool) (monotone : Monotone step)
    (startsInside : Included initial invariant) (closed : Included (step invariant) invariant)
    (fuel : Nat) : Included (iterate step initial fuel) invariant := by
  induction fuel with
  | zero => exact startsInside
  | succ fuel ih =>
      intro state marked
      exact closed state (monotone _ _ ih state marked)

/-- Strict inclusion of Boolean sets increases their count on a complete list. -/
theorem count_strict (states : List State) (left right : State → Bool)
    (included : ∀ state, state ∈ states → left state = true → right state = true)
    (witness : ∃ state, state ∈ states ∧ left state = false ∧ right state = true) :
    states.countP left < states.countP right := by
  induction states with
  | nil => simp at witness
  | cons state states ih =>
      have tailIncluded : ∀ other, other ∈ states → left other = true → right other = true :=
        fun other member => included other (by simp [member])
      have weak : states.countP left ≤ states.countP right :=
        List.countP_mono_left tailIncluded
      rcases witness with ⟨other, member, absent, added⟩
      rcases List.mem_cons.mp member with same | member
      · subst other
        simp [absent, added]
        omega
      · have strict := ih tailIncluded ⟨other, member, absent, added⟩
        have head := included state (by simp)
        cases hl : left state <;> cases hr : right state <;>
          simp_all <;> omega

/-- Unequal ascending state sets have strictly increasing counts. -/
theorem count_strict_of_ne (states : List State) (complete : ∀ state, state ∈ states)
    (left right : State → Bool) (included : Included left right) (different : left ≠ right) :
    states.countP left < states.countP right := by
  apply count_strict states left right (fun state _ => included state)
  classical
  apply Classical.byContradiction
  intro none
  apply different
  funext state
  have hn : ¬(left state = false ∧ right state = true) :=
    fun pair => none ⟨state, complete state, pair⟩
  have hs := included state
  cases hl : left state <;> cases hr : right state <;> simp_all

/-- If iteration has not stabilized, each preceding step added a state. -/
theorem growth_before_stability (states : List State) (complete : ∀ state, state ∈ states)
    (step : (State → Bool) → State → Bool) (initial : State → Bool)
    (monotone : Monotone step) (first : Included initial (step initial)) (fuel : Nat)
    (different : iterate step initial fuel ≠ iterate step initial (fuel + 1)) :
    fuel + 1 ≤ states.countP (iterate step initial (fuel + 1)) := by
  induction fuel with
  | zero =>
      have growth := count_strict_of_ne states complete _ _
        (iterate_ascending step initial monotone first 0) different
      omega
  | succ fuel ih =>
      have previous : iterate step initial fuel ≠ iterate step initial (fuel + 1) := by
        intro same
        apply different
        exact congrArg step same
      have bound := ih previous
      have growth := count_strict_of_ne states complete _ _
        (iterate_ascending step initial monotone first (fuel + 1)) different
      omega

/-- A monotone Boolean graph computation stabilizes within the number of states. -/
theorem finite_stability (states : List State) (complete : ∀ state, state ∈ states)
    (step : (State → Bool) → State → Bool) (initial : State → Bool)
    (monotone : Monotone step) (first : Included initial (step initial)) :
    step (iterate step initial states.length) = iterate step initial states.length := by
  classical
  apply Classical.byContradiction
  intro different
  have growth := growth_before_stability states complete step initial monotone first states.length
    (fun same => different same.symm)
  have bound := List.countP_le_length (p := iterate step initial (states.length + 1)) (l := states)
  omega

/-- The child states of all outgoing transitions. -/
def successors (automaton : Automaton State Symbol) (state : State) : List State :=
  (automaton state).flatMap Edge.children

/-- Reachability starts at the children of the representative. -/
inductive Reachable (next : State → List State) (seeds : List State) : State → Prop where
  | seed : state ∈ seeds → Reachable next seeds state
  | step : Reachable next seeds parent → child ∈ next parent → Reachable next seeds child

/-- Add the successors of every reached state. -/
def reachStep [DecidableEq State] (states : List State) (next : State → List State)
    (known : State → Bool) (target : State) : Bool :=
  known target || states.any (fun source => known source && decide (target ∈ next source))

/-- Reachability expansion preserves inclusion. -/
theorem reachStep_monotone [DecidableEq State] (states : List State) (next : State → List State) :
    Monotone (reachStep states next) := by
  intro left right included target reached
  simp only [reachStep, Bool.or_eq_true, List.any_eq_true, Bool.and_eq_true,
    decide_eq_true_eq] at reached ⊢
  rcases reached with here | ⟨source, member, active, child⟩
  · exact Or.inl (included target here)
  · exact Or.inr ⟨source, member, included source active, child⟩

/-- A reached state remains reached. -/
theorem reachStep_includes [DecidableEq State] (states : List State) (next : State → List State)
    (known : State → Bool) : Included known (reachStep states next known) := by
  intro state member
  simp [reachStep, member]

/-- Compute the finite descendant closure. -/
def reachClosure [DecidableEq State] (states : List State) (next : State → List State)
    (seeds : List State) : State → Bool :=
  iterate (reachStep states next) (fun state => decide (state ∈ seeds)) states.length

/-- Every reached bit has a finite graph path from a seed. -/
theorem reach_iterate_sound [DecidableEq State] (states : List State) (next : State → List State)
    (seeds : List State) (fuel : Nat) (state : State)
    (reached : iterate (reachStep states next) (fun state => decide (state ∈ seeds)) fuel state = true) :
    Reachable next seeds state := by
  induction fuel generalizing state with
  | zero => exact .seed (by simpa [iterate] using reached)
  | succ fuel ih =>
      simp only [iterate, reachStep, Bool.or_eq_true, List.any_eq_true,
        Bool.and_eq_true, decide_eq_true_eq] at reached
      rcases reached with here | ⟨source, _, active, child⟩
      · exact ih state here
      · exact .step (ih source active) child

/-- Every seed stays in every reachability iteration. -/
theorem reach_seed [DecidableEq State] (states : List State) (next : State → List State)
    (seeds : List State) (fuel : Nat) (state : State) (member : state ∈ seeds) :
    iterate (reachStep states next) (fun state => decide (state ∈ seeds)) fuel state = true := by
  induction fuel with
  | zero => simpa [iterate] using member
  | succ fuel ih => exact reachStep_includes states next _ state ih

/-- Descendant closure computes exactly finite reachability, including cycles. -/
theorem reachClosure_correct [DecidableEq State] (states : List State)
    (complete : ∀ state, state ∈ states) (next : State → List State) (seeds : List State)
    (state : State) : reachClosure states next seeds state = true ↔ Reachable next seeds state := by
  constructor
  · exact reach_iterate_sound states next seeds states.length state
  · intro reachable
    have fixed : reachStep states next (reachClosure states next seeds) =
        reachClosure states next seeds :=
      finite_stability states complete _ _ (reachStep_monotone states next)
        (reachStep_includes states next _)
    induction reachable with
    | seed member => exact reach_seed states next seeds states.length _ member
    | @step parent child reachable member ih =>
        rw [← fixed]
        simp only [reachStep, Bool.or_eq_true, List.any_eq_true, Bool.and_eq_true, decide_eq_true_eq]
        exact Or.inr ⟨parent, complete parent, ih, member⟩

/-- Remove guard checks but retain labels, edges, and child order. -/
def eraseGuards (automaton : Automaton State Symbol) : Automaton State Symbol :=
  fun state => (automaton state).map (fun edge => {edge with guard := fun _ => true})

/-- One structural productivity iteration. -/
def productiveStep (automaton : Automaton State Symbol) (known : State → Bool) (state : State) : Bool :=
  (automaton state).any (fun edge => edge.children.all known)

/-- Structural productivity preserves inclusion. -/
theorem productiveStep_monotone (automaton : Automaton State Symbol) : Monotone (productiveStep automaton) := by
  intro left right included state productive
  obtain ⟨edge, member, children⟩ := List.any_eq_true.mp productive
  apply List.any_eq_true.mpr
  refine ⟨edge, member, List.all_eq_true.mpr ?_⟩
  intro child belongs
  exact included child (List.all_eq_true.mp children child belongs)

/-- Compute structural productivity from the empty state set. -/
def productive (states : List State) (automaton : Automaton State Symbol) : State → Bool :=
  iterate (productiveStep automaton) (fun _ => false) states.length

/-- Finitely many inhabited child relations yield one tuple of witnesses. -/
theorem all₂_witnesses (relation : State → Term Symbol → Prop) (states : List State)
    (inhabited : ∀ state, state ∈ states → ∃ term, relation state term) :
    ∃ terms, All₂ relation states terms := by
  induction states with
  | nil => exact ⟨[], .nil⟩
  | cons state states ih =>
      obtain ⟨term, accepted⟩ := inhabited state (by simp)
      obtain ⟨terms, acceptedRest⟩ := ih (fun other member => inhabited other (by simp [member]))
      exact ⟨term :: terms, .cons accepted acceptedRest⟩

/-- Every productive bit has a finite structural run. -/
theorem productive_iterate_sound (automaton : Automaton State Symbol) (fuel : Nat) (state : State)
    (marked : iterate (productiveStep automaton) (fun _ => false) fuel state = true) :
    ∃ term, Accepts (eraseGuards automaton) state term := by
  induction fuel generalizing state with
  | zero => simp [iterate] at marked
  | succ fuel ih =>
      obtain ⟨edge, member, children⟩ := List.any_eq_true.mp marked
      obtain ⟨terms, runs⟩ := all₂_witnesses (Accepts (eraseGuards automaton)) edge.children
        (fun child belongs => ih child (List.all_eq_true.mp children child belongs))
      refine ⟨.node edge.label terms, .node {edge with guard := fun _ => true} terms ?_ runs rfl⟩
      exact List.mem_map.mpr ⟨edge, member, rfl⟩

/-- At a fixed point, every finite structural run has its state marked. -/
theorem productive_fixed_complete (automaton : Automaton State Symbol) (known : State → Bool)
    (fixed : productiveStep automaton known = known) {state : State} {term : Term Symbol}
    (accepted : Accepts (eraseGuards automaton) state term) : known state = true := by
  induction accepted using Accepts.rec
    (motive_2 := fun states terms _ => states.all known = true) with
  | @node state erased terms member runs guard ih =>
      obtain ⟨edge, originalMember, equality⟩ := List.mem_map.mp member
      subst erased
      rw [← fixed]
      exact List.any_eq_true.mpr ⟨edge, originalMember, ih⟩
  | nil => rfl
  | cons child children ih ihs => simp [List.all_cons, ih, ihs]

/-- The finite fixed point is exactly structural productivity, even with cycles. -/
theorem productive_correct (states : List State) (complete : ∀ state, state ∈ states)
    (automaton : Automaton State Symbol) (state : State) :
    productive states automaton state = true ↔ ∃ term, Accepts (eraseGuards automaton) state term := by
  constructor
  · exact productive_iterate_sound automaton states.length state
  · rintro ⟨term, accepted⟩
    apply productive_fixed_complete automaton (productive states automaton) ?_ accepted
    apply finite_stability states complete _ _ (productiveStep_monotone automaton)
    intro state impossible
    cases impossible

/-- Structural productivity is the least state set closed under productive edges. -/
theorem productive_least (states : List State) (automaton : Automaton State Symbol)
    (known : State → Bool) (closed : Included (productiveStep automaton known) known) :
    Included (productive states automaton) known := by
  apply iterate_below_closed _ _ known (productiveStep_monotone automaton) ?_ closed
  intro state impossible
  cases impossible

/-- Check the representative and every transition below its children. -/
def unconstrainedBelow [DecidableEq State] (states : List State)
    (automaton : Automaton State Symbol) (clear : Edge State Symbol → Bool)
    (representative : Edge State Symbol) : Bool :=
  clear representative && states.all (fun state =>
    !(reachClosure states (successors automaton) representative.children state) ||
      (automaton state).all clear)

/-- The executable below-check certifies every reachable transition. -/
theorem unconstrainedBelow_spec [DecidableEq State] (states : List State)
    (complete : ∀ state, state ∈ states) (automaton : Automaton State Symbol)
    (clear : Edge State Symbol → Bool) (representative : Edge State Symbol)
    (checked : unconstrainedBelow states automaton clear representative = true) :
    clear representative = true ∧
      ∀ state, Reachable (successors automaton) representative.children state →
        ∀ edge, edge ∈ automaton state → clear edge = true := by
  have checks := (Bool.and_eq_true _ _).mp checked
  refine ⟨checks.1, ?_⟩
  intro state reached edge member
  have row := List.all_eq_true.mp checks.2 state (complete state)
  have bit := (reachClosure_correct states complete _ _ state).mpr reached
  simp only [bit, Bool.not_true, Bool.false_or] at row
  exact List.all_eq_true.mp row edge member

/-- A child of a reachable transition is reachable. -/
theorem reachable_child (automaton : Automaton State Symbol) (seeds : List State)
    {state child : State} {edge : Edge State Symbol}
    (reached : Reachable (successors automaton) seeds state)
    (member : edge ∈ automaton state) (belongs : child ∈ edge.children) :
    Reachable (successors automaton) seeds child :=
  .step reached (List.mem_flatMap.mpr ⟨edge, member, belongs⟩)

/-- Erasing guards retains every original finite run. -/
theorem eraseGuards_accepts (automaton : Automaton State Symbol)
    {state : State} {term : Term Symbol} (accepted : Accepts automaton state term) :
    Accepts (eraseGuards automaton) state term := by
  induction accepted using Accepts.rec
    (motive_2 := fun states terms _ => All₂ (Accepts (eraseGuards automaton)) states terms) with
  | node edge terms member runs guard ih =>
      exact .node {edge with guard := fun _ => true} terms
        (List.mem_map.mpr ⟨edge, member, rfl⟩) ih rfl
  | nil => exact .nil
  | cons child children ih ihs => exact .cons ih ihs

/-- Structural runs are accepted in a closed region whose guards always hold. -/
theorem restoreGuards (automaton : Automaton State Symbol) (region : State → Prop)
    (closed : ∀ state, ∀ edge ∈ automaton state, ∀ child ∈ edge.children,
      region state → region child)
    (guards : ∀ state, region state → ∀ edge ∈ automaton state,
      ∀ term, edge.guard term = true)
    {state : State} {term : Term Symbol}
    (accepted : Accepts (eraseGuards automaton) state term) :
    region state → Accepts automaton state term := by
  induction accepted using Accepts.rec
    (motive_2 := fun states terms _ =>
      (∀ state, state ∈ states → region state) → All₂ (Accepts automaton) states terms) with
  | @node state erased terms member runs guard ih =>
      obtain ⟨edge, originalMember, equality⟩ := List.mem_map.mp member
      subst erased
      intro inside
      exact .node edge terms originalMember
        (ih (fun child belongs => closed state edge originalMember child belongs inside))
        (guards state inside edge originalMember _)
  | nil inside => exact .nil
  | cons child children ih ihs inside =>
      exact .cons (ih (inside _ (by simp)))
        (ihs (fun state member => inside state (by simp [member])))

/-- The below-check restores every structural run in the representative's descendants. -/
theorem unconstrainedBelow_restores_descendants [DecidableEq State] (states : List State)
    (complete : ∀ state, state ∈ states) (automaton : Automaton State Symbol)
    (clear : Edge State Symbol → Bool)
    (metadataSound : ∀ state, ∀ edge ∈ automaton state,
      clear edge = true → ∀ term, edge.guard term = true)
    (representative : Edge State Symbol)
    (checked : unconstrainedBelow states automaton clear representative = true)
    {state : State} {term : Term Symbol}
    (reached : Reachable (successors automaton) representative.children state)
    (run : Accepts (eraseGuards automaton) state term) : Accepts automaton state term := by
  have checkedEdges := (unconstrainedBelow_spec states complete automaton clear representative checked).2
  exact restoreGuards automaton (Reachable (successors automaton) representative.children)
    (fun _ _ member _ belongs reached => reachable_child automaton _ reached member belongs)
    (fun state reached edge member term => metadataSound state edge member (checkedEdges state reached edge member) term)
    run reached

/-- Restore the structural child tuple of a checked representative. -/
theorem unconstrainedBelow_restores_children [DecidableEq State] (states : List State)
    (complete : ∀ state, state ∈ states) (automaton : Automaton State Symbol)
    (clear : Edge State Symbol → Bool)
    (metadataSound : ∀ state, ∀ edge ∈ automaton state,
      clear edge = true → ∀ term, edge.guard term = true)
    (representative : Edge State Symbol)
    (checked : unconstrainedBelow states automaton clear representative = true)
    (children : List State) (terms : List (Term Symbol))
    (included : ∀ state, state ∈ children → state ∈ representative.children)
    (runs : All₂ (Accepts (eraseGuards automaton)) children terms) :
    All₂ (Accepts automaton) children terms := by
  induction runs with
  | nil => exact .nil
  | @cons state term children terms child rest ih =>
      exact .cons
        (unconstrainedBelow_restores_descendants states complete automaton clear metadataSound
          representative checked (.seed (included state (by simp))) child)
        (ih (fun state member => included state (by simp [member])))

/-- The actual below-check makes a structurally productive representative usable. -/
theorem checked_representative_has_accepted_term [DecidableEq State] (states : List State)
    (complete : ∀ state, state ∈ states) (automaton : Automaton State Symbol)
    (clear : Edge State Symbol → Bool)
    (metadataSound : ∀ state, ∀ edge ∈ automaton state,
      clear edge = true → ∀ term, edge.guard term = true)
    (representative : Edge State Symbol) (state : State)
    (member : representative ∈ automaton state)
    (checked : unconstrainedBelow states automaton clear representative = true)
    (productiveChildren : representative.children.all (productive states automaton) = true) :
    ∃ term, Accepts automaton state term := by
  obtain ⟨terms, runs⟩ := all₂_witnesses (Accepts (eraseGuards automaton)) representative.children
    (fun child belongs => (productive_correct states complete automaton child).mp
      (List.all_eq_true.mp productiveChildren child belongs))
  have restored := unconstrainedBelow_restores_children states complete automaton clear metadataSound
    representative checked representative.children terms (fun _ member => member) runs
  have clearRepresentative := (unconstrainedBelow_spec states complete automaton clear representative checked).1
  exact ⟨.node representative.label terms,
    .node representative terms member restored (metadataSound state representative member clearRepresentative _)⟩

/-- Guard erasure and acceptance agree throughout a checked descendant region. -/
theorem unconstrainedBelow_accepts_iff [DecidableEq State] (states : List State)
    (complete : ∀ state, state ∈ states) (automaton : Automaton State Symbol)
    (clear : Edge State Symbol → Bool)
    (metadataSound : ∀ state, ∀ edge ∈ automaton state,
      clear edge = true → ∀ term, edge.guard term = true)
    (representative : Edge State Symbol)
    (checked : unconstrainedBelow states automaton clear representative = true)
    (state : State) (term : Term Symbol)
    (reached : Reachable (successors automaton) representative.children state) :
    Accepts (eraseGuards automaton) state term ↔ Accepts automaton state term :=
  ⟨unconstrainedBelow_restores_descendants states complete automaton clear metadataSound
      representative checked reached, eraseGuards_accepts automaton⟩

/-!
## Deleting the initial state's accepted alternative

The local representative theorem does not make the initial state accepting.
If the removed transition belongs to the initial state, the representative
may remain accepted only at a descendant state. Another rejected initial
alternative can keep the initial state structurally productive.

The executable Haskell fixture uses `a : v >= 0` as the representative of
`b : true`. The simple surviving root has guard `Satisfies [] false`. A second
fixture uses a substitution guard that sparse pruning retains as `Unknown`.
The failing results have the rejected-root situation proved below. The link from the
Haskell rewrite to these automata is established by the executable fixture,
not by a formal translation of the minimization schedule.
-/

namespace RootDeletion

/-- False denotes the initial state. True denotes the representative state. -/
def states : List Bool := [false, true]

/-- The state list covers this concrete graph. -/
theorem states_complete (state : Bool) : state ∈ states := by
  cases state <;> simp [states]

/-- The selected representative has no children and no guard. -/
def representative : Edge Bool Nat := ⟨1, [], fun _ => true⟩

/-- The original root leaf is accepted. -/
def removed : Edge Bool Nat := ⟨2, [], fun _ => true⟩

/-- The other root transition rejects every term but has a productive child. -/
def surviving : Edge Bool Nat := ⟨0, [true], fun _ => false⟩

/-- The representative is reachable below a rejected initial alternative. -/
def before : Automaton Bool Nat
  | false => [removed, surviving]
  | true => [representative]

/-- Removing the initial leaf keeps the rejected alternative and the representative. -/
def after : Automaton Bool Nat
  | false => [surviving]
  | true => [representative]

/-- Constraint metadata for the stored edges in this example. -/
def clear (edge : Edge Bool Nat) : Bool := decide (edge.label ≠ 0)

/-- The concrete constraint metadata is sound for every stored original edge. -/
theorem clear_sound_before (state : Bool) (edge : Edge Bool Nat)
    (member : edge ∈ before state) (flag : clear edge = true) (term : Term Nat) :
    edge.guard term = true := by
  cases state
  · rcases (by simpa [before] using member : edge = removed ∨ edge = surviving) with rfl | rfl
    · rfl
    · simp [clear, surviving] at flag
  · have same : edge = representative := by simpa [before] using member
    subst edge
    rfl

/-- The repaired below-check accepts the chosen representative. -/
theorem representative_passes_below_check :
    unconstrainedBelow states before clear representative = true := by decide

/-- The original initial state accepts its leaf. -/
theorem before_accepts_root : Accepts before false (.node 2 []) :=
  .node removed [] (by simp [before]) .nil rfl

/-- The representative is still accepted after the deletion. -/
theorem after_accepts_representative : Accepts after true (.node 1 []) :=
  .node representative [] (by simp [after]) .nil rfl

/-- The remaining initial transition keeps a finite structural run. -/
theorem after_root_structurally_productive : productive states after false = true := by decide

/-- No finite term is accepted at the initial state after deletion. -/
theorem after_rejects_root (term : Term Nat) : ¬Accepts after false term := by
  intro accepted
  cases accepted with
  | node edge children member runs guard =>
      have same : edge = surviving := by simpa [after] using member
      subst edge
      cases guard

/-- A valid, accepted representative does not prevent total loss at the initial state. -/
theorem root_deletion_counterexample :
    unconstrainedBelow states before clear representative = true ∧
      (∃ term, Accepts before false term) ∧
      (∃ term, Accepts after true term) ∧
      productive states after false = true ∧
      ¬(∃ term, Accepts after false term) := by
  refine ⟨representative_passes_below_check, ⟨_, before_accepts_root⟩,
    ⟨_, after_accepts_representative⟩, after_root_structurally_productive, ?_⟩
  rintro ⟨term, accepted⟩
  exact after_rejects_root term accepted

end RootDeletion

end MicroCFTA.Productivity
