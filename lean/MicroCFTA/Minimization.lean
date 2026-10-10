import MicroCFTA.Guards
import MicroCFTA.Language

/-!
# Guard preservation under stronger refinements

This module models the read classification added to `Refinement.Minimize` in
`cb770b0`. It derives preservation from concrete atomic semantics. It proves
preservation of an accepted guard, not equality of all solver answers.

A compatible change preserves path presence, strengthens refinements at
monotone reads, preserves refinements at sensitive reads, and preserves whole
terms at structural reads. The graph traversal in `keepsGuards` and the
subtyping oracle must establish these conditions. They are not assumed to be
correct implementations of them. Substitution scopes are outside this model.
-/

namespace MicroCFTA.Minimization
open MicroCFTA.Guards

/-- Observations at paths, with formulas interpreted as predicates on values. -/
structure Context (Path Value Term : Type) where
  termAt : Path → Option Term
  refinement : Path → Value → Prop

/-- A path is present when its subterm exists. -/
def present (context : Context Path Value Term) (path : Path) : Bool :=
  (context.termAt path).isSome

/-- The atomic guards classified by the repaired minimizer. -/
inductive Atom (Path Value : Type) where
  | same (left right : Path)
  | entails (antecedent consequent : Path)
  | satisfies (target : Path) (requirement : Value → Prop)
  | holds (targets : List Path) (formula : (Path → Value) → Prop)

/-- A formula with its polarity, including refutation-style negation. -/
def polarized (positive : Bool) (proposition : Prop) : Prop :=
  if positive then proposition else ¬proposition

/-- Two paths contain one existing term. -/
def sameAt (context : Context Path Value Term) (left right : Path) : Prop :=
  ∃ term, context.termAt left = some term ∧ context.termAt right = some term

/-- Atomic guard semantics, including the missing-path rules. -/
def meaning (context : Context Path Value Term) : Atom Path Value → Bool → Prop
  | .same left right, positive => polarized positive (sameAt context left right)
  | .entails left right, positive => polarized positive
      (present context left = true ∧ present context right = true ∧
        Entails (context.refinement left) (context.refinement right))
  | .satisfies target requirement, positive =>
      if present context target then
        Entails (context.refinement target) (fun value => polarized positive (requirement value))
      else positive = false
  | .holds targets formula, positive =>
      if targets.all (present context) then
        ∀ values : Path → Value,
          (∀ path, path ∈ targets → context.refinement path (values path)) →
            polarized positive (formula values)
      else positive = false

/-- Paths that can strengthen, must stay fixed, or require whole terms. -/
structure Reads (Path : Type) where
  monotone : List Path
  sensitive : List Path
  structural : List Path

/-- An empty read classification. -/
def Reads.empty : Reads Path := ⟨[], [], []⟩

/-- Combine the reads from two guard branches. -/
def Reads.union (left right : Reads Path) : Reads Path :=
  ⟨left.monotone ++ right.monotone, left.sensitive ++ right.sensitive,
    left.structural ++ right.structural⟩

/-- The atomic classification in `guardReads`. -/
def atomReads : Atom Path Value → Bool → Reads Path
  | .same left right, _ => ⟨[], [], [left, right]⟩
  | .entails left right, true => ⟨[left], [right], []⟩
  | .entails left right, false => ⟨[], [left, right], []⟩
  | .satisfies target _, _ => ⟨[target], [], []⟩
  | .holds targets _, _ => ⟨targets, [], []⟩

/-- Push polarity through a guard and classify every atomic read. -/
def guardReads : Guard (Atom Path Value) → Bool → Reads Path
  | .top, _ | .bottom, _ => .empty
  | .atom atom, positive => atomReads atom positive
  | .not guard, positive => guardReads guard (!positive)
  | .and left right, positive | .or left right, positive =>
      .union (guardReads left positive) (guardReads right positive)

/-- The semantic conditions that a classification permits. -/
def Compatible (before after : Context Path Value Term) (reads : Reads Path) : Prop :=
  (∀ path, path ∈ reads.monotone →
    present before path = present after path ∧
      Entails (after.refinement path) (before.refinement path)) ∧
  (∀ path, path ∈ reads.sensitive →
    present before path = present after path ∧
      ∀ value, before.refinement path value ↔ after.refinement path value) ∧
  (∀ path, path ∈ reads.structural → before.termAt path = after.termAt path)

/-- Compatibility of combined reads gives compatibility for the left branch. -/
theorem compatible_union_left {before after : Context Path Value Term}
    {left right : Reads Path} (compatible : Compatible before after (.union left right)) :
    Compatible before after left := by
  refine ⟨?_, ?_, ?_⟩
  · intro path member
    exact compatible.1 path (List.mem_append_left _ member)
  · intro path member
    exact compatible.2.1 path (List.mem_append_left _ member)
  · intro path member
    exact compatible.2.2 path (List.mem_append_left _ member)

/-- Compatibility of combined reads gives compatibility for the right branch. -/
theorem compatible_union_right {before after : Context Path Value Term}
    {left right : Reads Path} (compatible : Compatible before after (.union left right)) :
    Compatible before after right := by
  refine ⟨?_, ?_, ?_⟩
  · intro path member
    exact compatible.1 path (List.mem_append_right _ member)
  · intro path member
    exact compatible.2.1 path (List.mem_append_right _ member)
  · intro path member
    exact compatible.2.2 path (List.mem_append_right _ member)

/-- Conjunction over a finite list uses only the observations in that list. -/
theorem all_ext_on_members (entries : List Path) (left right : Path → Bool)
    (same : ∀ path, path ∈ entries → left path = right path) :
    entries.all left = entries.all right := by
  induction entries with
  | nil => rfl
  | cons path rest ih =>
      simp only [List.all_cons]
      rw [same path (by simp), ih (fun other member => same other (by simp [member]))]

/-- Each permitted atomic change preserves the accepted atomic guard. -/
theorem atom_preserves {before after : Context Path Value Term}
    (atom : Atom Path Value) (positive : Bool)
    (compatible : Compatible before after (atomReads atom positive)) :
    meaning before atom positive → meaning after atom positive := by
  cases atom with
  | same left right =>
      have hl := compatible.2.2 left (by simp [atomReads])
      have hr := compatible.2.2 right (by simp [atomReads])
      simp only [meaning, sameAt]
      rw [hl, hr]
      exact id
  | entails left right =>
      cases positive
      · have hl := compatible.2.1 left (by simp [atomReads])
        have hr := compatible.2.1 right (by simp [atomReads])
        intro rejected accepted
        apply rejected
        refine ⟨hl.1.trans accepted.1, hr.1.trans accepted.2.1, ?_⟩
        intro value inside
        exact (hr.2 value).mpr (accepted.2.2 value ((hl.2 value).mp inside))
      · have hl := compatible.1 left (by simp [atomReads])
        have hr := compatible.2.1 right (by simp [atomReads])
        intro accepted
        refine ⟨hl.1.symm.trans accepted.1, hr.1.symm.trans accepted.2.1, ?_⟩
        intro value inside
        exact (hr.2 value).mp (accepted.2.2 value (hl.2 value inside))
  | satisfies target requirement =>
      have targetChange := compatible.1 target (by simp [atomReads])
      simp only [meaning]
      rw [targetChange.1]
      split
      · intro accepted value inside
        exact accepted value (targetChange.2 value inside)
      · exact id
  | holds targets formula =>
      have targetChange := fun path member => compatible.1 path member
      have presence : targets.all (present before) = targets.all (present after) :=
        all_ext_on_members targets _ _ (fun path member => (targetChange path member).1)
      simp only [meaning]
      rw [presence]
      split
      · intro accepted values inside
        apply accepted values
        intro path member
        exact (targetChange path member).2 (values path) (inside path member)
      · exact id

/-- The repaired polarity classification preserves arbitrary Boolean guards. -/
theorem classified_guard_preserves {before after : Context Path Value Term}
    (guard : Guard (Atom Path Value)) (positive : Bool)
    (compatible : Compatible before after (guardReads guard positive)) :
    Semantics (meaning before) positive guard → Semantics (meaning after) positive guard := by
  induction guard generalizing positive with
  | top => exact id
  | bottom => exact id
  | atom atom => exact atom_preserves atom positive compatible
  | not guard ih => exact ih (!positive) compatible
  | and left right ihl ihr =>
      have hl := ihl positive (compatible_union_left compatible)
      have hr := ihr positive (compatible_union_right compatible)
      cases positive
      · intro accepted
        exact accepted.elim (fun proof => Or.inl (hl proof)) (fun proof => Or.inr (hr proof))
      · intro accepted
        exact ⟨hl accepted.1, hr accepted.2⟩
  | or left right ihl ihr =>
      have hl := ihl positive (compatible_union_left compatible)
      have hr := ihr positive (compatible_union_right compatible)
      cases positive
      · intro accepted
        exact ⟨hl accepted.1, hr accepted.2⟩
      · intro accepted
        exact accepted.elim (fun proof => Or.inl (hl proof)) (fun proof => Or.inr (hr proof))

/-- Strengthening an assumed refinement can turn a rejected formula into a proved one. -/
theorem monotone_does_not_mean_equal_answers :
    Entails (fun value : Bool => value = true) (fun _ => True) ∧
      ¬Entails (fun _ : Bool => True) (fun value => value = true) ∧
      Entails (fun value : Bool => value = true) (fun value => value = true) := by
  unfold Entails
  decide

/-- Strengthening an entailment consequent need not preserve a positive answer. -/
theorem consequent_strengthening_counterexample :
    Entails (fun _ : Bool => True) (fun _ => True) ∧
      ¬Entails (fun _ : Bool => True) (fun value => value = true) := by
  unfold Entails
  decide

/-- Strengthening an antecedent need not preserve a negated entailment. -/
theorem negated_entailment_strengthening_counterexample :
    ¬Entails (fun _ : Bool => True) (fun value => value = true) ∧
      Entails (fun value : Bool => value = true) (fun value => value = true) := by
  unfold Entails
  decide

/-!
## A representative must have an accepted derivation

The repaired read classification cannot prove that a representative itself
accepts a term. A leaf with refinement `true` and guard `Satisfies [] false`
is structurally productive and accepts nothing. A subtype comparison of the
root refinements can select it over an accepted leaf. This is a counterexample
to direct `minimize`. The preceding pruning step in `reduce` removes the bad
representative in the simple executed fixture. In a second executed fixture,
compound substitution actuals make sparse evaluation return `Unknown`. Pruning
retains the rejected representative and `reduce` also loses every solution.
The model below proves the semantic problem with a rejected representative.
It does not encode the sparse substitution evaluation in that second fixture.
-/

namespace RejectedRepresentative
open MicroCFTA.Language

/-- The states of the representative counterexample. -/
inductive State where
  | root | representative | removed
  deriving DecidableEq

/-- The labels have equal leaf refinement types in the Haskell fixture. -/
inductive Symbol where
  | f | a | b
  deriving DecidableEq

/-- A leaf whose interpreted guard is the given Boolean. -/
def leaf (symbol : Symbol) (accepted : Bool) : Edge State Symbol :=
  ⟨symbol, [], fun _ => accepted⟩

/-- One unary parent alternative. -/
def parent (child : State) : Edge State Symbol :=
  ⟨.f, [child], fun _ => true⟩

/-- The accepted original alternative and the rejected representative coexist. -/
def before : Automaton State Symbol
  | .root => [parent .representative, parent .removed]
  | .representative => [leaf .a false]
  | .removed => [leaf .b true]

/-- Replacement deletes the accepted leaf and retains only the rejected one. -/
def after : Automaton State Symbol
  | .root => [parent .representative]
  | .representative => [leaf .a false]
  | .removed => []

/-- The original accepted term. -/
def witness : Term Symbol := .node .f [.node .b []]

/-- The representative's structural term, rejected by its leaf guard. -/
def structuralWitness : Term Symbol := .node .f [.node .a []]

/-- Interpret the representative's `true` refinement and present root path. -/
def representativeContext : Context Unit Bool Unit :=
  ⟨fun _ => some (), fun _ _ => True⟩

/-- The failed leaf guard is exactly the truth of `Satisfies [] false`. -/
theorem representative_guard_fails :
    ¬meaning representativeContext (.satisfies () (fun _ => False)) true := by
  intro proved
  exact proved false trivial

/-- The original automaton accepts a finite term. -/
theorem before_accepts : Accepts before .root witness :=
  enumerate_sound before 2 (by
    simp [enumerate, before, products, witness, leaf, parent])

/-- No finite derivation is accepted at the representative state. -/
theorem representative_accepts_nothing (term : Term Symbol) :
    ¬Accepts after .representative term := by
  intro accepted
  cases accepted with
  | node edge children member runs guard =>
      have he : edge = leaf .a false := by simpa [after] using member
      subst edge
      cases guard

/-- After replacement the root has no accepted term at any depth. -/
theorem after_accepts_nothing (term : Term Symbol) : ¬Accepts after .root term := by
  intro accepted
  cases accepted with
  | node edge children member runs guard =>
      have he : edge = parent .representative := by simpa [after] using member
      subst edge
      cases runs with
      | cons child rest => exact representative_accepts_nothing _ child

/-- The same graph with guards ignored. -/
def structuralAfter : Automaton State Symbol := fun state =>
  (after state).map (fun edge => {edge with guard := fun _ => true})

/-- The root and its representative remain structurally productive. -/
theorem after_structurally_productive :
    Accepts structuralAfter .root structuralWitness :=
  enumerate_sound structuralAfter 2 (by
    simp [enumerate, structuralAfter, after, products, structuralWitness, leaf, parent])

/-- Guard preservation at parent reads does not establish a usable representative. -/
theorem guarded_representative_counterexample :
    (∃ term, Accepts before .root term) ∧
      (∃ term, Accepts structuralAfter .root term) ∧
      ¬(∃ term, Accepts after .root term) := by
  refine ⟨⟨witness, before_accepts⟩,
    ⟨structuralWitness, after_structurally_productive⟩, ?_⟩
  rintro ⟨term, accepted⟩
  exact after_accepts_nothing term accepted

end RejectedRepresentative

end MicroCFTA.Minimization
