import MicroCFTA.SourceSizedReference
import MicroCFTA.SourceCompactGuards
import MicroCFTA.SourceCyclicAutomaton

/-!
# Equality filtering in the reference Sized worker

The executable class test traverses every path before it compares the
selected terms. An absent path rejects the class. The empty class holds.
The source positive-guard extraction and equality normalization theorems
connect this worker to complete constraint acceptance.
-/

namespace MicroCFTA.SourceSizedEqualities

open Language SourceGuards SourceObservations SourceSymbolicIndex SourceCompactGuards

/-- Traverse every path in its stored order and stop at an absent subtree. -/
def traversePaths (term : Term Symbol) : List (List Nat) → Option (List (Term Symbol))
  | [] => some []
  | first :: rest => do
      let value ← term.atPath first
      let values ← traversePaths term rest
      pure (value :: values)

/-- The source `allSame` compares all remaining terms with the first term. -/
def allSame [DecidableEq Symbol] : List (Term Symbol) → Bool
  | [] => true
  | first :: rest => rest.all (termEq first)

/-- A class holds only when every path exists and every result is equal. -/
def classHolds [DecidableEq Symbol] (term : Term Symbol) (paths : List (List Nat)) : Bool :=
  ((traversePaths term paths).map allSame).getD false

/-- Traversal followed by equality has one common existing subtree. -/
theorem traversal_common [DecidableEq Symbol] (term common : Term Symbol)
    (paths : List (List Nat)) :
    (∃ values, traversePaths term paths = some values ∧ values.all (termEq common) = true) ↔
      ∀ path ∈ paths, term.atPath path = some common := by
  induction paths with
  | nil => simp [traversePaths]
  | cons first rest ih =>
      simp only [traversePaths, Bind.bind, Pure.pure, Option.bind_eq_some_iff,
        Option.some.injEq, List.forall_mem_cons]
      constructor
      · rintro ⟨values, ⟨head, found, tail, traversed, rfl⟩, equal⟩
        have parts : termEq common head = true ∧ tail.all (termEq common) = true := by simpa using equal
        obtain ⟨headEqual, tailEqual⟩ := parts
        have same := (termEq_correct common head).mp headEqual
        subst head
        exact ⟨found, ih.mp ⟨tail, traversed, tailEqual⟩⟩
      · rintro ⟨found, every⟩
        obtain ⟨tail, traversed, tailEqual⟩ := ih.mpr every
        exact ⟨common :: tail, ⟨common, found, tail, traversed, rfl⟩,
          by simpa using And.intro ((termEq_correct common common).mpr rfl) tailEqual⟩

/-- The exact source traversal decides existence-sensitive class satisfaction. -/
theorem classHolds_exact [DecidableEq Symbol] (term : Term Symbol) (paths : List (List Nat)) :
    classHolds term paths = true ↔ Symbolic.ClassSatisfied term paths := by
  cases paths with
  | nil => simp [classHolds, traversePaths, allSame, Symbolic.ClassSatisfied]
  | cons first rest =>
      unfold classHolds
      simp only [traversePaths]
      cases head : term.atPath first with
      | none => simp [head, Symbolic.ClassSatisfied]
      | some common =>
          rw [show Symbolic.ClassSatisfied term (first :: rest) ↔
            ∀ path ∈ rest, term.atPath path = some common by
              simp [Symbolic.ClassSatisfied, head]]
          rw [← traversal_common term common rest]
          cases traversePaths term rest <;> simp [allSame]

/-- The source class traversal equals the existing symbolic class predicate. -/
theorem classHolds_eq_classTest [DecidableEq Symbol]
    (term : Term Symbol) (paths : List (List Nat)) :
    classHolds term paths = SymbolicDriver.classTest term paths := by
  apply Bool.eq_iff_iff.mpr
  simp only [classHolds_exact, SymbolicDriver.classTest, decide_eq_true_eq]

/-- Contradictory equalities reject the term; all other classes are checked. -/
def equalitiesHold [DecidableEq Symbol]
    (equalities : Option (List (List (List Nat)))) (term : Term Symbol) : Bool :=
  match equalities with
  | none => false
  | some classes => classes.all (classHolds term)

/-- The source equality worker has exactly the normalized-class meaning. -/
theorem equalitiesHold_eq [DecidableEq Symbol]
    (equalities : Option (List (List (List Nat)))) (term : Term Symbol) :
    equalitiesHold equalities term =
      ConstraintIndicators.equalityValue (SymbolicDriver.classTest term) equalities := by
  cases equalities with
  | none => rfl
  | some classes =>
      simp only [equalitiesHold, ConstraintIndicators.equalityValue]
      congr 1
      funext paths
      exact classHolds_eq_classTest term paths

/-- Positive source constraints require no external guard decision. -/
theorem positive_constraint_exact [DecidableEq Formula]
    (formulas : Formulas Formula) (solver : Entailment Formula)
    (constraint : Constraint Formula) (active : ActiveOption constraint.equalities)
    (positiveGuard : (positive constraint.guard).isSome = true)
    (term : Term (Label Formula)) :
    equalitiesHold (sourceEqualities constraint) term =
      acceptsConstraint formulas solver constraint term := by
  rw [equalitiesHold_eq]
  exact (sourceEqualities_exact formulas solver constraint active positiveGuard term).symm

/-- The public equality worker rejects an explicit Bottom guard before path checks. -/
noncomputable def constraintHolds [DecidableEq Symbol]
    (constraint : Constraint Formula) (term : Term Symbol) : Bool :=
  match constraint.guard with
  | .bottom => false
  | _ => equalitiesHold (sourceEqualities constraint) term

/-- The contradiction shortcut preserves the complete meaning of positive constraints. -/
theorem constraintHolds_exact [DecidableEq Formula]
    (formulas : Formulas Formula) (solver : Entailment Formula)
    (constraint : Constraint Formula) (active : ActiveOption constraint.equalities)
    (positiveGuard : (positive constraint.guard).isSome = true)
    (term : Term (Label Formula)) :
    constraintHolds constraint term = acceptsConstraint formulas solver constraint term := by
  unfold constraintHolds
  split
  next bottom => simp [bottom, positive] at positiveGuard
  next => exact positive_constraint_exact formulas solver constraint active positiveGuard term

/-- Keep the source row while replacing its constraint by the equality worker. -/
noncomputable def equalityRow [DecidableEq Formula]
    (row : SourceCyclicAutomaton.Row State Formula) : Edge State (Label Formula) :=
  ⟨row.symbol, row.children, constraintHolds row.constraint⟩

/-- A nonresidual row keeps exactly its complete constraint meaning. -/
theorem equalityRow_eq_guarded [DecidableEq Formula]
    (formulas : Formulas Formula) (solver : Entailment Formula)
    (row : SourceCyclicAutomaton.Row State Formula)
    (active : ActiveOption row.constraint.equalities)
    (positiveGuard : (positive row.constraint.guard).isSome = true) :
    equalityRow row = SourceCyclicAutomaton.guarded formulas solver row := by
  unfold equalityRow SourceCyclicAutomaton.guarded
  congr 1
  funext term
  exact constraintHolds_exact formulas solver row.constraint active positiveGuard term

/-- Every source equality-only class has the complete original graph language. -/
theorem source_classes_exact [DecidableEq Formula]
    (formulas : Formulas Formula) (solver : Entailment Formula)
    (rows : State → List (SourceCyclicAutomaton.Row State Formula))
    (active : ∀ state row, row ∈ rows state → ActiveOption row.constraint.equalities)
    (positiveGuard : ∀ state row, row ∈ rows state → (positive row.constraint.guard).isSome = true)
    (size : Nat) (state : State) (term : Term (Label Formula)) :
    term ∈ SourceSizedReference.classes (fun state => (rows state).map equalityRow) size state ↔
      Accepts (fun state => (rows state).map (SourceCyclicAutomaton.guarded formulas solver)) state term ∧
        RecursiveSize.nodeSize term = size := by
  have same : (fun state => (rows state).map equalityRow) =
      (fun state => (rows state).map (SourceCyclicAutomaton.guarded formulas solver)) := by
    funext state
    apply List.map_congr_left
    intro row member
    exact equalityRow_eq_guarded formulas solver row (active state row member) (positiveGuard state row member)
  rw [same]
  exact SourceSizedReference.mem_classes_iff _ size state term

end MicroCFTA.SourceSizedEqualities
