import MicroCFTA.SourceSynthesisConstructorProgramRoles
import MicroCFTA.SourceSynthesisLocalReduceProgramRoles
import MicroCFTA.SourceCurrentAllocatedPartialInvariant
import MicroCFTA.SourceCurrentAllocatedPrecheck

/-!
# Strict Program rows through actual Parent execution

The original caller derives the loaded field and precheck receipt.
Actual local returns derive the reduced layout and Program child roles.
The checked constructor keeps its full source guard and layout together,
or returns Top with the single Empty child. Raw rejection uses that sentinel.
These laws require a successful Parent return. They do not prove completion,
failure-prefix roles, all-reached roles, Type progress, or a driver bound.
-/
namespace MicroCFTA.SourceSynthesisParentProgramRoles
open InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open SourceSynthesisGeneralizeSyntax (Guard top eqGuard)
open SourceSynthesisProgramBuildRolesGeneric (ProgramValue ProgramEdge)
open SourceCurrentAllocatedPartialInvariant (Context)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "Edge" => EdgeValue Symbol Guard
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Fourth" => SourceCurrentEmptinessMemo.Memo
local notation "Memo" => SourceCurrentMemoMergeGraph.Memo Symbol Guard
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Allocated" => SourceEqualityConjoinAllocation.Constraint FullSyntax.Formula
local notation "EqValue" => SourceEqualityConstraintAllocation.Value
local notation "EqReady" => SourceEqualityConstraintAllocation.Ready
local notation "FieldAvailable" => SourceCurrentConjunctionEquality.FieldAvailable
variable {width : Nat} {literal : String → Symbol}

private theorem parent_bind_done {A B : Type}
    (first : SourceCurrentAllocatedParentWorker.Outcome A width)
    (next : A → Checked width → Fourth → Memo → SourceCurrentAllocatedParentWorker.Outcome B width)
    {output : B} {after : Checked width} {fourth : Fourth} {saved : Memo}
    (actual : first.bind next = .done output after fourth saved) :
    ∃ value middle current memo, first = .done value middle current memo ∧
      next value middle current memo = .done output after fourth saved := by
  cases first with
  | done value middle current memo => exact ⟨value, middle, current, memo, rfl, actual⟩
  | failed => cases actual

private theorem cons_of_length {values : List Node} {count : Nat}
    (length : values.length = count + 1) :
    ∃ first rest, values = first :: rest ∧ rest.length = count := by
  cases values with
  | nil => simp only [List.length_nil] at length; omega
  | cons first rest => exact ⟨first, rest, rfl, by simp only [List.length_cons] at length; omega⟩

variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Node]

private theorem local_done {g s r e p h m c n budget loaded inherited children fourth memo values saved current} {before after : Checked width}
    (actual : SourceCurrentAllocatedParentWorker.reduceChildren g s r e p h m c n budget
      loaded inherited children before fourth memo = .done values after saved current) :
    SourceCurrentAllocatedLocalWorker.reduce g s r e p h m c n budget loaded inherited children
      before fourth memo = .done values after saved current := by
  cases observed : SourceCurrentAllocatedLocalWorker.reduce g s r e p h m c n budget loaded inherited
      children before fourth memo with
  | failed => simp only [SourceCurrentAllocatedParentWorker.reduceChildren, observed] at actual; cases actual
  | done output checked next warm =>
      simp only [SourceCurrentAllocatedParentWorker.reduceChildren, observed] at actual
      cases actual
      rfl

omit [DecidableEq Symbol] [DecidableEq Node] in
private theorem build_done {symbol loaded children fourth memo result saved current} {before after : Checked width}
    (actual : SourceCurrentAllocatedParentWorker.build symbol loaded children before fourth memo =
      .done result after saved current) :
    SourceCurrentAllocatedMkEdge.build symbol loaded children before = (.ok result, after) := by
  cases observed : SourceCurrentAllocatedMkEdge.build symbol loaded children before with
  | mk output checked =>
      cases output with
      | error => simp only [SourceCurrentAllocatedParentWorker.build, observed] at actual; cases actual
      | ok value =>
          simp only [SourceCurrentAllocatedParentWorker.build, observed] at actual
          cases actual
          rfl

/-- An actual Parent return preserves the strict full Program row certificate. -/
theorem edge_roles
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula)
    {inventory : SourceCurrentAllocatedNativeInventoryState.Inventory}
    {g s r e p h m c n budget : Nat} {source result : Edge} {inherited : EqValue}
    {before : Caller width} {memos : Memos} {after : Checked width} {saved : Fourth} {current : Memo}
    (actual : SourceCurrentAllocatedParentWorker.edge g s r e p h m c n budget
      source.entry.key.symbol source.entry.key.constraint inherited source.children
      before.checked before.fourth before.merge = .done result after saved current)
    (initial : Context formulas solver inventory before memos) (role : ProgramEdge literal source)
    (live : SourceEqualityMkEdgeAllocation.contradictory source.entry.key.constraint = false →
      FieldAvailable before.checked.operations source.entry.key.constraint ∧
        EqReady before.checked.operations.constraints inherited ∧
        Values before.checked.native.machine.heap source.children) :
    ProgramEdge literal result := by
  have good := SourceCurrentNativeOperationHeap.Good.of_native
    (SourceCurrentNativeOperationInvariants.Good.of_checked initial.ready.good)
    initial.ready.semantic initial.ready.costs
  cases rejected : SourceEqualityMkEdgeAllocation.contradictory source.entry.key.constraint with
  | true =>
      simp only [SourceCurrentAllocatedParentWorker.edge, rejected, ite_true] at actual
      cases actual
      exact SourceSynthesisConstructorProgramRoles.reject_program literal _ before.checked good
  | false =>
      obtain ⟨field, inheritedReady, available⟩ := live rejected
      simp only [SourceCurrentAllocatedParentWorker.edge, rejected, Bool.false_eq_true, ite_false] at actual
      cases loadedAt : SourceEqualityConstraintFieldLookup.load source.entry.key.constraint
          before.checked.operations.constraints with
      | error => simp only [loadedAt] at actual; cases actual
      | ok loaded =>
          cases loaded with
          | none => simp only [loadedAt] at actual; cases actual
          | some loaded =>
              simp only [loadedAt] at actual
              obtain ⟨values, middle, completed, warm, first, last⟩ := parent_bind_done _ _ actual
              have reduced := local_done first
              obtain ⟨own, branch, receipt⟩ := SourceCurrentAllocatedPrecheck.loaded_complete
                formulas solver inventory before.checked initial.ready initial.admitted
                source.entry.key.constraint field.1 loaded loadedAt inherited inheritedReady
              obtain ⟨effect, _retained, known⟩ := SourceCurrentParentOperationInvariants.reduce
                reduced good initial.stored receipt.storedReady inheritedReady available
              have loadedReady := receipt.storedReady.grows effect.operations.constraint_growth
              have constructed := build_done last
              have count := SourceSynthesisLocalReduceProgramRoles.reduce_length reduced
              cases role with
              | annotated edge annotation guard children =>
                  have one : values.length = 1 := by rw [count, children]; rfl
                  obtain ⟨returnedAnnotation, shape⟩ := List.length_eq_one_iff.mp one
                  rw [shape] at constructed known
                  exact SourceSynthesisConstructorProgramRoles.build_annotated constructed effect.good loadedReady known
                    (receipt.readback.trans guard)
              | application edge types marker function argument symbol guard children functionRole argumentRole =>
                  have four : values.length = 4 := by rw [count, children]; rfl
                  obtain ⟨newTypes, rest, rfl, three⟩ := cons_of_length (count := 3) four
                  obtain ⟨newMarker, rest, rfl, two⟩ := cons_of_length (count := 2) three
                  obtain ⟨newFunction, rest, rfl, one⟩ := cons_of_length (count := 1) two
                  obtain ⟨newArgument, rest, rfl, zero⟩ := cons_of_length (count := 0) one
                  have empty : rest = [] := List.length_eq_zero_iff.mp zero
                  subst rest
                  have occurrence : SourceSynthesisFirstOrderConstruction.application .empty .empty .empty =
                      .node [.mk "app" source.entry.key.constraint
                        [.empty, SourceSynthesisTypeSyntax.arrowMarker top, .empty, .empty]] := by
                    rw [guard]
                    rfl
                  have newFunctionRole := SourceSynthesisLocalReduceProgramRoles.application_reduce_roles
                    .empty .empty .empty "app" _ occurrence receipt reduced good initial.stored available
                    2 (Or.inl rfl) (by rw [children]; rfl) rfl functionRole
                  have newArgumentRole := SourceSynthesisLocalReduceProgramRoles.application_reduce_roles
                    .empty .empty .empty "app" _ occurrence receipt reduced good initial.stored available
                    3 (Or.inr rfl) (by rw [children]; rfl) rfl argumentRole
                  rw [symbol] at constructed
                  exact SourceSynthesisConstructorProgramRoles.build_application constructed effect.good loadedReady known
                    (receipt.readback.trans guard) newFunctionRole newArgumentRole
              | filter edge goal candidates symbol guard children candidateRole =>
                  have two : values.length = 2 := by rw [count, children]; rfl
                  obtain ⟨newGoal, rest, rfl, one⟩ := cons_of_length (count := 1) two
                  obtain ⟨newCandidates, rest, rfl, zero⟩ := cons_of_length (count := 0) one
                  have empty : rest = [] := List.length_eq_zero_iff.mp zero
                  subst rest
                  have occurrence : SourceSynthesisFirstOrderConstruction.ofType .empty .empty =
                      .node [.mk "filter" source.entry.key.constraint [.empty, .empty]] := by
                    rw [guard]
                    rfl
                  have newCandidateRole := SourceSynthesisLocalReduceProgramRoles.filter_reduce_roles
                    .empty .empty "filter" _ occurrence receipt reduced good initial.stored available
                    (by rw [children]; rfl) rfl candidateRole
                  rw [symbol] at constructed
                  exact SourceSynthesisConstructorProgramRoles.build_filter constructed effect.good loadedReady known
                    (receipt.readback.trans guard) newCandidateRole

/-- A source application and its strict input child roles derive the returned Program row. -/
theorem application_roles
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula)
    {inventory : SourceCurrentAllocatedNativeInventoryState.Inventory}
    {g s r e p h m c n budget : Nat} {source result : Edge} {inherited : EqValue}
    {before : Caller width} {memos : Memos} {after : Checked width} {saved : Fourth} {current : Memo}
    (actual : SourceCurrentAllocatedParentWorker.edge g s r e p h m c n budget
      source.entry.key.symbol source.entry.key.constraint inherited source.children
      before.checked before.fourth before.merge = .done result after saved current)
    (initial : Context formulas solver inventory before memos)
    {types marker function argument : Node} (symbol : source.entry.key.symbol = literal "app")
    (guard : source.entry.key.constraint = eqGuard [[[1], [2, 0, 0]], [[3, 0], [2, 0, 1]], [[0], [2, 0, 2]]])
    (children : source.children = [types, marker, function, argument])
    (functionRole : ProgramValue literal function) (argumentRole : ProgramValue literal argument)
    (live : SourceEqualityMkEdgeAllocation.contradictory source.entry.key.constraint = false →
      FieldAvailable before.checked.operations source.entry.key.constraint ∧
        EqReady before.checked.operations.constraints inherited ∧
        Values before.checked.native.machine.heap source.children) :
    ProgramEdge literal result :=
  edge_roles formulas solver actual initial
    (.application source types marker function argument symbol guard children functionRole argumentRole) live

/-- A source filter and its candidate Program role derive the returned Program row. -/
theorem filter_roles
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula)
    {inventory : SourceCurrentAllocatedNativeInventoryState.Inventory}
    {g s r e p h m c n budget : Nat} {source result : Edge} {inherited : EqValue}
    {before : Caller width} {memos : Memos} {after : Checked width} {saved : Fourth} {current : Memo}
    (actual : SourceCurrentAllocatedParentWorker.edge g s r e p h m c n budget
      source.entry.key.symbol source.entry.key.constraint inherited source.children
      before.checked before.fourth before.merge = .done result after saved current)
    (initial : Context formulas solver inventory before memos)
    {goal candidates : Node} (symbol : source.entry.key.symbol = literal "filter")
    (guard : source.entry.key.constraint = eqGuard [[[0], [1, 0]]])
    (children : source.children = [goal, candidates]) (candidateRole : ProgramValue literal candidates)
    (live : SourceEqualityMkEdgeAllocation.contradictory source.entry.key.constraint = false →
      FieldAvailable before.checked.operations source.entry.key.constraint ∧
        EqReady before.checked.operations.constraints inherited ∧
        Values before.checked.native.machine.heap source.children) :
    ProgramEdge literal result :=
  edge_roles formulas solver actual initial (.filter source goal candidates symbol guard children candidateRole) live

/-- An annotated source row derives the returned Program row without a Type role premise. -/
theorem annotated_roles
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula)
    {inventory : SourceCurrentAllocatedNativeInventoryState.Inventory}
    {g s r e p h m c n budget : Nat} {source result : Edge} {inherited : EqValue}
    {before : Caller width} {memos : Memos} {after : Checked width} {saved : Fourth} {current : Memo}
    (actual : SourceCurrentAllocatedParentWorker.edge g s r e p h m c n budget
      source.entry.key.symbol source.entry.key.constraint inherited source.children
      before.checked before.fourth before.merge = .done result after saved current)
    (initial : Context formulas solver inventory before memos)
    {annotation : Node} (guard : source.entry.key.constraint = top) (children : source.children = [annotation])
    (live : SourceEqualityMkEdgeAllocation.contradictory source.entry.key.constraint = false →
      FieldAvailable before.checked.operations source.entry.key.constraint ∧
        EqReady before.checked.operations.constraints inherited ∧
        Values before.checked.native.machine.heap source.children) :
    ProgramEdge literal result :=
  edge_roles formulas solver actual initial (.annotated source annotation guard children) live

end MicroCFTA.SourceSynthesisParentProgramRoles
