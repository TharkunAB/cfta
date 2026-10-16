import MicroCFTA.SourceCurrentAllocatedParentWorker

namespace MicroCFTA.CurrentParentWorkerChecks
open Language InternedConstructorTemplates SourceCurrentAllocatedParentWorker
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Allocated" => SourceEqualityConjoinAllocation.Constraint FullSyntax.Formula
local notation "EqValue" => SourceEqualityConstraintAllocation.Value
local notation "Fourth" => SourceCurrentEmptinessMemo.Memo
local notation "Memo" => SourceCurrentMemoMergeGraph.Memo Symbol Guard
local notation "Edge" => EdgeValue Symbol Guard
local notation "load" => SourceEqualityConstraintFieldLookup.load
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
  [DecidableEq (Value Symbol Guard)] {width : Nat}

-- Bottom rejects without a field receipt, child residency, or positive stage bound.
example (symbol : Symbol) (equalities : Option EqualityNormalize.Constraints) (inherited : EqValue)
    (children : List (Value Symbol Guard)) (before : Checked width) (fourth : Fourth) (memo : Memo) :
    let returned := edge 0 0 0 0 0 0 0 0 0 0 symbol ⟨equalities, .bottom⟩ inherited children before fourth memo
    returned = .done (SourceCurrentAllocatedMkEdge.reject symbol before).1
      (SourceCurrentAllocatedMkEdge.reject symbol before).2 fourth memo ∧
      returned.state.native.nodes = before.native.nodes ∧
      returned.state.native.edges = before.native.edges ∧
      returned.state.native.machine.domains = before.native.machine.domains ∧
      returned.state.operations = SourceEqualityMkEdgeAllocation.emptyField before.operations ∧
      returned.fourth = fourth ∧ returned.memo = memo := by
  dsimp only
  rw [edge_rejected 0 0 0 0 0 0 0 0 0 0 symbol ⟨equalities, .bottom⟩ inherited children before fourth memo
    (by simp [SourceEqualityMkEdgeAllocation.contradictory])]
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

-- Field errors retain their message and the initial full state before local work.
example (symbol : Symbol) (original : Guard) (inherited : EqValue) (children : List (Value Symbol Guard))
    (before : Checked width) (fourth : Fourth) (memo : Memo) (message : String)
    (live : SourceEqualityMkEdgeAllocation.contradictory original = false)
    (failed : load original before.operations.constraints = .error message) :
    edge 0 0 0 0 0 0 0 0 0 0 symbol original inherited children before fourth memo =
      .failed (.field message) before fourth memo :=
  edge_field_error 0 0 0 0 0 0 0 0 0 0 symbol original inherited children before fourth memo message live failed

-- A missing field remains distinct from a checked source error and successful rejection.
example (symbol : Symbol) (original : Guard) (inherited : EqValue) (children : List (Value Symbol Guard))
    (before : Checked width) (fourth : Fourth) (memo : Memo)
    (live : SourceEqualityMkEdgeAllocation.contradictory original = false)
    (missing : load original before.operations.constraints = .ok none) :
    edge 0 0 0 0 0 0 0 0 0 0 symbol original inherited children before fourth memo =
      .failed .missingField before fourth memo :=
  edge_missing_field 0 0 0 0 0 0 0 0 0 0 symbol original inherited children before fourth memo live missing

-- A failed class retains the complete raw shared state inside the parent diagnostic.
example (g s r e p h m c n budget : Nat) (symbol : Symbol) (original : Guard) (loaded : Allocated)
    (inherited : EqValue) (children : List (Value Symbol Guard)) (before : Checked width)
    (fourth savedFourth : Fourth) (memo : Memo)
    (fault : SourceCurrentAllocatedSharedEditWorker.Fault width)
    (shared : SourceCurrentAllocatedSharedTargetState.State width)
    (live : SourceEqualityMkEdgeAllocation.contradictory original = false)
    (found : load original before.operations.constraints = .ok (some loaded))
    (localFailed : SourceCurrentAllocatedLocalWorker.reduce g s r e p h m c n budget
      loaded inherited children before fourth memo =
        .failed (.classes (.failed fault shared)) shared.checked savedFourth shared.memo) :
    edge g s r e p h m c n budget symbol original inherited children before fourth memo =
      .failed (.localReduction (.classes (.failed fault shared))) shared.checked savedFourth shared.memo := by
  simp only [edge, live, Bool.false_eq_true, ite_false, found, reduceChildren, localFailed, Outcome.bind]

-- Constructor failure follows the local return and keeps its own later operations and heap.
example (g s r e p h m c n budget : Nat) (symbol : Symbol) (original : Guard) (loaded : Allocated)
    (inherited : EqValue) (children results : List (Value Symbol Guard)) (before middle after : Checked width)
    (fourth savedFourth : Fourth) (memo saved : Memo) (message : String)
    (live : SourceEqualityMkEdgeAllocation.contradictory original = false)
    (found : load original before.operations.constraints = .ok (some loaded))
    (localDone : SourceCurrentAllocatedLocalWorker.reduce g s r e p h m c n budget
      loaded inherited children before fourth memo = .done results middle savedFourth saved)
    (built : SourceCurrentAllocatedMkEdge.build symbol loaded results middle = (.error message, after)) :
    edge g s r e p h m c n budget symbol original inherited children before fourth memo =
      .failed (.constructor message) after savedFourth saved := by
  simp only [edge, live, Bool.false_eq_true, ite_false, found, reduceChildren, localDone, Outcome.bind, build, built]

-- A live success builds exactly the local returned children at the local returned checked state.
example (g s r e p h m c n budget : Nat) (symbol : Symbol) (original : Guard) (loaded : Allocated)
    (inherited : EqValue) (children results : List (Value Symbol Guard)) (before middle after : Checked width)
    (fourth savedFourth : Fourth) (memo saved : Memo) (result : Edge)
    (live : SourceEqualityMkEdgeAllocation.contradictory original = false)
    (found : load original before.operations.constraints = .ok (some loaded))
    (localDone : SourceCurrentAllocatedLocalWorker.reduce g s r e p h m c n budget
      loaded inherited children before fourth memo = .done results middle savedFourth saved)
    (built : SourceCurrentAllocatedMkEdge.build symbol loaded results middle = (.ok result, after)) :
    edge g s r e p h m c n budget symbol original inherited children before fourth memo =
      .done result after savedFourth saved := by
  simp only [edge, live, Bool.false_eq_true, ite_false, found, reduceChildren, localDone, Outcome.bind, build, built]

-- Physical rejection constructs its own Top field and one-empty-child sentinel without input children.
example (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : SourceCurrentAllocatedNativeInventoryState.Inventory) (symbol : Symbol)
    (before : Checked width) (fourth : Fourth) (memo : Memo)
    (ready : SourceCurrentConjunctionClassScan.Ready before)
    (admitted : SourceCurrentAllocatedNativeInventoryState.At formulas solver inventory before) :
    let result := (SourceCurrentAllocatedMkEdge.reject symbol before).1
    let after := (SourceCurrentAllocatedMkEdge.reject symbol before).2
    edge 0 0 0 0 0 0 0 0 0 0 symbol ⟨none, .top⟩ .contradiction [] before fourth memo =
        .done result after fourth memo ∧
      result.entry.key.symbol = symbol ∧
      result.entry.key.constraint = SourceEqualityConstraintConstructors.top ∧
      result.children = [.empty] ∧
      InternedEdgeResidency.EdgeResident after.native.machine.heap result ∧
      ∀ ambient term, ¬ InternedGuardedLanguage.edgeMeaning (SourceEqualityPCSGuard.holds formulas solver) ambient result term := by
  dsimp only
  have receipt := SourceCurrentAllocatedMkEdge.reject_correct formulas solver inventory symbol before ready admitted
  exact ⟨edge_rejected 0 0 0 0 0 0 0 0 0 0 symbol ⟨none, .top⟩ .contradiction [] before fourth memo rfl,
    receipt.symbol, receipt.guard, receipt.children, receipt.resident, fun ambient term => receipt.empty _ ambient term⟩

end MicroCFTA.CurrentParentWorkerChecks
