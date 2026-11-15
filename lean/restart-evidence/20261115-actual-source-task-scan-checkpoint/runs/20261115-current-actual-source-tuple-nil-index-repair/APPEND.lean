namespace MicroCFTA.SourcePruningEnumerationSharedEagerReservation
section ActualSourceTupleNilResourceInduction
open EnumerationState EnumerationCorrectness EnumerationSchedule EnumerationDependencies
open InternedConstructorTemplates InternedProbeProvenance
open SourcePruningEnumerationNodes SourcePruningEnumerationObservation
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourcePruningEnumerationRecursive (Packet)
open SourcePruningEnumerationSharedPreparedRecursive (finish)
open SourcePruningEnumerationSharedSelectedContinuations
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Metadata" => SourcePruningRecordTypes.Metadata
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
variable {bits : Nat}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]

attribute [local irreducible] nodePlan tuplePlan fallbackPlan identity_actual_frame_plan
  identity_actual_frame_reserved IdentityActualSourceRoot.limit IdentityActualSourceRoot.own

/-- The actual empty tuple uses its captured leaf or its genuine smaller parent task. -/
private theorem identity_actual_source_tuple_nil_resources
    (graph : Graph Symbol Constraint) (checkEmpty : Bool)
    (edgesOf : Node → List (EdgeValue Symbol Constraint)) (recursiveDepth workFuel : Nat)
    (metadata : Metadata Unit) (uv : Nat)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (workerIH : IdentityEagerEmittedCompleteAtDepth (bits := bits)
      graph checkEmpty edgesOf formulas solver recursiveDepth)
    (root : IdentityActualSourceRoot bits) (point : IdentityActualSourcePoint bits)
    (selectionMembers : ∀ entry rows depth free, ∀ selected ∈ edgesOf (.node entry rows depth free), selected ∈ rows)
    (selectionLength : ∀ entry rows depth free, (edgesOf (.node entry rows depth free)).length ≤ rows.length)
    (taskIH : ∀ smaller : IdentityActualSourceTask bits,
      smaller.work root.limit < IdentityActualSourceTask.work root.limit (.tuple point []) →
      IdentityActualSourceCorrectAt graph checkEmpty edgesOf recursiveDepth workFuel metadata uv formulas solver root smaller) :
    IdentityActualSourceCorrectAt graph checkEmpty edgesOf recursiveDepth workFuel metadata uv formulas solver root
      (.tuple point []) := by
  intro scopeOriginal scopeBefore allInputs ledger origin current
  cases point with
  | mk frame completed currentCaller currentBefore currentQueries height count bound mass seed =>
    cases ledger with
    | captured inventory capturedCaller memos capturedQueries capturedBefore rowOwn scs edge residual handle
        staged packet querySame ready stored incoming prepared =>
      let currentPoint : IdentityActualSourcePoint bits := {
        frame := .captured edge residual scopeOriginal capturedQueries
        completed := completed
        caller := currentCaller
        before := currentBefore
        queries := currentQueries
        height := height
        count := count
        bound := bound
        mass := mass
        seed := seed }
      have capturedLedger : IdentityActualFrameLedger formulas solver root metadata uv
          (.captured edge residual scopeOriginal capturedQueries) scopeOriginal scopeBefore
          (staged.map (fun input => (input.1, input.2.1))) :=
        .captured inventory scopeOriginal memos capturedQueries capturedBefore scopeBefore scs edge residual handle
          staged packet querySame ready stored incoming prepared
      exact identity_actual_source_captured_nil_resources
        graph checkEmpty edgesOf recursiveDepth workFuel metadata uv formulas solver workerIH root currentPoint
        edge residual scopeOriginal capturedQueries scopeOriginal scopeBefore
        (staged.map (fun input => (input.1, input.2.1))) capturedLedger current selectionMembers selectionLength
    | selected parent outerOriginal outerBefore outerInputs ancestors completedPrefix rest incoming bucket
        capturedCaller capturedQueries capturedBefore rowOwn edge residual parentHeight parentCount parentBound
        parentMass parentSeed inventory memos staged packet querySame previous member prepared snapshot =>
      let entry : IdentityActualSourcePoint bits := {
        frame := parent
        completed := completedPrefix
        caller := scopeOriginal
        before := capturedBefore
        queries := capturedQueries
        height := parentHeight
        count := parentCount
        bound := parentBound
        mass := parentMass
        seed := parentSeed }
      let currentPoint : IdentityActualSourcePoint bits := {
        frame := .selected parent completedPrefix rest edge residual scopeOriginal capturedQueries
          parentHeight parentCount parentBound
        completed := completed
        caller := currentCaller
        before := currentBefore
        queries := currentQueries
        height := height
        count := count
        bound := bound
        mass := mass
        seed := seed }
      exact identity_actual_source_selected_nil_resources
        graph checkEmpty edgesOf recursiveDepth workFuel metadata uv formulas solver root
        outerOriginal outerBefore outerInputs entry currentPoint incoming bucket rest edge residual scopeBefore staged
        ancestors snapshot prepared origin current taskIH

end ActualSourceTupleNilResourceInduction
end MicroCFTA.SourcePruningEnumerationSharedEagerReservation
