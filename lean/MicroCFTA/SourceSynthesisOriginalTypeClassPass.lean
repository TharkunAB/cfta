import MicroCFTA.SourceSynthesisOriginalTypeSharedState
import MicroCFTA.SourceSynthesisNativeTypeClassPass
import MicroCFTA.SourceSynthesisActualSelectedProgramFootprints

/-!
# Original Type routes through a selected class pass

The actual precheck and record scan derive every selected record's coherence
and source endpoint routes. The pass starts at the original cold checked
state with empty Merge and target tables. Its entry state is not identified
with the scan return or the state after Required processing.

These laws concern completed pass graphs. They do not prove pass completion,
the intervening scan and Required state transitions, failure-prefix safety,
all reached source roles, or a global resource bound.
-/
namespace MicroCFTA.SourceSynthesisOriginalTypeClassPass
open Cache InternedConstructorTemplates InternedProbeProvenance
open InternedNestedConstruction (EdgeSyntax)
open InternedFreshOrdinaryConstruction (build)
open InternedNestedProvenance (Values)
open MergedColdReaderClosedInputs (ClosedValues)
open SourceSynthesisTypeSyntax
open SourceSynthesisGeneralizeSyntax (Guard top)
open SourceSynthesisFirstOrderConstruction (Expression firstOrderRaw typesOf)
open SourceSynthesisNativeTypeTrace (Origin cold)
open SourceCurrentHereditaryTypePaths (ForestPath)
open SourceCurrentHereditaryTypeRouteConstructors (ForestRoutes)
open SourceRecursiveIntersectionKernel (Extension)
open SourceCurrentStoredMuRetainedAlignment (RowCall)
open SourceSynthesisInitialTypeFields (Program)
open SourceEqualityClassOrder (Record Coherent)
open SourceCurrentAllocatedPrecheck (Receipt)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Memo" => SourceCurrentMemoMergeGraph.Memo Symbol Guard
local notation "Fourth" => SourceCurrentEmptinessMemo.Memo
local notation "Allocated" => SourceEqualityConjoinAllocation.Constraint FullSyntax.Formula
local notation "EqValue" => SourceEqualityConstraintAllocation.Value
local notation "Ready" => SourceSynthesisNativeTypeSharedState.Ready
local notation "ordinarySymbols" => SourceSynthesisUniverseCallerBoundary.ordinarySymbols
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Node]
variable {width : Nat}
variable {formulas : SourceGuards.Formulas FullSyntax.Formula}
variable {solver : SourceGuards.Entailment FullSyntax.Formula}
variable {inventory : SourceCurrentAllocatedNativeInventoryState.Inventory}
variable {loaded : Allocated} {inherited own : EqValue} {guard : Guard}
variable {records kept : List Record} {g s p h n budget : Nat}
variable {fourth savedFourth : Fourth} {outcome : Option EqualityNormalize.Class}
variable {scanned : Checked width}

/-- Actual selection retains coherent records and their initial forest routes. -/
theorem selected_records (lib : Library) {initial : Checked width} {values : List Node}
    (receipt : Receipt formulas solver inventory guard loaded inherited initial own (.classes records))
    (actual : SourceCurrentAllocatedRecordScanWorker.scan g s p h n budget values records
      (SourceCurrentAllocatedPrecheck.state initial loaded inherited) fourth =
        .done (outcome, kept) scanned savedFourth)
    (endpoints : ∀ path ∈ EqualityNormalize.members
      ((SourceCompactGuards.sourceEqualities guard).getD []),
      ForestPath (Origin lib) (path.map Int.ofNat) values) :
    ∀ record ∈ kept, Coherent record ∧ ∀ path ∈ record.paths,
      ForestPath (Origin lib) (path.map Int.ofNat) values :=
  SourceSynthesisActualSelectedProgramFootprints.selected_regions receipt actual
    (fun path => ForestPath (Origin lib) (path.map Int.ofNat) values) endpoints

section Source
variable (lib : Library) (query : Query) (signed : Int) (whole : Expression)
variable (accepted : firstOrderRaw lib query signed = .ok whole)
variable (rootValue : Node) (heap : State Symbol Guard)
variable (built : build (ordinarySymbols whole) [] empty = .done rootValue heap)
variable {expressions : List (EdgeSyntax Symbol Guard)} {before after : State Symbol Guard}
variable {outputs : List (EdgeValue Symbol Guard)} {rowIndex : Nat} {symbol : Symbol}
variable (operations : SourceEqualityConstraintMemoAllocation.State)
variable (good : SourceCurrentAllocatedNativePhysicalCompletion.Good (cold width heap operations))
variable {results : List Node} {finish : Checked width} {saved : Memo}
include accepted built good

/-- Selected original application records supply all routes for a cold-entry pass. -/
theorem application (function argument : Expression)
    (functionRole : Program lib query function) (argumentRole : Program lib query argument)
    (call : RowCall expressions [] before outputs after heap rowIndex symbol
      SourceSynthesisOriginalGuardAlphabet.applicationGuard
      [ordinarySymbols (typesOf lib query), ordinarySymbols (arrowMarker top),
        ordinarySymbols function, ordinarySymbols argument])
    (receipt : Receipt formulas solver inventory call.output.entry.key.constraint loaded inherited
      (cold width heap operations) own (.classes records))
    (scan : SourceCurrentAllocatedRecordScanWorker.scan g s p h n budget call.output.children records
      (SourceCurrentAllocatedPrecheck.state (cold width heap operations) loaded inherited) fourth =
        .done (outcome, kept) scanned savedFourth)
    (actual : SourceCurrentAllocatedClassPass.Pass kept call.output.children
      (cold width heap operations) SourceCurrentMemoMergeGraph.empty results finish saved) :
    Ready lib (SourceCurrentAllocatedSharedTargetState.initial finish saved) ∧
      Extension (cold width heap operations).native.machine finish.native.machine ∧
      Values finish.native.machine.heap results ∧ ClosedValues results ∧
      ForestRoutes (Origin lib) call.output.children results := by
  obtain ⟨ready, available, closed, endpoints⟩ :=
    SourceSynthesisOriginalTypeSharedState.application lib query signed whole accepted rootValue heap built
      operations good function argument functionRole argumentRole call
  have selected := selected_records lib receipt scan endpoints
  exact SourceSynthesisNativeTypeClassPass.pass lib actual ready available closed
    (fun record member => (selected record member).1)
    (fun record member => (selected record member).2)

/-- Selected original filter records supply all routes for a cold-entry pass. -/
theorem filter (candidates : Expression) (candidateRole : Program lib query candidates)
    (call : RowCall expressions [] before outputs after heap rowIndex symbol
      SourceSynthesisOriginalGuardAlphabet.filterGuard
      [ordinarySymbols (typeNode top query.queryGoal), ordinarySymbols candidates])
    (receipt : Receipt formulas solver inventory call.output.entry.key.constraint loaded inherited
      (cold width heap operations) own (.classes records))
    (scan : SourceCurrentAllocatedRecordScanWorker.scan g s p h n budget call.output.children records
      (SourceCurrentAllocatedPrecheck.state (cold width heap operations) loaded inherited) fourth =
        .done (outcome, kept) scanned savedFourth)
    (actual : SourceCurrentAllocatedClassPass.Pass kept call.output.children
      (cold width heap operations) SourceCurrentMemoMergeGraph.empty results finish saved) :
    Ready lib (SourceCurrentAllocatedSharedTargetState.initial finish saved) ∧
      Extension (cold width heap operations).native.machine finish.native.machine ∧
      Values finish.native.machine.heap results ∧ ClosedValues results ∧
      ForestRoutes (Origin lib) call.output.children results := by
  obtain ⟨ready, available, closed, endpoints⟩ :=
    SourceSynthesisOriginalTypeSharedState.filter lib query signed whole accepted rootValue heap built
      operations good candidates candidateRole call
  have selected := selected_records lib receipt scan endpoints
  exact SourceSynthesisNativeTypeClassPass.pass lib actual ready available closed
    (fun record member => (selected record member).1)
    (fun record member => (selected record member).2)
end Source
end MicroCFTA.SourceSynthesisOriginalTypeClassPass
