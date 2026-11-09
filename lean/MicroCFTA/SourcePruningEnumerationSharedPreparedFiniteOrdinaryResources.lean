import MicroCFTA.SourcePruningEnumerationSharedPreparedFiniteSiblingResources
import MicroCFTA.SourcePruningEnumerationSharedPreparedOutcomeResources

/-!
# Current ordinary resources for prepared shared recursion

The current prepared parent supplies its selected rows. Each callback runs
before the next sibling at its actual returned native endpoint. Every
output fits the whole current sibling schedule. This proof does not enter,
prepare, or decode the original stored target again.
-/
namespace MicroCFTA.SourcePruningEnumerationSharedPreparedRecursive
open EnumerationState EnumerationSchedule InternedConstructorTemplates InternedProbeProvenance
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentConstrainedCapGeneratedQueryResources (Fits)
open SourcePruningEnumerationSharedIncomingReservation (Seed)
open SourcePruningEnumerationSharedPreparedReservation (stage)
open SourcePruningEnumerationRecursive (Packet)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Heap" => SourceEqualityAnnotationHeap.Heap
local notation "Rows" => SourcePruningEnumerationSharedSelectedContinuations.NativeContinuations.Result
local notation "mass" => SourcePruningEnumerationPrefixAdmission.suspendedBound
variable {Typing Key : Type} {bits : Nat}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]

/-- The current prepared rows derive the literal finite fold and its whole scheduled resources. -/
theorem ordinary_finite_complete_resources
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Constraint))
    (stop : Option (SourcePruningRecordTypes.Metadata Typing → Nat → Bool))
    (order : SourcePruningRecordTypes.Metadata Typing → List Nat → Option Nat)
    (metadata : SourcePruningRecordTypes.Metadata Typing) (recursiveFuel : Nat) (seed : Seed)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (recursive : ResumeComplete (bits := bits) holeKey fits admits graph templates checkEmpty edgesOf stop order
      formulas solver recursiveFuel)
    (inventory : Inventory) (caller : Caller (bits + 2)) (memos : Memos) (before : Cached)
    (uv handle : Nat) (scs : List Suspended)
    (parentEntry : Cache.Interned InternedBinderProtocol.NodeKey)
    (parentEdges : List (EdgeValue Symbol Constraint)) (depth : Nat) (free : List InternedBinderProtocol.Reference)
    (packet : Packet formulas solver inventory caller memos metadata before)
    (ready : EnumerationDriver.Ready uv before.core)
    (stored : before.core.values[uv]? = some (.unenumerated (some handle) scs))
    (parentAvailable : Available caller.checked.native.machine.heap (.node parentEntry parentEdges depth free))
    (parentClosed : free = [])
    (incoming : EnumerationReferences.IncomingAvoid uv before.core)
    (bounded : Fits seed.2 caller.checked)
    (known : Heap (fun guard => guard ∈ seed.1) caller.checked.native.machine.heap)
    (selectionMembers : ∀ entry rows depth free, ∀ edge ∈ edgesOf (.node entry rows depth free), edge ∈ rows)
    (selectionLength : ∀ entry rows depth free, (edgesOf (.node entry rows depth free)).length ≤ rows.length)
    (ceiling : Nat) (initialMass : mass before.core ≤ ceiling) (inheritedLength : scs.length ≤ ceiling)
    (reserved : SourcePruningEnumerationSharedPreparedReservation.ScanReserved bits recursiveFuel seed ceiling ceiling
      (edgesOf (.node parentEntry parentEdges depth free)).length) :
    ∃ (bound : Nat) (result : Rows (Output (bits + 2) Typing) (Failure (bits + 2) Typing) (bits + 2)),
      (∀ extra, SourcePruningEnumerationSharedSelectedContinuations.NativeContinuations.run
        (continueWith (resume holeKey fits admits graph templates checkEmpty edgesOf stop order (bound + extra) recursiveFuel)
          graph templates stop order (bound + extra) metadata uv)
        checkEmpty (bound + extra) (bound + extra) (bound + extra) (bound + extra) (bound + extra)
        uv scs before (edgesOf (.node parentEntry parentEdges depth free)) caller memos.query = result) ∧
      OutcomeResources formulas solver caller
        (stage recursiveFuel seed ceiling ceiling (edgesOf (.node parentEntry parentEdges depth free)).length)
        (finish uv result) := by
  obtain ⟨bound, processed, outputs, afterCaller, next, final, result, running, post,
    _captured, afterFits, afterKnown, _processedLength, _receipts, outputPackets, shape⟩ :=
    SourcePruningEnumerationSharedPreparedFiniteSiblingResources.alternatives_finite_complete_resources
      holeKey fits admits graph templates checkEmpty edgesOf stop order metadata recursiveFuel seed formulas solver recursive
      inventory caller memos before uv handle scs parentEntry parentEdges
      (edgesOf (.node parentEntry parentEdges depth free)) depth free packet ready stored
      parentAvailable parentClosed (selectionMembers parentEntry parentEdges depth free) incoming bounded known
      selectionMembers selectionLength ceiling ceiling initialMass inheritedLength reserved
  have outputResources : ∀ output ∈ outputs, OutputResources formulas solver caller
      (stage recursiveFuel seed ceiling ceiling (edgesOf (.node parentEntry parentEdges depth free)).length) output := by
    intro output member
    obtain ⟨index, inside, certificate⟩ := outputPackets output member
    have own : OutputResources formulas solver caller (stage recursiveFuel seed ceiling ceiling (index + 1)) output :=
      certificate
    have growth := SourcePruningEnumerationSharedPreparedReservation.count_mono recursiveFuel seed ceiling ceiling
      (by omega : index + 1 ≤ (edgesOf (.node parentEntry parentEdges depth free)).length)
    exact own.mono growth.1 growth.2
  have actualShape : result = .complete processed outputs afterCaller final.query ∨
      ∃ current, result = .stopped processed outputs current ∧
        (endpoint current = none ∨ endpoint current = some (afterCaller, final.query)) := by
    rcases shape with completed | ⟨current, stopped, reached, _certificate⟩
    · exact .inl completed
    · exact .inr ⟨current, stopped, reached⟩
  exact ⟨bound, result, running, finish_resources_general formulas solver caller uv
    (stage recursiveFuel seed ceiling ceiling (edgesOf (.node parentEntry parentEdges depth free)).length)
    processed outputs afterCaller next final result post afterFits afterKnown outputResources actualShape⟩

end MicroCFTA.SourcePruningEnumerationSharedPreparedRecursive
