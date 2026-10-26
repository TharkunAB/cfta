import MicroCFTA.SourcePruningEnumerationSiblingResources
import MicroCFTA.SourcePruningEnumerationSubtreeEffects

/-!
# Resources after the actual sibling scan finishes

The original scan producer runs once. Every receipt, output and stop
certificate remains available. Each output keeps its own endpoint and full
memos. Resource padding uses only the original sibling schedule.
-/
namespace MicroCFTA.SourcePruningEnumerationNativeSiblingResources
open EnumerationState EnumerationSchedule InternedConstructorTemplates InternedProbeProvenance
open SourcePruningEnumerationNodes
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedPartialInvariant (Post)
open SourceCurrentConstrainedCapGeneratedQueryResources (Fits)
open SourcePruningEnumerationIncomingReservation (Seed)
open SourcePruningEnumerationSiblingReservation (stage Reserved)
open SourcePruningEnumerationRecursive (Packet Output Failure continueWith resume endpoint)
attribute [local irreducible] SourcePruningEnumerationRecursiveReservation.afterHook
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Receipt" => SourcePruningEnumerationSelectedEdge.Result
local notation "Heap" => SourceEqualityAnnotationHeap.Heap
local notation "Result" => SourcePruningEnumerationNativeContinuations.Result
local notation "HookResult" => SourcePruningEnumerationNativeContinuations.HookResult
local notation "afterHead" => SourcePruningEnumerationRecursiveReservation.afterHead
local notation "afterHook" => SourcePruningEnumerationRecursiveReservation.afterHook
local notation "advance" => SourcePruningEnumerationNativeBranches.advance
local notation "suspendedBound" => SourcePruningEnumerationPrefixAdmission.suspendedBound
variable {Typing Key : Type} {bits : Nat}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]

/-- Retain the complete sibling result and resources for its exact finished outcome. -/
theorem alternatives_one_finish_resources
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Constraint))
    (stop : Option (SourcePruningRecordTypes.Metadata Typing → Nat → Bool))
    (order : SourcePruningRecordTypes.Metadata Typing → List Nat → Option Nat)
    (metadata : SourcePruningRecordTypes.Metadata Typing)
    (seed : Seed) (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (inventory : Inventory)
    (caller : Caller (bits + 2)) (memos : Memos) (before : Cached) (uv handle : Nat) (scs : List Suspended)
    (parentEntry : Cache.Interned InternedBinderProtocol.NodeKey)
    (storedEdges selectedEdges : List (EdgeValue Symbol Constraint))
    (depth : Nat) (free : List InternedBinderProtocol.Reference)
    (packet : Packet formulas solver inventory caller memos metadata before)
    (ready : EnumerationDriver.Ready uv before.core)
    (stored : before.core.values[uv]? = some (.unenumerated (some handle) scs))
    (decoded : lookupNode caller.checked.native.machine.heap handle = some (.node parentEntry storedEdges depth free))
    (selected : ∀ edge ∈ selectedEdges, edge ∈ storedEdges)
    (incoming : EnumerationReferences.IncomingAvoid uv before.core)
    (bounded : Fits seed.2 caller.checked)
    (known : Heap (fun guard => guard ∈ seed.1) caller.checked.native.machine.heap)
    (selectionMembers : ∀ entry rows depth free, ∀ edge ∈ edgesOf (.node entry rows depth free), edge ∈ rows)
    (selectionLength : ∀ entry rows depth free, (edgesOf (.node entry rows depth free)).length ≤ rows.length)
    (capturedMass inherited : Nat) (initialMass : suspendedBound before.core ≤ capturedMass)
    (inheritedLength : scs.length ≤ inherited)
    (reserved : Reserved bits seed capturedMass inherited selectedEdges.length) :
    ∃ (bound : Nat) (processed : List (Receipt (bits + 2))) (outputs : List (Output (bits + 2) Typing))
      (afterCaller : Caller (bits + 2)) (next : Inventory) (final : Memos)
      (result : Result (Output (bits + 2) Typing) (Failure (bits + 2) Typing) (bits + 2)),
      (∀ extra, SourcePruningEnumerationNativeContinuations.run
        (continueWith (resume holeKey fits admits graph templates checkEmpty edgesOf stop order (bound + extra) 1)
          graph templates stop order (bound + extra) metadata uv)
        checkEmpty (bound + extra) (bound + extra) (bound + extra) (bound + extra) (bound + extra)
        uv scs before selectedEdges caller memos.query = result) ∧
      Post formulas solver next caller afterCaller final ∧
      Packet formulas solver next afterCaller final metadata before ∧
      Fits (stage seed capturedMass inherited selectedEdges.length).2 afterCaller.checked ∧
      Heap (fun guard => guard ∈ (stage seed capturedMass inherited selectedEdges.length).1)
        afterCaller.checked.native.machine.heap ∧
      processed.length ≤ selectedEdges.length ∧
      (∀ index receipt, processed[index]? = some receipt →
        ReceiptAt formulas solver caller before uv seed scs capturedMass inherited index receipt) ∧
      (∀ output ∈ outputs, ∃ index, index < selectedEdges.length ∧
        OutputAt formulas solver caller seed capturedMass inherited index output) ∧
      (result = .complete processed outputs afterCaller final.query ∨
        ∃ current, result = .stopped processed outputs current ∧
          (endpoint current = none ∨ endpoint current = some (afterCaller, final.query)) ∧
          StoppedAt formulas solver caller before uv seed scs capturedMass inherited processed.length outputs current) ∧
      SourcePruningEnumerationRecursive.OutcomeResources formulas solver caller
        (stage seed capturedMass inherited selectedEdges.length)
        (SourcePruningEnumerationRecursive.finish uv result) := by
  obtain ⟨bound, processed, outputs, afterCaller, next, final, result,
    observed, post, captured, afterFits, afterKnown, processedLength, receipts, outputCertificates, shape⟩ :=
    alternatives_one_complete_resources holeKey fits admits graph templates checkEmpty edgesOf stop order metadata
      seed formulas solver inventory caller memos before uv handle scs parentEntry storedEdges selectedEdges depth free
      packet ready stored decoded selected incoming bounded known selectionMembers selectionLength
      capturedMass inherited initialMass inheritedLength reserved
  have outputResources : ∀ output ∈ outputs,
      SourcePruningEnumerationRecursive.OutputResources formulas solver caller
        (stage seed capturedMass inherited selectedEdges.length) output := by
    intro output member
    obtain ⟨index, inside, certificate⟩ := outputCertificates output member
    have own : SourcePruningEnumerationRecursive.OutputResources formulas solver caller
        (stage seed capturedMass inherited (index + 1)) output := certificate
    have growth := SourcePruningEnumerationSiblingReservation.count_mono seed capturedMass inherited
      (by omega : index + 1 ≤ selectedEdges.length)
    exact own.mono growth.1 growth.2
  have actualShape : result = .complete processed outputs afterCaller final.query ∨
      ∃ current, result = .stopped processed outputs current ∧
        (endpoint current = none ∨ endpoint current = some (afterCaller, final.query)) := by
    rcases shape with completed | ⟨current, stopped, observedEndpoint, _certificate⟩
    · exact .inl completed
    · exact .inr ⟨current, stopped, observedEndpoint⟩
  have finished := SourcePruningEnumerationRecursive.finish_resources_general
    formulas solver caller uv (stage seed capturedMass inherited selectedEdges.length)
    processed outputs afterCaller next final result post afterFits afterKnown outputResources actualShape
  exact ⟨bound, processed, outputs, afterCaller, next, final, result,
    observed, post, captured, afterFits, afterKnown, processedLength, receipts, outputCertificates, shape, finished⟩

end MicroCFTA.SourcePruningEnumerationNativeSiblingResources
