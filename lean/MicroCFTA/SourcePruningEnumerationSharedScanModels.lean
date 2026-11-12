import MicroCFTA.SourcePruningEnumerationSharedPreparedFiniteResources
import MicroCFTA.SourcePruningEnumerationNativeLanguage

/-!
# One original assignment through actual finite scan prefixes

The existing finite sibling producer retains the full native resource packet.
Native growth preserves the same assignment for the fixed captured cache.
The prefix can stop before a later row. The append equation keeps that stop.
These results do not supply adequate source depth or prove a later row is reached.
-/
namespace MicroCFTA.SourcePruningEnumerationSharedPreparedFiniteSiblingResources
open Language EnumerationState EnumerationCorrectness EnumerationSchedule
open InternedConstructorTemplates InternedProbeProvenance
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedPartialInvariant (Post)
open SourceCurrentConstrainedCapGeneratedQueryResources (Fits)
open SourcePruningEnumerationSharedIncomingReservation (Seed)
open SourcePruningEnumerationSharedPreparedReservation (stage ScanReserved)
open SourcePruningEnumerationRecursive (Packet)
open SourcePruningEnumerationSharedPreparedRecursive (Output Failure continueWith resume endpoint)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Receipt" => SourcePruningEnumerationSharedSelectedContinuations.SelectedEdge.Result
local notation "Heap" => SourceEqualityAnnotationHeap.Heap
local notation "Result" => SourcePruningEnumerationSharedSelectedContinuations.NativeContinuations.Result
local notation "suspendedBound" => SourcePruningEnumerationPrefixAdmission.suspendedBound
variable {Typing Key : Type} {bits : Nat}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]

/-- One finite scan packet preserves the original assignment at its certified native endpoint. -/
theorem alternatives_finite_complete_resources_models
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Constraint))
    (stop : Option (SourcePruningRecordTypes.Metadata Typing → Nat → Bool))
    (order : SourcePruningRecordTypes.Metadata Typing → List Nat → Option Nat)
    (metadata : SourcePruningRecordTypes.Metadata Typing)
    (recursiveFuel : Nat)
    (seed : Seed) (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory)
    (caller : Caller (bits + 2)) (memos : Memos) (before : Cached) (uv handle : Nat) (scs : List Suspended)
    (parentEntry : Cache.Interned InternedBinderProtocol.NodeKey)
    (storedEdges selectedEdges : List (EdgeValue Symbol Constraint))
    (depth : Nat) (free : List InternedBinderProtocol.Reference)
    (packet : Packet formulas solver inventory caller memos metadata before)
    (ready : EnumerationDriver.Ready uv before.core)
    (stored : before.core.values[uv]? = some (.unenumerated (some handle) scs))
    (parentAvailable : Available caller.checked.native.machine.heap (.node parentEntry storedEdges depth free))
    (parentClosed : free = [])
    (selected : ∀ edge ∈ selectedEdges, edge ∈ storedEdges)
    (incoming : EnumerationReferences.IncomingAvoid uv before.core)
    (bounded : Fits seed.2 caller.checked)
    (known : Heap (fun guard => guard ∈ seed.1) caller.checked.native.machine.heap)
    (selectionMembers : ∀ entry rows depth free, ∀ edge ∈ edgesOf (.node entry rows depth free), edge ∈ rows)
    (selectionLength : ∀ entry rows depth free, (edgesOf (.node entry rows depth free)).length ≤ rows.length)
    (capturedMass inherited : Nat) (initialMass : suspendedBound before.core ≤ capturedMass)
    (inheritedLength : scs.length ≤ inherited)
    (reserved : ScanReserved bits recursiveFuel seed capturedMass inherited selectedEdges.length)
    (ambient : InternedGuardedLanguage.Env Symbol) (assignment : Nat → Term Symbol)
    (satisfied : Satisfies
      (SourcePruningEnumerationNativeLanguage.handles (SourceEqualityPCSGuard.holds formulas solver)
        ambient caller.checked.native.machine.heap)
      (fun guard candidate => SourceEqualityPCSGuard.holds formulas solver guard candidate = true)
      assignment before.core) :
    ∃ (bound : Nat) (processed : List (Receipt (bits + 2))) (outputs : List (Output (bits + 2) Typing))
      (afterCaller : Caller (bits + 2)) (next : Inventory) (final : Memos)
      (result : Result (Output (bits + 2) Typing) (Failure (bits + 2) Typing) (bits + 2)),
      (∀ extra, SourcePruningEnumerationSharedSelectedContinuations.NativeContinuations.run
        (continueWith (resume holeKey fits admits graph templates checkEmpty edgesOf stop order (bound + extra) recursiveFuel)
          graph templates stop order (bound + extra) metadata uv)
        checkEmpty (bound + extra) (bound + extra) (bound + extra) (bound + extra) (bound + extra)
        uv scs before selectedEdges caller memos.query = result) ∧
      Post formulas solver next caller afterCaller final ∧
      Packet formulas solver next afterCaller final metadata before ∧
      Fits (stage recursiveFuel seed capturedMass inherited selectedEdges.length).2 afterCaller.checked ∧
      Heap (fun guard => guard ∈ (stage recursiveFuel seed capturedMass inherited selectedEdges.length).1)
        afterCaller.checked.native.machine.heap ∧
      processed.length ≤ selectedEdges.length ∧
      (∀ index receipt, processed[index]? = some receipt →
        ReceiptAt recursiveFuel formulas solver caller before uv seed scs capturedMass inherited index receipt) ∧
      (∀ output ∈ outputs, ∃ index, index < selectedEdges.length ∧
        OutputAt recursiveFuel formulas solver caller seed capturedMass inherited index output) ∧
      (result = .complete processed outputs afterCaller final.query ∨
        ∃ current, result = .stopped processed outputs current ∧
          (endpoint current = none ∨ endpoint current = some (afterCaller, final.query)) ∧
          StoppedAt recursiveFuel formulas solver caller before uv seed scs capturedMass inherited processed.length outputs current) ∧
      Satisfies
        (SourcePruningEnumerationNativeLanguage.handles (SourceEqualityPCSGuard.holds formulas solver)
          ambient afterCaller.checked.native.machine.heap)
        (fun guard candidate => SourceEqualityPCSGuard.holds formulas solver guard candidate = true)
        assignment before.core := by
  obtain ⟨bound, processed, outputs, afterCaller, next, final, result,
    running, post, captured, afterFits, afterKnown, processedLength, receipts, outputPackets, shape⟩ :=
    alternatives_finite_complete_resources
      holeKey fits admits graph templates checkEmpty edgesOf stop order metadata recursiveFuel seed formulas solver
      (SourcePruningEnumerationSharedPreparedRecursive.finite_complete
        holeKey fits admits graph templates checkEmpty edgesOf stop order formulas solver recursiveFuel)
      inventory caller memos before uv handle scs parentEntry storedEdges selectedEdges depth free
      packet ready stored parentAvailable parentClosed selected incoming bounded known
      selectionMembers selectionLength capturedMass inherited initialMass inheritedLength reserved
  obtain ⟨_roots, _paths, _storage, realized, _counts, _flags⟩ := packet.valid
  have sameModel := (SourcePruningEnumerationNativeLanguage.satisfies_keeps
    (SourceEqualityPCSGuard.holds formulas solver) ambient caller.checked.native.machine.heap
    afterCaller.checked.native.machine.heap before.core
    (fun guard candidate => SourceEqualityPCSGuard.holds formulas solver guard candidate = true)
    assignment realized post.effects.keeps).mpr satisfied
  exact ⟨bound, processed, outputs, afterCaller, next, final, result,
    running, post, captured, afterFits, afterKnown, processedLength, receipts, outputPackets, shape, sameModel⟩

end MicroCFTA.SourcePruningEnumerationSharedPreparedFiniteSiblingResources

namespace MicroCFTA.SourcePruningEnumerationSharedSelectedContinuations.NativeContinuations
open EnumerationState InternedConstructorTemplates
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Fragment" => Fragments.Fragment Symbol
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Queries" => SourceEndpointMemo.Memos
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
universe u v
variable {width : Nat} {Output : Type u} {Reason : Type v}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq (Value Symbol Constraint)]

/-- A completed prefix supplies the exact suffix caller; a stopped prefix retains its stop. -/
theorem run_append
    (hook : Fragment → Caller width → Queries → Cached → HookResult Output Reason width)
    (checkEmpty : Bool) (r n p h k target : Nat) (scs : List Suspended) (before : Cached)
    (earlierRows suffix : List (EdgeValue Symbol Constraint)) (caller : Caller width) (queries : Queries) :
    run hook checkEmpty r n p h k target scs before (earlierRows ++ suffix) caller queries =
      match run hook checkEmpty r n p h k target scs before earlierRows caller queries with
      | .stopped processed outputs current => .stopped processed outputs current
      | .complete processed outputs reached saved =>
          match run hook checkEmpty r n p h k target scs before suffix reached saved with
          | .complete later more finalCaller finalQueries =>
              .complete (processed ++ later) (outputs ++ more) finalCaller finalQueries
          | .stopped later more current =>
              .stopped (processed ++ later) (outputs ++ more) current := by
  induction earlierRows generalizing caller queries with
  | nil =>
      simp only [List.nil_append, run]
      cases run hook checkEmpty r n p h k target scs before suffix caller queries <;> rfl
  | cons edge earlierRows ih =>
      rw [List.cons_append]
      cases head : CapturedEdge.run checkEmpty r n p h k target scs edge caller before queries with
      | none => simp only [run, head]
      | some receipt =>
          cases receipt with
          | complete fragment reached saved after =>
              cases continued : hook fragment reached saved after with
              | stopped outputs reason endpoint => simp only [run, head, continued]
              | complete outputs middleCaller middleQueries =>
                  simp only [run, head, continued]
                  rw [ih]
                  cases run hook checkEmpty r n p h k target scs before earlierRows middleCaller middleQueries with
                  | stopped processed more current => rfl
                  | complete processed more finalCaller finalQueries =>
                      dsimp only
                      cases run hook checkEmpty r n p h k target scs before suffix finalCaller finalQueries <;>
                        simp only [List.cons_append, List.append_assoc]
          | rejected reached saved after =>
              simp only [run, head, advance]
              rw [ih]
              cases run hook checkEmpty r n p h k target scs before earlierRows reached saved with
              | stopped processed more current => rfl
              | complete processed more finalCaller finalQueries =>
                  dsimp only
                  cases run hook checkEmpty r n p h k target scs before suffix finalCaller finalQueries <;> rfl
          | unhandled => simp only [run, head, advance]
          | finalizeStopped fragment reached saved after => simp only [run, head, advance]
          | stopped fragments observation candidate =>
              simp only [run, head]
              cases advanced : advance (.stopped fragments observation candidate) with
              | none => rfl
              | some pair =>
                  obtain ⟨middleCaller, middleQueries⟩ := pair
                  dsimp only
                  rw [ih]
                  cases run hook checkEmpty r n p h k target scs before earlierRows middleCaller middleQueries with
                  | stopped processed more current => rfl
                  | complete processed more finalCaller finalQueries =>
                      dsimp only
                      cases run hook checkEmpty r n p h k target scs before suffix finalCaller finalQueries <;> rfl

end MicroCFTA.SourcePruningEnumerationSharedSelectedContinuations.NativeContinuations
