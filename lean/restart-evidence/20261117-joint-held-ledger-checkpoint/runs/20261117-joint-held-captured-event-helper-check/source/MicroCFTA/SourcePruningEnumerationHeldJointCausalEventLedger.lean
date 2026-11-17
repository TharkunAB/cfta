import MicroCFTA.SourcePruningEnumerationSharedEagerReservation
import MicroCFTA.SourcePruningEnumerationJointCausalEventLedger
import MicroCFTA.SourcePruningEnumerationInvocationEventAuthenticity

namespace MicroCFTA.SourcePruningEnumerationHeldJointCausalEventLedger
open SourcePruningEnumerationRealEagerCausalOutputHistory
open SourcePruningEnumerationParkedOuterHeldHistory
open SourcePruningEnumerationJointCausalEventLedger
open SourcePruningEnumerationCausalHistoryInputInvariants
open EnumerationValidity EnumerationCorrectness EnumerationSchedule EnumerationSemantics
open EnumerationState InternedConstructorTemplates
open SourcePruningEnumerationSharedSelectedContinuations
open SourcePruningEnumerationSharedPreparedRecursive (Output Failure emitted continueWith)
open SourcePruningEnumerationSharedPreparedRecursiveChildPolicy (resumeWithNarrow CapturedCallbackInvocationAt)
open SourcePruningEnumerationSharedChildVisitors (visitCapturedWith)
open SourcePruningEnumerationSharedBranching (scan)
open SourcePruningEnumerationSharedScanOutputOrigins (outputs)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Edge" => EdgeValue Symbol Constraint
local notation "Fragment" => Fragments.Fragment Symbol
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Queries" => SourceEndpointMemo.Memos
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Metadata" => SourcePruningRecordTypes.Metadata
local notation "Core" => EnumerationState.State Symbol Constraint
variable {Typing Key : Type} {bits : Nat}
local notation "Fold" => NativeContinuations.Result (Output (bits + 2) Typing) (Failure (bits + 2) Typing) (bits + 2)
local notation "Prepared" => MergedSourceComparison.Result Symbol Constraint (Node × Option (EnumerateM Symbol Constraint Unit))
local notation "ActionRaw" => List (Except EnumerationState.Error (Unit × Core))
set_option autoImplicit false

variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]


/- See Note [One joint causal ledger] in SourcePruningEnumerationJointCausalEventLedger.
This helper uses one actual callback invocation for all nested event witnesses.
The public producer and authenticity proofs consume the same selected trace.
-/

private theorem captured_invocation_event_ledger
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (checkEmpty : Bool) (edgesOf : Node → List Edge)
    (stop : Option (Metadata Typing → Nat → Bool)) (order : Metadata Typing → List Nat → Option Nat)
    (workFuel recursiveDepth uv target : Nat) (metadata : Metadata Typing)
    (scs : List Suspended) (edge : Edge) (caller : Caller (bits + 2))
    (queries : Queries) (before : Cached) (index : Nat) (output : Output (bits + 2) Typing)
    (fragment : Fragments.Fragment Symbol) (reached : Caller (bits + 2)) (saved : Queries)
    (beforeFinalize finished : Cached) (updated : Metadata Typing) (callbackCore : Core)
    (earlier later : List (Output (bits + 2) Typing)) (localIndex : Nat)

    (invoked : CapturedCallbackInvocationAt holeKey fits admits graph templates checkEmpty edgesOf stop order
      workFuel recursiveDepth uv target metadata scs edge caller queries before index output fragment reached saved
      beforeFinalize finished updated callbackCore earlier later localIndex) :
    ∃ events, CapturedEventLedgerAt holeKey fits admits graph templates checkEmpty edgesOf stop order
      workFuel recursiveDepth uv target metadata scs edge caller queries before index output fragment reached saved
      beforeFinalize finished updated callbackCore localIndex events
 := by
  have receipt := invoked
  dsimp only [CapturedCallbackInvocationAt] at receipt
  obtain ⟨trace, _whole, _hit, _offset, finalized, recorded⟩ := receipt
  obtain ⟨events, ledger⟩ :=
    (SourcePruningEnumerationInvocationEventLedger.invocation_event_ledgers
      checkEmpty workFuel workFuel workFuel workFuel workFuel edgesOf).2.2
      .eager _ scs edge caller before queries index output
      (.complete fragment reached saved beforeFinalize) localIndex trace []
  have authentic :=
    (SourcePruningEnumerationInvocationEventLedger.invocation_ledger_events_authentic
      checkEmpty workFuel workFuel workFuel workFuel workFuel edgesOf).2.2
      .eager _ scs edge caller before queries index output
      (.complete fragment reached saved beforeFinalize) localIndex [] events ledger
  exact ⟨events, ledger, authentic, finalized, recorded⟩

end MicroCFTA.SourcePruningEnumerationHeldJointCausalEventLedger

#check @MicroCFTA.SourcePruningEnumerationHeldJointCausalEventLedger.captured_invocation_event_ledger
#print axioms MicroCFTA.SourcePruningEnumerationHeldJointCausalEventLedger.captured_invocation_event_ledger
