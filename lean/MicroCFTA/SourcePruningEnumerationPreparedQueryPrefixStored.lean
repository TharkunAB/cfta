import MicroCFTA.SourcePruningEnumerationIncomingNodePrefixStored
import MicroCFTA.SourcePruningEnumerationPreparedReservation

namespace MicroCFTA.SourcePruningEnumerationPreparedReservation
open SourceCurrentAllocatedNativeResourceForecast (Le)
open SourcePruningEnumerationIncomingReservation (Seed)

/-- Every reserved incoming query's native forecast fits the original driver envelope. -/
theorem incoming_native_profile_le_final
    (depth : Nat) (seed : Seed) (ceiling sibling queryIndex : Nat)
    (siblingBound : sibling < rows seed)
    (queryBound : queryIndex < SourcePruningEnumerationRecursiveReservation.edgeCount
      (stage depth (preparedSeed seed) ceiling ceiling sibling) ceiling) :
    Le (SourceCurrentAllocatedNativeResourceForecast.step
      (SourcePruningEnumerationIncomingReservation.advance
        (stage depth (preparedSeed seed) ceiling ceiling sibling) queryIndex).2)
      (final (depth + 1) seed ceiling).2 := by
  let current := stage depth (preparedSeed seed) ceiling ceiling sibling
  have nativeCombined :
      Le (SourceCurrentAllocatedNativeResourceForecast.step
        (SourcePruningEnumerationIncomingReservation.advance current queryIndex).2)
        (SourcePruningEnumerationIncomingReservation.step
          (SourcePruningEnumerationIncomingReservation.advance current queryIndex)).2 :=
    SourceCurrentConjunctionAlphabetBounds.callerForecast_ge _ _ _
  have nextSeed : SourcePruningEnumerationIncomingReservation.advance current (queryIndex + 1) =
      SourcePruningEnumerationIncomingReservation.step
        (SourcePruningEnumerationIncomingReservation.advance current queryIndex) := by
    simpa only [SourcePruningEnumerationIncomingReservation.advance] using
      SourcePruningEnumerationIncomingReservation.advance_add current queryIndex 1
  have throughHead : Le
      (SourcePruningEnumerationIncomingReservation.step
        (SourcePruningEnumerationIncomingReservation.advance current queryIndex)).2
      (SourcePruningEnumerationRecursiveReservation.afterHead current ceiling).2 := by
    rw [← nextSeed]
    exact SourcePruningEnumerationIncomingReservation.advance_count_profile_mono current
      (Nat.succ_le_of_lt queryBound)
  have throughCallback := (afterHead_le_step depth current ceiling ceiling).1
  have toFinal := (stage_le_final depth seed ceiling (sibling + 1)
    (Nat.succ_le_of_lt siblingBound)).1
  rw [stage_succ_right] at toFinal
  exact nativeCombined.trans (throughHead.trans (throughCallback.trans toFinal))

end MicroCFTA.SourcePruningEnumerationPreparedReservation

namespace MicroCFTA.SourcePruningEnumerationIncomingNode
open EnumerationState InternedConstructorTemplates InternedProbeProvenance
open SourcePruningEnumerationObservation
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedPartialInvariant (Context)
open SourceCurrentConstrainedCapGeneratedQueryResources (Fits)
open SourcePruningEnumerationIncomingReservation (Seed)
open SourcePruningEnumerationPreparedReservation (stage preparedSeed rows final Reserved)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Core" => EnumerationState.State Symbol
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Queries" => SourceEndpointMemo.Memos
variable {EnumGuard : Type} {bits : Nat}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]

/-- An actual incoming native stop fits the original fixed-capacity stored-payload ceiling. -/
theorem observed_native_error_stored_final
    (depth : Nat) (seed : Seed) (ceiling sibling queryIndex : Nat)
    (siblingBound : sibling < rows seed)
    (queryBound : queryIndex < SourcePruningEnumerationRecursiveReservation.edgeCount
      (stage depth (preparedSeed seed) ceiling ceiling sibling) ceiling)
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (beforeCaller : Caller (bits + 2)) (before : Core EnumGuard)
    (checkEmpty : Bool) (r n p h uv : Nat) (incoming : Node) (incomingScs : List Suspended)
    (memos : Memos) (initial : Context formulas solver inventory beforeCaller memos)
    (realized : PendingRealized beforeCaller.checked.native.machine.heap before)
    (available : Available beforeCaller.checked.native.machine.heap incoming) (closed : incoming.free = [])
    (fits : Fits (SourcePruningEnumerationIncomingReservation.advance
      (stage depth (preparedSeed seed) ceiling ceiling sibling) queryIndex).2 beforeCaller.checked)
    (reserved : Reserved bits (depth + 1) seed ceiling)
    {fault : SourceEqualityNativeDemand.Outcome (bits + 2) Node}
    {afterCaller : Caller (bits + 2)} {savedQueries : Queries} {read : Core EnumGuard}
    (observed : run checkEmpty r n p h beforeCaller before uv incoming incomingScs memos.query =
      (.error (.inl fault), afterCaller, savedQueries, read)) :
    InternedValueMassHeap.Stored (final (depth + 1) seed ceiling).2.mass
      afterCaller.checked.native.machine.heap := by
  have room := (reserved sibling siblingBound).1 queryIndex queryBound
  have stored := observed_native_error_stored
    (SourcePruningEnumerationIncomingReservation.advance
      (stage depth (preparedSeed seed) ceiling ceiling sibling) queryIndex).2
    formulas solver inventory beforeCaller before checkEmpty r n p h uv incoming incomingScs memos
    initial realized available closed fits room observed
  exact stored.mono
    (SourcePruningEnumerationPreparedReservation.incoming_native_profile_le_final
      depth seed ceiling sibling queryIndex siblingBound queryBound).2.2.2

end MicroCFTA.SourcePruningEnumerationIncomingNode
