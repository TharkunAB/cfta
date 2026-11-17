import MicroCFTA.SourcePruningEnumerationSharedEagerReservation
import MicroCFTA.SourcePruningEnumerationJointCausalEventLedger
import MicroCFTA.SourcePruningEnumerationHeldJointCausalEventLedger
import MicroCFTA.SourcePruningEnumerationParkedPrefixHeldStep
import MicroCFTA.SourcePruningEnumerationPreparationEntryInvariants

namespace MicroCFTA.SourcePruningEnumerationParkedOuterHeldHistory
open SourcePruningEnumerationRealEagerCausalOutputHistory EnumerationDischargeHistory
open EnumerationState InternedConstructorTemplates
open SourcePruningEnumerationRecursive (Packet)
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentConstrainedCapGeneratedQueryResources (Fits)
open SourcePruningEnumerationSharedIncomingReservation (Seed)
open SourcePruningEnumerationSharedEagerReservation (eagerReserved)
open SourcePruningEnumerationSharedPreparedRecursive (Output emitted)
open SourcePruningEnumerationSharedPreparedRecursiveChildPolicy (resumeWithNarrow)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Metadata" => SourcePruningRecordTypes.Metadata
local notation "Core" => EnumerationState.State Symbol Constraint
variable {Typing Key : Type} {bits : Nat}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]
set_option autoImplicit false

attribute [local irreducible]
  SourcePruningEnumerationSharedEagerReservation.eagerReserved
  SourcePruningEnumerationSharedEagerReservation.eagerFinal
  SourcePruningEnumerationSharedPreparedRecursiveChildPolicy.resumeWithNarrow

/- Note [One held derivation and one joint event ledger]
The actual parked worker produces one immediate-continuation Held derivation.
The original Canonical and Packet facts qualify that literal prefix endpoint.
The core adapter follows that same Held derivation and retains its event ledger.
No separately eliminated qualified history supplies hidden invocation fields.
This proves operational entry protection, not historical semantic satisfaction.
-/

-- OPEN prospective target. No proof or declaration is installed.
theorem actual_parked_same_joint_ledger_outer_entries_held_history
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Constraint))
    (stop : Option (Metadata Typing → Nat → Bool))
    (order : Metadata Typing → List Nat → Option Nat)
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (inventory : Inventory)
    (caller : Caller (bits + 2)) (memos : EndpointMemoGateTrace.Memos) (before parked : Cached)
    (metadata updated : Metadata Typing) (seed : Seed) (ceiling : Nat)
    (packet : Packet formulas solver inventory caller memos metadata before)
    (canonical : EnumerationValidity.Canonical before.core)
    (bounded : Fits seed.2 caller.checked)
    (known : SourceEqualityAnnotationHeap.Heap (fun guard => guard ∈ seed.1) caller.checked.native.machine.heap)
    (selectionMembers : ∀ entry rows depth free, ∀ edge ∈ edgesOf (.node entry rows depth free), edge ∈ rows)
    (selectionLength : ∀ entry rows depth free, (edgesOf (.node entry rows depth free)).length ≤ rows.length)
    (initialMass : SourcePruningEnumerationPrefixAdmission.suspendedBound before.core ≤ ceiling)
    (workFuel depth uv : Nat) (reserved : eagerReserved bits (depth + 1) seed ceiling)
    (checked core : Core) (next : Option Next)
    (chosen : SourcePruningEnumerationRestart.decision stop order metadata before = some (.expand uv))
    (actual : SourcePruningEnumerationSelectedStep.runPrefix holeKey fits admits graph templates stop order
      metadata workFuel workFuel workFuel workFuel workFuel workFuel uv caller before memos.query =
        .parked checked (some parked) (some [.ok ((updated, next), core)]))
    (index : Nat) (output : Output (bits + 2) Typing)
    (observed : (emitted (resumeWithNarrow
      (SourcePruningEnumerationSharedEagerChildren.eagerChild
        checkEmpty workFuel workFuel workFuel workFuel workFuel edgesOf)
      (SourcePruningOuterNarrow.narrow holeKey fits admits)
      graph templates checkEmpty edgesOf stop order workFuel (depth + 1)
      metadata caller memos.query before (some (.expand uv))))[index]? = some output) :
    ∃ (handle : Nat) (bucket : List EnumerationState.Suspended) (value : Node),
      before.core.values[uv]? = some (.unenumerated (some handle) bucket) ∧
      SourcePruningEnumerationNodes.lookupNode caller.checked.native.machine.heap handle = some value ∧
      MergedOrdinaryHeight.recursiveBoundary value = true ∧
      ∃ events : List (SourcePruningEnumerationJointCausalEventLedger.Operation Typing (bits + 2)),
        SourcePruningEnumerationJointCausalEventLedger.JointOutputLedgerAt
          holeKey fits admits graph templates checkEmpty edgesOf stop order workFuel
          depth updated caller memos.query (EnumerationExpandableIndex.frame core parked) next index output events ∧
        ∀ event ∈ events,
          match event with
          | .parked _ _ _ entry _ _ _ _ _ _ =>
              EnumerationDischargeHistory.HeldFragmentHistory uv handle parked.core entry.core
          | .selected _ _ _ entry _ _ _ _ _ _ _ _ _ =>
              EnumerationDischargeHistory.HeldFragmentHistory uv handle parked.core entry.core
          | .prepare _ _ entry _ _ _ _ _ _ _ =>
              EnumerationDischargeHistory.HeldFragmentHistory uv handle parked.core entry.core
          | .opaque .. | .finalize .. | .recordTypes .. | .nested .. => True
 := by
  obtain ⟨handle, bucket, value, stored, decoded, boundary, history, heldHistory⟩ :=
    actual_parked_all_later_outer_entries_held_history
      holeKey fits admits graph templates checkEmpty edgesOf stop order formulas solver inventory
      caller memos before parked metadata updated seed ceiling packet bounded known
      selectionMembers selectionLength initialMass workFuel depth uv reserved checked core next chosen actual
      index output observed
  have prefixFacts := SourcePruningEnumerationPreparationEntryInvariants.runPrefix_entry_invariants
    holeKey fits admits graph templates stop order metadata
    workFuel workFuel workFuel workFuel workFuel workFuel uv caller before memos.query
    canonical packet.safe.1.total
  rw [actual] at prefixFacts
  have parkedCanonical : EnumerationValidity.Canonical parked.core :=
    (prefixFacts.2.2 parked rfl).2
  have parkedTotal : UnionFind.Total parked.core.representatives :=
    (prefixFacts.2.2 parked rfl).1
  obtain ⟨_metadataSame, _checkedSame, _coreSame, framed, _trueNext, _notStuck,
      _callbackPacket, _callbackFits, _callbackKnown⟩ :=
    SourcePruningEnumerationParkedPrefixHeldStep.actual_parked_callback_packet_at_original_budget
      holeKey fits admits graph templates stop order metadata updated formulas solver inventory caller memos
      before parked seed.2 (fun guard => guard ∈ seed.1) packet bounded known workFuel uv checked core next
      chosen actual
  have restartCanonical : EnumerationValidity.Canonical (EnumerationExpandableIndex.frame core parked).core := by
    rw [framed]
    exact parkedCanonical
  have restartTotal : UnionFind.Total (EnumerationExpandableIndex.frame core parked).core.representatives := by
    rw [framed]
    exact parkedTotal
  obtain ⟨events, ledger, protectedEntries⟩ :=
    SourcePruningEnumerationHeldJointCausalEventLedger.held_output_history_joint_event_ledger
      holeKey fits admits graph templates checkEmpty edgesOf stop order workFuel uv handle parked.core
      depth updated caller memos.query (EnumerationExpandableIndex.frame core parked) next
      index output history heldHistory restartCanonical restartTotal
  refine ⟨handle, bucket, value, stored, decoded, boundary, events, ledger, ?_⟩
  intro event member
  have atEvent := protectedEntries event member
  cases event <;> exact atEvent

end MicroCFTA.SourcePruningEnumerationParkedOuterHeldHistory

#check MicroCFTA.SourcePruningEnumerationParkedOuterHeldHistory.actual_parked_same_joint_ledger_outer_entries_held_history
#print axioms MicroCFTA.SourcePruningEnumerationParkedOuterHeldHistory.actual_parked_same_joint_ledger_outer_entries_held_history
