import MicroCFTA.SourcePruningEnumerationPreparedOpaqueIsolation
import MicroCFTA.SourcePruningEnumerationPreparedHistoryBoundaryIsolation

/-!
# A selected opaque marker survives its own callback and history

The actual nonterminal opaque completion creates an isolated fresh slot.
The actual false callback and remaining history retain that slot.
Their output therefore cannot satisfy full structural discharge.
-/
namespace MicroCFTA.SourcePruningEnumerationSelectedOpaqueDispatch
open EnumerationState EnumerationCorrectness EnumerationDischargeHistory InternedConstructorTemplates
open SourcePruningEnumerationRecursive (Packet Output)
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourcePruningEnumerationIncomingReservation (Seed)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Metadata" => SourcePruningRecordTypes.Metadata
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Core" => EnumerationState.State Symbol Constraint
local notation "Fragment" => Fragments.Fragment Symbol
variable {Typing Key : Type} {bits : Nat}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]

/-- The actual nonterminal opaque receipt cannot reach a discharged output through its recorded tail. -/
theorem completed_opaque_output_not_discharged
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (inventory : Inventory)
    (caller : Caller (bits + 2)) (memos : Memos) (metadata : Metadata Typing)
    (before : Cached) (checkEmpty : Bool) (workFuel target : Nat) (scs : List Suspended) (value : Node)
    (packet : Packet formulas solver inventory caller memos metadata before)
    (inside : target < before.core.counter)
    (available : InternedProbeProvenance.Available caller.checked.native.machine.heap value)
    (closed : value.free = [])
    (nonterminal : scs.any (fun sc => EqualityTrie.isTerminal sc.trie) = false)
    (fragment : Fragment) (reached : Caller (bits + 2)) (after : Cached)
    (returnedInventory : Inventory) (returnedMemos : Memos)
    (observed : run checkEmpty workFuel workFuel workFuel workFuel workFuel target scs value
      caller before memos.query = some (.complete fragment reached returnedMemos.query after))
    (completed : Packet formulas solver returnedInventory reached returnedMemos metadata after)
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (edgesOf : Node → List (EdgeValue Symbol Constraint))
    (stop : Option (Metadata Typing → Nat → Bool)) (order : Metadata Typing → List Nat → Option Nat)
    (recursiveFuel : Nat) (recorded : Metadata Typing) (callbackCore : Core)
    (tailSeed : Seed) (tailCeiling : Nat) (output : Output (bits + 2) Typing)
    (callback : ExceptT.run (SourcePruningRecordTypes.recordTypes graph templates workFuel metadata target
      (.inl fragment) after.core) = [.ok ((false, recorded), callbackCore)])
    (tail : SourcePruningEnumerationPreparedRecursive.ResourceHistory
      holeKey fits admits graph templates checkEmpty edgesOf stop order formulas solver workFuel recursiveFuel
      returnedInventory reached returnedMemos recorded (EnumerationExpandableIndex.frame callbackCore after)
      tailSeed tailCeiling (SourcePruningEnumerationRestart.decision stop order recorded
        (EnumerationExpandableIndex.frame callbackCore after)) output) :
    ¬SourcePruningEnumerationRendering.Discharged output.cache.core := by
  have boundary := complete_boundary_of_nonterminal checkEmpty workFuel workFuel workFuel workFuel workFuel
    target scs value caller reached before after memos.query returnedMemos.query fragment closed nonterminal observed
  obtain ⟨_caller, _queries, _fragment, handle, _encoded, decoded, isolated⟩ :=
    complete_opaque_isolated formulas solver inventory caller memos metadata before checkEmpty workFuel workFuel
      workFuel workFuel workFuel target scs value packet inside available closed boundary nonterminal fragment
      reached returnedMemos.query after observed
  have callbackSuccess : Success (SourcePruningRecordTypes.recordTypes graph templates workFuel metadata target
      (.inl fragment)) after.core (false, recorded) callbackCore := by
    rw [Success, callback]
    exact List.mem_singleton_self _
  have callbackIsolated := isolated.through_recordTypes graph templates workFuel metadata target (.inl fragment)
    after.core callbackCore (false, recorded) completed.safe.1.total callbackSuccess
  exact tail.not_discharged before.core.counter handle value rfl callbackIsolated decoded boundary

end MicroCFTA.SourcePruningEnumerationSelectedOpaqueDispatch
