import MicroCFTA.SourcePruningEnumerationSharedPreparedSelectedDriver
import MicroCFTA.SourcePruningEnumerationSharedPreparedFiniteResources

/-!
# Finite prepared execution at the same actual root return

The root equation supplies the actual caller and encoded value. Its current
startup packet supplies the full memos and metadata. One current resource
reservation derives the stable prepared observation at that same entry.
This conditional entry law does not derive original-source capacity or
change the historical driver selector.
-/
namespace MicroCFTA.SourcePruningEnumerationSharedPreparedSelectedDriver
open EnumerationState InternedConstructorTemplates
open SourceSynthesisGeneralizeSyntax (Guard)
open SourceCurrentAllocatedPartialState (NodeRequest)
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentConstrainedCapGeneratedQueryResources (Fits)
open SourcePruningEnumerationSharedIncomingReservation (Seed)
open SourcePruningEnumerationRecursive (Packet)
open SourceSynthesisOriginalFiniteDriver (startup)
open SourcePruningEnumerationNodes (encodeNode)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Metadata" => SourcePruningRecordTypes.Metadata
local notation "Heap" => SourceEqualityAnnotationHeap.Heap
local notation "nodeCall" => SourceCurrentAllocatedSharedPartialWorker.nodeCall
local notation "suspendedBound" => SourcePruningEnumerationPrefixAdmission.suspendedBound

private theorem startup_mass (value : Node) (handle : Nat) :
    suspendedBound (startup value handle).core = 0 := rfl

variable {Typing Key : Type} {bits : Nat}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Node]

/-- One actual encoded root and its current reservation derive stable prepared execution. -/
theorem run_selected_complete_resources
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (graph : Graph Symbol Guard) (templates : List (Template.Pattern Symbol))
    (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Guard))
    (stop : Option (Metadata Typing → Nat → Bool)) (order : Metadata Typing → List Nat → Option Nat)
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (recursiveDepth : Nat) (inventory : Inventory)
    (fuel g s r e p h m c n budget : Nat) (request : NodeRequest) (before : Caller (bits + 2))
    (value : Node) (after : Caller (bits + 2)) (handle : Nat) (memos : Memos) (metadata : Metadata Typing)
    (seed : Seed) (ceiling : Nat)
    (actual : nodeCall fuel g s r e p h m c n budget request before = .done value after)
    (encoded : encodeNode value = some handle)
    (packet : Packet formulas solver inventory after memos metadata (startup value handle))
    (bounded : Fits seed.2 after.checked)
    (known : Heap (fun guard => guard ∈ seed.1) after.checked.native.machine.heap)
    (selectionMembers : ∀ entry rows depth free, ∀ edge ∈ edgesOf (.node entry rows depth free), edge ∈ rows)
    (selectionLength : ∀ entry rows depth free, (edgesOf (.node entry rows depth free)).length ≤ rows.length)
    (reserved : SourcePruningEnumerationSharedPreparedReservation.Reserved bits recursiveDepth seed ceiling) :
    ∃ bound outcome,
      (∀ extra, run_selected holeKey fits admits graph templates checkEmpty edgesOf stop order
          (bound + extra) recursiveDepth metadata fuel g s r e p h m c n budget request before memos.query =
        .started value handle after memos.query (startup value handle) outcome) ∧
      SourcePruningEnumerationSharedPreparedRecursive.OutcomeResources formulas solver after
        (SourcePruningEnumerationSharedPreparedReservation.final recursiveDepth seed ceiling) outcome := by
  have mass : suspendedBound (startup value handle).core ≤ ceiling := by
    rw [startup_mass]
    exact Nat.zero_le _
  obtain ⟨bound, outcome, running, resources⟩ :=
    SourcePruningEnumerationSharedPreparedRecursive.run_finite_complete_resources
      holeKey fits admits graph templates checkEmpty edgesOf stop order formulas solver recursiveDepth
      inventory after memos (startup value handle) metadata seed ceiling packet bounded known
      selectionMembers selectionLength mass reserved
  refine ⟨bound, outcome, ?_, resources⟩
  intro extra
  have selected := run_selected_of_done holeKey fits admits graph templates checkEmpty edgesOf stop order
    (bound + extra) recursiveDepth metadata fuel g s r e p h m c n budget request before memos.query
    value after handle actual encoded
  rw [running extra] at selected
  exact selected

end MicroCFTA.SourcePruningEnumerationSharedPreparedSelectedDriver
