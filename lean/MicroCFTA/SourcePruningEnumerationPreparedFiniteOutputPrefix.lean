import MicroCFTA.SourcePruningEnumerationPreparedRecursiveOutputPrefix
import MicroCFTA.SourcePruningEnumerationPreparedFiniteResources

/-!
# Ordered finite outputs at independent stable work bounds

The two actual depth observations can have different sufficient work bounds.
A common larger work bound compares their complete output lists.
Original resources construct both observations and their resource packets.
-/
namespace MicroCFTA.SourcePruningEnumerationPreparedRecursive
open EnumerationState InternedConstructorTemplates
open SourcePruningEnumerationRecursive (Packet Output)
open SourcePruningEnumerationHookInvocation (hookOutputs)
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentConstrainedCapGeneratedQueryResources (Fits)
open SourcePruningEnumerationIncomingReservation (Seed)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Queries" => SourceEndpointMemo.Memos
local notation "Metadata" => SourcePruningRecordTypes.Metadata
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Heap" => SourceEqualityAnnotationHeap.Heap
variable {Typing Key : Type} {width bits : Nat}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]

/-- Independent stable actual work bounds retain the ordered output prefix at greater depth. -/
theorem run_stable_outputs_prefix
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Constraint))
    (stop : Option (Metadata Typing → Nat → Bool)) (order : Metadata Typing → List Nat → Option Nat)
    (small large : Nat) (increase : small ≤ large)
    (metadata : Metadata Typing) (caller : Caller width) (queries : Queries) (before : Cached)
    (smallBound largeBound : Nat)
    (first last : SourcePruningEnumerationNativeContinuations.HookResult
      (Output width Typing) (Failure width Typing) width)
    (smallStable : ∀ extra, run holeKey fits admits graph templates checkEmpty edgesOf stop order
      (smallBound + extra) small metadata caller queries before = first)
    (largeStable : ∀ extra, run holeKey fits admits graph templates checkEmpty edgesOf stop order
      (largeBound + extra) large metadata caller queries before = last) :
    List.IsPrefix (hookOutputs first) (hookOutputs last) := by
  have retained := run_outputs_moreDepth holeKey fits admits graph templates checkEmpty edgesOf stop order
    (smallBound + largeBound) small large increase metadata caller queries before
  have largerRun := largeStable smallBound
  rw [Nat.add_comm largeBound smallBound] at largerRun
  rw [smallStable largeBound, largerRun] at retained
  exact retained

/-- Original packets and the two reservations derive actual finite results with ordered output inclusion. -/
theorem run_finite_resources_outputs_prefix
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Constraint))
    (stop : Option (Metadata Typing → Nat → Bool)) (order : Metadata Typing → List Nat → Option Nat)
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula)
    (small large : Nat) (increase : small ≤ large) (inventory : Inventory)
    (caller : Caller (bits + 2)) (memos : Memos) (before : Cached) (metadata : Metadata Typing)
    (seed : Seed) (ceiling : Nat)
    (packet : Packet formulas solver inventory caller memos metadata before)
    (bounded : Fits seed.2 caller.checked)
    (known : Heap (fun guard => guard ∈ seed.1) caller.checked.native.machine.heap)
    (selectionMembers : ∀ entry rows depth free, ∀ edge ∈ edgesOf (.node entry rows depth free), edge ∈ rows)
    (selectionLength : ∀ entry rows depth free, (edgesOf (.node entry rows depth free)).length ≤ rows.length)
    (initialMass : SourcePruningEnumerationPrefixAdmission.suspendedBound before.core ≤ ceiling)
    (smallReserved : SourcePruningEnumerationPreparedReservation.Reserved bits small seed ceiling)
    (largeReserved : SourcePruningEnumerationPreparedReservation.Reserved bits large seed ceiling) :
    ∃ smallBound first largeBound last,
      (∀ extra, run holeKey fits admits graph templates checkEmpty edgesOf stop order (smallBound + extra) small
        metadata caller memos.query before = first) ∧
      OutcomeResources formulas solver caller
        (SourcePruningEnumerationPreparedReservation.final small seed ceiling) first ∧
      (∀ extra, run holeKey fits admits graph templates checkEmpty edgesOf stop order (largeBound + extra) large
        metadata caller memos.query before = last) ∧
      OutcomeResources formulas solver caller
        (SourcePruningEnumerationPreparedReservation.final large seed ceiling) last ∧
      List.IsPrefix (hookOutputs first) (hookOutputs last) := by
  obtain ⟨smallBound, first, smallStable, smallResources⟩ :=
    run_finite_complete_resources holeKey fits admits graph templates checkEmpty edgesOf stop order
      formulas solver small inventory caller memos before metadata seed ceiling packet bounded known
      selectionMembers selectionLength initialMass smallReserved
  obtain ⟨largeBound, last, largeStable, largeResources⟩ :=
    run_finite_complete_resources holeKey fits admits graph templates checkEmpty edgesOf stop order
      formulas solver large inventory caller memos before metadata seed ceiling packet bounded known
      selectionMembers selectionLength initialMass largeReserved
  exact ⟨smallBound, first, largeBound, last, smallStable, smallResources, largeStable, largeResources,
    run_stable_outputs_prefix holeKey fits admits graph templates checkEmpty edgesOf stop order
      small large increase metadata caller memos.query before smallBound largeBound first last smallStable largeStable⟩

end MicroCFTA.SourcePruningEnumerationPreparedRecursive
