import MicroCFTA.SourceFlatPruningRecursiveBase
import MicroCFTA.SourcePruningEnumerationFiniteContract
import MicroCFTA.SourcePruningEnumerationFiniteResources

/-!
# A flat contract for finite recursive capacity

The contract retains the original input gates and stable output packet.
Each adequate work bound also produces a related actual flat result.
The zero theorem proves this contract without executing a selected step.
-/
namespace MicroCFTA.SourceFlatPruningRecursive
open EnumerationState InternedConstructorTemplates
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentConstrainedCapGeneratedQueryResources (Fits)
open SourcePruningEnumerationIncomingReservation (Seed)
open SourcePruningEnumerationRecursive (Packet OutcomeResources)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Metadata" => SourcePruningRecordTypes.Metadata
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Heap" => SourceEqualityAnnotationHeap.Heap
variable {Typing Key : Type} {bits : Nat}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]

/-- Retain the original finite result and relate each adequate actual flat execution to it. -/
def Complete
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Constraint))
    (stop : Option (Metadata Typing → Nat → Bool)) (order : Metadata Typing → List Nat → Option Nat)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (recursiveFuel : Nat) : Prop :=
  ∀ (inventory : Inventory) (caller : Caller (bits + 2)) (memos : Memos) (before : Cached)
    (metadata : Metadata Typing) (seed : Seed) (ceiling : Nat),
    Packet formulas solver inventory caller memos metadata before →
    Fits seed.2 caller.checked →
    Heap (fun guard => guard ∈ seed.1) caller.checked.native.machine.heap →
    (∀ entry rows depth free, ∀ edge ∈ edgesOf (.node entry rows depth free), edge ∈ rows) →
    (∀ entry rows depth free, (edgesOf (.node entry rows depth free)).length ≤ rows.length) →
    SourcePruningEnumerationPrefixAdmission.suspendedBound before.core ≤ ceiling →
    SourcePruningEnumerationFiniteReservation.Reserved bits recursiveFuel seed ceiling →
    ∃ bound outcome,
      (∀ extra, SourcePruningEnumerationRecursive.run holeKey fits admits graph templates checkEmpty edgesOf stop order (bound + extra) recursiveFuel
        metadata caller memos.query before = outcome) ∧
      OutcomeResources formulas solver caller
        (SourcePruningEnumerationFiniteReservation.final recursiveFuel seed ceiling) outcome ∧
      ∀ (flat : EnumerationFlatCached.Cached Symbol Constraint),
        EnumerationFlatCached.Related flat before →
        ∀ extra, ∃ flatOutcome,
          run holeKey fits admits graph templates checkEmpty edgesOf stop order (bound + extra) recursiveFuel
            metadata caller memos.query flat = flatOutcome ∧
          ResultRelated flatOutcome outcome

/-- The original zero-depth producer and the exact decision relation establish the flat zero case. -/
theorem zero_complete
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Constraint))
    (stop : Option (Metadata Typing → Nat → Bool)) (order : Metadata Typing → List Nat → Option Nat)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula) :
    Complete (bits := bits) holeKey fits admits graph templates checkEmpty edgesOf stop order
      formulas solver 0 := by
  intro inventory caller memos before metadata seed ceiling packet bounded known
    selectionMembers selectionLength initialMass reserved
  obtain ⟨bound, outcome, running, resources⟩ :=
    SourcePruningEnumerationRecursive.finite_complete (bits := bits)
      holeKey fits admits graph templates checkEmpty edgesOf stop order formulas solver 0
      inventory caller memos before metadata seed ceiling packet bounded known
      selectionMembers selectionLength initialMass reserved
  refine ⟨bound, outcome, running, resources, ?_⟩
  intro flat related extra
  have relatedResult := run_zero_related holeKey fits admits graph templates checkEmpty edgesOf stop order
    (bound + extra) metadata caller memos.query flat before related
  rw [running extra] at relatedResult
  exact ⟨_, rfl, relatedResult⟩

end MicroCFTA.SourceFlatPruningRecursive
