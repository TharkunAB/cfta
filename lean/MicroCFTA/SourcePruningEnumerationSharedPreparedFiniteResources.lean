import MicroCFTA.SourcePruningEnumerationSharedPreparedFiniteExpansionResources
import MicroCFTA.SourcePruningEnumerationSharedPreparedZeroOutcomeResources

/-!
# Resources for every finite prepared shared recursive depth

Actual depth induction supplies each smaller execution. Positive expansion
uses one preparation and the actual shared ordinary or opaque path.
No smaller-depth execution hypothesis remains in the public result.
This theorem does not establish adequate source depth, backward language
meaning, enumeration completeness or exact output order.
-/

namespace MicroCFTA.SourcePruningEnumerationSharedPreparedRecursive
open EnumerationState InternedConstructorTemplates
open SourcePruningEnumerationRecursive (Packet)
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentConstrainedCapGeneratedQueryResources (Fits)
open SourcePruningEnumerationSharedIncomingReservation (Seed)
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

/-- Actual depth induction discharges the smaller-depth resource hypothesis. -/
theorem finite_complete
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Constraint))
    (stop : Option (Metadata Typing → Nat → Bool)) (order : Metadata Typing → List Nat → Option Nat)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (recursiveFuel : Nat) :
    ResumeComplete (bits := bits) holeKey fits admits graph templates checkEmpty edgesOf stop order
      formulas solver recursiveFuel := by
  induction recursiveFuel with
  | zero =>
      exact zero_complete holeKey fits admits graph templates checkEmpty edgesOf stop order formulas solver
  | succ recursiveFuel ih =>
      intro inventory caller memos before metadata seed ceiling packet bounded known
        selectionMembers selectionLength initialMass reserved
      by_cases expanding : ∃ uv,
          SourcePruningEnumerationRestart.decision stop order metadata before = some (.expand uv)
      · obtain ⟨uv, selected⟩ := expanding
        obtain ⟨bound, outcome, running, resources⟩ := expansion_complete_resources
          holeKey fits admits graph templates checkEmpty edgesOf stop order formulas solver recursiveFuel ih
          inventory caller memos before metadata uv seed ceiling packet bounded known
          selectionMembers selectionLength initialMass reserved selected
        refine ⟨bound, outcome, ?_, resources⟩
        intro extra
        simpa only [selected] using running extra
      · obtain ⟨outcome, running, resources⟩ := resume_zero_outcome_resources
          holeKey fits admits graph templates checkEmpty edgesOf stop order formulas solver inventory caller
          memos before metadata (SourcePruningEnumerationRestart.decision stop order metadata before)
          seed packet bounded known
        have growth := SourcePruningEnumerationSharedPreparedReservation.final_ge
          (recursiveFuel + 1) seed ceiling
        refine ⟨0, outcome, ?_, resources.mono growth.1 growth.2⟩
        intro extra
        cases decision : SourcePruningEnumerationRestart.decision stop order metadata before with
        | none => simpa only [decision, resume] using running (0 + extra)
        | some next =>
            cases next with
            | done => simpa only [decision, resume] using running (0 + extra)
            | stuck => simpa only [decision, resume] using running (0 + extra)
            | expand uv => exact (expanding ⟨uv, decision⟩).elim

/-- Current inputs and one original reservation derive the stable actual finite-depth run. -/
theorem run_finite_complete_resources
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Constraint))
    (stop : Option (Metadata Typing → Nat → Bool)) (order : Metadata Typing → List Nat → Option Nat)
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (recursiveFuel : Nat) (inventory : Inventory)
    (caller : Caller (bits + 2)) (memos : Memos) (before : Cached) (metadata : Metadata Typing)
    (seed : Seed) (ceiling : Nat)
    (packet : Packet formulas solver inventory caller memos metadata before)
    (bounded : Fits seed.2 caller.checked)
    (known : Heap (fun guard => guard ∈ seed.1) caller.checked.native.machine.heap)
    (selectionMembers : ∀ entry rows depth free, ∀ edge ∈ edgesOf (.node entry rows depth free), edge ∈ rows)
    (selectionLength : ∀ entry rows depth free, (edgesOf (.node entry rows depth free)).length ≤ rows.length)
    (initialMass : SourcePruningEnumerationPrefixAdmission.suspendedBound before.core ≤ ceiling)
    (reserved : SourcePruningEnumerationSharedPreparedReservation.Reserved bits recursiveFuel seed ceiling) :
    ∃ bound outcome,
      (∀ extra, run holeKey fits admits graph templates checkEmpty edgesOf stop order (bound + extra) recursiveFuel
        metadata caller memos.query before = outcome) ∧
      OutcomeResources formulas solver caller
        (SourcePruningEnumerationSharedPreparedReservation.final recursiveFuel seed ceiling) outcome :=
  finite_complete holeKey fits admits graph templates checkEmpty edgesOf stop order formulas solver recursiveFuel
    inventory caller memos before metadata seed ceiling packet bounded known
    selectionMembers selectionLength initialMass reserved

end MicroCFTA.SourcePruningEnumerationSharedPreparedRecursive
