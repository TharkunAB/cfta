import MicroCFTA.SourcePruningEnumerationPrefixCheckpointModels
import MicroCFTA.SourcePruningEnumerationOrigins

/-!
# Original variable paths at the actual resource-bounded prefix

The old producer fixes the complete resource and model packet first.
Every retained parked or narrowed cache has the original counter.
The same assignment therefore retains exactly its original variable paths.
The original annotation policies remain separate from template policies.
-/
namespace MicroCFTA.SourcePruningEnumerationSelectedStep
open EnumerationState InternedConstructorTemplates
open SourceCurrentAllocatedNativeInventoryState (Inventory)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Metadata" => SourcePruningRecordTypes.Metadata
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
variable {Typing Key : Type} {width : Nat}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]

/-- The actual valid prefix keeps the allocation limit for every retained cache. -/
theorem PrefixValid.assignment_origins
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Constraint))
    (stop : Option (Metadata Typing → Nat → Bool))
    (order : Metadata Typing → List Nat → Option Nat) (metadata : Metadata Typing)
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (inventory : Inventory)
    (fuel uv : Nat) (caller : Caller width) (before : Cached) (memos : Memos)
    (observed : Result width Typing)
    (valid : PrefixValid holeKey fits admits graph templates checkEmpty edgesOf stop order metadata
      formulas solver inventory fuel uv caller before memos observed) :
    ∀ (whole : Language.Term Symbol) (assignment : Nat → Language.Term Symbol),
      match (generalizing := false) observed with
      | .parked _ (some after) _ | .narrowed _ _ _ _ _ (some after) _ _ =>
          SourcePruningEnumerationOrigins.AssignmentOrigins whole after.core.counter assignment ↔
            SourcePruningEnumerationOrigins.AssignmentOrigins whole before.core.counter assignment
      | _ => True := by
  intro whole assignment
  cases observed with
  | stopped _ _ => trivial
  | parked checked candidate raw =>
      cases candidate with
      | none => trivial
      | some after =>
          change SourcePruningEnumerationOrigins.AssignmentOrigins whole after.core.counter assignment ↔
            SourcePruningEnumerationOrigins.AssignmentOrigins whole before.core.counter assignment
          rw [valid.2.2.1]
  | narrowed checked prepared reached queries action candidate right ordinary =>
      cases candidate with
      | none => trivial
      | some after =>
          change SourcePruningEnumerationOrigins.AssignmentOrigins whole after.core.counter assignment ↔
            SourcePruningEnumerationOrigins.AssignmentOrigins whole before.core.counter assignment
          rw [valid.2.2.1]

end MicroCFTA.SourcePruningEnumerationSelectedStep

namespace MicroCFTA.SourcePruningEnumerationRecursive
open EnumerationState EnumerationCorrectness InternedConstructorTemplates
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedPartialInvariant (Post)
open SourceCurrentAllocatedNativeResourceForecast (Profile)
open SourceCurrentConstrainedCapGeneratedQueryResources (Fits)
open SourcePruningEnumerationSelectedStep (PrefixValid Resources runPrefix)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Metadata" => SourcePruningRecordTypes.Metadata
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Heap" => SourceEqualityAnnotationHeap.Heap
variable {Typing Key : Type} {width : Nat}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]

/-- Retain the complete prefix model packet and its same-assignment original paths. -/
theorem packet_prefix_complete_resources_origins
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Constraint))
    (stop : Option (Metadata Typing → Nat → Bool))
    (order : Metadata Typing → List Nat → Option Nat) (metadata : Metadata Typing)
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (inventory : Inventory)
    (caller : Caller width) (memos : Memos) (before : Cached)
    (packet : Packet formulas solver inventory caller memos metadata before)
    (profile : Profile) (property : Constraint → Prop)
    (bounded : Fits profile caller.checked) (known : Heap property caller.checked.native.machine.heap) :
    ∃ bound, ∀ extra selected,
      SourcePruningEnumerationRestart.decision stop order metadata before = some (.expand selected) →
      let observed := runPrefix holeKey fits admits graph templates stop order metadata
        (bound + extra) (bound + extra) (bound + extra) (bound + extra) (bound + extra) (bound + extra)
        selected caller before memos.query
      ((PrefixValid holeKey fits admits graph templates checkEmpty edgesOf stop order metadata
        formulas solver inventory (bound + extra) selected caller before memos observed ∧
      Resources profile property caller observed ∧
      match observed with
      | .parked _ (some after) _ => Packet formulas solver inventory caller memos metadata after
      | .narrowed _ _ reached queries _ (some after) _ _ =>
          ∃ final, Post formulas solver inventory caller reached final ∧ final.query = queries ∧
            Packet formulas solver inventory reached final metadata after
      | _ => True) ∧
        ∀ (ambient : InternedGuardedLanguage.Env Symbol)
          (residualMeaning : Constraint → Language.Term Symbol → Prop) (assignment : Nat → Language.Term Symbol),
          Satisfies (SourcePruningEnumerationNativeLanguage.handles
            (SourceEqualityPCSGuard.holds formulas solver) ambient caller.checked.native.machine.heap)
            residualMeaning assignment before.core →
          (∀ symbol annotation child, assignment selected = .node symbol [child] →
            InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver) ambient annotation child →
            admits (holeKey metadata.typing selected) annotation = true ∧
              fits (holeKey metadata.typing selected) symbol = true) →
          (∀ annotation first second third fourth,
            assignment selected = .node ("app", FullSyntax.Formula.top) [first, second, third, fourth] →
            InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver) ambient annotation first →
            admits (holeKey metadata.typing selected) annotation = true) →
          (∀ annotation first second,
            assignment selected = .node ("filter", FullSyntax.Formula.top) [first, second] →
            InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver) ambient annotation first →
            admits (holeKey metadata.typing selected) annotation = true) →
          match observed with
          | .parked _ (some after) _ =>
              Satisfies (SourcePruningEnumerationNativeLanguage.handles
                (SourceEqualityPCSGuard.holds formulas solver) ambient caller.checked.native.machine.heap)
                residualMeaning assignment after.core
          | .narrowed _ _ reached _ _ (some after) _ _ =>
              Satisfies (SourcePruningEnumerationNativeLanguage.handles
                (SourceEqualityPCSGuard.holds formulas solver) ambient reached.checked.native.machine.heap)
                residualMeaning assignment after.core
          | _ => False) ∧
      ∀ (whole : Language.Term Symbol) (assignment : Nat → Language.Term Symbol),
        match observed with
        | .parked _ (some after) _ | .narrowed _ _ _ _ _ (some after) _ _ =>
            SourcePruningEnumerationOrigins.AssignmentOrigins whole after.core.counter assignment ↔
              SourcePruningEnumerationOrigins.AssignmentOrigins whole before.core.counter assignment
        | _ => True := by
  obtain ⟨bound, complete⟩ := packet_prefix_complete_resources_models
    holeKey fits admits graph templates checkEmpty edgesOf stop order metadata
    formulas solver inventory caller memos before packet profile property bounded known
  refine ⟨bound, ?_⟩
  intro extra selected chosen
  have retained := complete extra selected chosen
  refine ⟨retained, ?_⟩
  exact SourcePruningEnumerationSelectedStep.PrefixValid.assignment_origins
    holeKey fits admits graph templates checkEmpty edgesOf stop order metadata
    formulas solver inventory (bound + extra) selected caller before memos
    (runPrefix holeKey fits admits graph templates stop order metadata
      (bound + extra) (bound + extra) (bound + extra) (bound + extra) (bound + extra) (bound + extra)
      selected caller before memos.query) retained.1.1

end MicroCFTA.SourcePruningEnumerationRecursive
