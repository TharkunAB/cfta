import MicroCFTA.SourcePruningEnumerationOrigins
import MicroCFTA.SourcePruningAssignmentRefutation
import MicroCFTA.SourcePruningEnumerationPreparedCallbackModels

/-!
# Original subterm policies at actual fragment callbacks

ProgramAt does not inspect annotation children.
The original policy therefore covers every structural subtree.
Actual origins derive local template and encoding policies.
Bounded raw pending IDs retain refutation under assignment extension.
-/
namespace MicroCFTA.SourcePruningTemplates
open Language
local notation "Symbol" => SourcePruningTemplates.Symbol

/-- Original policies cover program positions in every structural subtree. -/
def OriginPolicies (templates : List (Template.Pattern Symbol)) (whole : Term Symbol) : Prop :=
  ∀ term, SourcePruningEnumerationOrigins.Origin whole term →
    Avoids templates term ∧ ∀ program, ProgramAt term program → ProgramEncoding program

/-- A subtree inherits the original policies at all of its structural positions. -/
theorem OriginPolicies.restrict (templates : List (Template.Pattern Symbol))
    (whole term : Term Symbol) (policies : OriginPolicies templates whole)
    (origin : SourcePruningEnumerationOrigins.Origin whole term) : OriginPolicies templates term := by
  intro child nested
  exact policies child (SourcePruningEnumerationOrigins.origin_trans whole term child origin nested)

/-- An allocated variable with an original path inherits the local source policies. -/
theorem OriginPolicies.assignment (templates : List (Template.Pattern Symbol))
    (whole : Term Symbol) (limit : Nat) (assignment : Nat → Term Symbol)
    (policies : OriginPolicies templates whole)
    (origins : SourcePruningEnumerationOrigins.AssignmentOrigins whole limit assignment)
    (uv : Nat) (inside : uv < limit) :
    Avoids templates (assignment uv) ∧
      ∀ program, ProgramAt (assignment uv) program → ProgramEncoding program :=
  policies (assignment uv) (origins uv inside)

end MicroCFTA.SourcePruningTemplates

namespace MicroCFTA.SourcePruningRecordTypes
open Language SourcePruningPartialMatch
local notation "Symbol" => SourcePruningTemplates.Symbol
attribute [local instance] FormulaExecutable.formulaDecidableEq
variable {Typing Guard : Type}

/-- Original bounded pending IDs retain refutation under an agreeing assignment. -/
theorem pending_refutes_extension (limit : Nat) (original extended : Nat → Term Symbol)
    (metadata : Metadata Typing)
    (bounded : ∀ group ∈ metadata.pending, PendingBound limit group)
    (agree : ∀ uv < limit, extended uv = original uv)
    (refuted : ∀ group ∈ metadata.pending, SourcePruningResume.Refutes original group) :
    ∀ group ∈ metadata.pending, SourcePruningResume.Refutes extended group := by
  intro group member
  exact (SourcePruningResume.refutes_assignment_congr limit original extended group
    (bounded group member) agree).mpr (refuted group member)

/-- Actual recording uses original subtree policies and bounded old pending refutation. -/
theorem recordTypes_inl_refutes_of_origin (graph : EnumerationState.Graph Symbol Guard)
    (language : EnumerationCorrectness.NodeLanguage Symbol) (meaning : Guard → Term Symbol → Prop)
    (original extended : Nat → Term Symbol) (templates : List (Template.Pattern Symbol))
    (whole : Term Symbol) (fuel uv limit : Nat) (metadata : Metadata Typing)
    (fragment : Fragments.Fragment Symbol) (before after : EnumerationState.State Symbol Guard)
    (result : Bool × Metadata Typing) (total : UnionFind.Total before.representatives)
    (satisfied : EnumerationCorrectness.Satisfies language meaning extended before)
    (filled : Fragments.fill extended fragment = extended uv)
    (policies : SourcePruningTemplates.OriginPolicies templates whole)
    (origin : SourcePruningEnumerationOrigins.Origin whole (extended uv))
    (bounded : ∀ group ∈ metadata.pending, PendingBound limit group)
    (agree : ∀ key < limit, extended key = original key)
    (refuted : ∀ group ∈ metadata.pending, SourcePruningResume.Refutes original group)
    (success : EnumerationCorrectness.Success
      (recordTypes graph templates fuel metadata uv (.inl fragment)) before result after) :
    result.1 = false ∧ ∀ group ∈ result.2.pending, SourcePruningResume.Refutes extended group := by
  have localPolicies := policies (extended uv) origin
  have avoids : SourcePruningTemplates.Avoids templates (Fragments.fill extended fragment) := by
    simpa only [filled] using localPolicies.1
  have encoded : ∀ program, SourcePruningTemplates.ProgramAt (Fragments.fill extended fragment) program →
      SourcePruningTemplates.ProgramEncoding program := by
    simpa only [filled] using localPolicies.2
  exact recordTypes_inl_refutes graph language meaning extended templates fuel uv metadata fragment
    before after result total satisfied filled
    (pending_refutes_extension limit original extended metadata bounded agree refuted) avoids encoded success

end MicroCFTA.SourcePruningRecordTypes

namespace MicroCFTA.SourcePruningEnumerationPreparedRecursive
open EnumerationState EnumerationCorrectness EnumerationDriver EnumerationCompressionFrame
open InternedConstructorTemplates
open SourcePruningEnumerationRecursive (Packet Output)
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedPartialInvariant (Post)
open SourceCurrentConstrainedCapGeneratedQueryResources (Fits)
open SourcePruningEnumerationIncomingReservation (Seed)
open SourcePruningRecordTypes
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Fragment" => Fragments.Fragment Symbol
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Queries" => SourceEndpointMemo.Memos
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Metadata" => SourcePruningRecordTypes.Metadata
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Core" => EnumerationState.State Symbol Constraint
local notation "Heap" => SourceEqualityAnnotationHeap.Heap
local notation "suspendedBound" => SourcePruningEnumerationPrefixAdmission.suspendedBound
variable {Typing Key : Type} {bits : Nat}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]
local notation "Result" => SourcePruningEnumerationNativeContinuations.HookResult
  (Output (bits + 2) Typing) (Failure (bits + 2) Typing) (bits + 2)

/-- Retain the whole callback model packet and derive its policies from an original subtree. -/
theorem callback_finite_complete_resources_origins
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (inventory : Inventory)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (metadata : Metadata Typing) (uv : Nat) (fragment : Fragment)
    (caller : Caller (bits + 2)) (memos : Memos) (before : Cached)
    (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Constraint))
    (stop : Option (Metadata Typing → Nat → Bool)) (order : Metadata Typing → List Nat → Option Nat)
    (recursiveFuel : Nat)
    (seed : Seed) (ceiling : Nat)
    (packet : Packet formulas solver inventory caller memos metadata before)
    (allocated : FragmentBound before.core.counter fragment)
    (bounded : Fits seed.2 caller.checked)
    (known : Heap (fun guard => guard ∈ seed.1) caller.checked.native.machine.heap)
    (selectionMembers : ∀ entry rows depth free, ∀ edge ∈ edgesOf (.node entry rows depth free), edge ∈ rows)
    (selectionLength : ∀ entry rows depth free, (edgesOf (.node entry rows depth free)).length ≤ rows.length)
    (mass : suspendedBound before.core ≤ ceiling)
    (reserved : SourcePruningEnumerationPreparedReservation.Reserved bits recursiveFuel seed ceiling) :
    ∃ (fuel : Nat) (result : Bool × Metadata Typing) (after : Core) (outcome : Result),
      ((Packet formulas solver inventory caller memos result.2 (EnumerationExpandableIndex.frame after before) ∧
      RenderStable before.core after ∧ Frame before.core after ∧
      result.2.types = updatedTypes metadata uv (.inl fragment) ∧
      result.2.openHoles = metadata.openHoles ∧ result.2.typing = metadata.typing ∧
      (∀ extra,
        Success (recordTypes graph templates (fuel + extra) metadata uv (.inl fragment)) before.core result after ∧
        ExceptT.run (recordTypes graph templates (fuel + extra) metadata uv (.inl fragment) before.core) =
          [.ok (result, after)] ∧
        ∀ (recur : Metadata Typing → Caller (bits + 2) → Queries → Cached → Option Next → Result) stop order,
          continueWith recur graph templates stop order (fuel + extra) metadata uv fragment caller memos.query before =
            if result.1 then .complete [] caller memos.query
            else recur result.2 caller memos.query (EnumerationExpandableIndex.frame after before)
              (SourcePruningEnumerationRestart.decision stop order result.2
                (EnumerationExpandableIndex.frame after before))) ∧
      (∀ extra, continueWith
        (resume holeKey fits admits graph templates checkEmpty edgesOf stop order (fuel + extra) recursiveFuel)
        graph templates stop order (fuel + extra) metadata uv fragment caller memos.query before = outcome) ∧
      OutcomeResources formulas solver caller
        (SourcePruningEnumerationPreparedReservation.final recursiveFuel seed ceiling) outcome) ∧
      (∀ (language : NodeLanguage Symbol)
        (meaning : Constraint → Language.Term Symbol → Prop) (assignment : Nat → Language.Term Symbol),
        Satisfies language meaning assignment (EnumerationExpandableIndex.frame after before).core ↔
          Satisfies language meaning assignment before.core) ∧
      ∀ (language : NodeLanguage Symbol)
        (meaning : Constraint → Language.Term Symbol → Prop) (assignment : Nat → Language.Term Symbol),
        Satisfies language meaning assignment before.core →
        Fragments.fill assignment fragment = assignment uv →
        (∀ group ∈ metadata.pending, @SourcePruningResume.Refutes Symbol
          (@instDecidableEqProd String FullSyntax.Formula inferInstance FormulaExecutable.formulaDecidableEq) assignment group) →
        SourcePruningTemplates.Avoids templates (Fragments.fill assignment fragment) →
        (∀ program, SourcePruningTemplates.ProgramAt (Fragments.fill assignment fragment) program →
          SourcePruningTemplates.ProgramEncoding program) →
        Satisfies language meaning assignment (EnumerationExpandableIndex.frame after before).core ∧
          result.1 = false ∧
          (∀ group ∈ result.2.pending, @SourcePruningResume.Refutes Symbol
          (@instDecidableEqProd String FullSyntax.Formula inferInstance FormulaExecutable.formulaDecidableEq) assignment group) ∧
          ∀ extra, resume holeKey fits admits graph templates checkEmpty edgesOf stop order
              (fuel + extra) recursiveFuel result.2 caller memos.query
              (EnumerationExpandableIndex.frame after before)
              (SourcePruningEnumerationRestart.decision stop order result.2
                (EnumerationExpandableIndex.frame after before)) = outcome) ∧
      (∀ (whole : Language.Term Symbol) (assignment : Nat → Language.Term Symbol),
        SourcePruningEnumerationOrigins.AssignmentOrigins whole after.counter assignment ↔
          SourcePruningEnumerationOrigins.AssignmentOrigins whole before.core.counter assignment) ∧
      ∀ (language : NodeLanguage Symbol)
        (meaning : Constraint → Language.Term Symbol → Prop) (assignment : Nat → Language.Term Symbol)
        (whole : Language.Term Symbol),
        Satisfies language meaning assignment before.core →
        Fragments.fill assignment fragment = assignment uv →
        (∀ group ∈ metadata.pending, @SourcePruningResume.Refutes Symbol
          (@instDecidableEqProd String FullSyntax.Formula inferInstance FormulaExecutable.formulaDecidableEq) assignment group) →
        SourcePruningTemplates.OriginPolicies templates whole →
        SourcePruningEnumerationOrigins.Origin whole (assignment uv) →
        Satisfies language meaning assignment (EnumerationExpandableIndex.frame after before).core ∧
          result.1 = false ∧
          (∀ group ∈ result.2.pending, @SourcePruningResume.Refutes Symbol
          (@instDecidableEqProd String FullSyntax.Formula inferInstance FormulaExecutable.formulaDecidableEq) assignment group) ∧
          ∀ extra, resume holeKey fits admits graph templates checkEmpty edgesOf stop order
              (fuel + extra) recursiveFuel result.2 caller memos.query
              (EnumerationExpandableIndex.frame after before)
              (SourcePruningEnumerationRestart.decision stop order result.2
                (EnumerationExpandableIndex.frame after before)) = outcome := by
  obtain ⟨fuel, result, after, outcome, retained⟩ := callback_finite_complete_resources_models
    holeKey fits admits formulas solver inventory graph templates metadata uv fragment caller memos before
    checkEmpty edgesOf stop order recursiveFuel seed ceiling packet allocated bounded known
    selectionMembers selectionLength mass reserved
  refine ⟨fuel, result, after, outcome, retained, ?_, ?_⟩
  · intro whole assignment
    rw [retained.1.2.2.1.counter]
  intro language meaning assignment whole satisfied filled refuted policies origin
  have localPolicies := policies (assignment uv) origin
  have avoids : SourcePruningTemplates.Avoids templates (Fragments.fill assignment fragment) := by
    simpa only [filled] using localPolicies.1
  have encoded : ∀ program, SourcePruningTemplates.ProgramAt (Fragments.fill assignment fragment) program →
      SourcePruningTemplates.ProgramEncoding program := by
    simpa only [filled] using localPolicies.2
  exact retained.2.2 language meaning assignment satisfied filled refuted avoids encoded

end MicroCFTA.SourcePruningEnumerationPreparedRecursive
