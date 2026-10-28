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
