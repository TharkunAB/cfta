import MicroCFTA.SourceSynthesisHereditaryRawRebuild
import MicroCFTA.SourceCurrentHereditaryConstructors

/-!
# Complete row fields through ordered child results

Each child pair retains two conditional facts. An annotated input keeps
its annotation. A Program input keeps its recursive fields. The exact
source row assigns which fact each child needs. Contradiction erasure
supplies Empty at every position. These laws describe construction inputs,
not a future recursive call or a completed body certificate.
-/
namespace MicroCFTA.SourceSynthesisHereditaryChildTransport
open Cache Language InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values Edges)
open SourceSynthesisGeneralizeSyntax (Guard)
open SourceEqualityAnnotationLanguage (Annotated)
open SourceSynthesisHereditaryProgramFields (ValueFields EdgeFields)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "TypeRow" => SourceCurrentHereditaryConstructors.Edge
local notation "rawEdge" => SourceCurrentAllocatedRawRebuild.edge
local notation "rawModify" => SourceCurrentAllocatedRawRebuild.modify

/-- An actual input and result pair retains either supplied child certificate. -/
def ChildMap (valid : Guard → Prop) (literal : String → Symbol) (input output : Value Symbol Guard) : Prop :=
  (Annotated valid input → Annotated valid output) ∧
    (ValueFields valid literal input → ValueFields valid literal output)

/-- Ordered child facts retain the complete replacement request's strict recursive schema. -/
theorem edge_fields (valid : Guard → Prop) (literal : String → Symbol)
    (source : EdgeValue Symbol Guard) (children : List (Value Symbol Guard))
    (fields : EdgeFields valid literal source)
    (aligned : All₂ (ChildMap valid literal) source.children children) :
    EdgeFields valid literal (.mk source.entry children) := by
  cases fields with
  | annotated source annotation guard shape typed =>
      rw [shape] at aligned
      cases aligned with
      | @cons _ result _ _ first tail =>
          cases tail
          exact .annotated (.mk source.entry [result]) result guard rfl (first.1 typed)
  | application source types marker function argument symbol guard shape typesTyped markerTyped functionFields argumentFields =>
      rw [shape] at aligned
      cases aligned with
      | @cons _ resultTypes _ _ first tail =>
        cases tail with
        | @cons _ resultMarker _ _ second tail =>
          cases tail with
          | @cons _ resultFunction _ _ third tail =>
            cases tail with
            | @cons _ resultArgument _ _ fourth tail =>
              cases tail
              exact .application (.mk source.entry [resultTypes, resultMarker, resultFunction, resultArgument])
                resultTypes resultMarker resultFunction resultArgument symbol guard rfl
                (first.1 typesTyped) (second.1 markerTyped) (third.2 functionFields) (fourth.2 argumentFields)
  | filter source goal candidates symbol guard shape goalTyped candidateFields =>
      rw [shape] at aligned
      cases aligned with
      | @cons _ resultGoal _ _ first tail =>
        cases tail with
        | @cons _ resultCandidates _ _ second tail =>
          cases tail
          exact .filter (.mk source.entry [resultGoal, resultCandidates]) resultGoal resultCandidates symbol guard rfl
            (first.1 goalTyped) (second.2 candidateFields)

/-- Contradiction erasure supplies both conditional facts at every original child position. -/
theorem erased (valid : Guard → Prop) (literal : String → Symbol) (values : List (Value Symbol Guard)) :
    All₂ (ChildMap valid literal) values (EqualityLeafProjectionRuntimeEmpty.erase values) := by
  induction values with
  | nil => exact .nil
  | cons first rest ih =>
      exact .cons ⟨fun _ => Annotated.empty, fun _ => ValueFields.empty⟩ ih

private theorem typed_children {valid : Guard → Prop} {literal : String → Symbol}
    {inputs outputs : List (Value Symbol Guard)} (aligned : All₂ (ChildMap valid literal) inputs outputs) :
    (∀ value ∈ inputs, Annotated valid value) → ∀ value ∈ outputs, Annotated valid value := by
  induction aligned with
  | nil => intro _ value member; cases member
  | cons first rest ih =>
      intro typed value member
      rcases List.mem_cons.mp member with rfl | member
      · exact first.1 (typed _ List.mem_cons_self)
      · exact ih (fun original included => typed original (List.mem_cons_of_mem _ included)) value member

variable [DecidableEq (EdgeKey Symbol Guard)] {width : Nat}

/-- The actual raw row constructor retains a Type row from its ordered annotated child results. -/
theorem raw_typed_edge (valid : Guard → Prop) (literal : String → Symbol)
    (original : EdgeValue Symbol Guard) (children : List (Value Symbol Guard)) (before : Checked width)
    (facts : InternedNestedFacts.Facts before.native.machine.heap)
    (available : Values before.native.machine.heap children) (typed : TypeRow valid original)
    (aligned : All₂ (ChildMap valid literal) original.children children) :
    TypeRow valid (rawEdge original children before).1 := by
  change TypeRow valid
    (run (makeEdge original.entry.key.symbol original.entry.key.constraint children) before.native.machine.heap).1
  exact SourceCurrentHereditaryConstructors.makeEdge valid original.entry.key.symbol original.entry.key.constraint children
    before.native.machine.heap facts.coherent facts.cached available typed.1 (typed_children aligned typed.2)

/-- Actual unchanged and changed node reconstruction retain annotations from their construction inputs. -/
theorem raw_typed_modify (valid : Guard → Prop)
    (original : Value Symbol Guard) (oldRows newRows : List (EdgeValue Symbol Guard)) (before : Checked width)
    (facts : InternedNestedFacts.Facts before.native.machine.heap) (resident : Edges before.native.machine.heap newRows)
    (originalTyped : Annotated valid original) (rowTyped : ∀ row ∈ newRows, TypeRow valid row) :
    Annotated valid (rawModify original oldRows newRows before).1 := by
  by_cases same : newRows.map (fun row => row.entry.identity) = oldRows.map (fun row => row.entry.identity)
  · simpa only [SourceCurrentAllocatedRawRebuild.modify_unchanged original oldRows newRows before same] using originalTyped
  · simpa only [SourceCurrentAllocatedRawRebuild.modify, SourceEqualityPartialNodeRebuild.modify, same, ↓reduceIte] using
      SourceCurrentHereditaryConstructors.makeNode valid newRows before.native.machine.heap facts.coherent facts.linked resident rowTyped

end MicroCFTA.SourceSynthesisHereditaryChildTransport
