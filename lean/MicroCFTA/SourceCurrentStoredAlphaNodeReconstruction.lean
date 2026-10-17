import MicroCFTA.SourceCurrentStoredAlphaPlans
import MicroCFTA.SourceCurrentNodePlanCongruence

/-!
# Initial reconstruction of alpha-related open stored nodes

Source rows match by occurrence. Their symbols and full guards agree.
Their children use the ordered pure alpha relation. The encoded row plans
then construct one exact canonical result in two sequential executions.
This theorem does not derive alpha relations from stored Mu writers.
-/
namespace MicroCFTA.SourceCurrentStoredAlphaNodeReconstruction
open Cache InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedNestedConstruction (EdgeSyntax Outcome)
open InternedStoredSubstitution (Environment Replacements leaves edgeLeaves manyLeaves input encode encodeMany encodeEdges)
open InternedNestedProvenance (Values)
open SourceCurrentStoredAlphaPlans (ManyAlpha)
open SourceCurrentNodePlanCongruence (RowsEquivalent RowEquivalent)
open SourceEqualityRequiredCache (Ready Keeps)

/-- Stored rows match by occurrence with exact fields and ordered alpha-related children. -/
def RowsAlpha (first second : Environment Symbol Guard)
    (left right : List (EdgeValue Symbol Guard)) : Prop :=
  (∀ row ∈ left, ∃ other ∈ right,
    row.entry.key.symbol = other.entry.key.symbol ∧ row.entry.key.constraint = other.entry.key.constraint ∧
      ManyAlpha [] [] [] [] first second row.children other.children) ∧
  (∀ row ∈ right, ∃ other ∈ left,
    other.entry.key.symbol = row.entry.key.symbol ∧ other.entry.key.constraint = row.entry.key.constraint ∧
      ManyAlpha [] [] [] [] first second other.children row.children)

private theorem encode_map (context : List (Value Symbol Guard)) (rows : List (EdgeValue Symbol Guard)) :
    encodeEdges context [] rows = rows.map (fun row =>
      EdgeSyntax.mk row.entry.key.symbol row.entry.key.constraint (encodeMany context [] row.children)) := by
  induction rows with
  | nil => simp only [encodeEdges,List.map_nil]
  | cons row rest ih => cases row; simp only [encodeEdges,List.map_cons,EdgeValue.entry,EdgeValue.children,ih]

private theorem row_leaves (rows : List (EdgeValue Symbol Guard)) (row : EdgeValue Symbol Guard)
    (member : row ∈ rows) (leaf : Value Symbol Guard) (present : leaf ∈ manyLeaves row.children) :
    leaf ∈ edgeLeaves rows := by
  induction rows with
  | nil => cases member
  | cons first rest ih =>
      cases first with
      | mk entry children =>
          rcases List.mem_cons.mp member with rfl | later
          · simpa only [edgeLeaves,EdgeValue.children] using List.mem_append_left (edgeLeaves rest) present
          · simpa only [edgeLeaves] using List.mem_append_right (manyLeaves children) (ih later)

/-- Pure row alpha relations give equivalent encoded row occurrences in independently covered contexts. -/
theorem encode_rows (firstContext secondContext : List (Value Symbol Guard))
    (left right : List (EdgeValue Symbol Guard)) (first second : Environment Symbol Guard)
    (source : State Symbol Guard) (coherent : Coherent source)
    (firstAvailable : Values source firstContext) (secondAvailable : Values source secondContext)
    (firstCovered : ∀ leaf ∈ edgeLeaves left, leaf ∈ firstContext)
    (secondCovered : ∀ leaf ∈ edgeLeaves right, leaf ∈ secondContext)
    (related : RowsAlpha first second left right) :
    RowsEquivalent (encodeEdges firstContext [] left) (firstContext.map (input first))
      (encodeEdges secondContext [] right) (secondContext.map (input second)) := by
  rw [encode_map,encode_map]
  constructor
  · intro row present
    obtain ⟨original,member,rfl⟩ := List.mem_map.mp present
    obtain ⟨other,included,symbol,guard,children⟩ := related.1 original member
    refine ⟨.mk other.entry.key.symbol other.entry.key.constraint (encodeMany secondContext [] other.children),
      List.mem_map.mpr ⟨other,included,rfl⟩,symbol,guard,?_⟩
    simpa only [List.nil_append] using SourceCurrentStoredAlphaPlans.encodeMany_equivalent
      firstContext secondContext original.children other.children [] [] [] [] first second source coherent
      firstAvailable secondAvailable
      (fun leaf selected => firstCovered leaf (row_leaves left original member leaf selected))
      (fun leaf selected => secondCovered leaf (row_leaves right other included leaf selected)) rfl rfl children
  · intro row present
    obtain ⟨original,member,rfl⟩ := List.mem_map.mp present
    obtain ⟨other,included,symbol,guard,children⟩ := related.2 original member
    refine ⟨.mk other.entry.key.symbol other.entry.key.constraint (encodeMany firstContext [] other.children),
      List.mem_map.mpr ⟨other,included,rfl⟩,symbol,guard,?_⟩
    simpa only [List.nil_append] using SourceCurrentStoredAlphaPlans.encodeMany_equivalent
      firstContext secondContext other.children original.children [] [] [] [] first second source coherent
      firstAvailable secondAvailable
      (fun leaf selected => firstCovered leaf (row_leaves left other included leaf selected))
      (fun leaf selected => secondCovered leaf (row_leaves right original member leaf selected)) rfl rfl children

/-- Initial ready data constructs both open stored node reconstructions with one identical result. -/
theorem complete [DecidableEq (EdgeKey Symbol Guard)]
    (firstEntry secondEntry : Interned InternedBinderProtocol.NodeKey)
    (left right : List (EdgeValue Symbol Guard)) (firstLevel secondLevel : Nat)
    (firstFree secondFree : List InternedBinderProtocol.Reference)
    (first second : Environment Symbol Guard) (before : State Symbol Guard) (ready : Ready before)
    (leftAvailable : Available before (.node firstEntry left firstLevel firstFree))
    (rightAvailable : Available before (.node secondEntry right secondLevel secondFree))
    (firstReplacements : Replacements before first) (secondReplacements : Replacements before second)
    (firstOpen : firstFree.isEmpty = false) (secondOpen : secondFree.isEmpty = false)
    (related : RowsAlpha first second left right) :
    ∃ value middle after,
      InternedFreshOrdinaryStoredSubstitution.execute (.node firstEntry left firstLevel firstFree) first before =
        .done value middle ∧
      InternedFreshOrdinaryStoredSubstitution.execute (.node secondEntry right secondLevel secondFree) second middle =
        .done value after ∧ Keeps before middle ∧ Keeps middle after ∧ Available after value := by
  let firstRoot := Value.node firstEntry left firstLevel firstFree
  let secondRoot := Value.node secondEntry right secondLevel secondFree
  let firstContext := leaves firstRoot
  let secondContext := leaves secondRoot
  have firstLeaves : firstContext = edgeLeaves left := by
    change leaves firstRoot = edgeLeaves left
    rw [leaves.eq_def]
    simp only [firstRoot,Value.free,firstOpen,Bool.false_eq_true,ite_false]
  have secondLeaves : secondContext = edgeLeaves right := by
    change leaves secondRoot = edgeLeaves right
    rw [leaves.eq_def]
    simp only [secondRoot,Value.free,secondOpen,Bool.false_eq_true,ite_false]
  have plans := encode_rows firstContext secondContext left right first second before ready.semantic.1.normal.facts.coherent
    (InternedStoredSubstitution.leaves_available firstRoot before leftAvailable)
    (InternedStoredSubstitution.leaves_available secondRoot before rightAvailable)
    (fun leaf member => by simpa only [firstLeaves] using member)
    (fun leaf member => by simpa only [secondLeaves] using member) related
  obtain ⟨value,middle,after,firstDone,secondDone,firstKept,secondKept,output⟩ :=
    SourceCurrentNodePlanCongruence.initial (encodeEdges firstContext [] left) (encodeEdges secondContext [] right)
      (firstContext.map (input first)) (secondContext.map (input second)) before ready
      (InternedStoredSubstitution.inputs_available firstRoot first before leftAvailable firstReplacements)
      (InternedStoredSubstitution.inputs_available secondRoot second before rightAvailable secondReplacements) plans
  refine ⟨value,middle,after,?_,?_,firstKept,secondKept,output⟩
  · change InternedFreshOrdinaryConstruction.build (encode firstContext [] firstRoot) _ before = _
    rw [encode.eq_def]
    simpa only [firstRoot,Value.free,firstOpen,Bool.false_eq_true,ite_false] using firstDone
  · change InternedFreshOrdinaryConstruction.build (encode secondContext [] secondRoot) _ middle = _
    rw [encode.eq_def]
    simpa only [secondRoot,Value.free,secondOpen,Bool.false_eq_true,ite_false] using secondDone

end MicroCFTA.SourceCurrentStoredAlphaNodeReconstruction
