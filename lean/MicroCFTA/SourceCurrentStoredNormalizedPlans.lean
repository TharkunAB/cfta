import MicroCFTA.SourceCurrentStoredPlanEquivalence
import MicroCFTA.SourceCurrentNormalizedPlanCongruence

/-!
# Recursive normalized lexical plans for stored values

Closed captures agree literally. Open node rows match by occurrence at
all nested levels. Row symbols and full guards agree. Children and union
members retain their order. Each open Mu binds its original local name to
the same arbitrary replacement value on both sides. The relation contains
no execution equation. Initial ready data constructs both actual calls.
-/
namespace MicroCFTA.SourceCurrentStoredNormalizedPlans
open InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedStoredSubstitution InternedStoredSubstitutionScope InternedStoredSubstitutionBindings
open InternedStoredSubstitutionRebind (resolve reference_plan)
open InternedFreshOrdinaryPlanEquivalence
open InternedNestedProvenance (Values)
open InternedBinderProtocol (Reference)

mutual
/-- Closed captures agree literally. Open values retain recursively normalized lexical plans. -/
def Related (firstLocals secondLocals : List Reference)
    (firstValues secondValues : List (Value Symbol Guard)) (first second : Environment Symbol Guard)
    (left right : Value Symbol Guard) : Prop :=
  if left.free.isEmpty then left = right else
  right.free.isEmpty = false ∧ match left, right with
  | .reference a, .reference b => resolve firstLocals firstValues first a = resolve secondLocals secondValues second b
  | .node _ edges _ _, .node _ other _ _ =>
      RowsRelated firstLocals secondLocals firstValues secondValues first second edges other
  | .union _ members _ _, .union _ other _ _ =>
      ManyRelated firstLocals secondLocals firstValues secondValues first second members other
  | .mu entry body _ _, .mu other later _ _ =>
      ∀ argument : Value Symbol Guard,
        Related (.interned entry.identity :: firstLocals) (.interned other.identity :: secondLocals)
          (argument :: firstValues) (argument :: secondValues) first second body later
  | _, _ => False
termination_by sizeOf left

/-- Open union members and children retain their original order. -/
def ManyRelated (firstLocals secondLocals : List Reference)
    (firstValues secondValues : List (Value Symbol Guard)) (first second : Environment Symbol Guard) :
    List (Value Symbol Guard) → List (Value Symbol Guard) → Prop
  | [], [] => True
  | left :: rest, right :: tail =>
      Related firstLocals secondLocals firstValues secondValues first second left right ∧
      ManyRelated firstLocals secondLocals firstValues secondValues first second rest tail
  | _, _ => False
termination_by left => sizeOf left

/-- One stored row retains full fields and ordered related children. -/
def RowRelated (firstLocals secondLocals : List Reference)
    (firstValues secondValues : List (Value Symbol Guard)) (first second : Environment Symbol Guard)
    (left right : EdgeValue Symbol Guard) : Prop :=
  match left, right with
  | .mk entry children, .mk other later =>
      entry.key.symbol = other.key.symbol ∧ entry.key.constraint = other.key.constraint ∧
        ManyRelated firstLocals secondLocals firstValues secondValues first second children later
termination_by sizeOf left

/-- Every stored row occurrence has a related occurrence on the other side. -/
def RowsRelated (firstLocals secondLocals : List Reference)
    (firstValues secondValues : List (Value Symbol Guard)) (first second : Environment Symbol Guard)
    (left right : List (EdgeValue Symbol Guard)) : Prop :=
  (∀ row ∈ left, ∃ other, ∃ (_ : other ∈ right),
    RowRelated firstLocals secondLocals firstValues secondValues first second row other) ∧
  (∀ row ∈ right, ∃ other, ∃ (_ : other ∈ left),
    RowRelated firstLocals secondLocals firstValues secondValues first second other row)
termination_by sizeOf left
decreasing_by all_goals exact List.sizeOf_lt_of_mem (by assumption)
end

private theorem encode_map (context : List (Value Symbol Guard)) (locals : List Reference)
    (rows : List (EdgeValue Symbol Guard)) :
    encodeEdges context locals rows = rows.map (fun row =>
      InternedNestedConstruction.EdgeSyntax.mk row.entry.key.symbol row.entry.key.constraint
        (encodeMany context locals row.children)) := by
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

mutual
/-- Related stored values give recursively related encoded plans in independently covered contexts. -/
theorem encode_related (firstContext secondContext : List (Value Symbol Guard))
    (left right : Value Symbol Guard) (firstLocals secondLocals : List Reference)
    (firstValues secondValues : List (Value Symbol Guard)) (first second : Environment Symbol Guard)
    (source : State Symbol Guard) (coherent : Coherent source)
    (firstAvailable : Values source firstContext) (secondAvailable : Values source secondContext)
    (firstCovered : ∀ leaf ∈ leaves left, leaf ∈ firstContext)
    (secondCovered : ∀ leaf ∈ leaves right, leaf ∈ secondContext)
    (firstLength : firstValues.length = firstLocals.length) (secondLength : secondValues.length = secondLocals.length)
    (related : Related firstLocals secondLocals firstValues secondValues first second left right) :
    SourceCurrentNormalizedPlanRelation.Related (encode firstContext firstLocals left) (firstValues ++ firstContext.map (input first))
      (encode secondContext secondLocals right) (secondValues ++ secondContext.map (input second)) := by
  rw [Related.eq_def] at related
  by_cases closed : left.free.isEmpty = true
  · have same : left = right := by simpa only [closed, ite_true] using related
    subst right
    have firstMember : left ∈ firstContext := firstCovered left (by rw [leaves.eq_def]; simp [closed])
    have secondMember : left ∈ secondContext := secondCovered left (by rw [leaves.eq_def]; simp [closed])
    rw [encode.eq_def, encode.eq_def]
    simp only [closed, ite_true, SourceCurrentNormalizedPlanRelation.Related]
    rw [global_lookup firstContext firstLocals firstValues left first source coherent firstAvailable firstMember firstLength,
      global_lookup secondContext secondLocals secondValues left second source coherent secondAvailable secondMember secondLength]
    simp only [Option.getD_some, input_closed left first (List.isEmpty_iff.mp closed),
      input_closed left second (List.isEmpty_iff.mp closed)]
  · have opened : left.free.isEmpty = false := Bool.eq_false_iff.mpr closed
    have details := related
    simp only [opened, Bool.false_eq_true, ite_false] at details
    rw [encode.eq_def, encode.eq_def]
    simp only [opened, details.1, Bool.false_eq_true, ite_false]
    rw [leaves.eq_def] at firstCovered secondCovered
    simp only [opened, details.1, Bool.false_eq_true, ite_false] at firstCovered secondCovered
    cases left <;> cases right <;> simp only at details ⊢ <;> try exact False.elim details.2
    case reference.reference a b =>
      obtain ⟨left, leftPlan, leftRead⟩ := reference_plan firstContext firstLocals firstValues first a
        source coherent firstAvailable (firstCovered _ (by simp)) firstLength
      obtain ⟨right, rightPlan, rightRead⟩ := reference_plan secondContext secondLocals secondValues second b
        source coherent secondAvailable (secondCovered _ (by simp)) secondLength
      have matched : SourceCurrentNormalizedPlanRelation.Related (encode firstContext firstLocals (.reference a))
          (firstValues ++ firstContext.map (input first)) (encode secondContext secondLocals (.reference b))
          (secondValues ++ secondContext.map (input second)) := by
        rw [leftPlan, rightPlan]
        simp only [SourceCurrentNormalizedPlanRelation.Related]
        exact leftRead.trans (details.2.trans rightRead.symm)
      simpa only [encode, Value.free, List.isEmpty_cons, Bool.false_eq_true, ite_false] using matched
    case node.node entry edges level free other later otherLevel otherFree =>
      simp only [SourceCurrentNormalizedPlanRelation.Related]
      exact encodeRows_related firstContext secondContext edges later firstLocals secondLocals firstValues secondValues
        first second source coherent firstAvailable secondAvailable firstCovered secondCovered firstLength secondLength details.2
    case union.union entry members level free other later otherLevel otherFree =>
      simp only [SourceCurrentNormalizedPlanRelation.Related]
      exact encodeMany_related firstContext secondContext members later firstLocals secondLocals firstValues secondValues
        first second source coherent firstAvailable secondAvailable firstCovered secondCovered firstLength secondLength details.2
    case mu.mu entry body depth ordinary other later otherDepth otherOrdinary =>
      simp only [SourceCurrentNormalizedPlanRelation.Related]
      refine ⟨by trivial, ?_⟩
      intro name
      exact encode_related firstContext secondContext body later
        (.interned entry.identity :: firstLocals) (.interned other.identity :: secondLocals)
        (.reference name :: firstValues) (.reference name :: secondValues) first second source coherent
        firstAvailable secondAvailable firstCovered secondCovered (by simp [firstLength]) (by simp [secondLength])
        (details.2 (.reference name))
termination_by sizeOf left

/-- Ordered related children give recursively related encoded child plans. -/
theorem encodeMany_related (firstContext secondContext : List (Value Symbol Guard))
    (left right : List (Value Symbol Guard)) (firstLocals secondLocals : List Reference)
    (firstValues secondValues : List (Value Symbol Guard)) (first second : Environment Symbol Guard)
    (source : State Symbol Guard) (coherent : Coherent source)
    (firstAvailable : Values source firstContext) (secondAvailable : Values source secondContext)
    (firstCovered : ∀ leaf ∈ manyLeaves left, leaf ∈ firstContext)
    (secondCovered : ∀ leaf ∈ manyLeaves right, leaf ∈ secondContext)
    (firstLength : firstValues.length = firstLocals.length) (secondLength : secondValues.length = secondLocals.length)
    (related : ManyRelated firstLocals secondLocals firstValues secondValues first second left right) :
    SourceCurrentNormalizedPlanRelation.ManyRelated (encodeMany firstContext firstLocals left) (firstValues ++ firstContext.map (input first))
      (encodeMany secondContext secondLocals right) (secondValues ++ secondContext.map (input second)) := by
  cases left <;> cases right <;> simp only [ManyRelated] at related <;> try contradiction
  case nil.nil => simp only [encodeMany, SourceCurrentNormalizedPlanRelation.ManyRelated]
  case cons.cons head tail other later =>
    simp only [encodeMany, SourceCurrentNormalizedPlanRelation.ManyRelated]
    exact ⟨encode_related firstContext secondContext head other firstLocals secondLocals firstValues secondValues
        first second source coherent firstAvailable secondAvailable
        (fun leaf member => firstCovered leaf (by simp [manyLeaves, member]))
        (fun leaf member => secondCovered leaf (by simp [manyLeaves, member])) firstLength secondLength related.1,
      encodeMany_related firstContext secondContext tail later firstLocals secondLocals firstValues secondValues
        first second source coherent firstAvailable secondAvailable
        (fun leaf member => firstCovered leaf (by simp [manyLeaves, member]))
        (fun leaf member => secondCovered leaf (by simp [manyLeaves, member])) firstLength secondLength related.2⟩
termination_by sizeOf left

/-- A related stored row gives a recursively related encoded row plan. -/
theorem encodeRow_related (firstContext secondContext : List (Value Symbol Guard))
    (left right : EdgeValue Symbol Guard) (firstLocals secondLocals : List Reference)
    (firstValues secondValues : List (Value Symbol Guard)) (first second : Environment Symbol Guard)
    (source : State Symbol Guard) (coherent : Coherent source)
    (firstAvailable : Values source firstContext) (secondAvailable : Values source secondContext)
    (firstCovered : ∀ leaf ∈ manyLeaves left.children, leaf ∈ firstContext)
    (secondCovered : ∀ leaf ∈ manyLeaves right.children, leaf ∈ secondContext)
    (firstLength : firstValues.length = firstLocals.length) (secondLength : secondValues.length = secondLocals.length)
    (related : RowRelated firstLocals secondLocals firstValues secondValues first second left right) :
    SourceCurrentNormalizedPlanRelation.RowRelated
      (.mk left.entry.key.symbol left.entry.key.constraint (encodeMany firstContext firstLocals left.children))
      (firstValues ++ firstContext.map (input first))
      (.mk right.entry.key.symbol right.entry.key.constraint (encodeMany secondContext secondLocals right.children))
      (secondValues ++ secondContext.map (input second)) := by
  cases left with
  | mk entry children =>
    cases right with
    | mk other later =>
      simp only [RowRelated] at related
      simp only [SourceCurrentNormalizedPlanRelation.RowRelated]
      exact ⟨related.1,related.2.1,
        encodeMany_related firstContext secondContext children later firstLocals secondLocals
          firstValues secondValues first second source coherent firstAvailable secondAvailable firstCovered secondCovered
          firstLength secondLength related.2.2⟩
termination_by sizeOf left

/-- Bidirectional related stored rows give recursively related encoded row occurrences. -/
theorem encodeRows_related (firstContext secondContext : List (Value Symbol Guard))
    (left right : List (EdgeValue Symbol Guard)) (firstLocals secondLocals : List Reference)
    (firstValues secondValues : List (Value Symbol Guard)) (first second : Environment Symbol Guard)
    (source : State Symbol Guard) (coherent : Coherent source)
    (firstAvailable : Values source firstContext) (secondAvailable : Values source secondContext)
    (firstCovered : ∀ leaf ∈ edgeLeaves left, leaf ∈ firstContext)
    (secondCovered : ∀ leaf ∈ edgeLeaves right, leaf ∈ secondContext)
    (firstLength : firstValues.length = firstLocals.length) (secondLength : secondValues.length = secondLocals.length)
    (related : RowsRelated firstLocals secondLocals firstValues secondValues first second left right) :
    SourceCurrentNormalizedPlanRelation.RowsRelated (encodeEdges firstContext firstLocals left)
      (firstValues ++ firstContext.map (input first)) (encodeEdges secondContext secondLocals right)
      (secondValues ++ secondContext.map (input second)) := by
  rw [RowsRelated] at related
  rw [encode_map,encode_map,SourceCurrentNormalizedPlanRelation.RowsRelated]
  constructor
  · intro row present
    obtain ⟨original,member,rfl⟩ := List.mem_map.mp present
    obtain ⟨other,included,matching⟩ := related.1 original member
    refine ⟨.mk other.entry.key.symbol other.entry.key.constraint (encodeMany secondContext secondLocals other.children),
      List.mem_map.mpr ⟨other,included,rfl⟩,?_⟩
    exact encodeRow_related firstContext secondContext original other firstLocals secondLocals firstValues secondValues
      first second source coherent firstAvailable secondAvailable
      (fun leaf selected => firstCovered leaf (row_leaves left original member leaf selected))
      (fun leaf selected => secondCovered leaf (row_leaves right other included leaf selected)) firstLength secondLength matching
  · intro row present
    obtain ⟨original,member,rfl⟩ := List.mem_map.mp present
    obtain ⟨other,included,matching⟩ := related.2 original member
    refine ⟨.mk other.entry.key.symbol other.entry.key.constraint (encodeMany firstContext firstLocals other.children),
      List.mem_map.mpr ⟨other,included,rfl⟩,?_⟩
    exact encodeRow_related firstContext secondContext other original firstLocals secondLocals firstValues secondValues
      first second source coherent firstAvailable secondAvailable
      (fun leaf selected => firstCovered leaf (row_leaves left other included leaf selected))
      (fun leaf selected => secondCovered leaf (row_leaves right original member leaf selected)) firstLength secondLength matching
termination_by sizeOf left
decreasing_by all_goals exact List.sizeOf_lt_of_mem (by assumption)

end

/-- Initial ready data constructs both related stored reconstructions with one identical result. -/
theorem complete [DecidableEq (EdgeKey Symbol Guard)] (left right : Value Symbol Guard)
    (first second : Environment Symbol Guard) (before : State Symbol Guard) (ready : SourceEqualityRequiredCache.Ready before)
    (leftAvailable : Available before left) (rightAvailable : Available before right)
    (firstReplacements : Replacements before first) (secondReplacements : Replacements before second)
    (related : Related [] [] [] [] first second left right) :
    ∃ value middle after,
      InternedFreshOrdinaryStoredSubstitution.execute left first before = .done value middle ∧
      InternedFreshOrdinaryStoredSubstitution.execute right second middle = .done value after ∧
      SourceEqualityRequiredCache.Keeps before middle ∧ SourceEqualityRequiredCache.Keeps middle after ∧
      Available after value := by
  have plans := encode_related (leaves left) (leaves right) left right [] [] [] [] first second before
    ready.semantic.1.normal.facts.coherent (leaves_available left before leftAvailable)
    (leaves_available right before rightAvailable) (fun _ member => member) (fun _ member => member) rfl rfl related
  obtain ⟨value,middle,after,leftDone,rightDone,leftKept,rightKept,output⟩ :=
    SourceCurrentNormalizedPlanCongruence.initial (encode (leaves left) [] left) (encode (leaves right) [] right)
      ((leaves left).map (input first)) ((leaves right).map (input second)) before ready
      (inputs_available left first before leftAvailable firstReplacements)
      (inputs_available right second before rightAvailable secondReplacements) (by simpa only [List.nil_append] using plans)
  exact ⟨value,middle,after,leftDone,rightDone,leftKept,rightKept,output⟩

end MicroCFTA.SourceCurrentStoredNormalizedPlans
