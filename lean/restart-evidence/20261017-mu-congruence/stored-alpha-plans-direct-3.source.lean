import MicroCFTA.SourceCurrentStoredPlanEquivalence

/-!
# Ordered lexical alpha relations for stored plans

Different stored values can use different original local names and cache
identities. The relation retains closed captures exactly. Open constructors
retain their fields and order. Each open Mu binds its own original name to
the same argument on both sides. No execution equation defines the relation.
-/
namespace MicroCFTA.SourceCurrentStoredAlphaPlans
open InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedStoredSubstitution InternedStoredSubstitutionScope InternedStoredSubstitutionBindings
open InternedStoredSubstitutionRebind (resolve reference_plan)
open InternedFreshOrdinaryPlanEquivalence
open InternedNestedProvenance (Values)
open InternedBinderProtocol (Reference)

mutual
/-- Closed captures agree literally. Open values agree by their lexical constructor plans. -/
def Alpha (firstLocals secondLocals : List Reference)
    (firstValues secondValues : List (Value Symbol Guard)) (first second : Environment Symbol Guard)
    (left right : Value Symbol Guard) : Prop :=
  if left.free.isEmpty then left = right else
  right.free.isEmpty = false ∧ match left, right with
  | .reference a, .reference b => resolve firstLocals firstValues first a = resolve secondLocals secondValues second b
  | .node _ edges _ _, .node _ other _ _ =>
      EdgesAlpha firstLocals secondLocals firstValues secondValues first second edges other
  | .union _ members _ _, .union _ other _ _ =>
      ManyAlpha firstLocals secondLocals firstValues secondValues first second members other
  | .mu entry body _ _, .mu other later _ _ =>
      ∀ argument : Value Symbol Guard,
        Alpha (.interned entry.identity :: firstLocals) (.interned other.identity :: secondLocals)
          (argument :: firstValues) (argument :: secondValues) first second body later
  | _, _ => False
termination_by sizeOf left

/-- Open union members and children retain their original order. -/
def ManyAlpha (firstLocals secondLocals : List Reference)
    (firstValues secondValues : List (Value Symbol Guard)) (first second : Environment Symbol Guard) :
    List (Value Symbol Guard) → List (Value Symbol Guard) → Prop
  | [], [] => True
  | left :: rest, right :: tail =>
      Alpha firstLocals secondLocals firstValues secondValues first second left right ∧
      ManyAlpha firstLocals secondLocals firstValues secondValues first second rest tail
  | _, _ => False
termination_by left => sizeOf left

/-- Rows retain full symbols, full guards, and ordered paired child plans. -/
def EdgesAlpha (firstLocals secondLocals : List Reference)
    (firstValues secondValues : List (Value Symbol Guard)) (first second : Environment Symbol Guard) :
    List (EdgeValue Symbol Guard) → List (EdgeValue Symbol Guard) → Prop
  | [], [] => True
  | .mk entry children :: rest, .mk other later :: tail =>
      entry.key.symbol = other.key.symbol ∧ entry.key.constraint = other.key.constraint ∧
      ManyAlpha firstLocals secondLocals firstValues secondValues first second children later ∧
      EdgesAlpha firstLocals secondLocals firstValues secondValues first second rest tail
  | _, _ => False
termination_by left => sizeOf left
end

mutual
/-- Related distinct stored values have equivalent complete encoded plans in independently covered contexts. -/
theorem encode_equivalent (firstContext secondContext : List (Value Symbol Guard))
    (left right : Value Symbol Guard) (firstLocals secondLocals : List Reference)
    (firstValues secondValues : List (Value Symbol Guard)) (first second : Environment Symbol Guard)
    (source : State Symbol Guard) (coherent : Coherent source)
    (firstAvailable : Values source firstContext) (secondAvailable : Values source secondContext)
    (firstCovered : ∀ leaf ∈ leaves left, leaf ∈ firstContext)
    (secondCovered : ∀ leaf ∈ leaves right, leaf ∈ secondContext)
    (firstLength : firstValues.length = firstLocals.length) (secondLength : secondValues.length = secondLocals.length)
    (related : Alpha firstLocals secondLocals firstValues secondValues first second left right) :
    Equivalent (encode firstContext firstLocals left) (firstValues ++ firstContext.map (input first))
      (encode secondContext secondLocals right) (secondValues ++ secondContext.map (input second)) := by
  rw [Alpha.eq_def] at related
  by_cases closed : left.free.isEmpty = true
  · have same : left = right := by simpa only [closed, ite_true] using related
    subst right
    have firstMember : left ∈ firstContext := firstCovered left (by rw [leaves.eq_def]; simp [closed])
    have secondMember : left ∈ secondContext := secondCovered left (by rw [leaves.eq_def]; simp [closed])
    rw [encode.eq_def, encode.eq_def]
    simp only [closed, ite_true, Equivalent]
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
    cases left <;> cases right <;> simp only at details ⊢ <;> try contradiction
    case reference.reference a b =>
      obtain ⟨left, leftPlan, leftRead⟩ := reference_plan firstContext firstLocals firstValues first a
        source coherent firstAvailable (firstCovered _ (by simp)) firstLength
      obtain ⟨right, rightPlan, rightRead⟩ := reference_plan secondContext secondLocals secondValues second b
        source coherent secondAvailable (secondCovered _ (by simp)) secondLength
      have matched : Equivalent (encode firstContext firstLocals (.reference a))
          (firstValues ++ firstContext.map (input first)) (encode secondContext secondLocals (.reference b))
          (secondValues ++ secondContext.map (input second)) := by
        rw [leftPlan, rightPlan]
        exact leftRead.trans (details.2.trans rightRead.symm)
      simpa only [encode, Value.free, List.isEmpty_cons, Bool.false_eq_true, ite_false] using matched
    case node.node entry edges level free other later otherLevel otherFree =>
      simp only [Equivalent]
      exact encodeEdges_equivalent firstContext secondContext edges later firstLocals secondLocals firstValues secondValues
        first second source coherent firstAvailable secondAvailable firstCovered secondCovered firstLength secondLength details.2
    case union.union entry members level free other later otherLevel otherFree =>
      simp only [Equivalent]
      exact encodeMany_equivalent firstContext secondContext members later firstLocals secondLocals firstValues secondValues
        first second source coherent firstAvailable secondAvailable firstCovered secondCovered firstLength secondLength details.2
    case mu.mu entry body depth ordinary other later otherDepth otherOrdinary =>
      simp only [Equivalent]
      refine ⟨by trivial, ?_⟩
      intro name
      exact encode_equivalent firstContext secondContext body later
        (.interned entry.identity :: firstLocals) (.interned other.identity :: secondLocals)
        (.reference name :: firstValues) (.reference name :: secondValues) first second source coherent
        firstAvailable secondAvailable firstCovered secondCovered (by simp [firstLength]) (by simp [secondLength])
        (details.2 (.reference name))
termination_by sizeOf left

/-- Ordered related children give equivalent complete child plans. -/
theorem encodeMany_equivalent (firstContext secondContext : List (Value Symbol Guard))
    (left right : List (Value Symbol Guard)) (firstLocals secondLocals : List Reference)
    (firstValues secondValues : List (Value Symbol Guard)) (first second : Environment Symbol Guard)
    (source : State Symbol Guard) (coherent : Coherent source)
    (firstAvailable : Values source firstContext) (secondAvailable : Values source secondContext)
    (firstCovered : ∀ leaf ∈ manyLeaves left, leaf ∈ firstContext)
    (secondCovered : ∀ leaf ∈ manyLeaves right, leaf ∈ secondContext)
    (firstLength : firstValues.length = firstLocals.length) (secondLength : secondValues.length = secondLocals.length)
    (related : ManyAlpha firstLocals secondLocals firstValues secondValues first second left right) :
    ManyEquivalent (encodeMany firstContext firstLocals left) (firstValues ++ firstContext.map (input first))
      (encodeMany secondContext secondLocals right) (secondValues ++ secondContext.map (input second)) := by
  cases left <;> cases right <;> simp only [ManyAlpha] at related <;> try contradiction
  case nil.nil => simp only [encodeMany, ManyEquivalent]
  case cons.cons head tail other later =>
    simp only [encodeMany, ManyEquivalent]
    exact ⟨encode_equivalent firstContext secondContext head other firstLocals secondLocals firstValues secondValues
        first second source coherent firstAvailable secondAvailable
        (fun leaf member => firstCovered leaf (by simp [manyLeaves, member]))
        (fun leaf member => secondCovered leaf (by simp [manyLeaves, member])) firstLength secondLength related.1,
      encodeMany_equivalent firstContext secondContext tail later firstLocals secondLocals firstValues secondValues
        first second source coherent firstAvailable secondAvailable
        (fun leaf member => firstCovered leaf (by simp [manyLeaves, member]))
        (fun leaf member => secondCovered leaf (by simp [manyLeaves, member])) firstLength secondLength related.2⟩
termination_by sizeOf left

/-- Related rows retain the exact encoded symbols and guards and every ordered child plan. -/
theorem encodeEdges_equivalent (firstContext secondContext : List (Value Symbol Guard))
    (left right : List (EdgeValue Symbol Guard)) (firstLocals secondLocals : List Reference)
    (firstValues secondValues : List (Value Symbol Guard)) (first second : Environment Symbol Guard)
    (source : State Symbol Guard) (coherent : Coherent source)
    (firstAvailable : Values source firstContext) (secondAvailable : Values source secondContext)
    (firstCovered : ∀ leaf ∈ edgeLeaves left, leaf ∈ firstContext)
    (secondCovered : ∀ leaf ∈ edgeLeaves right, leaf ∈ secondContext)
    (firstLength : firstValues.length = firstLocals.length) (secondLength : secondValues.length = secondLocals.length)
    (related : EdgesAlpha firstLocals secondLocals firstValues secondValues first second left right) :
    EdgesEquivalent (encodeEdges firstContext firstLocals left) (firstValues ++ firstContext.map (input first))
      (encodeEdges secondContext secondLocals right) (secondValues ++ secondContext.map (input second)) := by
  cases left <;> cases right <;> try cases related
  case nil.nil => simp only [encodeEdges, EdgesEquivalent]
  case nil.cons head tail => cases head; simp only [EdgesAlpha] at related
  case cons.nil head tail => cases head; simp only [EdgesAlpha] at related
  case cons.cons head tail other later =>
    cases head with
    | mk entry children =>
      cases other with
      | mk other laterChildren =>
        simp only [EdgesAlpha] at related
        simp only [encodeEdges, EdgesEquivalent]
        exact ⟨related.1, related.2.1,
          encodeMany_equivalent firstContext secondContext children laterChildren firstLocals secondLocals firstValues secondValues
            first second source coherent firstAvailable secondAvailable
            (fun leaf member => firstCovered leaf (by simp [edgeLeaves, member]))
            (fun leaf member => secondCovered leaf (by simp [edgeLeaves, member])) firstLength secondLength related.2.2.1,
          encodeEdges_equivalent firstContext secondContext tail later firstLocals secondLocals firstValues secondValues
            first second source coherent firstAvailable secondAvailable
            (fun leaf member => firstCovered leaf (by simp [edgeLeaves, member]))
            (fun leaf member => secondCovered leaf (by simp [edgeLeaves, member])) firstLength secondLength related.2.2.2⟩
termination_by sizeOf left
end

/-- Related stored values have identical full repaired outcomes at any common current heap. -/
theorem execute_exact [DecidableEq (EdgeKey Symbol Guard)] (left right : Value Symbol Guard)
    (first second : Environment Symbol Guard) (source current : State Symbol Guard)
    (coherent : Coherent source) (leftAvailable : Available source left) (rightAvailable : Available source right)
    (related : Alpha [] [] [] [] first second left right) :
    InternedFreshOrdinaryStoredSubstitution.execute left first current =
      InternedFreshOrdinaryStoredSubstitution.execute right second current := by
  have plans := encode_equivalent (leaves left) (leaves right) left right [] [] [] [] first second source coherent
    (leaves_available left source leftAvailable) (leaves_available right source rightAvailable)
    (fun _ member => member) (fun _ member => member) rfl rfl related
  simpa only [List.nil_append, InternedFreshOrdinaryStoredSubstitution.execute] using
    build_exact _ _ _ _ current plans

end MicroCFTA.SourceCurrentStoredAlphaPlans
