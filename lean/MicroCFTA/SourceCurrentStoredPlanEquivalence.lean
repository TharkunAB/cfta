import MicroCFTA.InternedStoredSubstitutionRebind

/-!
# Exact stored execution with independent capture contexts

Each lexical context covers the original stored leaves in one coherent
source heap. Equal name resolution then gives equivalent complete plans.
Their actual executions agree at any current heap, including pending
outcomes and nested binder effects.
-/
namespace MicroCFTA.SourceCurrentStoredPlanEquivalence
open InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedStoredSubstitution InternedStoredSubstitutionScope InternedStoredSubstitutionBindings
open InternedStoredSubstitutionRebind (resolve resolve_cons reference_plan)
open InternedFreshOrdinaryPlanEquivalence
open InternedNestedConstruction (Syntax Outcome)
open InternedNestedProvenance (Values)
open InternedBinderProtocol (Reference)

mutual
/-- Independently covered contexts retain the complete plan under equal lexical name resolution. -/
theorem encode_equivalent (firstContext secondContext : List (Value Symbol Guard)) (value : Value Symbol Guard)
    (firstLocals secondLocals : List Reference) (firstValues secondValues : List (Value Symbol Guard))
    (first second : Environment Symbol Guard) (source : State Symbol Guard) (coherent : Coherent source)
    (firstAvailable : Values source firstContext) (secondAvailable : Values source secondContext)
    (firstCovered : ∀ leaf ∈ leaves value, leaf ∈ firstContext)
    (secondCovered : ∀ leaf ∈ leaves value, leaf ∈ secondContext)
    (firstLength : firstValues.length = firstLocals.length) (secondLength : secondValues.length = secondLocals.length)
    (agree : ∀ name, resolve firstLocals firstValues first name = resolve secondLocals secondValues second name) :
    Equivalent (encode firstContext firstLocals value) (firstValues ++ firstContext.map (input first))
      (encode secondContext secondLocals value) (secondValues ++ secondContext.map (input second)) := by
  rw [encode.eq_def, encode.eq_def]
  split
  · rename_i closed
    have firstMember : value ∈ firstContext := firstCovered value (by rw [leaves.eq_def]; simp [closed])
    have secondMember : value ∈ secondContext := secondCovered value (by rw [leaves.eq_def]; simp [closed])
    simp only [Equivalent]
    rw [global_lookup firstContext firstLocals firstValues value first source coherent firstAvailable firstMember firstLength,
      global_lookup secondContext secondLocals secondValues value second source coherent secondAvailable secondMember secondLength]
    simp only [Option.getD_some, input_closed value first (List.isEmpty_iff.mp closed),
      input_closed value second (List.isEmpty_iff.mp closed)]
  · rename_i opened
    rw [leaves.eq_def] at firstCovered secondCovered
    simp only [opened, Bool.false_eq_true, ite_false] at firstCovered secondCovered
    cases value with
    | empty => simp [Value.free] at opened
    | reference name =>
        obtain ⟨left, leftPlan, leftRead⟩ := reference_plan firstContext firstLocals firstValues first name
          source coherent firstAvailable (firstCovered _ (by simp)) firstLength
        obtain ⟨right, rightPlan, rightRead⟩ := reference_plan secondContext secondLocals secondValues second name
          source coherent secondAvailable (secondCovered _ (by simp)) secondLength
        have related : Equivalent (encode firstContext firstLocals (.reference name))
            (firstValues ++ firstContext.map (input first)) (encode secondContext secondLocals (.reference name))
            (secondValues ++ secondContext.map (input second)) := by
          rw [leftPlan, rightPlan]
          simp only [Equivalent]
          exact leftRead.trans ((agree name).trans rightRead.symm)
        simpa only [encode, Value.free, List.isEmpty_cons, Bool.false_eq_true, ite_false] using related
    | node entry edges depth free =>
        simp only [Equivalent]
        exact encodeEdges_equivalent firstContext secondContext edges firstLocals secondLocals firstValues secondValues
          first second source coherent firstAvailable secondAvailable firstCovered secondCovered firstLength secondLength agree
    | union entry members depth free =>
        simp only [Equivalent]
        exact encodeMany_equivalent firstContext secondContext members firstLocals secondLocals firstValues secondValues
          first second source coherent firstAvailable secondAvailable firstCovered secondCovered firstLength secondLength agree
    | mu entry body depth ordinary =>
        simp only [Equivalent]
        refine ⟨by trivial, ?_⟩
        intro name
        apply encode_equivalent firstContext secondContext body
          (.interned entry.identity :: firstLocals) (.interned entry.identity :: secondLocals)
          (.reference name :: firstValues) (.reference name :: secondValues) first second source coherent
          firstAvailable secondAvailable firstCovered secondCovered
          (by simp [firstLength]) (by simp [secondLength])
        intro named
        simp only [resolve_cons, agree named]
termination_by sizeOf value

/-- Independent capture contexts preserve every ordered child plan, including nested binders. -/
theorem encodeMany_equivalent (firstContext secondContext : List (Value Symbol Guard))
    (values : List (Value Symbol Guard)) (firstLocals secondLocals : List Reference)
    (firstValues secondValues : List (Value Symbol Guard)) (first second : Environment Symbol Guard)
    (source : State Symbol Guard) (coherent : Coherent source)
    (firstAvailable : Values source firstContext) (secondAvailable : Values source secondContext)
    (firstCovered : ∀ leaf ∈ manyLeaves values, leaf ∈ firstContext)
    (secondCovered : ∀ leaf ∈ manyLeaves values, leaf ∈ secondContext)
    (firstLength : firstValues.length = firstLocals.length) (secondLength : secondValues.length = secondLocals.length)
    (agree : ∀ name, resolve firstLocals firstValues first name = resolve secondLocals secondValues second name) :
    ManyEquivalent (encodeMany firstContext firstLocals values) (firstValues ++ firstContext.map (input first))
      (encodeMany secondContext secondLocals values) (secondValues ++ secondContext.map (input second)) := by
  cases values with
  | nil => simp only [encodeMany, ManyEquivalent]
  | cons head tail =>
      simp only [encodeMany, ManyEquivalent]
      exact ⟨encode_equivalent firstContext secondContext head firstLocals secondLocals firstValues secondValues
        first second source coherent firstAvailable secondAvailable
        (fun leaf member => firstCovered leaf (by simp [manyLeaves, member]))
        (fun leaf member => secondCovered leaf (by simp [manyLeaves, member])) firstLength secondLength agree,
        encodeMany_equivalent firstContext secondContext tail firstLocals secondLocals firstValues secondValues
          first second source coherent firstAvailable secondAvailable
          (fun leaf member => firstCovered leaf (by simp [manyLeaves, member]))
          (fun leaf member => secondCovered leaf (by simp [manyLeaves, member])) firstLength secondLength agree⟩
termination_by sizeOf values

/-- Independent contexts retain original symbols, guards, edge order, and child plans. -/
theorem encodeEdges_equivalent (firstContext secondContext : List (Value Symbol Guard))
    (edges : List (EdgeValue Symbol Guard)) (firstLocals secondLocals : List Reference)
    (firstValues secondValues : List (Value Symbol Guard)) (first second : Environment Symbol Guard)
    (source : State Symbol Guard) (coherent : Coherent source)
    (firstAvailable : Values source firstContext) (secondAvailable : Values source secondContext)
    (firstCovered : ∀ leaf ∈ edgeLeaves edges, leaf ∈ firstContext)
    (secondCovered : ∀ leaf ∈ edgeLeaves edges, leaf ∈ secondContext)
    (firstLength : firstValues.length = firstLocals.length) (secondLength : secondValues.length = secondLocals.length)
    (agree : ∀ name, resolve firstLocals firstValues first name = resolve secondLocals secondValues second name) :
    EdgesEquivalent (encodeEdges firstContext firstLocals edges) (firstValues ++ firstContext.map (input first))
      (encodeEdges secondContext secondLocals edges) (secondValues ++ secondContext.map (input second)) := by
  cases edges with
  | nil => simp only [encodeEdges, EdgesEquivalent]
  | cons head tail =>
      cases head with
      | mk entry children =>
          simp only [encodeEdges, EdgesEquivalent]
          exact ⟨by trivial, by trivial,
            encodeMany_equivalent firstContext secondContext children firstLocals secondLocals firstValues secondValues
              first second source coherent firstAvailable secondAvailable
              (fun leaf member => firstCovered leaf (by simp [edgeLeaves, member]))
              (fun leaf member => secondCovered leaf (by simp [edgeLeaves, member])) firstLength secondLength agree,
            encodeEdges_equivalent firstContext secondContext tail firstLocals secondLocals firstValues secondValues
              first second source coherent firstAvailable secondAvailable
              (fun leaf member => firstCovered leaf (by simp [edgeLeaves, member]))
              (fun leaf member => secondCovered leaf (by simp [edgeLeaves, member])) firstLength secondLength agree⟩
termination_by sizeOf edges
end

/-- Shared lexical execution equals repaired execution under its exact resolved bindings at any current heap. -/
theorem build_execute [DecidableEq (EdgeKey Symbol Guard)] (context : List (Value Symbol Guard))
    (locals : List Reference) (localValues : List (Value Symbol Guard)) (value : Value Symbol Guard)
    (environment : Environment Symbol Guard) (source current : State Symbol Guard) (coherent : Coherent source)
    (contextAvailable : Values source context) (available : Available source value)
    (covered : ∀ leaf ∈ leaves value, leaf ∈ context) (length : localValues.length = locals.length) :
    InternedFreshOrdinaryConstruction.build (encode context locals value)
      (localValues ++ context.map (input environment)) current =
        InternedFreshOrdinaryStoredSubstitution.execute value
          (fun name => some (resolve locals localValues environment name)) current := by
  have plans := encode_equivalent context (leaves value) value locals [] localValues [] environment
    (fun name => some (resolve locals localValues environment name)) source coherent contextAvailable
    (leaves_available value source available) covered (fun _ member => member) length rfl (by
      intro name
      simp only [resolve, List.findIdx?_nil, Option.getD_some])
  simpa only [List.nil_append, InternedFreshOrdinaryStoredSubstitution.execute] using
    build_exact _ _ _ _ current plans

/-- Recapturing each child's own leaves preserves the original replacement environment and full outcome. -/
theorem recapture [DecidableEq (EdgeKey Symbol Guard)] (context : List (Value Symbol Guard))
    (value : Value Symbol Guard) (environment : Environment Symbol Guard) (source current : State Symbol Guard)
    (coherent : Coherent source) (contextAvailable : Values source context) (available : Available source value)
    (covered : ∀ leaf ∈ leaves value, leaf ∈ context) :
    InternedFreshOrdinaryConstruction.build (encode context [] value) (context.map (input environment)) current =
      InternedFreshOrdinaryStoredSubstitution.execute value environment current := by
  have plans := encode_equivalent context (leaves value) value [] [] [] [] environment environment source coherent
    contextAvailable (leaves_available value source available) covered (fun _ member => member) rfl rfl (fun _ => rfl)
  simpa only [List.nil_append, InternedFreshOrdinaryStoredSubstitution.execute] using
    build_exact _ _ _ _ current plans

end MicroCFTA.SourceCurrentStoredPlanEquivalence
