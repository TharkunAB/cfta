import MicroCFTA.InternedFreshOrdinaryPlanEquivalence
import MicroCFTA.InternedStoredSubstitutionBindings
import MicroCFTA.InternedFreshOrdinaryStoredSubstitution

/-!
# Lexical rebinding of actual stored substitution plans

A local binder slot and an external substitution can read the same value.
The prepared source traversal then gives equivalent full constructor plans.
Nested binders retain local shadowing and the exact source leaf records.
-/
namespace MicroCFTA.InternedStoredSubstitutionRebind
open Cache InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedStoredSubstitution InternedStoredSubstitutionScope InternedStoredSubstitutionBindings
open InternedFreshOrdinaryPlanEquivalence
open InternedNestedConstruction (Syntax Outcome)
open InternedNestedProvenance (Values)
open InternedBinderProtocol (Reference)

/-- Local source binders shadow the external recursive substitution map. -/
def resolve (locals : List Reference) (localValues : List (Value Symbol Guard))
    (environment : Environment Symbol Guard) (name : Reference) : Value Symbol Guard :=
  match locals.findIdx? (· == name) with
  | some index => localValues[index]?.getD .empty
  | none => (environment name).getD (.reference name)

/-- The newest local binder overrides only its own original source name. -/
theorem resolve_cons (locals : List Reference) (localValues : List (Value Symbol Guard))
    (environment : Environment Symbol Guard) (bound name : Reference) (value : Value Symbol Guard) :
    resolve (bound :: locals) (value :: localValues) environment name =
      if bound = name then value else resolve locals localValues environment name := by
  by_cases same : bound = name
  · simp [resolve, List.findIdx?_cons, same]
  · simp only [resolve, List.findIdx?_cons, beq_eq_false_iff_ne.mpr same, same, ite_false]
    cases locals.findIdx? (· == name) <;> rfl

/-- Each encoded reference slot reads exactly the original local or external binding. -/
theorem reference_plan (context : List (Value Symbol Guard)) (locals : List Reference)
    (localValues : List (Value Symbol Guard)) (environment : Environment Symbol Guard)
    (name : Reference) (state : State Symbol Guard) (coherent : Coherent state)
    (available : Values state context) (member : Value.reference name ∈ context)
    (length : localValues.length = locals.length) :
    ∃ index, encode context locals (.reference name) = .var index ∧
      (localValues ++ context.map (input environment))[index]?.getD .empty = resolve locals localValues environment name := by
  cases foundLocal : locals.findIdx? (· == name) with
  | none =>
      refine ⟨locals.length + slot context (.reference name), ?_, ?_⟩
      · simp [encode, Value.free, foundLocal]
      · rw [global_lookup context locals localValues (.reference name) environment state coherent available member length]
        simp [resolve, foundLocal, input]
  | some index =>
      refine ⟨index, ?_, ?_⟩
      · simp [encode, Value.free, foundLocal]
      · have bound : index < localValues.length := by
          rw [length]
          exact (List.findIdx?_eq_some_iff_findIdx_eq.mp foundLocal).1
        rw [List.getElem?_append_left bound]
        simp only [resolve, foundLocal]

mutual
/-- Equivalent source-name resolution derives equivalent full stored plans, including open nested binders. -/
theorem encode_equivalent (context : List (Value Symbol Guard)) (value : Value Symbol Guard)
    (firstLocals secondLocals : List Reference) (firstValues secondValues : List (Value Symbol Guard))
    (first second : Environment Symbol Guard) (state : State Symbol Guard) (coherent : Coherent state)
    (available : Values state context) (covered : ∀ leaf ∈ leaves value, leaf ∈ context)
    (firstLength : firstValues.length = firstLocals.length) (secondLength : secondValues.length = secondLocals.length)
    (agree : ∀ name, resolve firstLocals firstValues first name = resolve secondLocals secondValues second name) :
    Equivalent (encode context firstLocals value) (firstValues ++ context.map (input first))
      (encode context secondLocals value) (secondValues ++ context.map (input second)) := by
  rw [encode.eq_def, encode.eq_def]
  split
  · rename_i closed
    have member : value ∈ context := covered value (by rw [leaves.eq_def]; simp [closed])
    simp only [Equivalent]
    rw [global_lookup context firstLocals firstValues value first state coherent available member firstLength,
      global_lookup context secondLocals secondValues value second state coherent available member secondLength]
    simp only [Option.getD_some, input_closed value first (List.isEmpty_iff.mp closed),
      input_closed value second (List.isEmpty_iff.mp closed)]
  · rename_i opened
    rw [leaves.eq_def] at covered
    simp only [opened, Bool.false_eq_true, ite_false] at covered
    cases value with
    | empty => simp [Value.free] at opened
    | reference name =>
        obtain ⟨left, leftPlan, leftRead⟩ := reference_plan context firstLocals firstValues first name state coherent available
          (covered _ (by simp)) firstLength
        obtain ⟨right, rightPlan, rightRead⟩ := reference_plan context secondLocals secondValues second name state coherent available
          (covered _ (by simp)) secondLength
        have related : Equivalent (encode context firstLocals (.reference name)) (firstValues ++ context.map (input first))
            (encode context secondLocals (.reference name)) (secondValues ++ context.map (input second)) := by
          rw [leftPlan, rightPlan]
          simp only [Equivalent]
          exact leftRead.trans ((agree name).trans rightRead.symm)
        simpa only [encode, Value.free, List.isEmpty_cons, Bool.false_eq_true, ite_false] using related
    | node entry edges depth free =>
        simp only [Equivalent]
        exact encodeEdges_equivalent context edges firstLocals secondLocals firstValues secondValues first second state
          coherent available covered firstLength secondLength agree
    | union entry members depth free =>
        simp only [Equivalent]
        exact encodeMany_equivalent context members firstLocals secondLocals firstValues secondValues first second state
          coherent available covered firstLength secondLength agree
    | mu entry body depth ordinary =>
        simp only [Equivalent]
        refine ⟨by trivial, ?_⟩
        intro name
        apply encode_equivalent context body (.interned entry.identity :: firstLocals) (.interned entry.identity :: secondLocals)
          (.reference name :: firstValues) (.reference name :: secondValues) first second state coherent available covered
          (by simp [firstLength]) (by simp [secondLength])
        intro named
        simp only [resolve_cons, agree named]
termination_by sizeOf value

/-- Rebinding preserves the ordered source child plans. -/
theorem encodeMany_equivalent (context : List (Value Symbol Guard)) (values : List (Value Symbol Guard))
    (firstLocals secondLocals : List Reference) (firstValues secondValues : List (Value Symbol Guard))
    (first second : Environment Symbol Guard) (state : State Symbol Guard) (coherent : Coherent state)
    (available : Values state context) (covered : ∀ leaf ∈ manyLeaves values, leaf ∈ context)
    (firstLength : firstValues.length = firstLocals.length) (secondLength : secondValues.length = secondLocals.length)
    (agree : ∀ name, resolve firstLocals firstValues first name = resolve secondLocals secondValues second name) :
    ManyEquivalent (encodeMany context firstLocals values) (firstValues ++ context.map (input first))
      (encodeMany context secondLocals values) (secondValues ++ context.map (input second)) := by
  cases values with
  | nil => simp only [encodeMany, ManyEquivalent]
  | cons head tail =>
      simp only [encodeMany, ManyEquivalent]
      exact ⟨encode_equivalent context head firstLocals secondLocals firstValues secondValues first second state coherent available
        (fun leaf member => covered leaf (by simp [manyLeaves, member])) firstLength secondLength agree,
        encodeMany_equivalent context tail firstLocals secondLocals firstValues secondValues first second state coherent available
        (fun leaf member => covered leaf (by simp [manyLeaves, member])) firstLength secondLength agree⟩
termination_by sizeOf values

/-- Rebinding preserves the actual source symbols, guards, and ordered edge requests. -/
theorem encodeEdges_equivalent (context : List (Value Symbol Guard)) (edges : List (EdgeValue Symbol Guard))
    (firstLocals secondLocals : List Reference) (firstValues secondValues : List (Value Symbol Guard))
    (first second : Environment Symbol Guard) (state : State Symbol Guard) (coherent : Coherent state)
    (available : Values state context) (covered : ∀ leaf ∈ edgeLeaves edges, leaf ∈ context)
    (firstLength : firstValues.length = firstLocals.length) (secondLength : secondValues.length = secondLocals.length)
    (agree : ∀ name, resolve firstLocals firstValues first name = resolve secondLocals secondValues second name) :
    EdgesEquivalent (encodeEdges context firstLocals edges) (firstValues ++ context.map (input first))
      (encodeEdges context secondLocals edges) (secondValues ++ context.map (input second)) := by
  cases edges with
  | nil => simp only [encodeEdges, EdgesEquivalent]
  | cons head tail =>
      cases head with
      | mk entry children =>
          simp only [encodeEdges, EdgesEquivalent]
          exact ⟨by trivial, by trivial,
            encodeMany_equivalent context children firstLocals secondLocals firstValues secondValues first second state coherent available
              (fun leaf member => covered leaf (by simp [edgeLeaves, member])) firstLength secondLength agree,
            encodeEdges_equivalent context tail firstLocals secondLocals firstValues secondValues first second state coherent available
              (fun leaf member => covered leaf (by simp [edgeLeaves, member])) firstLength secondLength agree⟩
termination_by sizeOf edges
end

/-- One source free-name replacement leaves every other reference unchanged. -/
def replacement (old : Reference) (value : Value Symbol Guard) : Environment Symbol Guard :=
  fun name => if name = old then some value else none

/-- Rebinding a stored source name to a local slot preserves the complete repaired substitution execution. -/
theorem rebind_build [DecidableEq (EdgeKey Symbol Guard)] (value : Value Symbol Guard)
    (old name : Reference) (source current : State Symbol Guard) (coherent : Coherent source)
    (available : Available source value) :
    InternedFreshOrdinaryConstruction.build (encode (leaves value) [old] value) (.reference name :: leaves value) current =
      InternedFreshOrdinaryStoredSubstitution.execute value (replacement old (.reference name)) current := by
  have noInputs : input (Symbol := Symbol) (Guard := Guard) (fun _ => none) = id := by
    funext captured
    cases captured <;> rfl
  have plans := encode_equivalent (leaves value) value [old] [] [.reference name] []
    (fun _ => none) (replacement old (.reference name)) source coherent (leaves_available value source available)
    (fun _ member => member) rfl rfl (by
      intro named
      rw [resolve_cons]
      simp only [resolve, List.findIdx?_nil]
      by_cases same : old = named
      · subst named
        simp [replacement]
      · simp [replacement, same, Ne.symm same])
  have execution := build_exact _ _ _ _ current plans
  simpa only [List.cons_append, List.nil_append, noInputs, List.map_id,
    InternedFreshOrdinaryStoredSubstitution.execute] using execution

end MicroCFTA.InternedStoredSubstitutionRebind
