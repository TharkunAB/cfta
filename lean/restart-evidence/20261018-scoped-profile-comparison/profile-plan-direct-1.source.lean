import MicroCFTA.SourceCurrentStoredProfileFunction
import MicroCFTA.InternedStoredSubstitutionBindings

/-!
# Pure profiles under independent stored capture contexts

Each context contains the original stored leaves in one coherent heap.
Equal closed captures and reference resolution preserve the full encoded
profile plan. Local scopes keep their nearest binding through nested Mu.
-/
namespace MicroCFTA.SourceCurrentStoredProfilePlan
open InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedStoredSubstitution (leaves manyLeaves edgeLeaves slot encode encodeMany encodeEdges)
open InternedStoredSubstitutionScope (slot_lookup)
open InternedNestedProvenance (Values)
open InternedProfileSemantics (Abstract evaluate evaluateMany evaluateEdges mapNames)
open InternedBinderProtocol (Reference)

/-- Resolve the nearest local profile before the original reference leaf. -/
def resolve (locals : List Reference) (values : List (Abstract Atom))
    (global : Value Symbol Guard → Abstract Atom) (name : Reference) : Abstract Atom :=
  match locals.findIdx? (· == name) with
  | some index => values[index]?.getD (some [])
  | none => global (.reference name)

private theorem resolve_cons (locals : List Reference) (values : List (Abstract Atom))
    (global : Value Symbol Guard → Abstract Atom) (bound name : Reference) (value : Abstract Atom) :
    resolve (bound :: locals) (value :: values) global name =
      if bound = name then value else resolve locals values global name := by
  by_cases same : bound = name
  · simp [resolve,List.findIdx?_cons,same]
  · simp only [resolve,List.findIdx?_cons,beq_eq_false_iff_ne.mpr same,same,ite_false]
    cases locals.findIdx? (· == name) <;> rfl

private theorem resolve_map (function : Atom → Other) (locals : List Reference) (values : List (Abstract Atom))
    (global : Value Symbol Guard → Abstract Atom) (name : Reference) :
    resolve locals (values.map (mapNames function)) (fun value => mapNames function (global value)) name =
      mapNames function (resolve locals values global name) := by
  simp only [resolve]
  cases locals.findIdx? (· == name) with
  | none => rfl
  | some index =>
      cases found : values[index]? <;> simp [List.getElem?_map,found,mapNames]

private theorem global_lookup (context : List (Value Symbol Guard)) (locals : List Reference)
    (values : List (Abstract Atom)) (global : Value Symbol Guard → Abstract Atom)
    (value : Value Symbol Guard) (state : State Symbol Guard) (coherent : Coherent state)
    (available : Values state context) (member : value ∈ context) (length : values.length = locals.length) :
    (values ++ context.map global)[locals.length + slot context value]? = some (global value) := by
  rw [List.getElem?_append_right (by omega),length,Nat.add_sub_cancel_left,List.getElem?_map,
    slot_lookup context value state coherent available member]
  rfl

private theorem reference_evaluate (context : List (Value Symbol Guard)) (locals : List Reference)
    (values : List (Abstract Atom)) (global : Value Symbol Guard → Abstract Atom)
    (name : Reference) (state : State Symbol Guard) (coherent : Coherent state)
    (available : Values state context) (member : Value.reference name ∈ context)
    (length : values.length = locals.length) :
    evaluate (encode context locals (.reference name)) (values ++ context.map global) =
      resolve locals values global name := by
  cases found : locals.findIdx? (· == name) with
  | none =>
      simp only [encode,Value.free,List.isEmpty_cons,Bool.false_eq_true,ite_false,found,evaluate]
      rw [global_lookup context locals values global (.reference name) state coherent available member length]
      simp only [resolve,found,Option.getD_some]
  | some index =>
      have bound : index < values.length := by
        rw [length]
        exact (List.findIdx?_eq_some_iff_findIdx_eq.mp found).1
      simp only [encode,Value.free,List.isEmpty_cons,Bool.false_eq_true,ite_false,found,evaluate,
        List.getElem?_append_left bound,resolve]

mutual
/-- Equal closed captures and reference resolution preserve the full stored profile plan. -/
theorem encode_evaluate (firstContext secondContext : List (Value Symbol Guard)) (value : Value Symbol Guard)
    (firstLocals secondLocals : List Reference) (firstValues secondValues : List (Abstract Atom))
    (first second : Value Symbol Guard → Abstract Atom) (state : State Symbol Guard) (coherent : Coherent state)
    (firstAvailable : Values state firstContext) (secondAvailable : Values state secondContext)
    (firstCovered : ∀ leaf ∈ leaves value, leaf ∈ firstContext)
    (secondCovered : ∀ leaf ∈ leaves value, leaf ∈ secondContext)
    (firstLength : firstValues.length = firstLocals.length) (secondLength : secondValues.length = secondLocals.length)
    (closed : ∀ captured, captured.free = [] → first captured = second captured)
    (agree : ∀ name, resolve firstLocals firstValues first name = resolve secondLocals secondValues second name) :
    evaluate (encode firstContext firstLocals value) (firstValues ++ firstContext.map first) =
      evaluate (encode secondContext secondLocals value) (secondValues ++ secondContext.map second) := by
  rw [encode.eq_def,encode.eq_def]
  split
  · rename_i capture
    have firstMember : value ∈ firstContext := firstCovered value (by rw [leaves.eq_def]; simp [capture])
    have secondMember : value ∈ secondContext := secondCovered value (by rw [leaves.eq_def]; simp [capture])
    simp only [evaluate]
    rw [global_lookup firstContext firstLocals firstValues first value state coherent firstAvailable firstMember firstLength,
      global_lookup secondContext secondLocals secondValues second value state coherent secondAvailable secondMember secondLength]
    exact closed value (List.isEmpty_iff.mp capture)
  · rename_i opened
    rw [leaves.eq_def] at firstCovered secondCovered
    simp only [opened,Bool.false_eq_true,ite_false] at firstCovered secondCovered
    cases value with
    | empty => simp [Value.free] at opened
    | reference name =>
        have same := (reference_evaluate firstContext firstLocals firstValues first name state coherent firstAvailable
          (firstCovered _ (by simp)) firstLength).trans ((agree name).trans
            (reference_evaluate secondContext secondLocals secondValues second name state coherent secondAvailable
              (secondCovered _ (by simp)) secondLength).symm)
        simpa only [encode,Value.free,List.isEmpty_cons,Bool.false_eq_true,ite_false] using same
    | node entry edges depth free =>
        rw [evaluate,evaluate,encodeEdges_evaluate firstContext secondContext edges firstLocals secondLocals firstValues secondValues
          first second state coherent firstAvailable secondAvailable firstCovered secondCovered firstLength secondLength closed agree]
    | union entry members depth free =>
        rw [evaluate,evaluate,encodeMany_evaluate firstContext secondContext members firstLocals secondLocals firstValues secondValues
          first second state coherent firstAvailable secondAvailable firstCovered secondCovered firstLength secondLength closed agree]
    | mu entry body depth ordinary =>
        simp only [evaluate,List.map_append,List.map_map,Function.comp_def]
        congr 1
        apply encode_evaluate firstContext secondContext body (.interned entry.identity :: firstLocals) (.interned entry.identity :: secondLocals)
          (some [Sum.inl ()] :: firstValues.map (mapNames Sum.inr))
          (some [Sum.inl ()] :: secondValues.map (mapNames Sum.inr))
          (fun captured => mapNames Sum.inr (first captured))
          (fun captured => mapNames Sum.inr (second captured)) state coherent firstAvailable secondAvailable firstCovered secondCovered
          (by simp [firstLength]) (by simp [secondLength])
        · intro captured capture
          rw [closed captured capture]
        · intro name
          rw [resolve_cons,resolve_cons]
          split
          · rfl
          · rw [resolve_map,resolve_map,agree]
termination_by sizeOf value

/-- Independent capture contexts preserve all ordered stored operand profiles. -/
theorem encodeMany_evaluate (firstContext secondContext : List (Value Symbol Guard)) (values : List (Value Symbol Guard))
    (firstLocals secondLocals : List Reference) (firstValues secondValues : List (Abstract Atom))
    (first second : Value Symbol Guard → Abstract Atom) (state : State Symbol Guard) (coherent : Coherent state)
    (firstAvailable : Values state firstContext) (secondAvailable : Values state secondContext)
    (firstCovered : ∀ leaf ∈ manyLeaves values, leaf ∈ firstContext)
    (secondCovered : ∀ leaf ∈ manyLeaves values, leaf ∈ secondContext)
    (firstLength : firstValues.length = firstLocals.length) (secondLength : secondValues.length = secondLocals.length)
    (closed : ∀ captured, captured.free = [] → first captured = second captured)
    (agree : ∀ name, resolve firstLocals firstValues first name = resolve secondLocals secondValues second name) :
    evaluateMany (encodeMany firstContext firstLocals values) (firstValues ++ firstContext.map first) =
      evaluateMany (encodeMany secondContext secondLocals values) (secondValues ++ secondContext.map second) := by
  cases values with
  | nil => simp only [encodeMany,evaluateMany]
  | cons head tail =>
      simp only [encodeMany,evaluateMany]
      rw [encode_evaluate firstContext secondContext head firstLocals secondLocals firstValues secondValues first second state coherent firstAvailable secondAvailable
        (fun leaf member => firstCovered leaf (by simp [manyLeaves,member]))
          (fun leaf member => secondCovered leaf (by simp [manyLeaves,member])) firstLength secondLength closed agree,
        encodeMany_evaluate firstContext secondContext tail firstLocals secondLocals firstValues secondValues first second state coherent firstAvailable secondAvailable
          (fun leaf member => firstCovered leaf (by simp [manyLeaves,member]))
          (fun leaf member => secondCovered leaf (by simp [manyLeaves,member])) firstLength secondLength closed agree]
termination_by sizeOf values

/-- Independent capture contexts preserve each stored edge viability test. -/
theorem encodeEdges_evaluate (firstContext secondContext : List (Value Symbol Guard)) (edges : List (EdgeValue Symbol Guard))
    (firstLocals secondLocals : List Reference) (firstValues secondValues : List (Abstract Atom))
    (first second : Value Symbol Guard → Abstract Atom) (state : State Symbol Guard) (coherent : Coherent state)
    (firstAvailable : Values state firstContext) (secondAvailable : Values state secondContext)
    (firstCovered : ∀ leaf ∈ edgeLeaves edges, leaf ∈ firstContext)
    (secondCovered : ∀ leaf ∈ edgeLeaves edges, leaf ∈ secondContext)
    (firstLength : firstValues.length = firstLocals.length) (secondLength : secondValues.length = secondLocals.length)
    (closed : ∀ captured, captured.free = [] → first captured = second captured)
    (agree : ∀ name, resolve firstLocals firstValues first name = resolve secondLocals secondValues second name) :
    evaluateEdges (encodeEdges firstContext firstLocals edges) (firstValues ++ firstContext.map first) =
      evaluateEdges (encodeEdges secondContext secondLocals edges) (secondValues ++ secondContext.map second) := by
  cases edges with
  | nil => simp only [encodeEdges,evaluateEdges]
  | cons head tail =>
      cases head with
      | mk entry children =>
          simp only [encodeEdges,evaluateEdges]
          rw [encodeMany_evaluate firstContext secondContext children firstLocals secondLocals firstValues secondValues first second state coherent firstAvailable secondAvailable
            (fun leaf member => firstCovered leaf (by simp [edgeLeaves,member]))
            (fun leaf member => secondCovered leaf (by simp [edgeLeaves,member])) firstLength secondLength closed agree,
            encodeEdges_evaluate firstContext secondContext tail firstLocals secondLocals firstValues secondValues first second state coherent firstAvailable secondAvailable
              (fun leaf member => firstCovered leaf (by simp [edgeLeaves,member]))
            (fun leaf member => secondCovered leaf (by simp [edgeLeaves,member])) firstLength secondLength closed agree]
termination_by sizeOf edges
end


end MicroCFTA.SourceCurrentStoredProfilePlan
