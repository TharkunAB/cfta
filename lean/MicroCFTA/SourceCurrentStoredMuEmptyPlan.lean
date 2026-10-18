import MicroCFTA.SourceCurrentStoredEmptyInterpreter
import MicroCFTA.InternedStoredSubstitutionRebind

/-!
# Symbolic local plans for open stored Mu execution

A local slot and a resolved reference leaf give the same full profile plan.
The proof retains closed captures and every nested smart binder. Actual
open Mu execution then tests the strict stored body and removes the outer
symbolic local. This does not compare a writer body with its ordinary probe.
-/
namespace MicroCFTA.SourceCurrentStoredMuEmptyPlan
open Cache InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedNestedConstruction (Outcome)
open InternedFreshOrdinaryStoredSubstitution (execute)
open InternedStoredSubstitution (Environment Replacements leaves manyLeaves edgeLeaves input slot encode encodeMany encodeEdges)
open InternedStoredSubstitutionScope (slot_lookup)
open InternedNestedProvenance (Values)
open InternedProfileSemantics (Abstract evaluate evaluateMany evaluateEdges mapNames lower isEmpty)
open InternedRootProfile (profile)
open InternedBinderProtocol (Reference)
open SourceEqualityRequiredCache (Ready)

private def resolve (locals : List Reference) (values : List (Abstract Atom))
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
private theorem encode_evaluate (context : List (Value Symbol Guard)) (value : Value Symbol Guard)
    (firstLocals secondLocals : List Reference) (firstValues secondValues : List (Abstract Atom))
    (first second : Value Symbol Guard → Abstract Atom) (state : State Symbol Guard) (coherent : Coherent state)
    (available : Values state context) (covered : ∀ leaf ∈ leaves value, leaf ∈ context)
    (firstLength : firstValues.length = firstLocals.length) (secondLength : secondValues.length = secondLocals.length)
    (closed : ∀ captured ∈ context, captured.free = [] → first captured = second captured)
    (agree : ∀ name, resolve firstLocals firstValues first name = resolve secondLocals secondValues second name) :
    evaluate (encode context firstLocals value) (firstValues ++ context.map first) =
      evaluate (encode context secondLocals value) (secondValues ++ context.map second) := by
  rw [encode.eq_def,encode.eq_def]
  split
  · rename_i capture
    have member : value ∈ context := covered value (by rw [leaves.eq_def]; simp [capture])
    simp only [evaluate]
    rw [global_lookup context firstLocals firstValues first value state coherent available member firstLength,
      global_lookup context secondLocals secondValues second value state coherent available member secondLength]
    exact closed value member (List.isEmpty_iff.mp capture)
  · rename_i opened
    rw [leaves.eq_def] at covered
    simp only [opened,Bool.false_eq_true,ite_false] at covered
    cases value with
    | empty => simp [Value.free] at opened
    | reference name =>
        have same := (reference_evaluate context firstLocals firstValues first name state coherent available
          (covered _ (by simp)) firstLength).trans ((agree name).trans
            (reference_evaluate context secondLocals secondValues second name state coherent available
              (covered _ (by simp)) secondLength).symm)
        simpa only [encode,Value.free,List.isEmpty_cons,Bool.false_eq_true,ite_false] using same
    | node entry edges depth free =>
        rw [evaluate,evaluate,encodeEdges_evaluate context edges firstLocals secondLocals firstValues secondValues
          first second state coherent available covered firstLength secondLength closed agree]
    | union entry members depth free =>
        rw [evaluate,evaluate,encodeMany_evaluate context members firstLocals secondLocals firstValues secondValues
          first second state coherent available covered firstLength secondLength closed agree]
    | mu entry body depth ordinary =>
        simp only [evaluate,List.map_append,List.map_map,Function.comp_def]
        congr 1
        apply encode_evaluate context body (.interned entry.identity :: firstLocals) (.interned entry.identity :: secondLocals)
          (some [Sum.inl ()] :: firstValues.map (mapNames Sum.inr))
          (some [Sum.inl ()] :: secondValues.map (mapNames Sum.inr))
          (fun captured => mapNames Sum.inr (first captured))
          (fun captured => mapNames Sum.inr (second captured)) state coherent available covered
          (by simp [firstLength]) (by simp [secondLength])
        · intro captured member capture
          rw [closed captured member capture]
        · intro name
          rw [resolve_cons,resolve_cons]
          split
          · rfl
          · rw [resolve_map,resolve_map,agree]
termination_by sizeOf value

private theorem encodeMany_evaluate (context : List (Value Symbol Guard)) (values : List (Value Symbol Guard))
    (firstLocals secondLocals : List Reference) (firstValues secondValues : List (Abstract Atom))
    (first second : Value Symbol Guard → Abstract Atom) (state : State Symbol Guard) (coherent : Coherent state)
    (available : Values state context) (covered : ∀ leaf ∈ manyLeaves values, leaf ∈ context)
    (firstLength : firstValues.length = firstLocals.length) (secondLength : secondValues.length = secondLocals.length)
    (closed : ∀ captured ∈ context, captured.free = [] → first captured = second captured)
    (agree : ∀ name, resolve firstLocals firstValues first name = resolve secondLocals secondValues second name) :
    evaluateMany (encodeMany context firstLocals values) (firstValues ++ context.map first) =
      evaluateMany (encodeMany context secondLocals values) (secondValues ++ context.map second) := by
  cases values with
  | nil => simp only [encodeMany,evaluateMany]
  | cons head tail =>
      simp only [encodeMany,evaluateMany]
      rw [encode_evaluate context head firstLocals secondLocals firstValues secondValues first second state coherent available
        (fun leaf member => covered leaf (by simp [manyLeaves,member])) firstLength secondLength closed agree,
        encodeMany_evaluate context tail firstLocals secondLocals firstValues secondValues first second state coherent available
          (fun leaf member => covered leaf (by simp [manyLeaves,member])) firstLength secondLength closed agree]
termination_by sizeOf values

private theorem encodeEdges_evaluate (context : List (Value Symbol Guard)) (edges : List (EdgeValue Symbol Guard))
    (firstLocals secondLocals : List Reference) (firstValues secondValues : List (Abstract Atom))
    (first second : Value Symbol Guard → Abstract Atom) (state : State Symbol Guard) (coherent : Coherent state)
    (available : Values state context) (covered : ∀ leaf ∈ edgeLeaves edges, leaf ∈ context)
    (firstLength : firstValues.length = firstLocals.length) (secondLength : secondValues.length = secondLocals.length)
    (closed : ∀ captured ∈ context, captured.free = [] → first captured = second captured)
    (agree : ∀ name, resolve firstLocals firstValues first name = resolve secondLocals secondValues second name) :
    evaluateEdges (encodeEdges context firstLocals edges) (firstValues ++ context.map first) =
      evaluateEdges (encodeEdges context secondLocals edges) (secondValues ++ context.map second) := by
  cases edges with
  | nil => simp only [encodeEdges,evaluateEdges]
  | cons head tail =>
      cases head with
      | mk entry children =>
          simp only [encodeEdges,evaluateEdges]
          rw [encodeMany_evaluate context children firstLocals secondLocals firstValues secondValues first second state coherent available
            (fun leaf member => covered leaf (by simp [edgeLeaves,member])) firstLength secondLength closed agree,
            encodeEdges_evaluate context tail firstLocals secondLocals firstValues secondValues first second state coherent available
              (fun leaf member => covered leaf (by simp [edgeLeaves,member])) firstLength secondLength closed agree]
termination_by sizeOf edges
end

/-- A symbolic local and the same resolved reference leaf give equal full stored-body profiles. -/
theorem rebind_profile (body : Value Symbol Guard) (own : Reference)
    (environment : Environment Symbol Guard) (source : State Symbol Guard) (coherent : Coherent source)
    (available : Available source body) :
    evaluate (encode (leaves body) [own] body)
        (some [Sum.inl ()] :: ((leaves body).map (fun leaf => profile (input environment leaf))).map (mapNames Sum.inr)) =
      evaluate (encode (leaves body) [] body) ((leaves body).map (fun leaf => match leaf with
        | .reference name => if own = name then some [Sum.inl ()] else mapNames Sum.inr (profile (input environment leaf))
        | _ => mapNames Sum.inr (profile (input environment leaf)))) := by
  simp only [List.map_map,Function.comp_def]
  apply encode_evaluate (leaves body) body [own] [] [some [Sum.inl ()]] []
    (fun leaf => mapNames Sum.inr (profile (input environment leaf)))
    (fun leaf => match leaf with
      | .reference name => if own = name then some [Sum.inl ()] else mapNames Sum.inr (profile (input environment leaf))
      | _ => mapNames Sum.inr (profile (input environment leaf))) source coherent
    (InternedStoredSubstitution.leaves_available body source available) (fun _ member => member) rfl rfl
  · intro captured _ closed
    cases captured <;> try rfl
    simp [Value.free] at closed
  · intro name
    rw [resolve_cons]
    simp only [resolve,List.findIdx?_nil]

/-- Actual open Mu execution tests its original body with a symbolic self leaf, then removes that local. -/
theorem open_execute [DecidableEq (EdgeKey Symbol Guard)]
    (entry : Interned InternedBinderProtocol.NodeKey) (body depth ordinary : Value Symbol Guard)
    (environment : Environment Symbol Guard) (before : State Symbol Guard) (ready : Ready before)
    (available : Available before (.mu entry body depth ordinary)) (replacements : Replacements before environment)
    (opened : (Value.mu entry body depth ordinary).free.isEmpty = false)
    (result : Value Symbol Guard) (after : State Symbol Guard)
    (actual : execute (.mu entry body depth ordinary) environment before = .done result after) :
    (result.referenceOf == .empty) = isEmpty (lower
      (evaluate (encode (leaves body) [] body) ((leaves body).map (fun leaf => match leaf with
        | .reference name => if .interned entry.identity = name then some [Sum.inl ()]
            else mapNames Sum.inr (profile (input environment leaf))
        | _ => mapNames Sum.inr (profile (input environment leaf)))))) := by
  rw [SourceCurrentStoredEmptyInterpreter.execute_test _ environment before ready available replacements result after actual,
    SourceCurrentStoredEmptyInterpreter.open_mu entry body depth ordinary environment opened,
    rebind_profile body (.interned entry.identity) environment before ready.semantic.1.normal.facts.coherent
      (available.children body (by simp [InternedProbeProvenance.children]))]

end MicroCFTA.SourceCurrentStoredMuEmptyPlan
