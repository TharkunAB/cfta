import MicroCFTA.InternedStoredPlanFreeSupport
import MicroCFTA.SourceCurrentStoredMuTrackedProfile

/-!
# Stored substitution as a function of reference profiles

The function interprets the actual stored encoding and its captured leaves.
Its free-name support uses coherent resident records. Actual execution
supplies an equivalent profile from initial semantic readiness.
This does not assert parametric correctness of an arbitrary cache writer.
-/
namespace MicroCFTA.SourceCurrentStoredProfileFunction
open InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedStoredSubstitution (Environment Replacements leaves input encode)
open InternedProfileSemantics (Abstract evaluate evaluateMany evaluateEdges mapNames)
open InternedRootProfile (Profile profile Equivalent)
open InternedFreeNameIndexedOrigins (Uses UsesMany UsesEdges)
open InternedNestedConstruction (Syntax EdgeSyntax)
open InternedBinderProtocol (Reference)
open SourceEqualityRequiredCache (Ready)

/-- Interpret the full stored encoding with the supplied reference profiles. -/
def denote (value : Value Symbol Guard) (assignment : Reference → Profile) : Profile :=
  evaluate (encode (leaves value) [] value) ((leaves value).map (fun leaf => match leaf with
    | .reference name => assignment name
    | _ => profile leaf))

private theorem mapped_lookup {Atom Other : Type} (function : Atom → Other)
    (values : List (Abstract Atom)) (index : Nat) :
    (values.map (mapNames function))[index]?.getD (some []) =
      mapNames function (values[index]?.getD (some [])) := by
  cases found : values[index]? <;> simp [List.getElem?_map, found, mapNames]

mutual
private theorem evaluate_congr {Atom : Type} (expression : Syntax Symbol Guard)
    (first second : List (Abstract Atom))
    (agree : ∀ index, Uses expression index → first[index]?.getD (some []) = second[index]?.getD (some [])) :
    evaluate expression first = evaluate expression second := by
  cases expression with
  | empty => simp only [evaluate]
  | var index => simpa only [evaluate] using agree index (by rw [Uses])
  | node edges =>
      simp only [Uses] at agree
      rw [evaluate, evaluate, evaluateEdges_congr edges first second agree]
  | union members =>
      simp only [Uses] at agree
      rw [evaluate, evaluate, evaluateMany_congr members first second agree]
  | binder smart body =>
      cases smart with
      | false => simp only [evaluate]
      | true =>
          rw [evaluate, evaluate]
          apply congrArg InternedProfileSemantics.lower
          apply evaluate_congr body
          intro index used
          cases index with
          | zero => rfl
          | succ index =>
              simp only [List.getElem?_cons_succ, mapped_lookup]
              exact congrArg (mapNames Sum.inr) (agree index (by simpa only [Uses] using used))
termination_by sizeOf expression

private theorem evaluateMany_congr {Atom : Type} (expressions : List (Syntax Symbol Guard))
    (first second : List (Abstract Atom))
    (agree : ∀ index, UsesMany expressions index → first[index]?.getD (some []) = second[index]?.getD (some [])) :
    evaluateMany expressions first = evaluateMany expressions second := by
  cases expressions with
  | nil => simp only [evaluateMany]
  | cons expression rest =>
      simp only [UsesMany] at agree
      rw [evaluateMany, evaluateMany]
      congr 1
      · exact evaluate_congr expression first second (fun index used => agree index (Or.inl used))
      · exact evaluateMany_congr rest first second (fun index used => agree index (Or.inr used))
termination_by sizeOf expressions

private theorem evaluateEdges_congr {Atom : Type} (edges : List (EdgeSyntax Symbol Guard))
    (first second : List (Abstract Atom))
    (agree : ∀ index, UsesEdges edges index → first[index]?.getD (some []) = second[index]?.getD (some [])) :
    evaluateEdges edges first = evaluateEdges edges second := by
  cases edges with
  | nil => simp only [evaluateEdges]
  | cons edge rest =>
      cases edge with
      | mk symbol guard children =>
          simp only [UsesEdges] at agree
          rw [evaluateEdges, evaluateEdges,
            evaluateMany_congr children first second (fun index used => agree index (Or.inl used)),
            evaluateEdges_congr rest first second (fun index used => agree index (Or.inr used))]
termination_by sizeOf edges
end

/-- An empty stored value has the empty pure profile. -/
theorem empty (assignment : Reference → Profile) : denote (.empty : Value Symbol Guard) assignment = some [] := by
  simp [denote, leaves, encode, InternedStoredSubstitution.slot, Value.free, evaluate, profile]

/-- A stored reference selects its assigned profile. -/
theorem reference (name : Reference) (assignment : Reference → Profile) :
    denote (.reference name : Value Symbol Guard) assignment = assignment name := by
  simp [denote, leaves, encode, InternedStoredSubstitution.slot, Value.free, evaluate]

/-- A closed stored value keeps its complete original root profile. -/
theorem closed (value : Value Symbol Guard) (assignment : Reference → Profile) (closed : value.free = []) :
    denote value assignment = profile value := by
  have collected : leaves value = [value] := by rw [leaves.eq_def]; simp [closed]
  have encoded : encode [value] [] value = .var 0 := by
    rw [encode.eq_def]
    simp [closed, InternedStoredSubstitution.slot]
  rw [denote, collected, encoded, evaluate]
  cases value <;> simp_all [Value.free]

/-- Coherent resident storage makes the function depend only on the value's free names. -/
theorem congr (value : Value Symbol Guard) (state : State Symbol Guard)
    (coherent : Coherent state) (available : Available state value)
    (first second : Reference → Profile) (agree : ∀ name ∈ value.free, first name = second name) :
    denote value first = denote value second := by
  apply evaluate_congr
  intro index used
  cases found : (leaves value)[index]? with
  | none => simp [List.getElem?_map, found]
  | some leaf =>
      simp only [List.getElem?_map, found, Option.map_some, Option.getD_some]
      cases leaf with
      | reference name =>
          apply agree name
          exact (InternedStoredPlanFreeSupport.encode_free (leaves value) [] value state coherent
            (InternedStoredSubstitution.leaves_available value state available) available
            (fun _ member => member) index (.reference name) found name (by simp [Value.free])
            (by simpa only [List.length_nil, Nat.zero_add] using used)).1
      | empty | node | union | mu => rfl

/-- Actual stored execution supplies the function's profile from initial ready inputs. -/
theorem execute [DecidableEq (EdgeKey Symbol Guard)] (value : Value Symbol Guard)
    (environment : Environment Symbol Guard) (before : State Symbol Guard) (ready : Ready before)
    (available : Available before value) (replacements : Replacements before environment)
    (result : Value Symbol Guard) (after : State Symbol Guard)
    (actual : InternedFreshOrdinaryStoredSubstitution.execute value environment before = .done result after) :
    Equivalent (profile result) (denote value (fun name => profile ((environment name).getD (.reference name)))) := by
  let inputs := (leaves value).map (input environment)
  let plan := encode (leaves value) [] value
  have context : InternedFreshOrdinaryContext.Context before inputs :=
    ⟨ready.semantic.1.normal, InternedStoredSubstitution.inputs_available value environment before available replacements,
      ready.semantic.1.profiles, ready.semantic.1.freeNames⟩
  have called : InternedFreshOrdinaryConstruction.build plan inputs before = .done result after := actual
  have matched := (InternedFreshOrdinaryProfiles.build_profile plan inputs before context.normal context.inputs
    context.profiles).result result after called
  have mapped : (leaves value).map (fun leaf => profile (input environment leaf)) =
      (leaves value).map (fun leaf => match leaf with
        | .reference name => profile ((environment name).getD (.reference name))
        | _ => profile leaf) := by
    apply List.map_congr_left
    intro leaf _
    cases leaf <;> rfl
  simpa only [inputs, plan, List.map_map, Function.comp_def, mapped, denote] using matched

end MicroCFTA.SourceCurrentStoredProfileFunction
