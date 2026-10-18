import MicroCFTA.SourceCurrentEmptyProjectionInputs

set_option linter.all true
set_option maxRecDepth 30000

namespace MicroCFTA.EmptyProjectionInputIntegration
open Cache InternedConstructorTemplates InternedProbeProvenance
open InternedNestedConstruction (Syntax Outcome)
open InternedFreshOrdinaryConstruction (build)
open InternedFreshOrdinaryLiveInputs (input)
open InternedStoredSubstitution (Environment Replacements)
open InternedBinderProtocol (Reference)
open InternedRootProfile (Profile profile)
open SourceCurrentStoredProfileEmptyProjection (canonical)
open SourceCurrentReaderReplacementSlots (Paired)
open SourceEqualityRequiredCache (Ready)
private def inputs : List (Sum (Value Nat Bool) Unit) := [.inl (.reference (.uninterned 10)),.inr ()]
private def firstNames : Unit → Reference := fun _ => .interned 999
private def secondNames : Unit → Reference := fun _ => .depth
private def first : Environment Nat Bool := fun name => if name = .uninterned 10 then some (.reference (.uninterned 20)) else none
private def second : Environment Nat Bool := fun _ => none
private def expression : Syntax Nat Bool := .union [.var 0,.var 1]
private theorem ready : Ready (empty : State Nat Bool) :=
  SourceEqualityRequiredCache.constructed .empty .empty empty (by rw [build])
private theorem first_replacements : Replacements empty first := by
  intro name value found
  unfold first at found
  split at found
  · obtain rfl := Option.some.inj found
    exact InternedNestedProvenance.ordinary_available empty _
  · cases found
private theorem second_replacements : Replacements empty second := by
  intro name value found
  cases found
private theorem paired : Paired (fun a b => (a.referenceOf == .empty) = (b.referenceOf == .empty)) first second
    (inputs.map (input firstNames)) (inputs.map (input secondNames)) := by
  exact .cons (by cbv) (.cons (by cbv) .nil)
private theorem absent : ¬Available (empty : State Nat Bool) (.reference (.interned 999)) := by
  intro available
  obtain ⟨key,found⟩ := available.issued 999 (by simp [Value.free])
  cases found

private theorem checked :
    ∃ (expression : Syntax Nat Bool) (inputs : List (Sum (Value Nat Bool) Unit))
      (firstNames secondNames : Unit → Reference) (first second : Environment Nat Bool),
      expression = .union [.var 0,.var 1] ∧
      inputs = [.inl (.reference (.uninterned 10)),.inr ()] ∧
      firstNames () = .interned 999 ∧ secondNames () = .depth ∧
      Ready (empty : State Nat Bool) ∧ Replacements empty first ∧ Replacements empty second ∧
      first (.uninterned 10) ≠ second (.uninterned 10) ∧
      ¬Available (empty : State Nat Bool) (.reference (.interned 999)) ∧
      Paired (fun a b => (a.referenceOf == .empty) = (b.referenceOf == .empty)) first second
        (inputs.map (input firstNames)) (inputs.map (input secondNames)) ∧
      SourceCurrentScopedProfileInputs.Compatible expression inputs firstNames secondNames
        (canonical (fun name => profile ((first name).getD (.reference name))))
        (canonical (fun name => profile ((second name).getD (.reference name)))) := by
  refine ⟨expression,inputs,firstNames,secondNames,first,second,rfl,rfl,rfl,rfl,ready,
    first_replacements,second_replacements,?_,absent,paired,?_⟩
  · simp [first,second]
  · exact SourceCurrentEmptyProjectionInputs.compatible empty ready expression inputs firstNames secondNames
      first second paired first_replacements second_replacements

/-- Fixed reference maps may differ, and an unmapped varying interned name need not be resident. -/
theorem fixed_reference_and_missing_default :
    ∃ (expression : Syntax Nat Bool) (inputs : List (Sum (Value Nat Bool) Unit))
      (firstNames secondNames : Unit → Reference) (first second : Environment Nat Bool),
      expression = .union [.var 0,.var 1] ∧
      inputs = [.inl (.reference (.uninterned 10)),.inr ()] ∧
      firstNames () = .interned 999 ∧ secondNames () = .depth ∧
      Ready (empty : State Nat Bool) ∧ Replacements empty first ∧ Replacements empty second ∧
      first (.uninterned 10) ≠ second (.uninterned 10) ∧
      ¬Available (empty : State Nat Bool) (.reference (.interned 999)) ∧
      Paired (fun a b => (a.referenceOf == .empty) = (b.referenceOf == .empty)) first second
        (inputs.map (input firstNames)) (inputs.map (input secondNames)) ∧
      SourceCurrentScopedProfileInputs.Compatible expression inputs firstNames secondNames
        (canonical (fun name => profile ((first name).getD (.reference name))))
        (canonical (fun name => profile ((second name).getD (.reference name)))) := checked

end MicroCFTA.EmptyProjectionInputIntegration

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.proofs true
set_option pp.proofs.threshold 254
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000

#check @MicroCFTA.EmptyProjectionInputIntegration.fixed_reference_and_missing_default
#print MicroCFTA.EmptyProjectionInputIntegration.fixed_reference_and_missing_default
#print axioms MicroCFTA.EmptyProjectionInputIntegration.fixed_reference_and_missing_default
