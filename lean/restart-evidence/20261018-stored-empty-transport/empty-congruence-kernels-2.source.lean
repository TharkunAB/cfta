import MicroCFTA.SourceCurrentStoredEmptyCongruence
import MicroCFTA.SourceCurrentStoredReconstruction

set_option linter.all true
set_option maxRecDepth 30000
set_option maxHeartbeats 5000000
set_option cbv.maxSteps 100000000

namespace MicroCFTA.EmptyCongruenceKernels
open Cache InternedConstructorTemplates InternedProbeProvenance
open InternedNestedConstruction (Syntax Outcome)
open InternedFreshOrdinaryConstruction (build)
open InternedFreshOrdinaryStoredSubstitution (execute)
open InternedStoredSubstitution (Environment Replacements)
open SourceEqualityRequiredCache (Ready Keeps)

private def source : Syntax Nat Bool := .binder false (.node [.mk 9 false [
  .binder false (.node [.mk 7 false [.var 0,.var 1]]),
  .node [.mk 1 false []],.node [.mk 2 false []]]])
private def result (outcome : Outcome Nat Bool (Value Nat Bool)) : Value Nat Bool :=
  match outcome with | .done value _ => value | .pending .. => .empty
private def built := build source [] empty
private def root := result built
private def before := built.state
private def body : Value Nat Bool := match root with | .mu _ stored _ _ => stored | _ => .empty
private def own : InternedBinderProtocol.Reference := match root with
  | .mu entry _ _ _ => .interned entry.identity | _ => .depth
private def value := (children body)[0]?.getD .empty
private def firstReplacement := (children body)[1]?.getD .empty
private def secondReplacement := (children body)[2]?.getD .empty
private def first : Environment Nat Bool := fun name => if name=own then some firstReplacement else none
private def second : Environment Nat Bool := fun name => if name=own then some secondReplacement else none
private def firstRun := execute value first before
private def left := result firstRun
private def middle := firstRun.state
private def secondRun := execute value second middle
private def right := result secondRun
private def after := secondRun.state
private def used : Value Nat Bool → Prop
  | .mu entry stored _ _ => .interned entry.identity ∈ stored.free
  | _ => False

private theorem built_done : build source [] empty = .done root before := by cbv
private theorem ready : Ready before := SourceEqualityRequiredCache.constructed source root before built_done
private theorem root_available : Available before root :=
  (InternedFreshOrdinaryFacts.build_verified source [] empty InternedNestedFacts.empty_facts
    (by intro value member; cases member)).result root before built_done
private theorem body_available : Available before body :=
  root_available.children body (by cbv; exact List.mem_cons_self)
private theorem value_available : Available before value :=
  body_available.children value (by cbv; exact List.mem_cons_self)
private theorem first_available : Available before firstReplacement :=
  body_available.children firstReplacement (by cbv; exact List.mem_cons_of_mem _ List.mem_cons_self)
private theorem second_available : Available before secondReplacement :=
  body_available.children secondReplacement (by cbv; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))
private theorem first_replacements : Replacements before first := by
  intro name value found
  dsimp only [first] at found
  split at found
  · cases found; exact first_available
  · cases found
private theorem first_done : execute value first before = .done left middle := by cbv
private theorem first_effect : Keeps before middle := by
  obtain ⟨value,state,called,kept,_,_⟩ := SourceCurrentStoredReconstruction.execute value first before
    ready value_available first_replacements
  have equal := Outcome.done.inj (called.symm.trans first_done)
  cases equal.1
  cases equal.2
  exact kept
private theorem second_replacements : Replacements middle second := by
  intro name value found
  dsimp only [second] at found
  split at found
  · cases found; exact first_effect.available secondReplacement second_available
  · cases found
private theorem second_done : execute value second middle = .done right after := by cbv
private theorem second_effect : Keeps middle after := by
  obtain ⟨value,state,called,kept,_,_⟩ := SourceCurrentStoredReconstruction.execute value second middle
    first_effect.ready (first_effect.available value value_available) second_replacements
  have equal := Outcome.done.inj (called.symm.trans second_done)
  cases equal.1
  cases equal.2
  exact kept
private theorem agree : ∀ name ∈ value.free,
    (((first name).getD (.reference name)).referenceOf == .empty) =
      (((second name).getD (.reference name)).referenceOf == .empty) := by
  intro name _
  by_cases selected : name=own
  · simp only [first,second,ite_eq_left selected,Option.getD_some]
    cbv
  · simp only [first,second,ite_eq_right selected]
private theorem empty_equal : (left.referenceOf == .empty) = (right.referenceOf == .empty) :=
  SourceCurrentStoredEmptyCongruence.execute_same value first second before middle ready first_effect.ready
    value_available (first_effect.available value value_available) first_replacements second_replacements
    left middle right after first_done second_done agree

private theorem checked : ∃ expression : Syntax Nat Bool, ∃ root value firstReplacement secondReplacement : Value Nat Bool,
    ∃ before middle after : State Nat Bool, ∃ first second : Environment Nat Bool, ∃ left right : Value Nat Bool,
      build expression [] empty = .done root before ∧ Ready before ∧ Available before value ∧ used value ∧
      Available before firstReplacement ∧ Available before secondReplacement ∧ firstReplacement ≠ secondReplacement ∧
      firstReplacement.referenceOf ≠ .empty ∧ secondReplacement.referenceOf ≠ .empty ∧
      (∃ name ∈ value.free, first name = some firstReplacement ∧ second name = some secondReplacement) ∧
      Replacements before first ∧ Replacements middle second ∧
      (∀ name ∈ value.free, (((first name).getD (.reference name)).referenceOf == .empty) =
        (((second name).getD (.reference name)).referenceOf == .empty)) ∧
      execute value first before = .done left middle ∧ execute value second middle = .done right after ∧
      left ≠ right ∧ left.referenceOf ≠ .empty ∧ right.referenceOf ≠ .empty ∧
      (left.referenceOf == .empty) = (right.referenceOf == .empty) ∧
      Keeps before middle ∧ Keeps middle after := by
  refine ⟨source,root,value,firstReplacement,secondReplacement,before,middle,after,first,second,left,right,
    built_done,ready,value_available,?_,first_available,second_available,?_,?_,?_,?_,first_replacements,second_replacements,agree,
    first_done,second_done,?_,?_,?_,empty_equal,first_effect,second_effect⟩
  · cbv; exact List.mem_cons_of_mem _ List.mem_cons_self
  · cbv; intro impossible; cases impossible
  · cbv; intro impossible; cases impossible
  · cbv; intro impossible; cases impossible
  · refine ⟨own,?_,?_,?_⟩
    · cbv; exact List.mem_cons_self
    · simp only [first,ite_true]
    · simp only [second,ite_true]
  · cbv; intro impossible; cases impossible
  · cbv; intro impossible; cases impossible
  · cbv; intro impossible; cases impossible

/-- Distinct source-built nonempty replacements preserve Empty while their actual recursive outputs differ. -/
theorem witness : ∃ expression : Syntax Nat Bool, ∃ root value firstReplacement secondReplacement : Value Nat Bool,
    ∃ before middle after : State Nat Bool, ∃ first second : Environment Nat Bool, ∃ left right : Value Nat Bool,
      build expression [] empty = .done root before ∧ Ready before ∧ Available before value ∧ used value ∧
      Available before firstReplacement ∧ Available before secondReplacement ∧ firstReplacement ≠ secondReplacement ∧
      firstReplacement.referenceOf ≠ .empty ∧ secondReplacement.referenceOf ≠ .empty ∧
      (∃ name ∈ value.free, first name = some firstReplacement ∧ second name = some secondReplacement) ∧
      Replacements before first ∧ Replacements middle second ∧
      (∀ name ∈ value.free, (((first name).getD (.reference name)).referenceOf == .empty) =
        (((second name).getD (.reference name)).referenceOf == .empty)) ∧
      execute value first before = .done left middle ∧ execute value second middle = .done right after ∧
      left ≠ right ∧ left.referenceOf ≠ .empty ∧ right.referenceOf ≠ .empty ∧
      (left.referenceOf == .empty) = (right.referenceOf == .empty) ∧
      Keeps before middle ∧ Keeps middle after := checked

end MicroCFTA.EmptyCongruenceKernels
