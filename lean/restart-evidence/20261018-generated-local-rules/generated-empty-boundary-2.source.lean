import MicroCFTA.SourceCurrentRetainedMuDirectedCase
import MicroCFTA.InternedFreshOrdinaryClosedCompletion

set_option linter.all true
set_option maxRecDepth 30000
set_option maxHeartbeats 5000000
set_option cbv.maxSteps 100000000

namespace MicroCFTA.GeneratedEmptyBoundary
open Cache InternedConstructorTemplates InternedProbeProvenance
open InternedNestedConstruction (Syntax Outcome)
open InternedFreshOrdinaryConstruction (build)
open InternedFreshOrdinaryStoredSubstitution (execute)
open InternedStoredSubstitution (Environment Replacements)
open InternedRecordDepthShape (shape)
open SourceEqualityRequiredCache (Ready Keeps)

private def source : Syntax Nat Bool := .binder false (.node [.mk 9 false [
  .binder false (.node [.mk 7 false [.var 0,.var 1]]),
  .binder false (.union [.node [.mk 7 false [.var 0]],.node [.mk 7 false [.var 1]]])]])
private def result (outcome : Outcome Nat Bool (Value Nat Bool)) : Value Nat Bool :=
  match outcome with | .done value _ => value | .pending .. => .empty
private def built := build source [] empty
private def root := result built
private def before := built.state
private def body : Value Nat Bool := match root with | .mu _ stored _ _ => stored | _ => .empty
private def own : InternedBinderProtocol.Reference := match root with
  | .mu entry _ _ _ => .interned entry.identity | _ => .depth
private def first := (children body)[0]?.getD .empty
private def second := (children body)[1]?.getD .empty
private def replacements : Environment Nat Bool := fun name => if name=own then some .empty else none
private def firstRun := execute first replacements before
private def middle := firstRun.state
private def secondRun := execute second replacements middle
private def after := secondRun.state
private def output := result secondRun
private def used : Value Nat Bool → Prop
  | .mu entry stored _ _ => .interned entry.identity ∈ stored.free
  | _ => False

private theorem built_done : build source [] empty = .done root before := by cbv
private theorem initial_ready : Ready before := SourceEqualityRequiredCache.constructed source root before built_done
private theorem root_available : Available before root :=
  (InternedFreshOrdinaryFacts.build_verified source [] empty InternedNestedFacts.empty_facts
    (by intro value member; cases member)).result root before built_done
private theorem body_available : Available before body :=
  root_available.children body (by cbv; exact List.mem_cons_self)
private theorem first_available : Available before first :=
  body_available.children first (by cbv; exact List.mem_cons_self)
private theorem second_available : Available before second :=
  body_available.children second (by cbv; exact List.mem_cons_of_mem _ List.mem_cons_self)
private theorem replacements_available (state : State Nat Bool) : Replacements state replacements := by
  intro name value found
  dsimp only [replacements] at found
  split at found
  · cases found; exact empty_available state
  · cases found
private theorem first_done : execute first replacements before = .done .empty middle := by cbv
private theorem second_done : execute second replacements middle = .done output after := by cbv
private theorem first_effect : Keeps before middle := by
  obtain ⟨value,state,called,kept,_,_⟩ := SourceCurrentStoredReconstruction.execute first replacements before
    initial_ready first_available (replacements_available before)
  have equal := Outcome.done.inj (called.symm.trans first_done)
  cases equal.1
  cases equal.2
  exact kept
private theorem second_effect : Keeps middle after := by
  obtain ⟨value,state,called,kept,_,_⟩ := SourceCurrentStoredReconstruction.execute second replacements middle
    first_effect.ready (first_effect.available second second_available) (replacements_available middle)
  have equal := Outcome.done.inj (called.symm.trans second_done)
  cases equal.1
  cases equal.2
  exact kept

private theorem checked : ∃ expression : Syntax Nat Bool, ∃ root first second : Value Nat Bool,
    ∃ before middle after : State Nat Bool, ∃ environment : Environment Nat Bool, ∃ output : Value Nat Bool,
      build expression [] empty = .done root before ∧ Ready before ∧
      Available before first ∧ Available before second ∧ used first ∧ used second ∧
      shape first = shape second ∧ first.referenceOf ≠ .empty ∧ second.referenceOf ≠ .empty ∧
      Replacements before environment ∧ execute first environment before = .done .empty middle ∧
      execute second environment middle = .done output after ∧ output.referenceOf ≠ .empty ∧
      Keeps before middle ∧ Keeps middle after := by
  refine ⟨source,root,first,second,before,middle,after,replacements,output,built_done,initial_ready,
    first_available,second_available,?_,?_,?_,?_,?_,replacements_available before,first_done,second_done,?_,first_effect,second_effect⟩
  · cbv; exact List.mem_cons_of_mem _ List.mem_cons_self
  · cbv; exact List.mem_cons_of_mem _ List.mem_cons_self
  · cbv
  · cbv; intro impossible; cases impossible
  · cbv; intro impossible; cases impossible
  · cbv; intro impossible; cases impossible

/-- Equal decoded shapes do not determine physical Empty after stored substitution. -/
theorem witness : ∃ expression : Syntax Nat Bool, ∃ root first second : Value Nat Bool,
    ∃ before middle after : State Nat Bool, ∃ environment : Environment Nat Bool, ∃ output : Value Nat Bool,
      build expression [] empty = .done root before ∧ Ready before ∧
      Available before first ∧ Available before second ∧ used first ∧ used second ∧
      shape first = shape second ∧ first.referenceOf ≠ .empty ∧ second.referenceOf ≠ .empty ∧
      Replacements before environment ∧ execute first environment before = .done .empty middle ∧
      execute second environment middle = .done output after ∧ output.referenceOf ≠ .empty ∧
      Keeps before middle ∧ Keeps middle after := checked

end MicroCFTA.GeneratedEmptyBoundary
