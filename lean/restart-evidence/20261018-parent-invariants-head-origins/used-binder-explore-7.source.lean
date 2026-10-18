import MicroCFTA.SourceCurrentStoredNormalizedPlans
import MicroCFTA.SourceCurrentStoredProbeCompatibility
import MicroCFTA.SourceCurrentNestedSourceInertBinder

set_option linter.all true
set_option maxHeartbeats 3000000
set_option maxRecDepth 30000

namespace MicroCFTA.UsedBinderExplore
open Cache InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedNestedConstruction (Syntax Outcome)
open InternedNestedProvenance (Values)
open InternedFreshOrdinaryConstruction InternedFreshOrdinaryFacts
open InternedBinderProtocol (Reference NodeKey)
open SourceEqualityRequiredCache (Ready Keeps)
open SourceCurrentNativeMuPublication (Publication History)

private def output (outcome : Outcome Nat Bool (Value Nat Bool)) :=
  match outcome with | .done value _ => value | .pending .. => .empty
private def source : Syntax Nat Bool :=
  .binder false (.node [.mk 7 false [.union [.var 1,.var 2],.var 0]])
private def firstInputs : List (Value Nat Bool) := [.reference .depth,.reference .depth]
private def secondInputs : List (Value Nat Bool) := [.reference .depth,.reference (.uninterned 0)]
private def firstCall := build source firstInputs empty
private def first := output firstCall
private def middle := firstCall.state
private def secondCall := build source secondInputs middle
private def second := output secondCall
private def reader := secondCall.state
private theorem firstDone : build source firstInputs empty = .done first middle := by cbv
private theorem secondDone : build source secondInputs middle = .done second reader := by cbv

private def parts : Value Nat Bool → Interned NodeKey × Value Nat Bool × Value Nat Bool × Value Nat Bool
  | .mu entry body depth ordinary => (entry,body,depth,ordinary)
  | _ => (⟨0,.node []⟩,.empty,.empty,.empty)
private def firstEntry := (parts first).1
private def firstBody := (parts first).2.1
private def secondEntry := (parts second).1
private def secondBody := (parts second).2.1
private def firstDepth := (parts first).2.2.1
private def firstOrdinary := (parts first).2.2.2
private def secondDepth := (parts second).2.2.1
private def secondOrdinary := (parts second).2.2.2
private theorem firstShape : first = .mu firstEntry firstBody firstDepth firstOrdinary := by cbv
private theorem secondShape : second = .mu secondEntry secondBody secondDepth secondOrdinary := by cbv
private def environment : InternedStoredSubstitution.Environment Nat Bool := fun _ => some .empty

private theorem not_related :
    ¬ SourceCurrentStoredNormalizedPlans.Related [] [] [] [] environment environment first second := by
  intro related
  rw [SourceCurrentStoredNormalizedPlans.Related.eq_def] at related
  have opened : first.free.isEmpty = false := by cbv
  simp only [opened,Bool.false_eq_true,ite_false] at related
  rw [firstShape,secondShape] at related
  have bodies := related.2 (.empty : Value Nat Bool)
  change SourceCurrentStoredNormalizedPlans.Related [.interned firstEntry.identity]
    [.interned secondEntry.identity] [.empty] [.empty] environment environment firstBody secondBody at bodies
  cbv at bodies
  simp only [List.mem_singleton,forall_eq,exists_eq_left,
    SourceCurrentStoredNormalizedPlans.RowRelated.eq_def,
    SourceCurrentStoredNormalizedPlans.ManyRelated.eq_def,
    SourceCurrentStoredNormalizedPlans.Related.eq_def] at bodies
  exact bodies

private theorem used :
    (match first with | .mu _ _ depth ordinary => InternedFreshOrdinaryDepthHeap.usesLocal depth ordinary = true | _ => False) ∧
    (match second with | .mu _ _ depth ordinary => InternedFreshOrdinaryDepthHeap.usesLocal depth ordinary = true | _ => False) := by cbv

end MicroCFTA.UsedBinderExplore
