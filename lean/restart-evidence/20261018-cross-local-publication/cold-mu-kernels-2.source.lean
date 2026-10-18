import MicroCFTA.SourceCurrentObservationReaderSupport
import MicroCFTA.SourceCurrentNativeMuIssuedHistory

set_option linter.all true
set_option maxRecDepth 30000
set_option maxHeartbeats 5000000
set_option cbv.maxSteps 100000000

namespace MicroCFTA.ColdMuKernels
open Cache InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedNestedConstruction (Syntax Outcome)
open InternedFreshOrdinaryConstruction (build)
open InternedFreshOrdinaryStoredSubstitution (execute unfold)
open InternedBinderProtocol (NodeKey)
open SourceEqualityRequiredCache (Ready Keeps)
open SourceCurrentNativeMuIssuedHistory (Path)
open SourceCurrentObservationReaderSupport (WarmSupport)
open InternedFreshMuUnfoldBudget (Settled)
open MergedFreshOrdinaryGraph (successors)

private def value (outcome : Outcome Nat Bool (Value Nat Bool)) : Value Nat Bool :=
  match outcome with | .done result _ => result | .pending .. => .empty
private def source : Syntax Nat Bool :=
  .binder true (.binder true (.node [.mk 7 true [.var 1,.var 0]]))
private def built := build source [] empty
private def root := value built
private def before := built.state
private def opened := unfold root before
private def next := value opened
private def after := opened.state
private def oldRun := unfold next before
private def oldRow := value oldRun
private def oldAfter := oldRun.state
private def grownRun := unfold next after
private def grownRow := value grownRun
private def grownAfter := grownRun.state
private def fields : Value Nat Bool → Interned NodeKey × Value Nat Bool × Value Nat Bool × Value Nat Bool
  | .mu entry body depth ordinary => (entry,body,depth,ordinary)
  | _ => (⟨0,.node []⟩,.empty,.empty,.empty)

private theorem actual : build source [] empty = .done root before := by cbv
private theorem ready : Ready before := SourceEqualityRequiredCache.constructed source root before actual
private theorem available : Available before root :=
  (InternedFreshOrdinaryFacts.build_verified source [] empty InternedNestedFacts.empty_facts
    (by intro supplied member; cases member)).result root before actual
private theorem shape : root = .mu (fields root).1 (fields root).2.1 (fields root).2.2.1 (fields root).2.2.2 := by cbv
private theorem next_shape : next = .mu (fields next).1 (fields next).2.1 (fields next).2.2.1 (fields next).2.2.2 := by cbv
private theorem called : unfold root before = .done next after := by cbv
private theorem effects : Keeps before after ∧ Available after next := by
  obtain ⟨result,final,done,context,heap,covered,output,growth,issued⟩ :=
    InternedFreshOrdinaryStoredSubstitution.unfold_complete_decoded root before ready.semantic.1 available
      ready.semantic.2 ready.covered
  obtain ⟨sameResult,sameFinal⟩ := Outcome.done.inj (done.symm.trans called)
  subst result; subst final
  have afterDepth : InternedOpenDepthReadback.Heap after := by
    simpa only [called,Outcome.state] using
      InternedStoredPlanBinderDepthProgress.unfold_heap root before ready.semantic.1 ready.semantic.2 ready.depth available
  exact ⟨⟨⟨⟨context,heap⟩,covered,afterDepth⟩,growth,issued⟩,output⟩
private theorem missing : before.nodeRecords (fields next).1.key = none := by cbv
private theorem absent : ¬ Available before next := by
  intro present
  have stored := present.resident (fields next).1 (by rw [next_shape]; rfl)
  rw [missing] at stored
  cases stored
private theorem cold : ¬ Settled before root := by
  rintro ⟨result,done⟩
  have same := (Outcome.done.inj (called.symm.trans done)).2
  have sizes := congrArg (fun heap : State Nat Bool => heap.nodes.next) same
  cbv at sizes
  contradiction
private theorem old_called : unfold next before = .done oldRow oldAfter := by cbv
private theorem grown_called : unfold next after = .done grownRow grownAfter := by cbv
private theorem distinct_rows : oldRow ≠ grownRow := by
  intro same
  have ids := congrArg Value.referenceOf same
  cbv at ids
  cases ids
private theorem not_available_support : ¬ WarmSupport before (Available before) := by
  intro support
  exact absent (support.1 root available next (by rw [shape]; simp only [successors,←shape,called]; exact List.mem_cons_self))

/-- A source-built closed Mu allocates a new closed Mu before its ordinary successor is read. -/
private theorem checked :
    ∃ (first second : Value Nat Bool) (initial completed : State Nat Bool)
      (oldResult grownResult : Value Nat Bool) (oldFinal grownFinal : State Nat Bool),
      build (.binder true (.binder true (.node [.mk 7 true [.var 1,.var 0]]))) [] empty = .done first initial ∧
      Ready initial ∧ Available initial first ∧ Nonempty (Path empty initial) ∧
      first.free = [] ∧ second.free = [] ∧ first.referenceOf = .mu 8 ∧ second.referenceOf = .mu 15 ∧
      initial.nodes.next = 13 ∧ completed.nodes.next = 17 ∧
      first.depth = 2 ∧ second.depth = 3 ∧
      InternedStoredPlanBinderDepth.bodyDepth first = 1 ∧ InternedStoredPlanBinderDepth.bodyDepth second = 0 ∧
      unfold first initial = .done second completed ∧ Keeps initial completed ∧ Available completed second ∧
      ¬ Available initial second ∧ ¬ Settled initial first ∧ ¬ WarmSupport initial (Available initial) ∧
      successors initial first = [second] ∧
      unfold second initial = .done oldResult oldFinal ∧ successors initial second = [oldResult] ∧
      unfold second completed = .done grownResult grownFinal ∧ oldResult ≠ grownResult ∧
      oldResult.referenceOf = .node 13 ∧ grownResult.referenceOf = .node 17 := by
  refine ⟨root,next,before,after,oldRow,grownRow,oldAfter,grownAfter,actual,ready,available,
    ⟨SourceCurrentNativeMuIssuedHistory.closed_path source⟩,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,
    called,effects.1,effects.2,absent,cold,not_available_support,?_,old_called,?_,grown_called,distinct_rows,?_,?_⟩
  all_goals first
    | solve | (rw [shape]; simp only [successors,←shape,called])
    | solve | (rw [next_shape]; simp only [successors,←next_shape,old_called])
    | cbv

/-- The fixed reader graph retains its original reader after a fresh Mu allocation. -/
theorem cold_nested_mu :
    ∃ (first second : Value Nat Bool) (initial completed : State Nat Bool)
      (oldResult grownResult : Value Nat Bool) (oldFinal grownFinal : State Nat Bool),
      build (.binder true (.binder true (.node [.mk 7 true [.var 1,.var 0]]))) [] empty = .done first initial ∧
      Ready initial ∧ Available initial first ∧ Nonempty (Path empty initial) ∧
      first.free = [] ∧ second.free = [] ∧ first.referenceOf = .mu 8 ∧ second.referenceOf = .mu 15 ∧
      initial.nodes.next = 13 ∧ completed.nodes.next = 17 ∧
      first.depth = 2 ∧ second.depth = 3 ∧
      InternedStoredPlanBinderDepth.bodyDepth first = 1 ∧ InternedStoredPlanBinderDepth.bodyDepth second = 0 ∧
      unfold first initial = .done second completed ∧ Keeps initial completed ∧ Available completed second ∧
      ¬ Available initial second ∧ ¬ Settled initial first ∧ ¬ WarmSupport initial (Available initial) ∧
      successors initial first = [second] ∧
      unfold second initial = .done oldResult oldFinal ∧ successors initial second = [oldResult] ∧
      unfold second completed = .done grownResult grownFinal ∧ oldResult ≠ grownResult ∧
      oldResult.referenceOf = .node 13 ∧ grownResult.referenceOf = .node 17 := checked
end MicroCFTA.ColdMuKernels
