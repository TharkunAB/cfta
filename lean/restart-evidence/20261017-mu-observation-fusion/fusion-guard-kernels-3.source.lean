import MicroCFTA.SourceCurrentStoredSubstitutionOrigins
import MicroCFTA.SourceCurrentStoredReconstructionReplay
import MicroCFTA.SourceEqualityNativeDemandHeapPrimitives
import MicroCFTA.SourceCurrentOpenObservationConstructors

set_option linter.all true
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.proofs true
set_option pp.proofs.threshold 254
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000
set_option maxRecDepth 30000
set_option maxHeartbeats 5000000

namespace MicroCFTA.FusionGuardClosedCapture
open Cache InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedNestedConstruction (Syntax Outcome work)
open InternedFreshOrdinaryConstruction (build)
open InternedFreshOrdinaryStoredSubstitution (execute)
open InternedBinderProtocol (Reference)
open InternedNestedProvenance (Values)
open SourceEqualityRequiredCache (Ready Keeps)
private def expression : Syntax Nat Bool := .node [.mk 9 false
  [.node [.mk 0 false [.binder false .empty]],
   .node [.mk 0 false [.binder false (.var 1)]]]]
private def inputs : List (Value Nat Bool) := [.reference (.uninterned 0)]
private def children : Value Nat Bool → List (Value Nat Bool)
  | .node _ (.mk _ values :: _) _ _ => values
  | _ => []
private def memberCalls (environment : InternedStoredSubstitution.Environment Nat Bool)
    (values : List (Value Nat Bool)) (state : State Nat Bool) : Outcome Nat Bool (List (Value Nat Bool)) :=
  match values with
  | [] => .done [] state
  | value :: rest => (execute value environment state).bind fun output middle =>
      (memberCalls environment rest middle).bind fun outputs after => .done (output :: outputs) after
private def built := build expression inputs empty
private def source : Value Nat Bool := match built with | .done value _ => value | .pending .. => .empty
private def heap := built.state
private def original := (children source).take 2
private def replacement : Value Nat Bool := .empty
private def environment : InternedStoredSubstitution.Environment Nat Bool :=
  fun name => if name = Reference.uninterned 0 then some replacement else none
private def normalized := run (makeUnion original) heap
private def first := execute normalized.1 environment normalized.2
private def left : Value Nat Bool := match first with | .done value _ => value | .pending .. => .empty
private def rebuilt := memberCalls environment original first.state
private def second := rebuilt.bind fun values next => work (makeUnion values) next
private def right : Value Nat Bool := match second with | .done value _ => value | .pending .. => .empty

private theorem built_done : built = .done source heap := by cbv
private theorem first_done : first = .done left first.state := by cbv
private theorem second_done : second = .done right second.state := by cbv

private theorem empty_ready : Ready (empty : State Nat Bool) :=
  SourceEqualityRequiredCache.constructed .empty .empty empty (by rw [build])
private theorem inputs_available : Values (empty : State Nat Bool) inputs := by
  intro value member
  simp only [inputs,List.mem_cons,List.not_mem_nil,or_false] at member
  subst value
  apply reference_available
  all_goals intro identity impossible; simp [Value.free] at impossible

private theorem source_ready : Ready heap := by
  let context := SourceRecursiveIntersectionSemanticHeap.context empty empty_ready.semantic inputs inputs_available
  have actual : build expression inputs empty = .done source heap := built_done
  refine ⟨?_,?_,?_⟩
  · simpa only [actual,Outcome.state] using
      SourceRecursiveIntersectionSemanticHeap.source expression inputs empty empty_ready.semantic inputs_available
  · exact InternedFreshOrdinaryCoverage.build_covered expression inputs empty context.normal.facts.coherent.valid
      empty_ready.covered source heap built_done
  · simpa only [actual,Outcome.state] using
      (InternedOpenDepthExecution.build_depth expression inputs empty context empty_ready.semantic.2 empty_ready.depth).heap

private theorem source_available : Available heap source :=
  (InternedFreshOrdinaryFacts.build_verified expression inputs empty empty_ready.semantic.1.normal.facts inputs_available).result
    source heap built_done

private theorem child_available (state : State Nat Bool) (value : Value Nat Bool) (available : Available state value) :
    Values state (children value) := by
  cases value <;> try (intro child impossible; cases impossible)
  case node entry rows level free =>
    cases rows with
    | nil => intro child impossible; cases impossible
    | cons row rest =>
        cases row with
        | mk edge values =>
            intro child member
            exact available.children child (List.mem_flatMap.mpr ⟨.mk edge values,List.mem_cons_self,member⟩)
private theorem original_available : Values heap original := by
  intro value member
  exact child_available heap source source_available value (List.mem_of_mem_take member)
private theorem replacement_available : Available heap replacement := InternedProbeProvenance.empty_available heap
private theorem replacements : InternedStoredSubstitution.Replacements heap environment := by
  intro name value found
  simp only [environment] at found
  split at found
  · cases found; exact replacement_available
  · cases found
private theorem normalization_keeps : Keeps heap normalized.2 :=
  SourceEqualityNativeDemandHeapPrimitives.work_keeps (makeUnion original) heap source_ready (.union original original_available)
private theorem normalized_available : Available normalized.2 normalized.1 :=
  (InternedNestedFacts.union_verified original heap source_ready.semantic.1.normal.facts original_available).result _ _ rfl
private theorem first_keeps : Keeps normalized.2 first.state ∧ Available first.state left := by
  obtain ⟨value,after,actual,keeps,available,_⟩ := SourceCurrentStoredReconstruction.execute normalized.1 environment normalized.2
    normalization_keeps.ready normalized_available (fun name value found => normalization_keeps.available value (replacements name value found))
  have same := Outcome.done.inj (first_done.symm.trans actual)
  rcases same with ⟨rfl,rfl⟩
  exact ⟨keeps,available⟩

private theorem calls_complete (values : List (Value Nat Bool)) (before : State Nat Bool) (ready : Ready before)
    (available : Values before values) (provided : InternedStoredSubstitution.Replacements before environment) :
    ∃ outputs after, memberCalls environment values before = .done outputs after ∧ Keeps before after ∧ Values after outputs := by
  induction values generalizing before with
  | nil => exact ⟨[],before,rfl,SourceEqualityRequiredCache.pure_keeps before ready,fun _ impossible => False.elim (List.not_mem_nil impossible)⟩
  | cons value rest ih =>
      obtain ⟨output,middle,called,keeps,result,_⟩ := SourceCurrentStoredReconstruction.execute value environment before ready
        (available value List.mem_cons_self) provided
      obtain ⟨outputs,after,remaining,tail,results⟩ := ih middle keeps.ready
        (fun item member => keeps.available item (available item (List.mem_cons_of_mem _ member)))
        (fun name item found => keeps.available item (provided name item found))
      refine ⟨output::outputs,after,?_,keeps.trans tail,?_⟩
      · simp only [memberCalls,called,Outcome.bind,remaining]
      · intro item member
        rcases List.mem_cons.mp member with rfl | later
        · exact tail.available _ result
        · exact results item later
private theorem second_keeps : Keeps first.state second.state ∧ Available second.state right := by
  obtain ⟨outputs,middle,actual,keeps,available⟩ := calls_complete original first.state first_keeps.1.ready
    (fun value member => first_keeps.1.available value (normalization_keeps.available value (original_available value member)))
    (fun name value found => first_keeps.1.available value (normalization_keeps.available value (replacements name value found)))
  have done : second = .done (run (makeUnion outputs) middle).1 (run (makeUnion outputs) middle).2 := by
    simp only [second,rebuilt,actual,Outcome.bind,work]
  have same := Outcome.done.inj (second_done.symm.trans done)
  rw [same.1,same.2]
  exact ⟨keeps.trans (SourceEqualityNativeDemandHeapPrimitives.work_keeps (makeUnion outputs) middle keeps.ready (.union outputs available)),
    (InternedNestedFacts.union_verified outputs middle keeps.ready.semantic.1.normal.facts available).result _ _ rfl⟩

private def closedNode : Value Nat Bool := original[0]?.getD Value.empty
private def openNode : Value Nat Bool := original[1]?.getD Value.empty
private def closedMu : Value Nat Bool := (children closedNode)[0]?.getD Value.empty
private def openMu : Value Nat Bool := (children openNode)[0]?.getD Value.empty

/-- A closed raw unused Mu stays captured while an open counterpart becomes a physical empty child. -/
theorem closed_capture_fusion :
    build expression inputs empty = .done source heap ∧ Ready heap ∧ Values heap original ∧
    InternedStoredSubstitution.Replacements heap environment ∧
    run (makeUnion original) heap = normalized ∧
    first = .done left first.state ∧ second = .done right second.state ∧
    Keeps heap normalized.2 ∧ Keeps normalized.2 first.state ∧ Keeps first.state second.state ∧
    Available second.state left ∧ Available second.state right ∧
    closedNode.free = [] ∧ openNode.free ≠ [] ∧ closedMu.free = [] ∧ openMu.free ≠ [] ∧
    execute closedNode environment normalized.2 = .done closedNode normalized.2 ∧
    left = right ∧ left = closedNode ∧ left ≠ .empty ∧
    children left = [closedMu] ∧ closedMu ≠ .empty := by
  refine ⟨built_done,source_ready,original_available,replacements,rfl,first_done,second_done,
    normalization_keeps,first_keeps.1,second_keeps.1,second_keeps.1.available left first_keeps.2,second_keeps.2,
    ?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals cbv <;> simp

/-- All observations can agree with EmptyNode while source child filtering keeps the physical Mu. -/
theorem observations_do_not_control_filter (view : State Nat Bool) (depth : Nat) :
    SourceCurrentOpenObservations.Same depth view [closedMu] [Value.empty] ∧
    closedMu ≠ Value.empty ∧ left ≠ Value.empty := by
  have literal : closedMu = .mu ⟨0, .mu ⟨.empty,.empty⟩⟩ .empty .empty .empty := by cbv
  refine ⟨?_,?_,?_⟩
  · rw [literal]
    exact SourceCurrentOpenObservations.unfold depth view _ _ _ _ .empty view (by cbv)
  · rw [literal]; intro impossible; cases impossible
  · cbv; simp

#check @closed_capture_fusion
#print axioms closed_capture_fusion
#check @observations_do_not_control_filter
#print axioms observations_do_not_control_filter
end MicroCFTA.FusionGuardClosedCapture
