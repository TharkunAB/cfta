import MicroCFTA.SourceCurrentCommonReaderBinderSupport
import MicroCFTA.InternedFreshOrdinaryClosedCompletion
namespace MicroCFTA.CommonReaderKernels
open Cache Language InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedBinderProtocol (Reference NodeKey)
open InternedNestedConstruction (Syntax Outcome)
open InternedFreshOrdinaryConstruction (build)
open InternedFreshOrdinaryStoredSubstitution (execute unfold)
open InternedStoredSubstitution (Environment)
open SourceEqualityRequiredCache (Ready Keeps Ordinary)
open SourceCurrentObservationReaderSupport (WarmSupport)
set_option maxRecDepth 30000
set_option maxHeartbeats 5000000
set_option cbv.maxSteps 100000000
private def value (outcome : Outcome Nat Bool (Value Nat Bool)) : Value Nat Bool :=
  match outcome with | .done result _ => result | .pending .. => .empty
private theorem source_effect (term : Syntax Nat Bool) (names : List Reference)
    (before : State Nat Bool) (ready : Ready before)
    (available : InternedNestedProvenance.Values before (names.map Value.reference)) :
    build term (names.map Value.reference) before =
      .done (value (build term (names.map Value.reference) before)) (build term (names.map Value.reference) before).state ∧
      Keeps before (build term (names.map Value.reference) before).state ∧
      Available (build term (names.map Value.reference) before).state (value (build term (names.map Value.reference) before)) := by
  have context := SourceRecursiveIntersectionSemanticHeap.context before ready.semantic _ available
  obtain ⟨result,after,called⟩ := InternedFreshOrdinaryClosedCompletion.literal_complete term names before context ready.semantic.2 ready.covered
  have checked := InternedFreshOrdinaryFacts.build_verified term _ before ready.semantic.1.normal.facts available
  have kept : Keeps before after := by
    refine ⟨⟨?_,?_,?_⟩,?_,?_⟩
    · simpa only [called,Outcome.state] using SourceRecursiveIntersectionSemanticHeap.source term _ before ready.semantic available
    · exact InternedFreshOrdinaryCoverage.build_covered term _ before ready.semantic.1.normal.facts.coherent.valid ready.covered result after called
    · simpa only [called,Outcome.state] using (InternedOpenDepthExecution.build_depth term _ before context ready.semantic.2 ready.depth).heap
    · simpa only [called,Outcome.state] using checked.growth
    · simpa only [called,Outcome.state] using checked.history
  rw [called]
  exact ⟨rfl,kept,checked.result result after called⟩

private def marker : Reference := .uninterned 9
private def expression : Syntax Nat Bool := .binder true (.node [.mk 0 false [.var 0,.var 1]])
private def built := build expression [.reference marker] empty
private def mu := value built
private def before := built.state
private def fields : Value Nat Bool → Interned NodeKey × Value Nat Bool × Value Nat Bool × Value Nat Bool
  | .mu entry body depth ordinary => (entry,body,depth,ordinary)
  | _ => (⟨0,.node []⟩,.empty,.empty,.empty)
private def nodeFields : Value Nat Bool → Interned NodeKey × List (EdgeValue Nat Bool) × Nat × List Reference
  | .node entry rows level free => (entry,rows,level,free)
  | _ => (⟨0,.node []⟩,[],0,[])
private def nodeParts := nodeFields (fields mu).2.1
private def recursive : Value Nat Bool := .mu (fields mu).1
  (.node nodeParts.1 nodeParts.2.1 nodeParts.2.2.1 nodeParts.2.2.2) (fields mu).2.2.1 (fields mu).2.2.2
private theorem actual_effect : build expression [.reference marker] empty = .done mu before ∧
    Keeps empty before ∧ Available before mu :=
  source_effect expression [marker] empty
    (SourceEqualityRequiredCache.constructed (.empty : Syntax Nat Bool) .empty empty (by simp only [build])) (by
      intro supplied member
      have same := List.mem_singleton.mp member
      subst supplied
      exact reference_available _ _ (InternedFreshProbeKeys.sentinel_references_issued _ 9).2)
private theorem recursive_eq : recursive = mu := by cbv
private def firstRow : EdgeValue Nat Bool := nodeParts.2.1[0]?.getD (.mk ⟨0,⟨0,[],false⟩⟩ [])
private theorem sources : ∀ row ∈ nodeParts.2.1, ∀ child ∈ row.children,
    child = .reference (.interned (fields mu).1.identity) ∨ child = .reference marker := by
  intro row member child included
  have rows : nodeParts.2.1 = [firstRow] := by cbv
  rw [rows] at member
  have same := List.mem_singleton.mp member
  subst row
  have choices : firstRow.children = [.reference (.interned (fields mu).1.identity),.reference marker] := by cbv
  rw [choices] at included
  rcases List.mem_cons.mp included with own | captured
  · exact Or.inl own
  · exact Or.inr (List.mem_singleton.mp captured)

private def support (value : Value Nat Bool) : Prop := value = .reference marker
private theorem warm : WarmSupport before support := by
  refine ⟨?_,?_,?_⟩
  · intro value same next member
    change value = .reference marker at same
    subst value
    cases member
  · intro value same row member
    change value = .reference marker at same
    subst value
    cases member
  · intro value same
    change value = .reference marker at same
    subst value
    exact ⟨_,rfl⟩
private theorem reference_execute (name : Reference) (environment : Environment Nat Bool) (state : State Nat Bool) :
    execute (.reference name) environment state = .done ((environment name).getD (.reference name)) state := by
  simp [execute,InternedStoredSubstitution.leaves,Value.free,InternedStoredSubstitution.encode,
    InternedStoredSubstitution.slot,build,InternedStoredSubstitution.input]

private theorem checked_witness :
    ∃ (before after : State Nat Bool) (root result : Value Nat Bool)
      (entry nodeEntry : Interned NodeKey) (rows : List (EdgeValue Nat Bool)) (level : Nat) (free : List Reference)
      (depth ordinary : Value Nat Bool),
      build (.binder true (.node [.mk 0 false [.var 0,.var 1]])) [.reference (.uninterned 9)] empty = .done root before ∧
      Ready before ∧ Available before root ∧
      root = .mu entry (.node nodeEntry rows level free) depth ordinary ∧
      root.free ≠ [] ∧ InternedStoredPlanBinderDepth.valueDepth root > 0 ∧
      InternedFreshOrdinaryDepthHeap.usesLocal depth ordinary = true ∧
      WarmSupport before (fun value => value = .reference (.uninterned 9)) ∧
      unfold root before = .done result after ∧ Keeps before after ∧ Available after result ∧
      unfold root after = .done result after ∧ Ordinary result ∧
      before.nodes.next < after.nodes.next ∧
      WarmSupport after (fun value => value = .reference (.uninterned 9) ∨ value = root ∨ value = result) := by
  have available : Available before recursive := recursive_eq.symm ▸ actual_effect.2.2
  obtain ⟨result,after,actual,kept,output,repeated,ordinary,supported⟩ :=
    SourceCurrentCommonReaderBinderSupport.node before actual_effect.2.1.ready support warm
      (fields mu).1 nodeParts.1 nodeParts.2.1 nodeParts.2.2.1 nodeParts.2.2.2
      (fields mu).2.2.1 (fields mu).2.2.2 available (by
        intro row member child included _ common _ output called
        rcases sources row member child included with own | captured
        · subst child
          rw [reference_execute] at called
          apply Or.inr
          simpa only [ite_true,Option.getD_some] using (Outcome.done.inj called).1.symm
        · subst child
          rw [reference_execute] at called
          have same : output = .reference marker := by
            simpa only [marker,reduceCtorEq,ite_false,Option.getD_none] using (Outcome.done.inj called).1.symm
          exact Or.inl same)
  change unfold recursive before = .done result after at actual
  change unfold recursive after = .done result after at repeated
  change WarmSupport after (fun value => support value ∨ value = recursive ∨ value = result) at supported
  rw [recursive_eq] at actual repeated supported
  have allocated : before.nodes.next < (unfold mu before).state.nodes.next := by cbv
  rw [actual] at allocated
  refine ⟨before,after,mu,result,(fields mu).1,nodeParts.1,nodeParts.2.1,nodeParts.2.2.1,nodeParts.2.2.2,
    (fields mu).2.2.1,(fields mu).2.2.2,actual_effect.1,actual_effect.2.1.ready,actual_effect.2.2,
    recursive_eq.symm,?_,?_,?_,warm,actual,kept,output,repeated,ordinary,allocated,supported⟩
  · cbv
    intro impossible
    cases impossible
  · cbv
  · cbv

/-- Actual open used-Mu construction adds its recursive node unfolding to primitive-reference support. -/
theorem open_used :
    ∃ (before after : State Nat Bool) (root result : Value Nat Bool)
      (entry nodeEntry : Interned NodeKey) (rows : List (EdgeValue Nat Bool)) (level : Nat) (free : List Reference)
      (depth ordinary : Value Nat Bool),
      build (.binder true (.node [.mk 0 false [.var 0,.var 1]])) [.reference (.uninterned 9)] empty = .done root before ∧
      Ready before ∧ Available before root ∧
      root = .mu entry (.node nodeEntry rows level free) depth ordinary ∧
      root.free ≠ [] ∧ InternedStoredPlanBinderDepth.valueDepth root > 0 ∧
      InternedFreshOrdinaryDepthHeap.usesLocal depth ordinary = true ∧
      WarmSupport before (fun value => value = .reference (.uninterned 9)) ∧
      unfold root before = .done result after ∧ Keeps before after ∧ Available after result ∧
      unfold root after = .done result after ∧ Ordinary result ∧
      before.nodes.next < after.nodes.next ∧
      WarmSupport after (fun value => value = .reference (.uninterned 9) ∨ value = root ∨ value = result) := checked_witness

end MicroCFTA.CommonReaderKernels

set_option linter.all true
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.proofs true
set_option pp.proofs.threshold 254
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000
set_option maxHeartbeats 5000000
set_option maxRecDepth 30000

#check @MicroCFTA.CommonReaderKernels.open_used
#print MicroCFTA.CommonReaderKernels.open_used
#print axioms MicroCFTA.CommonReaderKernels.open_used
