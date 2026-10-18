import MicroCFTA.SourceCurrentCausalCrossLocalMuGenerators
import MicroCFTA.InternedFreshOrdinaryClosedCompletion

set_option linter.all true
set_option maxRecDepth 30000
set_option maxHeartbeats 5000000
set_option cbv.maxSteps 100000000

namespace MicroCFTA.CausalCrossLocalIntegration
open Cache Language InternedConstructorTemplates InternedProbeProvenance
open InternedNestedConstruction (Syntax Outcome)
open InternedFreshOrdinaryConstruction (build ordinaryLevel)
open InternedFreshOrdinaryStoredSubstitution (execute unfold)
open InternedStoredSubstitution (Environment Replacements)
open InternedBinderProtocol (Reference NodeKey)
open SourceCurrentConstrainedCapSourceHistory (Context)
open SourceCurrentNativeMuIssuedHistory (Path)
open SourceCurrentStoredMuBinderChildLineage (bind)
open SourceCurrentRetainedMuDirectedCase (Generated)
open SourceEqualityRequiredCache (Ready Keeps)
open SourceCurrentOpenPreorderSimulation (Mutual)
open InternedEdgeResidency (nodeEdges)

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


private def baseSource : Syntax Nat Bool := .node [.mk 1 false []]
private def baseRun := build baseSource [] empty
private def leaf := value baseRun
private def before := baseRun.state
private def marker : Reference := .uninterned 17
private def expression : Syntax Nat Bool := .binder false (.node [.mk 7 true [.var 0,.var 1]])
private def sourceRun := build expression [.reference marker] before
private def mu := value sourceRun
private def reader := sourceRun.state
private def fields : Value Nat Bool → Interned NodeKey × Value Nat Bool × Value Nat Bool × Value Nat Bool
  | .mu entry body depth ordinary => (entry,body,depth,ordinary)
  | _ => (⟨0,.node []⟩,.empty,.empty,.empty)
private def entry := (fields mu).1
private def body := (fields mu).2.1
private def depth := (fields mu).2.2.1
private def ordinary := (fields mu).2.2.2
private def key := muKey depth ordinary
private def environment : Environment Nat Bool := fun name => if name=marker then some leaf else none

private theorem base_done : build baseSource [] empty = .done leaf before := by cbv
private theorem base_ready : Ready before := SourceEqualityRequiredCache.constructed baseSource leaf before base_done
private theorem leaf_available : Available before leaf :=
  (InternedFreshOrdinaryFacts.build_verified baseSource [] empty InternedNestedFacts.empty_facts
    (by intro supplied impossible; cases impossible)).result leaf before base_done
private theorem inputs_available : InternedNestedProvenance.Values before [.reference marker] := by
  intro supplied member
  have same := List.mem_singleton.mp member
  subst supplied
  exact InternedNestedProvenance.ordinary_available before 17
private theorem source_effects : build expression [.reference marker] before = .done mu reader ∧
    Keeps before reader ∧ Available reader mu :=
  source_effect expression [marker] before base_ready inputs_available
private theorem context : Context before [.reference marker] :=
  ⟨SourceRecursiveIntersectionSemanticHeap.context before base_ready.semantic _ inputs_available,base_ready.semantic.2⟩
private noncomputable def path : Path empty reader :=
  .trans (SourceCurrentNativeMuIssuedHistory.closed_path baseSource)
    (Classical.choice (SourceCurrentNativeMuIssuedHistory.build_path expression [.reference marker] before context))
private theorem shape : mu = .mu entry body depth ordinary := by cbv
private theorem present : reader.nodeRecords key = some (.mu entry body depth ordinary) := by cbv
private theorem replacements : Replacements reader environment := by
  intro name output found
  dsimp only [environment] at found
  split at found
  · cases found
    exact source_effects.2.1.available leaf leaf_available
  · cases found
private def bodyRun := execute body (bind (.interned entry.identity) mu environment) reader
private def bodyResult := value bodyRun
private def bodyAfter := bodyRun.state
private def row : EdgeValue Nat Bool :=
  (nodeEdges bodyResult)[0]?.getD (.mk ⟨0,.mk 0 [] false⟩ [])
private theorem body_done : execute body (bind (.interned entry.identity) mu environment) reader =
    .done bodyResult bodyAfter := by cbv
private theorem actual_row : row ∈ nodeEdges bodyResult ∧ row.entry.key.symbol = 7 ∧
    row.entry.key.constraint = true ∧ row.children = [mu,leaf] := by
  refine ⟨?_,?_,?_,?_⟩
  · cbv; exact List.mem_cons_self
  · cbv
  · cbv
  · cbv

private def Claim : Prop :=
  build baseSource [] empty = .done leaf before ∧
    build expression [.reference marker] before = .done mu reader ∧
    Context before [.reference marker] ∧ Ready reader ∧ Available reader mu ∧
    Nonempty (Path empty reader) ∧ mu = .mu entry body depth ordinary ∧
    marker ∈ mu.free ∧ InternedFreshOrdinaryDepthHeap.usesLocal depth ordinary = true ∧
    reader.nodeRecords key = some (.mu entry body depth ordinary) ∧
    Replacements reader environment ∧
    ∃ left middle right final,
      execute body (bind (.interned entry.identity) mu environment) reader = .done left middle ∧
      execute ordinary (bind (.uninterned (ordinaryLevel depth)) mu environment) middle = .done right final ∧
      Keeps reader middle ∧ Keeps middle final ∧ Available final left ∧ Available final right ∧
      Nonempty (Path reader middle) ∧ Nonempty (Path middle final) ∧ Nonempty (Path empty final) ∧
      final.nodeRecords key = some (.mu entry body depth ordinary) ∧
      execute body (bind (.interned entry.identity) mu environment) final = .done left final ∧
      execute ordinary (bind (.uninterned (ordinaryLevel depth)) mu environment) final = .done right final ∧
      Mutual (Generated final) mu mu ∧ Mutual (Generated final) left right ∧
      (left.referenceOf == .empty) = (right.referenceOf == .empty) ∧
      ∃ selectedRow ∈ nodeEdges left,
        selectedRow.entry.key.symbol = 7 ∧ selectedRow.entry.key.constraint = true ∧
        selectedRow.children = [mu,leaf]

private theorem checked : Claim := by
  refine ⟨base_done,source_effects.1,context,source_effects.2.1.ready,source_effects.2.2,⟨path⟩,shape,?_,?_,present,replacements,?_⟩
  · cbv; exact List.mem_cons_self
  · cbv
  · obtain ⟨left,middle,right,final,firstDone,secondDone,first,second,leftAvailable,rightAvailable,
      firstPath,secondPath,finalPath,finalPresent,bodyWarm,ordinaryWarm,finalRelated,_generated,flags⟩ :=
      SourceCurrentCausalCrossLocalMuGenerators.complete key entry body depth ordinary reader source_effects.2.1.ready path
        present environment replacements mu mu source_effects.2.2 source_effects.2.2 ⟨.refl _,.refl _⟩
    have kept := first.trans second
    obtain ⟨finalIssuedPath⟩ := finalPath
    have selected := SourceCurrentCausalCrossLocalMuGenerators.selected key entry body depth ordinary
      final kept.ready finalIssuedPath finalPresent environment
      (fun name output found => kept.available output (replacements name output found))
      mu mu (kept.available mu source_effects.2.2) (kept.available mu source_effects.2.2)
      finalRelated left right bodyWarm ordinaryWarm
    refine ⟨left,middle,right,final,firstDone,secondDone,first,second,leftAvailable,rightAvailable,
      firstPath,secondPath,⟨finalIssuedPath⟩,finalPresent,bodyWarm,ordinaryWarm,finalRelated,selected,flags,?_⟩
    have same := (Outcome.done.inj (firstDone.symm.trans body_done)).1
    subst left
    exact ⟨row,actual_row.1,actual_row.2⟩

/-- One source-built open used Mu supplies actual recursive-child cross-local calls with the same local value. -/
theorem witness :
  build baseSource [] empty = .done leaf before ∧
    build expression [.reference marker] before = .done mu reader ∧
    Context before [.reference marker] ∧ Ready reader ∧ Available reader mu ∧
    Nonempty (Path empty reader) ∧ mu = .mu entry body depth ordinary ∧
    marker ∈ mu.free ∧ InternedFreshOrdinaryDepthHeap.usesLocal depth ordinary = true ∧
    reader.nodeRecords key = some (.mu entry body depth ordinary) ∧
    Replacements reader environment ∧
    ∃ left middle right final,
      execute body (bind (.interned entry.identity) mu environment) reader = .done left middle ∧
      execute ordinary (bind (.uninterned (ordinaryLevel depth)) mu environment) middle = .done right final ∧
      Keeps reader middle ∧ Keeps middle final ∧ Available final left ∧ Available final right ∧
      Nonempty (Path reader middle) ∧ Nonempty (Path middle final) ∧ Nonempty (Path empty final) ∧
      final.nodeRecords key = some (.mu entry body depth ordinary) ∧
      execute body (bind (.interned entry.identity) mu environment) final = .done left final ∧
      execute ordinary (bind (.uninterned (ordinaryLevel depth)) mu environment) final = .done right final ∧
      Mutual (Generated final) mu mu ∧ Mutual (Generated final) left right ∧
      (left.referenceOf == .empty) = (right.referenceOf == .empty) ∧
      ∃ selectedRow ∈ nodeEdges left,
        selectedRow.entry.key.symbol = 7 ∧ selectedRow.entry.key.constraint = true ∧
        selectedRow.children = [mu,leaf] := checked

end MicroCFTA.CausalCrossLocalIntegration

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.proofs true
set_option pp.proofs.threshold 254
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000
#check @MicroCFTA.CausalCrossLocalIntegration.witness
#print MicroCFTA.CausalCrossLocalIntegration.witness
#print axioms MicroCFTA.CausalCrossLocalIntegration.witness
