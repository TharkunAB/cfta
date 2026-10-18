import MicroCFTA.SourceCurrentCausalStoredMuGenerators
import MicroCFTA.InternedFreshOrdinaryClosedCompletion

set_option linter.all true
set_option maxRecDepth 30000
set_option maxHeartbeats 5000000
set_option cbv.maxSteps 100000000

namespace MicroCFTA.MuGeneratorsIntegration
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
open InternedRootProfile (Equivalent profile)

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
private theorem empty_done : execute body (bind (.interned entry.identity) .empty environment) reader = .done .empty reader := by cbv
private def positiveRun := execute body (bind (.interned entry.identity) leaf environment) reader
private def positive := value positiveRun
private theorem positive_done : execute body (bind (.interned entry.identity) leaf environment) reader =
    .done positive positiveRun.state := by cbv
private theorem positive_nonempty : (positive.referenceOf == .empty) = false := by cbv

private theorem body_flag (replacement left : Value Nat Bool) (middle : State Nat Bool)
    (member : replacement ∈ [.empty,leaf])
    (called : execute body (bind (.interned entry.identity) replacement environment) reader = .done left middle) :
    (left.referenceOf == .empty) = (replacement.referenceOf == .empty) := by
  rcases List.mem_cons.mp member with rfl | member
  · have same := (Outcome.done.inj (called.symm.trans empty_done)).1
    cases same
    rfl
  · have sameReplacement := List.mem_singleton.mp member
    subst replacement
    have same := (Outcome.done.inj (called.symm.trans positive_done)).1
    cases same
    exact positive_nonempty

private def Claim : Prop :=
  build baseSource [] empty = .done leaf before ∧
    build expression [.reference marker] before = .done mu reader ∧
    Context before [.reference marker] ∧ Ready reader ∧ Available reader mu ∧
    Nonempty (Path empty reader) ∧ mu = .mu entry body depth ordinary ∧
    marker ∈ mu.free ∧ InternedFreshOrdinaryDepthHeap.usesLocal depth ordinary = true ∧
    reader.nodeRecords key = some (.mu entry body depth ordinary) ∧
    Replacements reader environment ∧ (leaf.referenceOf == .empty) = false ∧
    (∀ replacement ∈ [.empty,leaf], ∃ left middle right final,
      execute body (bind (.interned entry.identity) replacement environment) reader = .done left middle ∧
      execute ordinary (bind (.uninterned (ordinaryLevel depth)) replacement environment) middle = .done right final ∧
      Keeps reader middle ∧ Keeps middle final ∧ Available final left ∧ Available final right ∧
      Nonempty (Path reader middle) ∧ Nonempty (Path middle final) ∧ Nonempty (Path empty final) ∧
      final.nodeRecords key = some (.mu entry body depth ordinary) ∧
      execute body (bind (.interned entry.identity) replacement environment) final = .done left final ∧
      execute ordinary (bind (.uninterned (ordinaryLevel depth)) replacement environment) final = .done right final ∧
      Generated final left right ∧ Generated final right left ∧
      Equivalent (profile left) (profile right) ∧
      (left.referenceOf == .empty) = (replacement.referenceOf == .empty) ∧
      (right.referenceOf == .empty) = (replacement.referenceOf == .empty)) ∧
    ∃ left middle right final,
      unfold (.mu entry body depth ordinary) reader = .done left middle ∧
      execute ordinary (bind (.uninterned (ordinaryLevel depth)) (.mu entry body depth ordinary) (fun _ => none))
        middle = .done right final ∧
      unfold (.mu entry body depth ordinary) final = .done left final ∧
      left ∈ MergedFreshOrdinaryGraph.successors reader (.mu entry body depth ordinary) ∧
      left ∈ MergedFreshOrdinaryGraph.successors final (.mu entry body depth ordinary) ∧
      Keeps reader middle ∧ Keeps middle final ∧ Nonempty (Path empty final) ∧
      Generated final left right ∧ Generated final right left

private theorem checked : Claim := by
  refine ⟨base_done,source_effects.1,context,source_effects.2.1.ready,source_effects.2.2,⟨path⟩,shape,?_,?_,present,replacements,?_,?_,?_⟩
  · cbv; simp
  · cbv
  · cbv
  · intro replacement member
    have available : Available reader replacement := by
      rcases List.mem_cons.mp member with rfl | member
      · exact InternedNestedProvenance.empty_available _
      · have same := List.mem_singleton.mp member
        subst replacement
        exact source_effects.2.1.available leaf leaf_available
    obtain ⟨left,middle,right,final,firstDone,secondDone,first,second,leftAvailable,rightAvailable,
      firstPath,secondPath,finalPath,finalPresent,bodyWarm,ordinaryWarm,forward,backward,profiles,flags⟩ :=
      SourceCurrentCausalStoredMuGenerators.complete key entry body depth ordinary reader source_effects.2.1.ready path
        present environment replacements replacement available
    have firstFlag := body_flag replacement left middle member firstDone
    have secondFlag := flags.symm.trans firstFlag
    exact ⟨left,middle,right,final,firstDone,secondDone,first,second,leftAvailable,rightAvailable,
      firstPath,secondPath,finalPath,finalPresent,bodyWarm,ordinaryWarm,forward,backward,profiles,firstFlag,secondFlag⟩
  · exact SourceCurrentCausalStoredMuGenerators.unfolding key entry body depth ordinary reader source_effects.2.1.ready path present

/-- An actual open used Mu supplies Empty and nonempty reconstruction cases and genuine unfolding generators. -/
theorem witness :
  build baseSource [] empty = .done leaf before ∧
    build expression [.reference marker] before = .done mu reader ∧
    Context before [.reference marker] ∧ Ready reader ∧ Available reader mu ∧
    Nonempty (Path empty reader) ∧ mu = .mu entry body depth ordinary ∧
    marker ∈ mu.free ∧ InternedFreshOrdinaryDepthHeap.usesLocal depth ordinary = true ∧
    reader.nodeRecords key = some (.mu entry body depth ordinary) ∧
    Replacements reader environment ∧ (leaf.referenceOf == .empty) = false ∧
    (∀ replacement ∈ [.empty,leaf], ∃ left middle right final,
      execute body (bind (.interned entry.identity) replacement environment) reader = .done left middle ∧
      execute ordinary (bind (.uninterned (ordinaryLevel depth)) replacement environment) middle = .done right final ∧
      Keeps reader middle ∧ Keeps middle final ∧ Available final left ∧ Available final right ∧
      Nonempty (Path reader middle) ∧ Nonempty (Path middle final) ∧ Nonempty (Path empty final) ∧
      final.nodeRecords key = some (.mu entry body depth ordinary) ∧
      execute body (bind (.interned entry.identity) replacement environment) final = .done left final ∧
      execute ordinary (bind (.uninterned (ordinaryLevel depth)) replacement environment) final = .done right final ∧
      Generated final left right ∧ Generated final right left ∧
      Equivalent (profile left) (profile right) ∧
      (left.referenceOf == .empty) = (replacement.referenceOf == .empty) ∧
      (right.referenceOf == .empty) = (replacement.referenceOf == .empty)) ∧
    ∃ left middle right final,
      unfold (.mu entry body depth ordinary) reader = .done left middle ∧
      execute ordinary (bind (.uninterned (ordinaryLevel depth)) (.mu entry body depth ordinary) (fun _ => none))
        middle = .done right final ∧
      unfold (.mu entry body depth ordinary) final = .done left final ∧
      left ∈ MergedFreshOrdinaryGraph.successors reader (.mu entry body depth ordinary) ∧
      left ∈ MergedFreshOrdinaryGraph.successors final (.mu entry body depth ordinary) ∧
      Keeps reader middle ∧ Keeps middle final ∧ Nonempty (Path empty final) ∧
      Generated final left right ∧ Generated final right left := checked

end MicroCFTA.MuGeneratorsIntegration
