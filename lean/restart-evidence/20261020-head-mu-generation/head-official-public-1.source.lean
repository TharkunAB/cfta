import MicroCFTA.SourceCurrentHeadIssuedHistory
import MicroCFTA.SourceCurrentCompletedBuildRootedWriters

/-!
# Actual Head operations that install selected Mu records

The ordered exposure recovers the stored unfold that first installs a
selected full cell. The same operation supplies its generated source root,
mapped self inputs and rooted writer. Initial cells remain explicit.
-/
namespace MicroCFTA.SourceCurrentHeadMuGeneration
open Cache InternedConstructorTemplates InternedProbeProvenance
open InternedNestedConstruction (Outcome)
open InternedNestedProvenance (Values)
open InternedStoredSubstitution (leaves input encode Replacements inputs_available)
open SourceEqualityRequiredCache SourceEqualityRequiredSemanticCache
open SourceCurrentConstrainedCapSourceHistory (Context)
open SourceCurrentNativeMuIssuedHistory (Path)
open SourceCurrentCompletedBuildRootedWriters (Written build_writer_or_prior)
local notation "CostHeap" => InternedFreshOrdinaryCostHeap.Heap

private theorem prior_or_none {before after : State Symbol Guard}
    {key : InternedBinderProtocol.NodeKey} {target : Value Symbol Guard}
    (growth : Grows before after) (selected : after.nodeRecords key = some target) :
    before.nodeRecords key = some target ∨ before.nodeRecords key = none := by
  cases old : before.nodeRecords key with
  | none => exact .inr rfl
  | some value =>
    have retained := growth.nodeRecords key value old
    have same : value = target := Option.some.inj (retained.symm.trans selected)
    cases same
    exact .inl rfl

private def Generated [DecidableEq (EdgeKey Symbol Guard)]
    (before after : State Symbol Guard) (key : InternedBinderProtocol.NodeKey)
    (target : Value Symbol Guard) : Prop :=
  ∃ parentEntry parentBody parentDepth parentOrdinary operationBefore operationResult operationAfter,
    SemanticReady operationBefore ∧ CostHeap operationBefore ∧
    Available operationBefore (.mu parentEntry parentBody parentDepth parentOrdinary) ∧
    InternedFreshOrdinaryStoredSubstitution.unfold (.mu parentEntry parentBody parentDepth parentOrdinary)
      operationBefore = .done operationResult operationAfter ∧
    operationBefore.nodeRecords key = none ∧ operationAfter.nodeRecords key = some target ∧
    Nonempty (Path before operationBefore) ∧ Grows operationAfter after ∧
    Extends operationAfter.nodes.issued after.nodes.issued ∧
    Context operationBefore ((leaves parentBody).map (input (fun name =>
      if name = .interned parentEntry.identity then some (.mu parentEntry parentBody parentDepth parentOrdinary) else none))) ∧
    InternedFreshOrdinaryConstruction.build (encode (leaves parentBody) [] parentBody)
      ((leaves parentBody).map (input (fun name =>
        if name = .interned parentEntry.identity then some (.mu parentEntry parentBody parentDepth parentOrdinary) else none)))
      operationBefore = .done operationResult operationAfter ∧
    Written (encode (leaves parentBody) [] parentBody)
      ((leaves parentBody).map (input (fun name =>
        if name = .interned parentEntry.identity then some (.mu parentEntry parentBody parentDepth parentOrdinary) else none)))
      operationBefore operationAfter key target

private theorem generated_later [DecidableEq (EdgeKey Symbol Guard)]
    {before middle after : State Symbol Guard} {key : InternedBinderProtocol.NodeKey}
    {target : Value Symbol Guard} (generated : Generated before middle key target)
    (growth : Grows middle after) (issued : Extends middle.nodes.issued after.nodes.issued) :
    Generated before after key target := by
  obtain ⟨entry,body,depth,ordinary,start,result,stop,semantic,costs,available,called,missing,present,
    earlier,later,laterIssued,context,built,written⟩ := generated
  exact ⟨entry,body,depth,ordinary,start,result,stop,semantic,costs,available,called,missing,present,
    earlier,grows_trans later growth,extends_trans laterIssued issued,context,built,written⟩

private theorem generated_prepend [DecidableEq (EdgeKey Symbol Guard)]
    {before middle after : State Symbol Guard} {key : InternedBinderProtocol.NodeKey}
    {target : Value Symbol Guard} (earlier : Path before middle)
    (generated : Generated middle after key target) : Generated before after key target := by
  obtain ⟨entry,body,depth,ordinary,start,result,stop,semantic,costs,available,called,missing,present,
    ⟨first⟩,later,laterIssued,context,built,written⟩ := generated
  exact ⟨entry,body,depth,ordinary,start,result,stop,semantic,costs,available,called,missing,present,
    ⟨.trans earlier first⟩,later,laterIssued,context,built,written⟩

private theorem unfold_generated [DecidableEq (EdgeKey Symbol Guard)]
    (parentEntry : Interned InternedBinderProtocol.NodeKey) (parentBody parentDepth parentOrdinary : Value Symbol Guard)
    (before : State Symbol Guard) (semantic : SemanticReady before) (costs : CostHeap before)
    (available : Available before (.mu parentEntry parentBody parentDepth parentOrdinary))
    (result : Value Symbol Guard) (after : State Symbol Guard)
    (called : InternedFreshOrdinaryStoredSubstitution.unfold (.mu parentEntry parentBody parentDepth parentOrdinary)
      before = .done result after)
    (key : InternedBinderProtocol.NodeKey) (entry : Interned InternedBinderProtocol.NodeKey)
    (body depth ordinary : Value Symbol Guard)
    (missing : before.nodeRecords key = none)
    (present : after.nodeRecords key = some (.mu entry body depth ordinary)) :
    Generated before after key (.mu entry body depth ordinary) := by
  let environment := fun name => if name = InternedBinderProtocol.Reference.interned parentEntry.identity
    then some (Value.mu parentEntry parentBody parentDepth parentOrdinary) else none
  have bodyAvailable : Available before parentBody := available.children parentBody (by simp [children])
  have replacements : Replacements before environment := by
    intro name value found
    dsimp only [environment] at found
    split at found
    · cases found; exact available
    · cases found
  have context : Context before ((leaves parentBody).map (input environment)) :=
    ⟨⟨semantic.ready.semantic.1.normal,inputs_available parentBody environment before bodyAvailable replacements,
      semantic.ready.semantic.1.profiles,semantic.ready.semantic.1.freeNames⟩,semantic.ready.semantic.2⟩
  have built : InternedFreshOrdinaryConstruction.build (encode (leaves parentBody) [] parentBody)
      ((leaves parentBody).map (input environment)) before = .done result after := called
  have written : Written (encode (leaves parentBody) [] parentBody)
      ((leaves parentBody).map (input environment)) before after key (.mu entry body depth ordinary) := by
    rcases build_writer_or_prior _ _ before context result after built key entry body depth ordinary present with old | writer
    · rw [missing] at old
      cases old
    · exact writer
  exact ⟨parentEntry,parentBody,parentDepth,parentOrdinary,before,result,after,semantic,costs,available,
    called,missing,present,⟨.refl before⟩,grows_refl _,extends_refl _,context,built,written⟩

private theorem through_unfold [DecidableEq (EdgeKey Symbol Guard)]
    (parentEntry : Interned InternedBinderProtocol.NodeKey) (parentBody parentDepth parentOrdinary : Value Symbol Guard)
    (before : State Symbol Guard) (semantic : SemanticReady before) (costs : CostHeap before)
    (available : Available before (.mu parentEntry parentBody parentDepth parentOrdinary))
    (result : Value Symbol Guard) (middle after : State Symbol Guard)
    (called : InternedFreshOrdinaryStoredSubstitution.unfold (.mu parentEntry parentBody parentDepth parentOrdinary)
      before = .done result middle) (first : Path before middle) (last : Path middle after)
    (key : InternedBinderProtocol.NodeKey) (entry : Interned InternedBinderProtocol.NodeKey)
    (body depth ordinary : Value Symbol Guard)
    (later : middle.nodeRecords key = some (.mu entry body depth ordinary) ∨
      Generated middle after key (.mu entry body depth ordinary)) :
    before.nodeRecords key = some (.mu entry body depth ordinary) ∨
      Generated before after key (.mu entry body depth ordinary) := by
  rcases later with present | generated
  · rcases prior_or_none first.growth present with old | missing
    · exact .inl old
    · exact .inr (generated_later
        (unfold_generated parentEntry parentBody parentDepth parentOrdinary before semantic costs available
          result middle called key entry body depth ordinary missing present) last.growth last.issued)
  · exact .inr (generated_prepend first generated)

private theorem collect [DecidableEq (EdgeKey Symbol Guard)]
    (fuel : Nat) (before : State Symbol Guard) (semantic : SemanticReady before) (costs : CostHeap before)
    (seen : List Nat) (pending : List (Value Symbol Guard)) (available : Values before pending)
    (key : InternedBinderProtocol.NodeKey) (entry : Interned InternedBinderProtocol.NodeKey)
    (body depth ordinary : Value Symbol Guard)
    (selected : (MergedFreshOrdinaryExposure.collect fuel before seen pending).state.nodeRecords key =
      some (.mu entry body depth ordinary)) :
    Nonempty (Path before (MergedFreshOrdinaryExposure.collect fuel before seen pending).state) ∧
      (before.nodeRecords key = some (.mu entry body depth ordinary) ∨
        Generated before (MergedFreshOrdinaryExposure.collect fuel before seen pending).state
          key (.mu entry body depth ordinary)) := by
  induction fuel generalizing before seen pending with
  | zero => cases pending <;> exact ⟨⟨.refl before⟩,.inl selected⟩
  | succ fuel ih =>
    cases pending with
    | nil => exact ⟨⟨.refl before⟩,.inl selected⟩
    | cons value rest =>
      have own := available value List.mem_cons_self
      have tail : Values before rest := fun value member => available value (List.mem_cons_of_mem _ member)
      cases value with
      | empty => exact ih before semantic costs seen rest tail selected
      | reference => exact ⟨⟨.refl before⟩,.inl selected⟩
      | node parentEntry edges level free =>
        simpa only [MergedFreshOrdinaryExposure.collect,SourceEqualityAnnotationExposure.prepend_state] using
          ih before semantic costs seen rest tail
            (by simpa only [MergedFreshOrdinaryExposure.collect,SourceEqualityAnnotationExposure.prepend_state] using selected)
      | union parentEntry members level free =>
        by_cases visited : parentEntry.identity ∈ seen
        · simpa only [MergedFreshOrdinaryExposure.collect,ite_eq_left visited] using
            ih before semantic costs seen rest tail
              (by simpa only [MergedFreshOrdinaryExposure.collect,ite_eq_left visited] using selected)
        · have next : Values before (members ++ rest) := by
            intro value member
            rcases List.mem_append.mp member with first | later
            · exact own.children value first
            · exact tail value later
          simpa only [MergedFreshOrdinaryExposure.collect,ite_eq_right visited] using
            ih before semantic costs (parentEntry.identity :: seen) (members ++ rest) next
              (by simpa only [MergedFreshOrdinaryExposure.collect,ite_eq_right visited] using selected)
      | mu parentEntry parentBody parentDepth parentOrdinary =>
        by_cases visited : parentEntry.identity ∈ seen
        · simpa only [MergedFreshOrdinaryExposure.collect,ite_eq_left visited] using
            ih before semantic costs seen rest tail
              (by simpa only [MergedFreshOrdinaryExposure.collect,ite_eq_left visited] using selected)
        · obtain ⟨value,middle,done,kept,middleSemantic,valueAvailable,_⟩ :=
            SourceEqualityOpenOrdinaryHead.unfold_complete (.mu parentEntry parentBody parentDepth parentOrdinary)
              before semantic own
          obtain ⟨first⟩ := SourceCurrentHeadIssuedHistory.unfold
            (.mu parentEntry parentBody parentDepth parentOrdinary) before semantic.ready own
          have firstPath : Path before middle := by simpa only [done,Outcome.state] using first
          have middleCosts : CostHeap middle := by
            simpa only [done,Outcome.state] using InternedFreshOrdinaryStoredSubstitution.unfold_cost_heap
              (.mu parentEntry parentBody parentDepth parentOrdinary) before semantic.ready.semantic.1
              semantic.ready.semantic.2 costs own
          have next : Values middle (value :: rest) := by
            intro value member
            rcases List.mem_cons.mp member with rfl | later
            · exact valueAvailable
            · exact kept.available value (tail value later)
          have selectedLater : (MergedFreshOrdinaryExposure.collect fuel middle
              (parentEntry.identity :: seen) (value :: rest)).state.nodeRecords key = some (.mu entry body depth ordinary) := by
            simpa only [MergedFreshOrdinaryExposure.collect,ite_eq_right visited,done] using selected
          obtain ⟨⟨last⟩,route⟩ := ih middle middleSemantic middleCosts (parentEntry.identity :: seen) (value :: rest) next selectedLater
          have result := through_unfold parentEntry parentBody parentDepth parentOrdinary before semantic costs own
            value middle _ done firstPath last key entry body depth ordinary route
          simpa only [MergedFreshOrdinaryExposure.collect,ite_eq_right visited,done] using
            (show Nonempty (Path before _) ∧ _ from ⟨⟨.trans firstPath last⟩,result⟩)

private theorem nodeEdges [DecidableEq (EdgeKey Symbol Guard)]
    (fuel : Nat) (value : Value Symbol Guard) (before : State Symbol Guard)
    (semantic : SemanticReady before) (costs : CostHeap before) (available : Available before value)
    (key : InternedBinderProtocol.NodeKey) (entry : Interned InternedBinderProtocol.NodeKey)
    (body depth ordinary : Value Symbol Guard)
    (selected : (MergedFreshOrdinaryExposure.nodeEdges fuel value before).state.nodeRecords key =
      some (.mu entry body depth ordinary)) :
    before.nodeRecords key = some (.mu entry body depth ordinary) ∨
      Generated before (MergedFreshOrdinaryExposure.nodeEdges fuel value before).state
        key (.mu entry body depth ordinary) := by
  have fallback (current : State Symbol Guard) (currentSemantic : SemanticReady current) (currentCosts : CostHeap current)
      (root : Value Symbol Guard) (rootAvailable : Available current root)
      (present : (MergedFreshOrdinaryExposure.collect fuel current [] [root]).canonical.state.nodeRecords key =
        some (.mu entry body depth ordinary)) :=
    collect fuel current currentSemantic currentCosts [] [root]
      (by intro child member; simpa only [List.mem_singleton.mp member] using rootAvailable)
      key entry body depth ordinary (by simpa only [SourceEqualityAnnotationExposure.canonical_state] using present)
  cases value with
  | empty | reference | node => exact .inl selected
  | union =>
    have next := fallback before semantic costs _ available selected
    simpa only [MergedFreshOrdinaryExposure.nodeEdges,SourceEqualityAnnotationExposure.canonical_state] using next.2
  | mu parentEntry parentBody parentDepth parentOrdinary =>
    obtain ⟨result,middle,done,kept,middleSemantic,_resultAvailable,_⟩ :=
      SourceEqualityOpenOrdinaryHead.unfold_complete (.mu parentEntry parentBody parentDepth parentOrdinary)
        before semantic available
    obtain ⟨first⟩ := SourceCurrentHeadIssuedHistory.unfold
      (.mu parentEntry parentBody parentDepth parentOrdinary) before semantic.ready available
    have firstPath : Path before middle := by simpa only [done,Outcome.state] using first
    have middleCosts : CostHeap middle := by
      simpa only [done,Outcome.state] using InternedFreshOrdinaryStoredSubstitution.unfold_cost_heap
        (.mu parentEntry parentBody parentDepth parentOrdinary) before semantic.ready.semantic.1
        semantic.ready.semantic.2 costs available
    have next (present : (MergedFreshOrdinaryExposure.collect fuel middle []
        [.mu parentEntry parentBody parentDepth parentOrdinary]).canonical.state.nodeRecords key =
          some (.mu entry body depth ordinary)) :
        before.nodeRecords key = some (.mu entry body depth ordinary) ∨
          Generated before (MergedFreshOrdinaryExposure.collect fuel middle []
            [.mu parentEntry parentBody parentDepth parentOrdinary]).canonical.state key (.mu entry body depth ordinary) := by
      obtain ⟨⟨last⟩,route⟩ := fallback middle middleSemantic middleCosts
        (.mu parentEntry parentBody parentDepth parentOrdinary) (kept.available _ available) present
      simpa only [SourceEqualityAnnotationExposure.canonical_state] using
        through_unfold parentEntry parentBody parentDepth parentOrdinary before semantic costs available result middle _
          done firstPath last key entry body depth ordinary route
    cases result with
    | node =>
      have present : middle.nodeRecords key = some (.mu entry body depth ordinary) := by
        simpa only [MergedFreshOrdinaryExposure.nodeEdges,done,MergedSourceExposure.Result.state] using selected
      simpa only [MergedFreshOrdinaryExposure.nodeEdges,done,MergedSourceExposure.Result.state] using
        through_unfold parentEntry parentBody parentDepth parentOrdinary before semantic costs available _ middle middle
          done firstPath (.refl middle) key entry body depth ordinary (.inl present)
    | empty | reference | union | mu =>
      simpa only [MergedFreshOrdinaryExposure.nodeEdges,done] using
        next (by simpa only [MergedFreshOrdinaryExposure.nodeEdges,done] using selected)

/-- An actual Head selects an initial full cell or recovers the actual stored unfold and its same generated writer. -/
theorem head [DecidableEq (EdgeKey Symbol Guard)]
    {value result : Value Symbol Guard} {before after : State Symbol Guard}
    (actual : SourceEqualityRequiredHead.Head value before result after)
    (semantic : SemanticReady before) (costs : CostHeap before) (available : Available before value)
    (key : InternedBinderProtocol.NodeKey) (entry : Interned InternedBinderProtocol.NodeKey)
    (body depth ordinary : Value Symbol Guard)
    (selected : after.nodeRecords key = some (.mu entry body depth ordinary)) :
    before.nodeRecords key = some (.mu entry body depth ordinary) ∨
    ∃ parentEntry parentBody parentDepth parentOrdinary operationBefore operationResult operationAfter,
      SemanticReady operationBefore ∧ CostHeap operationBefore ∧
      Available operationBefore (.mu parentEntry parentBody parentDepth parentOrdinary) ∧
      InternedFreshOrdinaryStoredSubstitution.unfold (.mu parentEntry parentBody parentDepth parentOrdinary)
        operationBefore = .done operationResult operationAfter ∧
      operationBefore.nodeRecords key = none ∧
      operationAfter.nodeRecords key = some (.mu entry body depth ordinary) ∧
      Nonempty (Path before operationBefore) ∧ Grows operationAfter after ∧
      Extends operationAfter.nodes.issued after.nodes.issued ∧
      Context operationBefore ((leaves parentBody).map (input (fun name =>
        if name = .interned parentEntry.identity then some (.mu parentEntry parentBody parentDepth parentOrdinary) else none))) ∧
      InternedFreshOrdinaryConstruction.build (encode (leaves parentBody) [] parentBody)
        ((leaves parentBody).map (input (fun name =>
          if name = .interned parentEntry.identity then some (.mu parentEntry parentBody parentDepth parentOrdinary) else none)))
        operationBefore = .done operationResult operationAfter ∧
      Written (encode (leaves parentBody) [] parentBody)
        ((leaves parentBody).map (input (fun name =>
          if name = .interned parentEntry.identity then some (.mu parentEntry parentBody parentDepth parentOrdinary) else none)))
        operationBefore operationAfter key (.mu entry body depth ordinary) := by
  cases actual with
  | read fuel edges middle exposed rebuilt =>
    have old := InternedShallowHeap.makeNode_noNewMu edges middle
    rw [rebuilt] at old
    have present : middle.nodeRecords key = some (.mu entry body depth ordinary) :=
      old key entry body depth ordinary selected
    have found := nodeEdges fuel value before semantic costs available key entry body depth ordinary
      (by simpa only [exposed,MergedSourceExposure.Result.state] using present)
    rcases found with prior | generated
    · exact .inl prior
    · have effects := SourceEqualityProjectionCosts.read_effects (.done fuel exposed) semantic costs available
      have valid := effects.2.1.ready.semantic.1.normal.facts.coherent.valid
      have growth := (InternedConstructorTemplates.run_correct (makeNode edges) middle valid).2
      have issued := InternedProbeProvenance.run_issued_extends (makeNode edges) middle valid
      rw [rebuilt] at growth issued
      have actualGenerated : Generated before middle key (.mu entry body depth ordinary) := by
        simpa only [exposed,MergedSourceExposure.Result.state] using generated
      exact .inr (generated_later actualGenerated growth issued)

end MicroCFTA.SourceCurrentHeadMuGeneration

set_option linter.all true
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.proofs true
set_option pp.proofs.threshold 254
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000

#check @MicroCFTA.SourceCurrentHeadMuGeneration.head
#print MicroCFTA.SourceCurrentHeadMuGeneration.head
#print axioms MicroCFTA.SourceCurrentHeadMuGeneration.head
