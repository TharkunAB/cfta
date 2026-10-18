import MicroCFTA.SourceCurrentRetainedMuDirectedCase
import MicroCFTA.SourceCurrentSourceEmptyAbstraction
import MicroCFTA.SourceCurrentStoredNonemptyReplacement
import MicroCFTA.InternedFilterEmptiness

/-!
# Physical Empty agreement for actual filtered source reconstructions

Varying lexical references are nonempty. Fixed captures retain their exact
values. Actual source calls therefore have equal Empty tests. Root filtering
and stored reconstruction with nonempty replacements retain those tests.
The binder endpoint recovers the actual selected earlier writer.
This module does not prove observation or directional simulation laws.
-/
namespace MicroCFTA.SourceCurrentFilteredNonemptyFusion
open Cache InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedNestedConstruction (Syntax Outcome)
open InternedFreshOrdinaryConstruction InternedFreshOrdinaryFacts
open InternedFreshOrdinaryStoredSubstitution (execute unfold)
open InternedStoredSubstitution (Environment Replacements)
open InternedFreshOrdinaryLiveInputs (input)
open InternedBinderProtocol (Reference)
open SourceCurrentConstrainedCapSourceHistory (Context)
open SourceCurrentNativeMuPublication (Publication)
open SourceCurrentNativeMuGrowthHistory (Path)
open SourceCurrentNativeMuGrowthWriters (Written)
open SourceCurrentStoredMuBinderChildLineage (bind)
open SourceCurrentRetainedMuDirectedCase (Generated)
open SourceEqualityRequiredCache (Ready Keeps)

private theorem lexical_empty (inputs : List (Sum (Value Symbol Guard) Atom))
    (firstNames secondNames : Atom → Reference) :
    (inputs.map (input firstNames)).map (fun value => value.referenceOf == .empty) =
      (inputs.map (input secondNames)).map (fun value => value.referenceOf == .empty) := by
  simp only [List.map_map]
  apply List.map_congr_left
  intro value _
  cases value <;> rfl

private theorem filter_empty [DecidableEq (EdgeKey Symbol Guard)] (expression : Syntax Symbol Guard)
    (inputs : List (Value Symbol Guard)) (before : State Symbol Guard)
    (context : InternedFreshOrdinaryContext.Context before inputs)
    (raw : Value Symbol Guard) (rawHeap : State Symbol Guard)
    (built : build expression inputs before = .done raw rawHeap)
    (own : Reference) (filtered : Value Symbol Guard) (after : State Symbol Guard)
    (actual : run (withoutSelfReference own raw) rawHeap = (filtered,after)) :
    (filtered.referenceOf == .empty) = (raw.referenceOf == .empty) := by
  have returned : InternedFreshOrdinaryContext.Context rawHeap inputs := by
    simpa only [built,Outcome.state] using context.build expression
  have available := (build_verified expression inputs before context.normal.facts context.inputs).result raw rawHeap built
  have same := InternedFilterEmptiness.filter_empty_iff own raw rawHeap returned.normal.facts.coherent
    returned.normal.facts.linked returned.normal.live returned.normal.proper returned.normal.members available
  apply Bool.eq_iff_iff.mpr
  simpa only [actual,beq_iff_eq] using same

variable [DecidableEq (EdgeKey Symbol Guard)]

/-- Actual source, filter and stored calls derive Empty agreement from nonempty replacements. -/
theorem filtered (expression : Syntax Symbol Guard) (inputs : List (Sum (Value Symbol Guard) Atom))
    (firstNames secondNames : Atom → Reference) (firstOwn secondOwn : Reference)
    (firstBefore secondBefore firstRawHeap secondRawHeap firstFilterHeap secondFilterHeap : State Symbol Guard)
    (firstRaw secondRaw firstFiltered secondFiltered : Value Symbol Guard)
    (firstContext : Context firstBefore (inputs.map (input firstNames)))
    (secondContext : Context secondBefore (inputs.map (input secondNames)))
    (firstBuild : build expression (inputs.map (input firstNames)) firstBefore = .done firstRaw firstRawHeap)
    (secondBuild : build expression (inputs.map (input secondNames)) secondBefore = .done secondRaw secondRawHeap)
    (firstFilter : run (withoutSelfReference firstOwn firstRaw) firstRawHeap = (firstFiltered,firstFilterHeap))
    (secondFilter : run (withoutSelfReference secondOwn secondRaw) secondRawHeap = (secondFiltered,secondFilterHeap))
    (firstMap secondMap : Environment Symbol Guard) (firstEntry secondEntry : State Symbol Guard)
    (firstReady : Ready firstEntry) (secondReady : Ready secondEntry)
    (firstAvailable : Available firstEntry firstFiltered) (secondAvailable : Available secondEntry secondFiltered)
    (firstReplacements : Replacements firstEntry firstMap) (secondReplacements : Replacements secondEntry secondMap)
    (left right : Value Symbol Guard) (after final : State Symbol Guard)
    (firstDone : execute firstFiltered firstMap firstEntry = .done left after)
    (secondDone : execute secondFiltered secondMap secondEntry = .done right final)
    (firstNonempty : ∀ name ∈ firstFiltered.free, ((firstMap name).getD (.reference name)).referenceOf ≠ .empty)
    (secondNonempty : ∀ name ∈ secondFiltered.free, ((secondMap name).getD (.reference name)).referenceOf ≠ .empty) :
    (left.referenceOf == .empty) = (right.referenceOf == .empty) := by
  have raw := SourceCurrentSourceEmptyAbstraction.source expression _ _ firstBefore firstRawHeap secondBefore secondRawHeap
    firstContext.base secondContext.base firstRaw secondRaw firstBuild secondBuild (lexical_empty inputs firstNames secondNames)
  have first := filter_empty expression _ firstBefore firstContext.base firstRaw firstRawHeap firstBuild firstOwn
    firstFiltered firstFilterHeap firstFilter
  have second := filter_empty expression _ secondBefore secondContext.base secondRaw secondRawHeap secondBuild secondOwn
    secondFiltered secondFilterHeap secondFilter
  have firstStored := SourceCurrentStoredNonemptyReplacement.execute_nonempty firstFiltered firstMap firstEntry
    firstReady firstAvailable firstReplacements left after firstDone firstNonempty
  have secondStored := SourceCurrentStoredNonemptyReplacement.execute_nonempty secondFiltered secondMap secondEntry
    secondReady secondAvailable secondReplacements right final secondDone secondNonempty
  exact firstStored.trans (first.trans (raw.trans (second.symm.trans secondStored.symm)))

/-- One actual publication aligns its body and ordinary calls under its nonempty Mu replacement. -/
theorem publication (event : Publication (Symbol := Symbol) (Guard := Guard))
    (firstEntry secondEntry : State Symbol Guard) (firstReady : Ready firstEntry) (secondReady : Ready secondEntry)
    (firstAvailable : Available firstEntry event.candidate) (secondAvailable : Available secondEntry event.candidate)
    (left right : Value Symbol Guard) (after final : State Symbol Guard)
    (firstDone : execute event.body (bind (.interned event.entry.identity) event.candidate (fun _ => none))
      firstEntry = .done left after)
    (secondDone : execute event.ordinary (bind (.uninterned (ordinaryLevel event.depth)) event.candidate (fun _ => none))
      secondEntry = .done right final) :
    (left.referenceOf == .empty) = (right.referenceOf == .empty) := by
  obtain ⟨ordinary,ordinaryHeap,body,bodyHeap,ordinaryBuild,ordinaryFilter,bodyBuild,bodyFilter,
    _,_,ordinaryContext,bodyContext⟩ := SourceCurrentNativeMuPublicationCallbacks.raw_callbacks event
  have cutContext := (SourceCurrentNativeMuPublicationCallbacks.contexts event).2.1
  have bodyArgument := (InternedConstructionProvenance.reserve_available event.key event.cut
    cutContext.base.normal.facts.coherent cutContext.base.normal.facts.cached).2
  have firstContext := bodyContext.local (.interned event.entry.identity) bodyArgument
  have secondContext := ordinaryContext.local (.uninterned (ordinaryLevel event.depth))
    (InternedNestedProvenance.ordinary_available _ _)
  let inputs : List (Sum (Value Symbol Guard) Unit) := .inr () :: event.environment.map Sum.inl
  let firstNames : Unit → Reference := fun _ => .interned event.entry.identity
  let secondNames : Unit → Reference := fun _ => .uninterned (ordinaryLevel event.depth)
  have instantiated (names : Unit → Reference) : inputs.map (input names) = .reference (names ()) :: event.environment := by
    simp [inputs,input,List.map_map,Function.comp_def]
  have replacements (own : Reference) (state : State Symbol Guard) (available : Available state event.candidate) :
      Replacements state (bind own event.candidate (fun _ => none)) := by
    intro name value found
    dsimp only [SourceCurrentStoredMuBinderChildLineage.bind] at found
    split at found
    · cases found; exact available
    · cases found
  have nonempty (own : Reference) (name : Reference) :
      (((bind own event.candidate (fun _ => none)) name).getD (.reference name)).referenceOf ≠ .empty := by
    dsimp only [SourceCurrentStoredMuBinderChildLineage.bind]
    split <;> simp [Publication.candidate,Value.referenceOf]
  exact filtered event.expression inputs firstNames secondNames _ _ event.allocated event.afterDepth bodyHeap ordinaryHeap
    event.afterBody event.cut body ordinary event.body event.ordinary
    (by simpa only [instantiated,firstNames] using firstContext)
    (by simpa only [instantiated,secondNames] using secondContext)
    (by simpa only [instantiated,firstNames] using bodyBuild)
    (by simpa only [instantiated,secondNames] using ordinaryBuild)
    bodyFilter ordinaryFilter _ _ firstEntry secondEntry firstReady secondReady
    (firstAvailable.children _ (by simp [Publication.candidate,children]))
    (secondAvailable.children _ (by simp [Publication.candidate,children]))
    (replacements _ _ firstAvailable) (replacements _ _ secondAvailable)
    left right after final firstDone secondDone (fun name _ => nonempty _ name) (fun name _ => nonempty _ name)

/-- Actual binder execution derives Empty agreement at the recovered earlier writer's reconstruction endpoints. -/
theorem binder (smart : Bool) (expression : Syntax Symbol Guard) (environment : List (Value Symbol Guard))
    (before : State Symbol Guard) (result : Value Symbol Guard) (after : State Symbol Guard)
    (context : Context before environment)
    (actual : build (.binder smart expression) environment before = .done result after)
    (reader : State Symbol Guard) (current : Keeps after reader) (history : Path empty reader) :
    ∃ depth ordinary entry body, ∃ event : Publication (Symbol := Symbol) (Guard := Guard), ∃ left middle right final,
      reader.nodeRecords (muKey depth ordinary) = some (.mu entry body depth ordinary) ∧
      result = InternedNestedConstruction.finish smart (.mu entry body depth ordinary) ∧
      Written empty reader (muKey depth ordinary) (.mu entry body depth ordinary) ∧
      event.key = muKey depth ordinary ∧ event.candidate = .mu entry body depth ordinary ∧
      unfold (.mu entry body depth ordinary) reader = .done left middle ∧
      execute ordinary (bind (.uninterned (ordinaryLevel depth)) (.mu entry body depth ordinary) (fun _ => none))
        middle = .done right final ∧
      unfold (.mu entry body depth ordinary) final = .done left final ∧
      execute ordinary (bind (.uninterned (ordinaryLevel depth)) (.mu entry body depth ordinary) (fun _ => none))
        final = .done right final ∧
      left ∈ MergedFreshOrdinaryGraph.successors reader (.mu entry body depth ordinary) ∧
      Keeps reader middle ∧ Keeps middle final ∧ Available final left ∧ Available final right ∧
      Generated final left right ∧ Generated final right left ∧
      (left.referenceOf == .empty) = (right.referenceOf == .empty) := by
  obtain ⟨depth,ordinary,entry,body,event,left,middle,right,final,selected,returned,written,
    keySame,valueSame,missing,writerPrefix,depthPath,ordinaryPath,bodyPath,eventGrowth,
    firstDone,secondDone,firstWarm,secondWarm,epsilon,finalEpsilon,firstKept,secondKept,
    leftAvailable,rightAvailable,generated,reverse⟩ :=
    SourceCurrentRetainedMuDirectedCase.binder smart expression environment before result after context actual reader current history
  have finalKept := firstKept.trans secondKept
  have selectedAvailable := finalKept.ready.semantic.1.normal.facts.cached.nodes (muKey depth ordinary) _
    (finalKept.growth.nodeRecords _ _ selected)
  have payload : Value.mu event.entry event.body event.depth event.ordinary = Value.mu entry body depth ordinary := valueSame
  obtain ⟨sameEntry,sameBody,sameDepth,sameOrdinary⟩ := Value.mu.inj payload
  have bodyWarm : execute event.body (bind (.interned event.entry.identity) event.candidate (fun _ => none))
      final = .done left final := by
    rw [sameEntry,sameBody,valueSame]
    exact firstWarm
  have ordinaryWarm : execute event.ordinary (bind (.uninterned (ordinaryLevel event.depth)) event.candidate (fun _ => none))
      final = .done right final := by
    rw [sameDepth,sameOrdinary,valueSame]
    exact secondWarm
  have same := publication event final final finalKept.ready finalKept.ready
    (valueSame.symm ▸ selectedAvailable) (valueSame.symm ▸ selectedAvailable) left right final final bodyWarm ordinaryWarm
  exact ⟨depth,ordinary,entry,body,event,left,middle,right,final,selected,returned,written,keySame,valueSame,
    firstDone,secondDone,firstWarm,secondWarm,epsilon,firstKept,secondKept,leftAvailable,rightAvailable,generated,reverse,same⟩

end MicroCFTA.SourceCurrentFilteredNonemptyFusion
