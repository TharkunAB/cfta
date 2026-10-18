import MicroCFTA.SourceCurrentStoredMuRowOrigins

/-!
# Literal ordinary rows through stored Mu substitution

A literal row can occur below a root union. It cannot occur below a
retained Mu. Actual stored execution supplies an original-body call for
each such returned row. Its intermediate heaps retain the semantic inputs
and both record and issued-name growth needed for further body reasoning.
-/
namespace MicroCFTA.SourceCurrentStoredMuLiteralRows
open Cache InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedNestedConstruction (Outcome finish)
open InternedFreshOrdinaryConstruction (build ordinaryLevel)
open InternedFreshOrdinaryFacts (callback)
open InternedStoredSubstitution (Environment Replacements leaves input encode)
open InternedFreshOrdinaryStoredSubstitution (execute)
open SourceCurrentConstrainedCapSourceHistory (Context)
open SourceCurrentStoredMuLexicalInputs (shadow)
open SourceCurrentNativeMuPublication (History)
open SourceRecursiveIntersectionSemanticHeap (SemanticHeap)
open SourceCurrentLiteralRootParts (Row)
open InternedBinderProtocol (NodeKey Reference)

private theorem unused (entry : Interned NodeKey) (storedBody depth ordinary : Value Symbol Guard)
    (correct : InternedFreshOrdinaryDepthHeap.Correct entry storedBody depth ordinary)
    (result : Value Symbol Guard) (finished : finish true (.mu entry storedBody depth ordinary) = result)
    (row : EdgeValue Symbol Guard) (literal : Row result row) :
    InternedFreshOrdinaryDepthHeap.usesLocal depth ordinary = false := by
  have bodyOnly : result = storedBody := by
    have actual := finished
    simp only [finish, ite_true, cleanup] at actual
    split at actual
    · exact actual.symm
    · split at actual
      · rw [← actual] at literal
        cases literal
      · rw [← actual] at literal
        cases literal
  have bodyDepth : storedBody.depth = depth.depth := by
    simpa only [finish, Value.depth, InternedFreshOrdinaryDepthHeap.decodedDepth, Bool.not_false,
      Bool.true_or, Bool.false_eq_true, ite_true, ite_false, Nat.add_right_cancel_iff] using (correct false).1
  have smart := (correct true).1
  rw [finished, bodyOnly, bodyDepth] at smart
  cases found : InternedFreshOrdinaryDepthHeap.usesLocal depth ordinary <;>
    simp [InternedFreshOrdinaryDepthHeap.decodedDepth, found] at smart ⊢

private theorem closed [DecidableEq (EdgeKey Symbol Guard)] (value : Value Symbol Guard)
    (environment : Environment Symbol Guard) (before : State Symbol Guard) (noFree : value.free = []) :
    execute value environment before = .done value before := by
  unfold execute
  have captured : leaves value = [value] := by
    rw [leaves.eq_def]
    simp only [noFree, List.isEmpty_nil, ite_true]
  rw [captured]
  have encoded : encode [value] [] value = .var 0 := by
    rw [encode.eq_def]
    simp [noFree, InternedStoredSubstitution.slot]
  rw [encoded]
  simpa only [List.map_cons, List.map_nil, build, List.getElem?_cons_zero, Option.getD_some] using
    congrArg (fun result => (Outcome.done result before : Outcome Symbol Guard (Value Symbol Guard)))
      (InternedStoredSubstitutionScope.input_closed value environment noFree)

/-- Each returned literal row has an actual original-body call with semantic inputs and exact heap growth. -/
theorem mu [DecidableEq (EdgeKey Symbol Guard)] (entry : Interned NodeKey) (body : Value Symbol Guard)
    (depth ordinary : Value Symbol Guard) (environment : Environment Symbol Guard)
    (before : State Symbol Guard) (semantic : SemanticHeap before)
    (available : Available before (.mu entry body depth ordinary)) (replacements : Replacements before environment)
    (value : Value Symbol Guard) (after : State Symbol Guard)
    (actual : execute (.mu entry body depth ordinary) environment before = .done value after)
    (reader : State Symbol Guard) (history : History empty reader) (growth : Grows after reader)
    (row : EdgeValue Symbol Guard) (literal : Row value row) :
    ∃ currentDepth afterDepth raw middle,
      callback (encode (leaves (.mu entry body depth ordinary)) [.interned entry.identity] body)
        ((leaves (.mu entry body depth ordinary)).map (input environment)) .depth before =
          .done currentDepth afterDepth ∧
      execute body (shadow (.interned entry.identity)
        (.reference (.uninterned (ordinaryLevel currentDepth))) environment) afterDepth = .done raw middle ∧
      SemanticHeap afterDepth ∧ Available afterDepth body ∧
      Replacements afterDepth (shadow (.interned entry.identity)
        (.reference (.uninterned (ordinaryLevel currentDepth))) environment) ∧
      Grows afterDepth middle ∧ Extends afterDepth.nodes.issued middle.nodes.issued ∧
      Grows middle after ∧ Extends middle.nodes.issued after.nodes.issued ∧ Row raw row := by
  by_cases noFree : (Value.mu entry body depth ordinary).free = []
  · rw [closed (.mu entry body depth ordinary) environment before noFree] at actual
    have same := Outcome.done.inj actual
    rw [← same.1] at literal
    cases literal
  · have opened : (Value.mu entry body depth ordinary).free.isEmpty = false := by
      simpa only [List.isEmpty_eq_false_iff] using noFree
    let captures := leaves (.mu entry body depth ordinary)
    let expression := encode captures [.interned entry.identity] body
    let inputs := captures.map (input environment)
    have compiled : encode captures [] (.mu entry body depth ordinary) = .binder true expression := by
      rw [encode.eq_def]
      simp only [opened, Bool.false_eq_true, ite_false]
      rfl
    have inputAvailable := InternedStoredSubstitution.inputs_available _ environment before available replacements
    have context : Context before inputs := ⟨SourceRecursiveIntersectionSemanticHeap.context before semantic
      inputs inputAvailable, semantic.2⟩
    change build (encode captures [] (.mu entry body depth ordinary)) inputs before = .done value after at actual
    rw [compiled] at actual
    obtain ⟨currentDepth,afterDepth,currentOrdinary,cut,raw,middle,depthDone,ordinaryDone,requestDone,
      depthContext,_cutContext,finalContext,rawDone,filtered,rawContext,rawGrowth,rawIssued,
      depthAvailable,ordinaryAvailable⟩ :=
      SourceCurrentNativeBinderExecution.decompose true expression inputs before value after context actual
    have depthChecked := InternedFreshOrdinaryFacts.callback_verified expression inputs .depth before
      context.base.normal.facts (context.local .depth (InternedNestedProvenance.depth_available before)).base.inputs
    have depthGrowth : Grows before afterDepth := by
      simpa only [depthDone, Outcome.state] using depthChecked.growth
    have depthIssued : Extends before.nodes.issued afterDepth.nodes.issued := by
      simpa only [depthDone, Outcome.state] using depthChecked.history
    have localContext := depthContext.local (.uninterned (ordinaryLevel currentDepth))
      (InternedNestedProvenance.ordinary_available afterDepth (ordinaryLevel currentDepth))
    have rawChecked := InternedFreshOrdinaryFacts.build_verified expression _ afterDepth
      localContext.base.normal.facts localContext.base.inputs
    have rawAvailable := rawChecked.result raw middle rawDone
    have rawStepGrowth : Grows afterDepth middle := by
      simpa only [rawDone, Outcome.state] using rawChecked.growth
    have rawStepIssued : Extends afterDepth.nodes.issued middle.nodes.issued := by
      simpa only [rawDone, Outcome.state] using rawChecked.history
    obtain ⟨winner,storedBody,present,returned⟩ := SourceCurrentNativeRequestProbes.request_probes
      true currentDepth currentOrdinary _ cut value after requestDone finalContext.base.normal.facts
      depthAvailable ordinaryAvailable
    have correct := finalContext.depth (muKey currentDepth currentOrdinary) winner storedBody _ _ present
    have unusedLocal := unused winner storedBody currentDepth currentOrdinary correct value returned.symm row literal
    have readerCell := growth.nodeRecords (muKey currentDepth currentOrdinary) _ present
    have erased : value = SourceCurrentNativeCallbackErasure.eraseSelf
        (.uninterned (ordinaryLevel currentDepth)) currentOrdinary :=
      returned.trans (SourceCurrentNativeNormalizedComparisonExecution.history_unused reader history
        (muKey currentDepth currentOrdinary) winner storedBody _ _ readerCell unusedLocal)
    have bodyAvailable : Available before body := available.children body (by simp [children])
    have covered : ∀ leaf ∈ leaves body, leaf ∈ captures := by
      intro leaf member
      change leaf ∈ leaves (.mu entry body depth ordinary)
      rw [leaves.eq_def]
      simpa only [opened, Bool.false_eq_true, ite_false] using member
    have bodyCall := SourceCurrentStoredMuLexicalInputs.build_shadow captures body (.interned entry.identity)
      (.reference (.uninterned (ordinaryLevel currentDepth))) environment before afterDepth semantic.1.normal.facts.coherent
      (InternedStoredSubstitution.leaves_available _ before available) bodyAvailable covered
    have executed : execute body (shadow (.interned entry.identity)
        (.reference (.uninterned (ordinaryLevel currentDepth))) environment) afterDepth = .done raw middle := by
      rw [← bodyCall]
      exact rawDone
    have semanticLater : SemanticHeap afterDepth :=
      ⟨⟨depthContext.base.normal,(by intro child member; cases member),depthContext.base.profiles,
        depthContext.base.freeNames⟩,depthContext.depth⟩
    have replacementsLater := SourceCurrentStoredMuLexicalInputs.replacements (.interned entry.identity)
      (.reference (.uninterned (ordinaryLevel currentDepth))) environment before afterDepth replacements
      depthGrowth depthIssued (InternedNestedProvenance.ordinary_available afterDepth (ordinaryLevel currentDepth))
    have preserved := SourceCurrentPublicationFilterSource.filtered_row middle rawContext.base.normal
      (.uninterned (ordinaryLevel currentDepth)) raw rawAvailable row
    rw [filtered] at preserved
    exact ⟨currentDepth,afterDepth,raw,middle,depthDone,executed,semanticLater,
      bodyAvailable.grows before afterDepth depthGrowth depthIssued,replacementsLater,
      rawStepGrowth,rawStepIssued,rawGrowth,rawIssued,preserved.mp (erased ▸ literal)⟩

end MicroCFTA.SourceCurrentStoredMuLiteralRows
