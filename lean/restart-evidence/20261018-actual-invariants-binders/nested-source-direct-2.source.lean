import MicroCFTA.SourceCurrentNativeBinderExecution
import MicroCFTA.SourceCurrentNativeNormalizedComparisonExecution
import MicroCFTA.SourceCurrentStoredReconstruction

/-!
# Actual nested source binders with an inert local

Static free-name support excludes the supplied lexical argument.
The actual Depth callback makes the ordinary argument fresh for captures.
The raw ordinary result then needs no root filter or bare-self erasure.
Actual source history selects the earlier winner before smart cleanup.
-/
namespace MicroCFTA.SourceCurrentNestedSourceInertBinder
open Cache InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedNestedConstruction (Syntax Outcome work request finish)
open InternedNestedProvenance (Values)
open InternedFreshOrdinaryConstruction InternedFreshOrdinaryFacts
open InternedBinderProtocol (Reference NodeKey)
open SourceEqualityRequiredCache (Ready Keeps)
open SourceCurrentNativeMuPublication (History)

/-- The pure source support has no contribution from the supplied local slot. -/
def Inert (body : Syntax Symbol Guard) (captures : List (Value Symbol Guard)) : Prop :=
  InternedProfileCallbackForm.usesArgument
    (InternedFreeNameForm.symbolic body (captures.map InternedRootProfile.profile) (captures.map Value.free)) = false

private theorem filter_absent [DecidableEq (EdgeKey Symbol Guard)]
    (name : Reference) (value : Value Symbol Guard) (state : State Symbol Guard)
    (coherent : Coherent state) (available : Available state value) (absent : name ∉ value.free) :
    run (withoutSelfReference name value) state = (value,state) := by
  cases value with
  | empty | reference | node | mu => rfl
  | union entry members depth free =>
      have missing : Value.reference name ∉ members := by
        intro member
        apply absent
        rw [Value.free,InternedNormalizationFree.union_free state coherent entry members depth free available.resident,
          childFree_member]
        exact ⟨.reference name,member,by simp [Value.free]⟩
      rw [withoutSelfReference_absent name entry members depth free missing]
      rfl

/-- Actual Depth freshness and static support exclude the ordinary argument from the raw body result. -/
theorem raw_ordinary_absent [DecidableEq (EdgeKey Symbol Guard)]
    (body : Syntax Symbol Guard) (captures : List (Value Symbol Guard))
    (before afterDepth afterRaw : State Symbol Guard)
    (context : InternedFreshOrdinaryContext.Context before captures)
    (inert : Inert body captures) (depth raw : Value Symbol Guard)
    (depthDone : callback body captures .depth before = .done depth afterDepth)
    (rawDone : build body (.reference (.uninterned (ordinaryLevel depth)) :: captures) afterDepth =
      .done raw afterRaw) :
    .uninterned (ordinaryLevel depth) ∉ raw.free := by
  have afterContext : InternedFreshOrdinaryContext.Context afterDepth captures := by
    simpa only [depthDone,Outcome.state] using context.callback body .depth (InternedNestedProvenance.depth_available before)
  have localContext := afterContext.local (.uninterned (ordinaryLevel depth))
    (InternedNestedProvenance.ordinary_available afterDepth (ordinaryLevel depth))
  have free := (InternedFreshOrdinaryFreeNames.build_free body _ afterDepth localContext.normal
    localContext.inputs localContext.freeNames localContext.profiles).result raw afterRaw rawDone
  intro present
  have supplied := (free (.uninterned (ordinaryLevel depth))).mp present
  simp only [List.map_cons,InternedRootProfile.profile,Value.free] at supplied
  rw [InternedFreeNameForm.supplied_member] at supplied
  rcases supplied with captured | ⟨used,_⟩
  · have observed := (InternedFreshOrdinarySourceFreeNames.callback_other body captures .depth before
      context.normal (context.local .depth (InternedNestedProvenance.depth_available before)).inputs
      context.freeNames context.profiles depth afterDepth depthDone
      (.uninterned (ordinaryLevel depth)) (by intro impossible; cases impossible)).mpr captured
    exact ordinary_fresh depth observed
  · rw [Inert] at inert
    rw [inert] at used
    cases used

private theorem source_keeps [DecidableEq (EdgeKey Symbol Guard)]
    (expression : Syntax Symbol Guard) (inputs : List (Value Symbol Guard))
    (before after : State Symbol Guard) (ready : Ready before) (available : Values before inputs)
    (value : Value Symbol Guard) (actual : build expression inputs before = .done value after) : Keeps before after := by
  have context := SourceRecursiveIntersectionSemanticHeap.context before ready.semantic inputs available
  have checked := InternedFreshOrdinaryFacts.build_verified expression inputs before ready.semantic.1.normal.facts available
  refine ⟨⟨?_,?_,?_⟩,?_,?_⟩
  · simpa only [actual,Outcome.state] using SourceRecursiveIntersectionSemanticHeap.source expression inputs before ready.semantic available
  · exact InternedFreshOrdinaryCoverage.build_covered expression inputs before
      ready.semantic.1.normal.facts.coherent.valid ready.covered value after actual
  · simpa only [actual,Outcome.state] using
      (InternedOpenDepthExecution.build_depth expression inputs before context ready.semantic.2 ready.depth).heap
  · simpa only [actual,Outcome.state] using checked.growth
  · simpa only [actual,Outcome.state] using checked.history

/-- Initial causal data constructs the smart binder and its unchanged raw ordinary result. -/
theorem complete [DecidableEq (EdgeKey Symbol Guard)]
    (body : Syntax Symbol Guard) (captures : List (Value Symbol Guard))
    (before : State Symbol Guard) (ready : Ready before) (available : Values before captures)
    (past : History empty before) (inert : Inert body captures) :
    ∃ depth afterDepth raw afterRaw after,
      callback body captures .depth before = .done depth afterDepth ∧
      build body (.reference (.uninterned (ordinaryLevel depth)) :: captures) afterDepth = .done raw afterRaw ∧
      run (withoutSelfReference (.uninterned (ordinaryLevel depth)) raw) afterRaw = (raw,afterRaw) ∧
      callback body captures (.uninterned (ordinaryLevel depth)) afterDepth = .done raw afterRaw ∧
      build (.binder true body) captures before = .done raw after ∧
      request true depth raw (callback body captures) afterRaw = .done raw after ∧
      .uninterned (ordinaryLevel depth) ∉ raw.free ∧
      InternedFreshOrdinaryDepthHeap.usesLocal depth raw = false ∧
      Keeps before after ∧ Available after raw ∧
      Nonempty (History before after) ∧ Nonempty (History empty after) := by
  have base := SourceRecursiveIntersectionSemanticHeap.context before ready.semantic captures available
  have context : SourceCurrentConstrainedCapSourceHistory.Context before captures := ⟨base,ready.semantic.2⟩
  obtain ⟨value,after,actual⟩ := InternedRecordDepthCompletion.source_complete (.binder true body) captures before
    base ready.semantic.2 ready.covered
  have kept := source_keeps (.binder true body) captures before after ready available value actual
  obtain ⟨localHistory⟩ := SourceCurrentNativeMuPublication.build_history (.binder true body) captures before context
  have localHistory : History before after := by simpa only [actual,Outcome.state] using localHistory
  have finalHistory : History empty after := .trans past localHistory
  obtain ⟨depth,afterDepth,ordinary,cut,raw,afterRaw,depthDone,ordinaryDone,called,
    depthContext,_cutContext,_finalContext,rawDone,filtered,rawContext,_growth,_issued,depthAvailable,ordinaryAvailable⟩ :=
    SourceCurrentNativeBinderExecution.decompose true body captures before value after context actual
  have absent := raw_ordinary_absent body captures before afterDepth afterRaw base inert depth raw depthDone rawDone
  have rawAvailable := (InternedFreshOrdinaryFacts.build_verified body _ afterDepth
    depthContext.base.normal.facts (depthContext.local (.uninterned (ordinaryLevel depth))
      (InternedNestedProvenance.ordinary_available afterDepth (ordinaryLevel depth))).base.inputs).result raw afterRaw rawDone
  have unchanged := filter_absent (.uninterned (ordinaryLevel depth)) raw afterRaw
    rawContext.base.normal.facts.coherent rawAvailable absent
  have same := unchanged.symm.trans filtered
  obtain ⟨rfl,rfl⟩ := Prod.mk.inj same
  have unused : InternedFreshOrdinaryDepthHeap.usesLocal depth raw = false := by
    simp only [InternedFreshOrdinaryDepthHeap.usesLocal,decide_eq_false_iff_not]
    intro member
    exact absent (InternedDeepFreeNormalization.deep_free raw after kept.ready.semantic.1.normal.facts.coherent
      ordinaryAvailable _ member)
  obtain ⟨entry,storedBody,present,returned⟩ := SourceCurrentNativeRequestProbes.request_probes true depth raw
    (callback body captures) afterRaw value after called kept.ready.semantic.1.normal.facts depthAvailable ordinaryAvailable
  have clean := SourceCurrentNativeNormalizedComparisonExecution.history_unused after finalHistory
    (muKey depth raw) entry storedBody depth raw present unused
  have notBare : raw.referenceOf ≠ .ref (.uninterned (ordinaryLevel depth)) := by
    intro same
    have equal := (referenceOf_self_iff _ raw).mp same
    exact absent (by rw [equal]; simp [Value.free])
  have sameValue : value = raw := returned.trans (clean.trans (by simp [SourceCurrentNativeCallbackErasure.eraseSelf,notBare]))
  rw [sameValue] at actual called
  exact ⟨depth,afterDepth,raw,afterRaw,after,depthDone,rawDone,unchanged,ordinaryDone,actual,called,
    absent,unused,kept,ordinaryAvailable,⟨localHistory⟩,⟨finalHistory⟩⟩

end MicroCFTA.SourceCurrentNestedSourceInertBinder
