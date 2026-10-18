import MicroCFTA.SourceCurrentNativeMuGrowthWriters
import MicroCFTA.InternedFreshOrdinaryCallbackDepth

/-!
# Strict original callback depth at a selected Mu writer

The actual three callback calls have equal physical depth. Each raw body
therefore has smaller depth than the selected Mu record. The source syntax
of an earlier writer can be larger than the current requester's syntax.
These bounds concern original callback values. They do not bound values
that a later replacement map reconstructs.
-/
namespace MicroCFTA.SourceCurrentBinderFusionInduction
open Cache InternedConstructorTemplates InternedProbeProvenance
open InternedNestedConstruction (Outcome)
open InternedFreshOrdinaryConstruction InternedFreshOrdinaryFacts
open InternedBinderProtocol (Reference NodeKey)
open SourceCurrentConstrainedCapSourceHistory (Context)
open SourceCurrentNativeMuPublication (Publication)

private theorem callback_depth [DecidableEq (EdgeKey Symbol Guard)]
    (expression : InternedNestedConstruction.Syntax Symbol Guard)
    (environment : List (Value Symbol Guard)) (name : Reference)
    (before : State Symbol Guard) (context : Context before environment)
    (available : Available before (.reference name)) (value : Value Symbol Guard)
    (after : State Symbol Guard) (actual : callback expression environment name before = .done value after) :
    value.depth = (InternedRecordDepthCallback.symbolic expression environment).depth :=
  ((InternedRecordDepthExecution.callback_depth expression environment name before context.base
    available context.depth).result value after actual).1

private theorem raw_depth [DecidableEq (EdgeKey Symbol Guard)]
    (expression : InternedNestedConstruction.Syntax Symbol Guard)
    (environment : List (Value Symbol Guard)) (name : Reference)
    (before : State Symbol Guard) (context : Context before environment)
    (available : Available before (.reference name)) (value : Value Symbol Guard)
    (after : State Symbol Guard) (actual : callback expression environment name before = .done value after)
    (raw : Value Symbol Guard) (middle : State Symbol Guard)
    (build : InternedFreshOrdinaryConstruction.build expression (.reference name :: environment) before =
      .done raw middle) : raw.depth = value.depth := by
  obtain ⟨other, next, returned, sameDepth⟩ :=
    InternedFreshOrdinaryCallbackDepth.callback_depth expression environment name before context.base.normal
      (context.base.local name available).inputs value after actual
  have same := (Outcome.done.inj (returned.symm.trans build)).1
  simpa only [same] using sameDepth.symm

/-- Actual raw callbacks have equal depth and lie strictly below their published Mu record. -/
theorem publication [DecidableEq (EdgeKey Symbol Guard)]
    (event : Publication (Symbol := Symbol) (Guard := Guard)) :
    ∃ rawOrdinary ordinaryHeap rawBody bodyHeap,
      build event.expression (.reference (.uninterned (ordinaryLevel event.depth)) :: event.environment)
        event.afterDepth = .done rawOrdinary ordinaryHeap ∧
      run (withoutSelfReference (.uninterned (ordinaryLevel event.depth)) rawOrdinary) ordinaryHeap =
        (event.ordinary, event.cut) ∧
      build event.expression (.reference (.interned event.entry.identity) :: event.environment)
        event.allocated = .done rawBody bodyHeap ∧
      run (withoutSelfReference (.interned event.entry.identity) rawBody) bodyHeap =
        (event.body, event.afterBody) ∧
      Context event.afterDepth event.environment ∧ Context event.allocated event.environment ∧
      Grows ordinaryHeap event.afterBody ∧ Grows bodyHeap event.afterBody ∧
      rawOrdinary.depth = event.ordinary.depth ∧ rawBody.depth = event.body.depth ∧
      event.ordinary.depth = event.body.depth ∧ event.body.depth = event.depth.depth ∧
      rawOrdinary.depth < event.candidate.depth ∧ rawBody.depth < event.candidate.depth := by
  obtain ⟨rawOrdinary, ordinaryHeap, rawBody, bodyHeap, ordinaryBuild, ordinaryFilter, bodyBuild,
    bodyFilter, ordinaryGrowth, bodyGrowth, ordinaryContext, bodyContext⟩ :=
    SourceCurrentNativeMuPublicationCallbacks.raw_callbacks event
  obtain ⟨_, cutContext, _⟩ := SourceCurrentNativeMuPublicationCallbacks.contexts event
  have ordinaryAvailable := InternedNestedProvenance.ordinary_available event.afterDepth (ordinaryLevel event.depth)
  have bodyAvailable : Available event.allocated (.reference (.interned event.entry.identity)) :=
    (InternedConstructionProvenance.reserve_available event.key event.cut cutContext.base.normal.facts.coherent
      cutContext.base.normal.facts.cached).2
  have originalOrdinary := raw_depth event.expression event.environment _ _ ordinaryContext ordinaryAvailable
    event.ordinary event.cut event.ordinaryDone rawOrdinary ordinaryHeap ordinaryBuild
  have originalBody := raw_depth event.expression event.environment _ _ bodyContext bodyAvailable
    event.body event.afterBody event.bodyDone rawBody bodyHeap bodyBuild
  have depth := callback_depth event.expression event.environment .depth event.before event.context
    (InternedNestedProvenance.depth_available event.before) event.depth event.afterDepth event.depthDone
  have ordinary := callback_depth event.expression event.environment _ _ ordinaryContext ordinaryAvailable
    event.ordinary event.cut event.ordinaryDone
  have body := callback_depth event.expression event.environment _ _ bodyContext bodyAvailable
    event.body event.afterBody event.bodyDone
  refine ⟨rawOrdinary, ordinaryHeap, rawBody, bodyHeap, ordinaryBuild, ordinaryFilter, bodyBuild, bodyFilter,
    ordinaryContext, bodyContext, ordinaryGrowth, bodyGrowth, originalOrdinary, originalBody,
    ordinary.trans body.symm, body.trans depth.symm, ?_, ?_⟩
  · change rawOrdinary.depth < event.body.depth + 1
    rw [originalOrdinary, ordinary.trans body.symm]
    exact Nat.lt_succ_self _
  · change rawBody.depth < event.body.depth + 1
    rw [originalBody]
    exact Nat.lt_succ_self _

/-- A selected earlier writer supplies the same strict original-depth bounds at the actual reader. -/
theorem writer [DecidableEq (EdgeKey Symbol Guard)]
    {before reader : State Symbol Guard} {key : NodeKey} {value : Value Symbol Guard}
    (written : SourceCurrentNativeMuGrowthWriters.Written before reader key value) :
    ∃ event : Publication (Symbol := Symbol) (Guard := Guard),
      key = event.key ∧ value = event.candidate ∧
      ∃ rawOrdinary ordinaryHeap rawBody bodyHeap,
        build event.expression (.reference (.uninterned (ordinaryLevel event.depth)) :: event.environment)
          event.afterDepth = .done rawOrdinary ordinaryHeap ∧
        run (withoutSelfReference (.uninterned (ordinaryLevel event.depth)) rawOrdinary) ordinaryHeap =
          (event.ordinary, event.cut) ∧
        build event.expression (.reference (.interned event.entry.identity) :: event.environment)
          event.allocated = .done rawBody bodyHeap ∧
        run (withoutSelfReference (.interned event.entry.identity) rawBody) bodyHeap =
          (event.body, event.afterBody) ∧
        Context event.afterDepth event.environment ∧ Context event.allocated event.environment ∧
        Grows ordinaryHeap reader ∧ Grows bodyHeap reader ∧
        rawOrdinary.depth = event.ordinary.depth ∧ rawBody.depth = event.body.depth ∧
        event.ordinary.depth = event.body.depth ∧ event.body.depth = event.depth.depth ∧
        rawOrdinary.depth < value.depth ∧ rawBody.depth < value.depth := by
  obtain ⟨event, sameKey, sameValue, _, _, _, _, _, growth⟩ := written
  obtain ⟨rawOrdinary, ordinaryHeap, rawBody, bodyHeap, ordinaryBuild, ordinaryFilter, bodyBuild,
    bodyFilter, ordinaryContext, bodyContext, ordinaryGrowth, bodyGrowth, originalOrdinary,
    originalBody, sameDepth, probeDepth, ordinaryLess, bodyLess⟩ := publication event
  have later := grows_trans (SourceCurrentNativeMuGrowthHistory.publication_growth event) growth
  exact ⟨event, sameKey, sameValue, rawOrdinary, ordinaryHeap, rawBody, bodyHeap, ordinaryBuild,
    ordinaryFilter, bodyBuild, bodyFilter, ordinaryContext, bodyContext,
    grows_trans ordinaryGrowth later, grows_trans bodyGrowth later, originalOrdinary, originalBody,
    sameDepth, probeDepth, sameValue.symm ▸ ordinaryLess, sameValue.symm ▸ bodyLess⟩

end MicroCFTA.SourceCurrentBinderFusionInduction
