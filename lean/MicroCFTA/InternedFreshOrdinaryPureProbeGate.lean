import MicroCFTA.InternedFreshOrdinaryBodyFilter
import MicroCFTA.InternedFreshOrdinaryContext
import MicroCFTA.InternedFreshOrdinaryStoredSubstitution
import MicroCFTA.InternedPureProbeGate

/-!
# Pure-probe gate progress with the repaired stored executor

The repaired profile heap derives a pure actual body from two pure probes.
The source body filter then supplies a guarded shallow unfolding. That
prepared plan has no binder requests, so both stored executors agree on
the complete result and cache. The strict rank conclusion therefore applies
to the repaired executor itself.
-/
namespace MicroCFTA.InternedFreshOrdinaryPureProbeGate
open Cache InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedNestedConstruction (Syntax Outcome)
open InternedNestedProvenance (Values)
open InternedStoredMuOrigins (Normal)
open InternedRootProfile InternedRootProfileCleanup InternedGateRank
open InternedStoredSelfFilter InternedFreshOrdinaryContext
open InternedBinderProtocol (NodeKey Reference)

/-- Two pure repaired canonical probes force a pure actual stored body. -/
theorem body_pure (entry : Interned NodeKey) (body depth ordinary : Value Symbol Guard)
    (correct : InternedFreshOrdinaryProfileHeap.Correct entry body depth ordinary)
    (depthNames ordinaryNames : List Reference)
    (depthPure : profile depth = some depthNames) (ordinaryPure : profile ordinary = some ordinaryNames) :
    ∃ names, profile body = some names := by
  cases computed : profile body with
  | some names => exact ⟨names, rfl⟩
  | none =>
      have impossible := correct.1.mp (opaque_finish entry body depth ordinary computed)
      simp [InternedProbeDecoder.decode, depthPure, ordinaryPure] at impossible

/-- Available stored records with pure repaired probes have actual body depth zero. -/
theorem body_zero (entry : Interned NodeKey) (body depth ordinary : Value Symbol Guard)
    (state : State Symbol Guard) (context : Context state captures)
    (available : Available state (.mu entry body depth ordinary))
    (depthNames ordinaryNames : List Reference)
    (depthPure : profile depth = some depthNames) (ordinaryPure : profile ordinary = some ordinaryNames) :
    body.depth = 0 := by
  obtain ⟨names, pure⟩ := body_pure entry body depth ordinary
    (context.profiles entry.key entry body depth ordinary (available.resident entry rfl))
    depthNames ordinaryNames depthPure ordinaryPure
  exact InternedPureProbeGate.pure_depth_zero body state context.normal.facts.coherent
    (available.children body (by simp [children])) names pure

/-- A depth-zero stored body uses an identical prepared plan in both executors. -/
theorem unfold_shallow_eq [DecidableEq (EdgeKey Symbol Guard)]
    (entry : Interned NodeKey) (body depth ordinary : Value Symbol Guard)
    (state : State Symbol Guard) (coherent : Coherent state)
    (available : Available state body) (zero : body.depth = 0) :
    InternedFreshOrdinaryStoredSubstitution.unfold (.mu entry body depth ordinary) state =
      InternedStoredSubstitution.unfold (.mu entry body depth ordinary) state := by
  exact InternedFreshOrdinaryStoredSubstitution.build_eq _ _ state
    (InternedStoredShallowCompletion.encode_zero (InternedStoredSubstitution.leaves body) [] body state coherent available zero)

/-- Pure repaired probes derive actual completed unfolding with a strict head-rank decrease. -/
theorem unfold_decreases [DecidableEq (EdgeKey Symbol Guard)]
    (entry : Interned NodeKey) (body depth ordinary : Value Symbol Guard)
    (state : State Symbol Guard) (context : Context state captures) (clean : Clean state)
    (available : Available state (.mu entry body depth ordinary))
    (depthNames ordinaryNames : List Reference)
    (depthPure : profile depth = some depthNames) (ordinaryPure : profile ordinary = some ordinaryNames)
    (opened : (Value.mu entry body depth ordinary).free ≠ []) :
    ∃ value final, InternedFreshOrdinaryStoredSubstitution.unfold (.mu entry body depth ordinary) state = .done value final ∧
      headRank value < headRank (.mu entry body depth ordinary) := by
  have zero := body_zero entry body depth ordinary state context available depthNames ordinaryNames depthPure ordinaryPure
  rw [unfold_shallow_eq entry body depth ordinary state context.normal.facts.coherent
    (available.children body (by simp [children])) zero]
  exact InternedStoredShallowCompletion.unfold_complete_decreases entry body depth ordinary state
    context.normal.facts context.normal.flat clean available zero opened

/-- Empty-cache repaired source execution derives every representation premise of the pure-probe rank. -/
theorem closed_unfold_decreases [DecidableEq (EdgeKey Symbol Guard)]
    (expression : Syntax Symbol Guard) (key : NodeKey)
    (entry : Interned NodeKey) (body depth ordinary : Value Symbol Guard)
    (stored : (InternedFreshOrdinaryConstruction.build expression [] empty).state.nodeRecords key =
      some (.mu entry body depth ordinary))
    (depthNames ordinaryNames : List Reference)
    (depthPure : profile depth = some depthNames) (ordinaryPure : profile ordinary = some ordinaryNames)
    (opened : (Value.mu entry body depth ordinary).free ≠ []) :
    ∃ value final, InternedFreshOrdinaryStoredSubstitution.unfold (.mu entry body depth ordinary)
      (InternedFreshOrdinaryConstruction.build expression [] empty).state = .done value final ∧
      headRank value < headRank (.mu entry body depth ordinary) := by
  have context := (empty_context (Symbol := Symbol) (Guard := Guard)).build expression
  exact unfold_decreases entry body depth ordinary _ context (InternedFreshOrdinaryBodyFilter.closed_clean expression)
    (context.normal.facts.cached.nodes key _ stored) depthNames ordinaryNames depthPure ordinaryPure opened

end MicroCFTA.InternedFreshOrdinaryPureProbeGate
