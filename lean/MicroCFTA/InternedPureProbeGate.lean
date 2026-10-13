import MicroCFTA.InternedNestedProfiles
import MicroCFTA.InternedRootProfileCleanup
import MicroCFTA.InternedStoredShallowCompletion

/-!
# Pure canonical probes derive actual shallow unfolding

The complete source profile invariant makes a body pure when both stored
probes are pure. A pure available record has cached Mu depth zero. The
actual stored-body executor therefore completes its unfolding and strictly
decreases head rank for an open binder. The source expression can contain
arbitrary nested constructors and unrelated cached recursive records.
-/
namespace MicroCFTA.InternedPureProbeGate
open Cache InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedNestedConstruction InternedNestedFacts InternedNestedProvenance InternedStoredMuOrigins
open InternedRootProfile InternedRootProfileReflection InternedRootProfileCleanup InternedNestedProfiles
open InternedGateRank InternedStoredBodyInvariant InternedStoredSelfFilter
open InternedBinderProtocol (Reference NodeKey)

/-- Every actual pure root profile has cached Mu depth zero. -/
theorem pure_depth_zero (value : Value Symbol Guard) (state : State Symbol Guard) (coherent : Coherent state)
    (available : Available state value) (names : List Reference) (pure : profile value = some names) : value.depth = 0 := by
  cases value with
  | empty | reference => rfl
  | node | mu => simp [profile] at pure
  | union entry members depth free =>
      have combined : many members = some names := by simpa only [profile] using pure
      have allZero : ∀ child ∈ members, child.depth = 0 := by
        intro child member
        obtain ⟨refs, childPure⟩ := member_pure members names combined child member
        exact pure_depth_zero child state coherent (available.children child member) refs childPure
      obtain ⟨actual, _, fields⟩ := coherent.nodes entry.key (.union entry members depth free) (available.resident entry rfl)
      change depth = 0
      rw [fields.2.2.1]
      apply Nat.eq_zero_of_le_zero
      exact (maximumDepth_exact members 0).mpr (fun child member => by simp [allZero child member])
termination_by sizeOf value
decreasing_by
  have smaller := List.sizeOf_lt_of_mem member
  simp_wf
  simp_all
  omega

/-- Two pure canonical probes force a pure actual stored body. -/
theorem body_pure (entry : Interned NodeKey) (body depth ordinary : Value Symbol Guard)
    (correct : InternedProfileHeap.Correct entry body depth ordinary)
    (depthNames ordinaryNames : List Reference)
    (depthPure : profile depth = some depthNames) (ordinaryPure : profile ordinary = some ordinaryNames) :
    ∃ names, profile body = some names := by
  cases computed : profile body with
  | some names => exact ⟨names, rfl⟩
  | none =>
      have hidden := opaque_finish entry body depth ordinary computed
      have impossible := correct.1.mp hidden
      simp [InternedProbeDecoder.decode, depthPure, ordinaryPure] at impossible

/-- Every source-created stored record with pure probes has an actual depth-zero body. -/
theorem closed_body_zero [DecidableEq (EdgeKey Symbol Guard)] (expression : Syntax Symbol Guard) (key : NodeKey)
    (entry : Interned NodeKey) (body depth ordinary : Value Symbol Guard)
    (stored : (build expression [] empty).state.nodeRecords key = some (.mu entry body depth ordinary))
    (depthNames ordinaryNames : List Reference)
    (depthPure : profile depth = some depthNames) (ordinaryPure : profile ordinary = some ordinaryNames) : body.depth = 0 := by
  let state := (build expression [] empty).state
  have normal : Normal state := build_normal expression [] empty empty_normal (by simp [Values])
  have available := normal.facts.cached.nodes key (.mu entry body depth ordinary) stored
  obtain ⟨names, pure⟩ := body_pure entry body depth ordinary (closed_heap expression key entry body depth ordinary stored)
    depthNames ordinaryNames depthPure ordinaryPure
  exact pure_depth_zero body state normal.facts.coherent (available.children body (by simp [children])) names pure

/-- The source gate's pure-probe branch has actual completion and a strict unfolding rank. -/
theorem closed_unfold_decreases [DecidableEq (EdgeKey Symbol Guard)] (expression : Syntax Symbol Guard) (key : NodeKey)
    (entry : Interned NodeKey) (body depth ordinary : Value Symbol Guard)
    (stored : (build expression [] empty).state.nodeRecords key = some (.mu entry body depth ordinary))
    (depthNames ordinaryNames : List Reference)
    (depthPure : profile depth = some depthNames) (ordinaryPure : profile ordinary = some ordinaryNames)
    (opened : (Value.mu entry body depth ordinary).free ≠ []) :
    ∃ value final, InternedStoredSubstitution.unfold (.mu entry body depth ordinary) (build expression [] empty).state = .done value final ∧
      headRank value < headRank (.mu entry body depth ordinary) := by
  have normal := build_normal expression [] empty empty_normal (by simp [Values])
  exact InternedStoredShallowCompletion.unfold_complete_decreases entry body depth ordinary _ normal.facts normal.flat
    (closed_clean expression) (normal.facts.cached.nodes key _ stored)
    (closed_body_zero expression key entry body depth ordinary stored depthNames ordinaryNames depthPure ordinaryPure) opened

end MicroCFTA.InternedPureProbeGate
