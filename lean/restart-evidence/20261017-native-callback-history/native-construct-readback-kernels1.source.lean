import MicroCFTA.SourceCurrentNativeConstructReadback
set_option linter.all true
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.proofs true
set_option pp.proofs.threshold 254
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000

set_option maxRecDepth 30000
set_option maxHeartbeats 5000000
namespace MicroCFTA.NativeConstructReadbackKernels
open Cache InternedConstructorTemplates InternedProbeProvenance
open InternedNestedConstruction (Syntax Outcome)
open InternedFreshOrdinaryConstruction
open InternedBinderProtocol (Reference)
open SourceCurrentNativeMuPublication (History)
open SourceCurrentNativeConstructReadback (Readback)
private def pair : Nat × Nat := (0, 1)
private def old : Reference := .intersection pair.1 pair.2
private def source : Syntax Nat Bool := .node [.mk 7 false []]
private def built := build source [] empty
private def leaf : Value Nat Bool := match built with | .done value _ => value | .pending .. => .empty
private def initial := built.state
private theorem built_done : built = .done leaf initial := by cbv
private theorem initialReady : SourceEqualityRequiredCache.Ready initial :=
  SourceEqualityRequiredCache.constructed source leaf initial built_done
private theorem leafAvailable : Available initial leaf :=
  (InternedFreshOrdinaryFacts.build_verified source [] empty InternedNestedFacts.empty_facts
    (by intro value member; cases member)).result leaf initial built_done
private def values : List (Value Nat Bool) := [.reference old, leaf]
private theorem inputs : InternedNestedProvenance.Values initial values := by
  intro value member
  rcases List.mem_cons.mp member with same | member
  · subst value
    exact reference_available initial old (by simp [InternedFreshProbeKeys.IssuedReferences,Value.free,old])
  · cases List.mem_singleton.mp member
    exact leafAvailable
private def body : Value Nat Bool := (run (makeUnion values) initial).1
private def heap : State Nat Bool := (run (makeUnion values) initial).2
private theorem checked : SourceEqualityRequiredCache.Keeps initial heap ∧ Available heap body :=
  SourceEqualityNativeDemandHeapPrimitives.union values initial initialReady inputs
private def history : History empty heap := .trans (SourceCurrentNativeMuPublication.closed_history source)
  (.retain initial heap (InternedShallowHeap.makeUnion_noNewMu values initial))
private theorem used : old ∈ body.free := by cbv; exact .head _
private def depthOutcome := SourceRecursiveIntersectionMaybeMu.callback old body .depth heap
private def depth : Value Nat Bool := match depthOutcome with | .done value _ => value | .pending .. => .empty
private def afterDepth := depthOutcome.state
private def ordinaryOutcome := SourceRecursiveIntersectionMaybeMu.callback old body (.uninterned (ordinaryLevel depth)) afterDepth
private def ordinary : Value Nat Bool := match ordinaryOutcome with | .done value _ => value | .pending .. => .empty
private def cut := ordinaryOutcome.state
private theorem depthDone : depthOutcome = .done depth afterDepth := by cbv
private theorem ordinaryDone : ordinaryOutcome = .done ordinary cut := by cbv
private theorem unused : InternedFreshOrdinaryDepthHeap.usesLocal depth ordinary = false := by cbv
private theorem ordinaryLeaf : ordinary = leaf := by cbv

/-- A live ordinary row survives unused native binding and the exact warm replay. -/
theorem produced :
    old ∈ body.free ∧
    SourceRecursiveIntersectionMaybeMu.callback old body .depth heap = .done depth afterDepth ∧
    SourceRecursiveIntersectionMaybeMu.callback old body (.uninterned (ordinaryLevel depth)) afterDepth = .done ordinary cut ∧
    InternedFreshOrdinaryDepthHeap.usesLocal depth ordinary = false ∧
    ∃ value after, SourceRecursiveIntersectionMaybeMu.maybeMu pair body heap = .done value after ∧
      Readback old body heap value after ∧ value = leaf ∧
      SourceRecursiveIntersectionMaybeMu.maybeMu pair body after = .done value after := by
  obtain ⟨value, after, actual, keeps, _available, _history, branch⟩ :=
    SourceCurrentNativeConstructReadback.optional_complete pair body heap checked.1.ready checked.2 history
  have receipt : Readback old body heap value after := by
    rcases branch with absent | active
    · exact False.elim (absent.1 used)
    · exact active.2
  have equal : value = leaf := by
    obtain ⟨actualDepth, actualAfterDepth, actualOrdinary, actualCut, raw, middle, entry, storedBody,
      first, second, _request, _raw, _filter, _normal, _rawAvailable, _present, _returned, _whole, law⟩ := receipt
    obtain ⟨rfl, rfl⟩ := Outcome.done.inj (depthDone.symm.trans first)
    obtain ⟨rfl, rfl⟩ := Outcome.done.inj (ordinaryDone.symm.trans second)
    have erased := (law unused).1
    exact erased.trans (by rw [ordinaryLeaf]; cbv)
  refine ⟨used, depthDone, ordinaryDone, unused, value, after, actual, receipt, equal, ?_⟩
  exact SourceRecursiveIntersectionMaybeMu.replay pair body heap after after
    checked.1.ready.semantic.1.normal.facts checked.2 value actual (grows_refl after)
end MicroCFTA.NativeConstructReadbackKernels
#check @MicroCFTA.NativeConstructReadbackKernels.produced
#print axioms MicroCFTA.NativeConstructReadbackKernels.produced
