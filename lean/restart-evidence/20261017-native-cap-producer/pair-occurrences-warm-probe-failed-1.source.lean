import MicroCFTA.SourceEqualityRequiredSemanticCache

set_option linter.all true
set_option pp.explicit true
set_option pp.proofs true
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000
set_option format.width 200

namespace MicroCFTA.PairOccurrenceWarmProbe
open Cache InternedConstructorTemplates InternedProbeProvenance
open InternedBinderProtocol (NodeKey Reference)
open InternedNestedConstruction (finish)
open InternedFreshOrdinaryDepthHeap InternedFreshOrdinaryConstruction

/-- Current semantic readiness excludes a retained warm wrapper when its actual ordinary probe has no deep local. -/
theorem actual_warm_no_wrapper {Symbol Guard : Type} (state : State Symbol Guard)
    (semantic : SourceEqualityRequiredSemanticCache.SemanticReady state)
    (key : NodeKey) (entry : Interned NodeKey) (body depth ordinary : Value Symbol Guard)
    (present : state.nodeRecords key = some (.mu entry body depth ordinary))
    (noLocal : .uninterned (ordinaryLevel depth) ∉ InternedDeepFreeDepth.deepNames ordinary) :
    finish true (.mu entry body depth ordinary) = body ∨ finish true (.mu entry body depth ordinary) = .empty := by
  have decoded := semantic.ready.semantic.2 key entry body depth ordinary present
  have raw := (decoded false).1
  have smart := (decoded true).1
  have unused : usesLocal depth ordinary = false := by simp [usesLocal, noLocal]
  have sameDepth : body.depth = depth.depth := by
    simp only [finish, Bool.false_eq_true, ↓reduceIte, Value.depth, decodedDepth, Bool.not_false,
      Bool.true_or, Bool.true_eq] at raw
    omega
  have resultDepth : (finish true (.mu entry body depth ordinary)).depth = depth.depth := by
    simpa only [decodedDepth, Bool.not_true, unused, Bool.false_or, Bool.false_eq_true, ↓reduceIte] using smart
  by_cases absent : .interned entry.identity ∉ body.free
  · exact .inl (by simp [finish, cleanup, absent])
  · by_cases self : body.referenceOf == .ref (.interned entry.identity) = true
    · exact .inr (by simp [finish, cleanup, absent, self])
    · have retained : finish true (.mu entry body depth ordinary) = .mu entry body depth ordinary := by
        simp [finish, cleanup, absent, self]
      rw [retained, Value.depth, sameDepth] at resultDepth
      omega

#print axioms actual_warm_no_wrapper
#check @actual_warm_no_wrapper
end MicroCFTA.PairOccurrenceWarmProbe
