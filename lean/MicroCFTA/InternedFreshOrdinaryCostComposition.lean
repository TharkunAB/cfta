import MicroCFTA.InternedFreshOrdinaryCostExecutionFacts

/-!
# Actual repaired probe costs select the pure binder interpretation

The existing decoded deep-name observations select smart retention.
The actual Depth probe proves freshness for captured occurrence costs.
The ordinary probe then supplies every exact captured cost.
-/
namespace MicroCFTA.InternedFreshOrdinaryCostComposition
open InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedNestedConstruction (Syntax)
open InternedDepthSemantics (Shape)
open InternedFreshOrdinaryConstruction InternedFreeOccurrenceRank
open InternedFreshOrdinaryCostHeap
open InternedBinderProtocol (Reference)

/-- The actual deep-name observations determine exactly the pure retained-wrapper cost. -/
theorem binder_cost (smart : Bool) (bodyShape : Shape (Sum Unit Reference))
    (depth ordinary : Value Symbol Guard) (state : State Symbol Guard)
    (coherent : Coherent state) (available : Available state depth)
    (depthObserved : InternedFreshOrdinaryDepthHeap.Observed (InternedProfileCallbackForm.captures bodyShape.deep)
      (InternedProfileCallbackForm.usesArgument bodyShape.deep) .depth depth)
    (ordinaryObserved : InternedFreshOrdinaryDepthHeap.Observed (InternedProfileCallbackForm.captures bodyShape.deep)
      (InternedProfileCallbackForm.usesArgument bodyShape.deep) (.uninterned (ordinaryLevel depth)) ordinary) :
    binderCost smart depth ordinary = InternedOccurrenceCostSemantics.binderShift smart bodyShape := by
  have fresh : .uninterned (ordinaryLevel depth) ∉ InternedProfileCallbackForm.captures bodyShape.deep := by
    intro included
    have deep := (InternedFreshOrdinaryDepthHeap.observed_other _ _ .depth depth depthObserved _
      (by intro impossible; cases impossible)).mpr included
    exact ordinary_fresh depth (InternedDeepFreeNormalization.deep_free depth state coherent available _ deep)
  have uses : InternedFreshOrdinaryDepthHeap.usesLocal depth ordinary = InternedProfileCallbackForm.usesArgument bodyShape.deep := by
    apply Bool.eq_iff_iff.mpr
    simpa only [InternedFreshOrdinaryDepthHeap.usesLocal, decide_eq_true_eq] using
      InternedFreshOrdinaryDepthHeap.observed_own _ _ _ ordinary ordinaryObserved fresh
  simp only [binderCost, uses, InternedOccurrenceCostSemantics.binderShift,
    InternedFreshOrdinaryDepthComposition.hasLocal_uses]

/-- Actual probe observations give exactly the interpreted binder's complete cost membership. -/
theorem binder_decoded (smart : Bool) (expression : Syntax Symbol Guard) (environment : List (Shape Reference))
    (occurrences : List (List (Reference × Nat))) (depth ordinary : Value Symbol Guard) (state : State Symbol Guard)
    (coherent : Coherent state) (available : Available state depth)
    (depthSame : ∀ name count, name ≠ .depth → ((name, count) ∈ costs depth ↔
      (name, count) ∈ InternedOccurrenceCostSemantics.captured expression environment occurrences))
    (ordinarySame : ∀ name count, name ≠ .uninterned (ordinaryLevel depth) → ((name, count) ∈ costs ordinary ↔
      (name, count) ∈ InternedOccurrenceCostSemantics.captured expression environment occurrences))
    (retention : binderCost smart depth ordinary = InternedOccurrenceCostSemantics.binderShift smart
      (InternedDepthSemantics.evaluate expression (⟨[Sum.inl ()], [], false, 0⟩ :: environment.map (Shape.map Sum.inr))))
    (name : Reference) (count : Nat) :
    (name, count) ∈ decodedCosts smart depth ordinary ↔
      (name, count) ∈ InternedOccurrenceCostSemantics.evaluate (.binder smart expression) environment occurrences := by
  have fresh : ∀ prior, (.uninterned (ordinaryLevel depth), prior) ∉
      InternedOccurrenceCostSemantics.captured expression environment occurrences := by
    intro prior present
    have cost := (depthSame _ prior (by intro impossible; cases impossible)).mpr present
    exact ordinary_fresh depth ((costs_free depth state coherent available _).mp ⟨prior, cost⟩)
  have captured : ∀ prior, ((name, prior) ∈ costs ordinary ∧ name ≠ .uninterned (ordinaryLevel depth)) ↔
      (name, prior) ∈ InternedOccurrenceCostSemantics.captured expression environment occurrences := by
    intro prior
    constructor
    · rintro ⟨present, different⟩
      exact (ordinarySame name prior different).mp present
    · intro present
      have different : name ≠ .uninterned (ordinaryLevel depth) := fun same => fresh prior (same ▸ present)
      exact ⟨(ordinarySame name prior different).mpr present, different⟩
  rw [decoded_member, InternedOccurrenceCostSemantics.binder_member, retention]
  simp only [captured]

end MicroCFTA.InternedFreshOrdinaryCostComposition
