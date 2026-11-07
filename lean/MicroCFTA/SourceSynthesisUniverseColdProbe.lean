import MicroCFTA.SourceSynthesisUniverseNativeInput
import MicroCFTA.InternedFreshOrdinaryCoverage
import MicroCFTA.InternedStoredMuOrigins

/-!
# Fresh reservation from actual universe probe history

The two binder-free callbacks introduce no complete Mu record. Starting
from empty caches, coverage and record coherence therefore exclude a Mu-key
hit after the probes. The missing reservation is derived from execution.
It is not supplied by the caller. Canonical body reconstruction remains
a separate obligation.
-/
namespace MicroCFTA.SourceSynthesisUniverseColdProbe
open Cache InternedConstructorTemplates InternedNestedFacts InternedProbeProvenance
open InternedRecordCoherence InternedStoredShallowCompletion InternedShallowHeap
open InternedNestedConstruction (Syntax Outcome work request)
open InternedBinderProtocol (Reference)
open SourceSynthesisTypeSyntax

variable {Guard : Type} [DecidableEq (EdgeKey String Guard)]

/-- A binder-free plan preserves the original complete Mu records in both executors. -/
theorem binderFree_build_noNewMu (expression : Expr Guard)
    (environment : List (Value String Guard)) (state : State String Guard)
    (free : BinderFree expression) :
    NoNewMu state (InternedFreshOrdinaryConstruction.build expression environment state).state := by
  rw [InternedFreshOrdinaryStoredSubstitution.build_eq expression environment state free]
  exact InternedShallowHeap.build_noNewMu expression environment state free

/-- Actual callback normalization adds no complete Mu record. -/
theorem binderFree_callback_noNewMu (expression : Expr Guard)
    (environment : List (Value String Guard)) (name : Reference) (state : State String Guard)
    (free : BinderFree expression) :
    NoNewMu state (InternedFreshOrdinaryFacts.callback expression environment name state).state := by
  unfold InternedFreshOrdinaryFacts.callback
  apply bind_noNewMu state _ _ (binderFree_build_noNewMu expression _ state free)
  intro value after _
  exact InternedStoredMuOrigins.filter_noNewMu name value after

/-- Every actual allTypes callback has the required binder-free history. -/
theorem allTypes_callback_noNewMu (top : Guard) (catalog : List (String × Nat))
    (environment : List (Value String Guard)) (name : Reference) (state : State String Guard) :
    NoNewMu state
      (InternedFreshOrdinaryFacts.callback (allTypesBody top catalog) environment name state).state :=
  binderFree_callback_noNewMu _ environment name state
    (SourceSynthesisUniverseNativeInput.allTypesBody_binderFree top catalog)

omit [DecidableEq (EdgeKey String Guard)] in
/-- Full coherent coverage cannot contain a Mu key without a complete Mu payload. -/
theorem empty_mu_key_absent (state : State String Guard) (facts : Facts state)
    (covered : Covered [] state) (old : NoNewMu empty state)
    (depth ordinary : Value String Guard) : state.nodes.table (muKey depth ordinary) = none := by
  cases present : state.nodes.table (muKey depth ordinary) with
  | none => rfl
  | some entry =>
      rcases covered.nodes _ entry present with pending | ⟨value, stored⟩
      · cases pending
      · obtain ⟨actual, _, fields⟩ := facts.coherent.nodes _ value stored
        cases value with
        | empty | reference | node | union => simp [NodeFields, muKey] at fields
        | mu original body first second =>
            have impossible := old _ original body first second stored
            cases impossible

/-- The actual cold probes complete and derive their fresh key and exact continuation. -/
theorem allTypes_cold_probes (top : Guard) (catalog : List (String × Nat)) :
    ∃ depth afterDepth ordinary afterOrdinary,
      InternedFreshOrdinaryFacts.callback (allTypesBody top catalog) [] .depth empty =
        .done depth afterDepth ∧
      InternedFreshOrdinaryFacts.callback (allTypesBody top catalog) []
        (.uninterned (InternedFreshOrdinaryConstruction.ordinaryLevel depth)) afterDepth =
        .done ordinary afterOrdinary ∧
      Facts afterOrdinary ∧ Available afterOrdinary depth ∧ Available afterOrdinary ordinary ∧
      afterOrdinary.nodes.table (muKey depth ordinary) = none ∧
      InternedFreshOrdinaryConstruction.build (allTypes top catalog) [] empty =
        request true depth ordinary
          (InternedFreshOrdinaryFacts.callback (allTypesBody top catalog) []) afterOrdinary := by
  let body := allTypesBody top catalog
  have free := SourceSynthesisUniverseNativeInput.allTypesBody_binderFree top catalog
  obtain ⟨depth, afterDepth, firstDone⟩ :=
    InternedFreshOrdinaryFirstOrderCompletion.callback_complete body free [] .depth empty
  have firstChecked := InternedFreshOrdinaryFacts.callback_verified body [] .depth empty empty_facts (by
    intro value member
    have same := List.mem_singleton.mp member
    subst value
    exact InternedNestedProvenance.depth_available empty)
  have depthFacts : Facts afterDepth := by
    simpa only [firstDone, Outcome.state] using firstChecked.facts
  have depthCovered := InternedFreshOrdinaryCoverage.callback_covered body [] .depth empty
    empty_valid InternedRecordCoherence.empty_correct.2 depth afterDepth firstDone
  obtain ⟨ordinary, afterOrdinary, secondDone⟩ :=
    InternedFreshOrdinaryFirstOrderCompletion.callback_complete body free []
      (.uninterned (InternedFreshOrdinaryConstruction.ordinaryLevel depth)) afterDepth
  have secondChecked := InternedFreshOrdinaryFacts.callback_verified body []
    (.uninterned (InternedFreshOrdinaryConstruction.ordinaryLevel depth)) afterDepth depthFacts (by
      intro value member
      have same := List.mem_singleton.mp member
      subst value
      exact InternedNestedProvenance.ordinary_available afterDepth _)
  have ordinaryFacts : Facts afterOrdinary := by
    simpa only [secondDone, Outcome.state] using secondChecked.facts
  have ordinaryCovered := InternedFreshOrdinaryCoverage.callback_covered body []
    (.uninterned (InternedFreshOrdinaryConstruction.ordinaryLevel depth)) afterDepth
    depthFacts.coherent.valid depthCovered ordinary afterOrdinary secondDone
  have firstOld : NoNewMu empty afterDepth := by
    simpa only [firstDone, Outcome.state] using
      binderFree_callback_noNewMu body [] .depth empty free
  have secondOld : NoNewMu afterDepth afterOrdinary := by
    simpa only [secondDone, Outcome.state] using binderFree_callback_noNewMu body []
      (.uninterned (InternedFreshOrdinaryConstruction.ordinaryLevel depth)) afterDepth free
  have absent := empty_mu_key_absent afterOrdinary ordinaryFacts ordinaryCovered
    (noNewMu_trans firstOld secondOld) depth ordinary
  have growth : Grows afterDepth afterOrdinary := by
    simpa only [secondDone, Outcome.state] using secondChecked.growth
  have history : Cache.Extends afterDepth.nodes.issued afterOrdinary.nodes.issued := by
    simpa only [secondDone, Outcome.state] using secondChecked.history
  have depthAvailable := Available.grows afterDepth afterOrdinary growth history
    (firstChecked.result depth afterDepth firstDone)
  refine ⟨depth, afterDepth, ordinary, afterOrdinary, firstDone, secondDone, ordinaryFacts,
    depthAvailable, secondChecked.result ordinary afterOrdinary secondDone, absent, ?_⟩
  have expanded : InternedFreshOrdinaryConstruction.build (allTypes top catalog) [] empty =
      (InternedFreshOrdinaryFacts.callback body [] .depth empty).bind fun depth afterDepth =>
      (InternedFreshOrdinaryFacts.callback body []
        (.uninterned (InternedFreshOrdinaryConstruction.ordinaryLevel depth)) afterDepth).bind
        fun ordinary afterOrdinary => request true depth ordinary
          (InternedFreshOrdinaryFacts.callback body []) afterOrdinary := by
    change InternedFreshOrdinaryConstruction.build (.binder true body) [] empty = _
    rw [InternedFreshOrdinaryConstruction.build]
    rfl
  rw [expanded, firstDone]
  simp only [Outcome.bind, secondDone]
  rfl

end MicroCFTA.SourceSynthesisUniverseColdProbe
