import MicroCFTA.InternedFreshOrdinaryDepthHeap
import MicroCFTA.InternedFreshOrdinaryContext
import MicroCFTA.InternedFreshOrdinaryPending

/-!
# Exact depth and deep observations through repaired source requests

Complete hits use the stored probe invariant. A miss uses the actual fresh
body callback and the independently proved free-name heap. The statement
retains recursive source premises for use in a syntax induction.
-/
namespace MicroCFTA.InternedFreshOrdinaryDepthRequest
open Cache InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedNestedConstruction (Syntax Outcome request finish IsPending)
open InternedNestedRequestFacts InternedConstructionProvenance InternedFreshProbeKeys
open InternedFreshOrdinaryConstruction InternedFreshOrdinaryFacts InternedFreshOrdinaryNormal
open InternedFreshOrdinaryContext InternedFreshOrdinaryDepthHeap InternedFreshOrdinaryPending
open InternedDeepFreeDepth InternedDeepFreeNormalization InternedDeepLocalNormal
open InternedBinderProtocol (Reference NodeKey)

/-- An execution keeps the recursive observation heap and verifies every returned result. -/
structure Checked (outcome : Outcome Symbol Guard Result) (property : Result → Prop) : Prop where
  heap : Heap outcome.state
  result : ∀ value after, outcome = .done value after → property value

/-- A pure result satisfies its retained observation obligation. -/
theorem done_checked (value : Result) (state : State Symbol Guard) (property : Result → Prop)
    (heap : Heap state) (holds : property value) : Checked (.done value state) property := by
  refine ⟨heap, ?_⟩
  intro actual after same
  cases same
  exact holds

/-- Pending requests return no result whose depth must be interpreted. -/
theorem pending_checked (key : NodeKey) (state : State Symbol Guard) (property : Result → Prop)
    (heap : Heap state) : Checked (.pending key state) property := by
  refine ⟨heap, ?_⟩
  intro value after impossible
  cases impossible

/-- Exact source sequencing retains all earlier complete observation records. -/
theorem bind_checked (outcome : Outcome Symbol Guard First)
    (next : First → State Symbol Guard → Outcome Symbol Guard Result)
    (firstProperty : First → Prop) (property : Result → Prop)
    (checked : Checked outcome firstProperty)
    (later : ∀ value after, outcome = .done value after → Heap after → firstProperty value →
      Checked (next value after) property) : Checked (outcome.bind next) property := by
  cases outcome with
  | pending key state => exact pending_checked key state property checked.heap
  | done value state => exact later value state rfl checked.heap (checked.result value state rfl)

/-- Actual hit, miss, and pending branches preserve the decoded depth/deep heap. -/
theorem request_checked [DecidableEq (EdgeKey Symbol Guard)] (smart : Bool) (expression : Syntax Symbol Guard)
    (environment : List (Value Symbol Guard)) (depth ordinary : Value Symbol Guard) (state : State Symbol Guard)
    (context : Context state environment) (heap : Heap state)
    (depthAvailable : Available state depth) (ordinaryAvailable : Available state ordinary)
    (captured : List Reference) (uses : Bool) (expectedDepth : Nat)
    (depthExpected : depth.depth = expectedDepth)
    (depthObserved : Observed captured uses .depth depth)
    (ordinaryObserved : Observed captured uses (.uninterned (ordinaryLevel depth)) ordinary)
    (freeResult : InternedFreshOrdinaryFreeHeap.Heap
      (request smart depth ordinary (callback expression environment) state).state)
    (recurse : ∀ name current, Context current environment → Available current (.reference name) → Heap current →
      Checked (callback expression environment name current)
        (fun value => value.depth = expectedDepth ∧ Observed captured uses name value)) :
    Checked (request smart depth ordinary (callback expression environment) state)
      (fun value => value.depth = decodedDepth smart depth ordinary ∧
        ∀ name, name ∈ deepNames value ↔ name ∈ decodedDeep smart depth ordinary) := by
  have ordinaryFresh : .uninterned (ordinaryLevel depth) ∉ captured := by
    intro member
    have observed := (observed_other captured uses .depth depth depthObserved
      (.uninterned (ordinaryLevel depth)) (by intro impossible; cases impossible)).mpr member
    exact ordinary_fresh depth (deep_free depth state context.normal.facts.coherent depthAvailable _ observed)
  cases installed : state.nodes.table (muKey depth ordinary) with
  | some entry =>
      cases present : state.nodeRecords (muKey depth ordinary) with
      | none =>
          simp only [request, installed, present]
          exact pending_checked _ _ _ heap
      | some value =>
          simp only [request, installed, present]
          exact done_checked _ _ _ heap
            (hit_observation smart depth ordinary value state context.normal.facts depthAvailable ordinaryAvailable heap present)
  | none =>
      let key := muKey depth ordinary
      let entry := Cache.intern state.nodes key
      let allocated := {state with nodes := entry.2}
      have reserved : Context allocated environment := context.reserve key
      have argument : Available allocated (.reference (.interned entry.1.identity)) :=
        (reserve_available key state context.normal.facts.coherent context.normal.facts.cached).2
      have bodyFresh : .interned entry.1.identity ∉ captured := by
        intro member
        have observed := (observed_other captured uses .depth depth depthObserved
          (.interned entry.1.identity) (by intro impossible; cases impossible)).mpr member
        have free := deep_free depth state context.normal.facts.coherent depthAvailable _ observed
        change .interned (Cache.intern state.nodes key).1.identity ∈ depth.free at free
        rw [intern_miss_identity state.nodes key installed] at free
        exact next_absent state.nodes context.normal.facts.coherent.valid.2 depth depthAvailable.issued free
      have pending : IsPending key allocated :=
        ⟨⟨entry.1, (Cache.intern_correct state.nodes key context.normal.facts.coherent.valid.2).2.1⟩,
          InternedNestedMissReadback.missing_record state context.normal.facts.coherent key installed⟩
      have retained := callback_pending expression environment (.interned entry.1.identity)
        ⟨depth.referenceOf, ordinary.referenceOf⟩ allocated reserved.normal.facts.coherent.valid pending
      have actual := recurse (.interned entry.1.identity) allocated reserved argument heap
      simp only [request, installed]
      change Checked ((callback expression environment (.interned entry.1.identity) allocated).bind
        (fun body after => complete smart entry.1 body depth ordinary after)) _
      apply bind_checked _ _ _ _ actual
      intro body afterBody returned afterHeap bodyCorrect
      have absent : afterBody.nodeRecords key = none := by
        simpa only [returned, Outcome.state, key, muKey] using retained.2
      let final := {afterBody with nodeRecords := keepFirst afterBody.nodeRecords key (.mu entry.1 body depth ordinary)}
      have completed : complete smart entry.1 body depth ordinary afterBody =
          .done (finish smart (.mu entry.1 body depth ordinary)) final := by
        simp [complete, final, key, keepFirst, absent, put]
      have whole : request smart depth ordinary (callback expression environment) state =
          .done (finish smart (.mu entry.1 body depth ordinary)) final := by
        simp only [request, installed]
        change (callback expression environment (.interned entry.1.identity) allocated).bind
          (fun body after => complete smart entry.1 body depth ordinary after) = _
        rw [returned]
        exact completed
      have finalFree : InternedFreshOrdinaryFreeHeap.Heap final := by simpa only [whole, Outcome.state] using freeResult
      have present : final.nodeRecords key = some (.mu entry.1 body depth ordinary) := by simp [final, keepFirst, absent, put]
      have freeCorrect := finalFree key entry.1 body depth ordinary present
      have bodyInputs := (reserved.local _ argument).inputs
      have verified := callback_verified expression environment (.interned entry.1.identity) allocated reserved.normal.facts bodyInputs
      have afterContext : Context afterBody environment := by
        simpa only [returned, Outcome.state] using reserved.callback expression (.interned entry.1.identity) argument
      have candidateCorrect := candidate entry.1 body depth ordinary afterBody afterContext.normal.facts.coherent
        (verified.result body afterBody returned)
        (callback_local expression environment (.interned entry.1.identity) allocated reserved.normal bodyInputs body afterBody returned)
        (bodyCorrect.1.trans depthExpected.symm) captured uses depthObserved ordinaryObserved bodyCorrect.2 ordinaryFresh bodyFresh freeCorrect
      have finalHeap := complete_heap smart entry.1 body depth ordinary afterBody afterHeap candidateCorrect
      rw [completed]
      exact done_checked _ _ _ (by simpa only [completed, Outcome.state] using finalHeap) (candidateCorrect smart)

end MicroCFTA.InternedFreshOrdinaryDepthRequest
