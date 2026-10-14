import MicroCFTA.InternedGuardedProbeHeap

/-!
# Semantic heap preservation at actual repaired requests

A fresh request derives its candidate invariant from its ordinary probe and
fresh body. The actual completed record determines readback. This includes
canonical hits and retains the first completed payload.
-/
namespace MicroCFTA.InternedGuardedRequest
open Cache Language InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedNestedConstruction (Syntax Outcome request)
open InternedFreshOrdinaryFacts InternedFreshOrdinaryContext InternedGuardedLanguage InternedGuardedProbeHeap
open InternedNestedRequestFacts InternedConstructionProvenance
open InternedBinderProtocol (Reference)
open BinderLanguage (Lang least)

/-- An actual outcome retains the semantic probe heap and verifies each returned result. -/
structure Checked (outcome : Outcome Symbol Guard Result) (property : Result → Prop) : Prop where
  heap : Heap outcome.state
  result : ∀ value after, outcome = .done value after → property value

/-- A pure completed outcome retains its heap and result property. -/
theorem done_checked (value : Result) (state : State Symbol Guard) (property : Result → Prop)
    (heap : Heap state) (holds : property value) : Checked (.done value state) property := by
  refine ⟨heap, ?_⟩
  intro actual after same
  cases same
  exact holds

/-- Source sequencing retains pending heaps and verifies completed continuations. -/
theorem bind_checked (outcome : Outcome Symbol Guard First)
    (next : First → State Symbol Guard → Outcome Symbol Guard Result)
    (firstProperty : First → Prop) (property : Result → Prop) (checked : Checked outcome firstProperty)
    (later : ∀ value after, outcome = .done value after → Heap after → firstProperty value →
      Checked (next value after) property) : Checked (outcome.bind next) property := by
  cases outcome with
  | pending key state => exact ⟨checked.heap, by intro value after impossible; cases impossible⟩
  | done value after => exact later value after rfl checked.heap (checked.result value after rfl)

/-- Source sequencing can retain the semantic heap without a result assertion. -/
theorem bind_heap (outcome : Outcome Symbol Guard First)
    (next : First → State Symbol Guard → Outcome Symbol Guard Result) (heap : Heap outcome.state)
    (later : ∀ value after, outcome = .done value after → Heap after → Heap (next value after).state) :
    Heap (outcome.bind next).state := by
  cases outcome with
  | pending => exact heap
  | done value after => exact later value after rfl heap

/-- Actual request effects install their semantic invariant from the two proved callback least languages. -/
theorem request_heap [DecidableEq (EdgeKey Symbol Guard)] (smart : Bool) (expression : Syntax Symbol Guard)
    (environment : List (Value Symbol Guard)) (depth ordinary : Value Symbol Guard) (state : State Symbol Guard)
    (context : Context state environment) (heap : Heap state)
    (expected : (Guard → Term Symbol → Bool) → Env Symbol → Lang Symbol)
    (ordinaryExpected : ∀ holds ambient,
      least (fun candidate => meaning holds (bind ambient (.uninterned (InternedFreshOrdinaryConstruction.ordinaryLevel depth)) candidate) ordinary) =
        expected holds ambient)
    (recurse : ∀ argument current, Context current environment → Available current (.reference argument) →
      Heap current → argument ∉ InternedProfileCallbackForm.captures
        (InternedFreeNameForm.symbolic expression (environment.map InternedRootProfile.profile) (environment.map Value.free)) →
      Checked (callback expression environment argument current) (fun value => ∀ holds ambient,
        least (fun candidate => meaning holds (bind ambient argument candidate) value) = expected holds ambient)) :
    Heap (request smart depth ordinary (callback expression environment) state).state := by
  cases installed : state.nodes.table (muKey depth ordinary) with
  | some entry =>
      cases present : state.nodeRecords (muKey depth ordinary) <;>
        simpa only [request, installed, present, Outcome.state] using heap
  | none =>
      let key := muKey depth ordinary
      let entry := Cache.intern state.nodes key
      let allocated := {state with nodes := entry.2}
      have reserved : Context allocated environment := context.reserve key
      have argument : Available allocated (.reference (.interned entry.1.identity)) :=
        (reserve_available key state context.normal.facts.coherent context.normal.facts.cached).2
      have fresh : .interned entry.1.identity ∉ InternedProfileCallbackForm.captures
          (InternedFreeNameForm.symbolic expression (environment.map InternedRootProfile.profile) (environment.map Value.free)) := by
        rw [InternedFreshProbeKeys.intern_miss_identity state.nodes key installed]
        exact next_fresh_captures expression environment state context
      have actual := recurse (.interned entry.1.identity) allocated reserved argument heap fresh
      simp only [request, installed]
      change Heap ((callback expression environment (.interned entry.1.identity) allocated).bind
        (fun body after => complete smart entry.1 body depth ordinary after)).state
      apply bind_heap _ _ actual.heap
      intro body after returned afterHeap
      apply complete_heap smart entry.1 body depth ordinary after afterHeap
      intro holds ambient
      rw [meaning]
      exact (actual.result body after returned holds ambient).trans (ordinaryExpected holds ambient).symm

/-- Every completed request reads the least language of its actual requested ordinary probe. -/
theorem request_language [DecidableEq (EdgeKey Symbol Guard)] (holds : Guard → Term Symbol → Bool)
    (ambient : Env Symbol) (smart : Bool) (expression : Syntax Symbol Guard)
    (environment : List (Value Symbol Guard)) (depth ordinary : Value Symbol Guard) (state : State Symbol Guard)
    (facts : InternedNestedFacts.Facts state) (depthAvailable : Available state depth)
    (ordinaryAvailable : Available state ordinary) (value : Value Symbol Guard) (after : State Symbol Guard)
    (done : request smart depth ordinary (callback expression environment) state = .done value after)
    (afterFacts : InternedNestedFacts.Facts after) (heap : Heap after) :
    meaning holds ambient value = least (fun candidate => meaning holds
      (bind ambient (.uninterned (InternedFreshOrdinaryConstruction.ordinaryLevel depth)) candidate) ordinary) := by
  cases installed : state.nodes.table (muKey depth ordinary) with
  | none =>
      obtain ⟨body, afterBody, _, present, same⟩ := InternedFreshOrdinaryReadback.request_miss_record smart
        expression environment depth ordinary state facts.coherent installed value after done
      rw [same, finish_exact holds ambient smart _ after afterFacts.coherent (afterFacts.cached.nodes _ _ present)]
      exact heap _ _ body depth ordinary present holds ambient
  | some entry =>
      cases present : state.nodeRecords (muKey depth ordinary) with
      | none => simp only [request, installed, present] at done; cases done
      | some stored =>
          simp only [request, installed, present, Outcome.done.injEq] at done
          cases done.1
          cases done.2
          exact hit_language holds ambient smart depth ordinary stored state facts depthAvailable ordinaryAvailable heap present

end MicroCFTA.InternedGuardedRequest
