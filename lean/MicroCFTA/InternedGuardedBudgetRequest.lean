import MicroCFTA.InternedGuardedBudgetCallback

/-!
# Actual requests retain both ordinary-probe budget languages

Fresh completion derives both readbacks from the actual callbacks. Stored
local normalization supplies the cleanup invariant. Canonical hits retain
the first complete payload and both exact requested probe records.
-/
namespace MicroCFTA.InternedGuardedBudgetRequest
open Cache Language InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedNestedConstruction (Syntax Outcome request)
open InternedFreshOrdinaryFacts InternedFreshOrdinaryContext
open InternedGuardedBudget InternedGuardedBudgetProbeHeap
open InternedNestedRequestFacts InternedConstructionProvenance
open InternedBinderProtocol (Reference)
open BinderBudgetLanguage (Lang)

/-- An actual outcome retains both heaps and verifies each completed budget result. -/
structure Checked (outcome : Outcome Symbol Guard Result) (property : Result → Prop) : Prop where
  heap : Heap outcome.state
  depthHeap : InternedFreshOrdinaryDepthHeap.Heap outcome.state
  result : ∀ value after, outcome = .done value after → property value

/-- A pure result retains both complete probe heaps and its stated budget property. -/
theorem done_checked (value : Result) (state : State Symbol Guard) (property : Result → Prop)
    (heap : Heap state) (depthHeap : InternedFreshOrdinaryDepthHeap.Heap state) (holds : property value) :
    Checked (.done value state) property := by
  refine ⟨heap, depthHeap, ?_⟩
  intro actual after same
  cases same
  exact holds

/-- Actual source sequencing retains both heaps and the checked continuation property. -/
theorem bind_checked (outcome : Outcome Symbol Guard First)
    (next : First → State Symbol Guard → Outcome Symbol Guard Result)
    (firstProperty : First → Prop) (property : Result → Prop) (checked : Checked outcome firstProperty)
    (later : ∀ value after, outcome = .done value after → Heap after → InternedFreshOrdinaryDepthHeap.Heap after →
      firstProperty value → Checked (next value after) property) : Checked (outcome.bind next) property := by
  cases outcome with
  | pending key state => exact ⟨checked.heap, checked.depthHeap, by intro value after impossible; cases impossible⟩
  | done value after => exact later value after rfl checked.heap checked.depthHeap (checked.result value after rfl)

/-- Source sequencing retains the budget heap through exact completed or pending effects. -/
theorem bind_heap (outcome : Outcome Symbol Guard First)
    (next : First → State Symbol Guard → Outcome Symbol Guard Result) (heap : Heap outcome.state)
    (later : ∀ value after, outcome = .done value after → Heap after → Heap (next value after).state) :
    Heap (outcome.bind next).state := by
  cases outcome with
  | pending => exact heap
  | done value after => exact later value after rfl heap

/-- Every actual request installs both budget invariants from its proved normalized callbacks. -/
theorem request_heap [DecidableEq (EdgeKey Symbol Guard)] (smart : Bool) (expression : Syntax Symbol Guard)
    (environment : List (Value Symbol Guard)) (depth ordinary : Value Symbol Guard) (state : State Symbol Guard)
    (context : Context state environment) (heap : Heap state) (depthHeap : InternedFreshOrdinaryDepthHeap.Heap state)
    (expected : (Guard → Term Symbol → Bool) → Env Symbol → Lang Symbol → Lang Symbol)
    (ordinaryExpected : ∀ holds ambient, InternedGuardedBudgetCallback.View holds ambient
      (.uninterned (InternedFreshOrdinaryConstruction.ordinaryLevel depth)) ordinary (expected holds ambient))
    (recurse : ∀ argument current, Context current environment → Available current (.reference argument) →
      Heap current → InternedFreshOrdinaryDepthHeap.Heap current →
      argument ∉ InternedProfileCallbackForm.captures
        (InternedFreeNameForm.symbolic expression (environment.map InternedRootProfile.profile) (environment.map Value.free)) →
      Checked (callback expression environment argument current) (fun value => ∀ holds ambient,
        InternedGuardedBudgetCallback.View holds ambient argument value (expected holds ambient))) :
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
        exact InternedGuardedProbeHeap.next_fresh_captures expression environment state context
      have actual := recurse (.interned entry.1.identity) allocated reserved argument heap depthHeap fresh
      simp only [request, installed]
      change Heap ((callback expression environment (.interned entry.1.identity) allocated).bind
        (fun body after => complete smart entry.1 body depth ordinary after)).state
      apply bind_heap _ _ actual.heap
      intro body after returned afterHeap
      apply complete_heap smart entry.1 body depth ordinary after afterHeap
      refine ⟨?_, ?_, ?_⟩
      · exact InternedDeepLocalNormal.callback_local expression environment (.interned entry.1.identity) allocated
          reserved.normal (reserved.local _ argument).inputs body after returned
      · intro holds ambient
        rw [meaning]
        exact ((actual.result body after returned holds ambient).1).trans ((ordinaryExpected holds ambient).1).symm
      · intro holds ambient
        exact ((actual.result body after returned holds ambient).2).trans ((ordinaryExpected holds ambient).2).symm

/-- Every completed actual request reads the exact budget branch of its complete stored ordinary probe. -/
theorem request_language [DecidableEq (EdgeKey Symbol Guard)] (holds : Guard → Term Symbol → Bool)
    (ambient : Env Symbol) (smart : Bool) (expression : Syntax Symbol Guard)
    (environment : List (Value Symbol Guard)) (depth ordinary : Value Symbol Guard) (state : State Symbol Guard)
    (facts : InternedNestedFacts.Facts state) (depthAvailable : Available state depth)
    (ordinaryAvailable : Available state ordinary) (value : Value Symbol Guard) (after : State Symbol Guard)
    (done : request smart depth ordinary (callback expression environment) state = .done value after)
    (afterFacts : InternedNestedFacts.Facts after) (heap : Heap after) (depthHeap : InternedFreshOrdinaryDepthHeap.Heap after) :
    meaning holds ambient value =
      if !smart || InternedFreshOrdinaryDepthHeap.usesLocal depth ordinary then
        BinderBudgetLanguage.mu (fun candidate => meaning holds
          (InternedGuardedBudget.bind ambient (.uninterned (InternedFreshOrdinaryConstruction.ordinaryLevel depth)) candidate) ordinary)
      else meaning holds (InternedGuardedBudget.bind ambient
        (.uninterned (InternedFreshOrdinaryConstruction.ordinaryLevel depth)) (fun _ _ => False)) ordinary := by
  cases installed : state.nodes.table (muKey depth ordinary) with
  | none =>
      obtain ⟨body, afterBody, _, present, same⟩ := InternedFreshOrdinaryReadback.request_miss_record smart
        expression environment depth ordinary state facts.coherent installed value after done
      rw [same]
      exact finish_language holds ambient smart _ body depth ordinary after afterFacts.coherent
        ((afterFacts.cached.nodes _ _ present).children body (by simp [InternedProbeProvenance.children]))
        (heap _ _ body depth ordinary present) (depthHeap _ _ body depth ordinary present)
  | some entry =>
      cases present : state.nodeRecords (muKey depth ordinary) with
      | none => simp only [request, installed, present] at done; cases done
      | some stored =>
          simp only [request, installed, present, Outcome.done.injEq] at done
          cases done.1
          cases done.2
          exact hit_language holds ambient smart depth ordinary stored state facts depthAvailable ordinaryAvailable heap depthHeap present

end MicroCFTA.InternedGuardedBudgetRequest
