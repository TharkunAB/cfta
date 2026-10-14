import MicroCFTA.InternedOpenDepthReadback
import MicroCFTA.InternedOpenDepthSemantics
import MicroCFTA.InternedFreshOrdinaryContext

/-!
# Open-depth heap preservation at repaired source requests

A fresh body and its completed Depth probe have the same interpreted
depth. Completion installs that equality. Canonical hits retain the
earlier equality and both exact requested probe records.
-/
namespace MicroCFTA.InternedOpenDepthRequest
open Cache InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedNestedConstruction (Syntax Outcome request)
open InternedNestedRequestFacts InternedConstructionProvenance
open InternedFreshOrdinaryContext InternedFreshOrdinaryFacts
open InternedOpenDepthReadback InternedStoredPlanBinderDepth
open InternedBinderProtocol (Reference)

/-- An actual outcome retains the open-depth heap and verifies every returned result. -/
structure Checked (outcome : Outcome Symbol Guard Result) (property : Result → Prop) : Prop where
  heap : Heap outcome.state
  result : ∀ value after, outcome = .done value after → property value

/-- A completed pure outcome retains its actual heap and result property. -/
theorem done_checked (value : Result) (state : State Symbol Guard) (property : Result → Prop)
    (heap : Heap state) (holds : property value) : Checked (.done value state) property := by
  refine ⟨heap, ?_⟩
  intro actual after same
  cases same
  exact holds

/-- Source sequencing retains the exact completed or pending heap. -/
theorem bind_checked (outcome : Outcome Symbol Guard First)
    (next : First → State Symbol Guard → Outcome Symbol Guard Result)
    (firstProperty : First → Prop) (property : Result → Prop) (checked : Checked outcome firstProperty)
    (later : ∀ value after, outcome = .done value after → Heap after → firstProperty value →
      Checked (next value after) property) : Checked (outcome.bind next) property := by
  cases outcome with
  | pending key state => exact ⟨checked.heap, by intro value after impossible; cases impossible⟩
  | done value after => exact later value after rfl checked.heap (checked.result value after rfl)

/-- Sequencing retains an exact heap property without assuming a completed result. -/
theorem bind_heap (outcome : Outcome Symbol Guard First)
    (next : First → State Symbol Guard → Outcome Symbol Guard Result) (heap : Heap outcome.state)
    (later : ∀ value after, outcome = .done value after → Heap after → Heap (next value after).state) :
    Heap (outcome.bind next).state := by
  cases outcome with
  | pending => exact heap
  | done value after => exact later value after rfl heap

/-- Actual request effects derive the candidate equality from recursive callback observations. -/
theorem request_heap [DecidableEq (EdgeKey Symbol Guard)] (smart : Bool) (expression : Syntax Symbol Guard)
    (environment : List (Value Symbol Guard)) (depth ordinary : Value Symbol Guard) (state : State Symbol Guard)
    (context : Context state environment) (cached : InternedFreshOrdinaryDepthHeap.Heap state)
    (heap : Heap state) (expected : Nat) (depthExpected : valueDepth depth = expected)
    (recurse : ∀ argument current, Context current environment → Available current (.reference argument) →
      InternedFreshOrdinaryDepthHeap.Heap current → Heap current →
      Checked (callback expression environment argument current) (fun value => valueDepth value = expected)) :
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
      have actual := recurse (.interned entry.1.identity) allocated reserved argument cached heap
      simp only [request, installed]
      change Heap ((callback expression environment (.interned entry.1.identity) allocated).bind
        (fun body after => complete smart entry.1 body depth ordinary after)).state
      apply bind_heap _ _ actual.heap
      intro body after returned afterHeap
      exact complete_heap smart entry.1 body depth ordinary after afterHeap
        ((actual.result body after returned).trans depthExpected.symm)

end MicroCFTA.InternedOpenDepthRequest
