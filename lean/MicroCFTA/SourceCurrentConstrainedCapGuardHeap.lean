import MicroCFTA.SourceCurrentConstrainedCapGuardDepth
import MicroCFTA.InternedNestedRequestFacts
import MicroCFTA.InternedShallowHeap

/-!
# Guard observations retained by actual completed Mu records

The conditional invariant records equality of the literal stored body and
ordinary probe profiles. Actual construction must derive a new candidate's
equality before publication. An earlier first writer retains its own proof.
The checked outcome also retains this invariant when execution is pending.
-/
namespace MicroCFTA.SourceCurrentConstrainedCapGuardHeap
open Cache InternedConstructorTemplates InternedRecordCoherence
open InternedNestedConstruction (Outcome)
open InternedBinderProtocol (NodeKey)
local notation "profile" => SourceCurrentConstrainedCapGuardDepth.profile
variable {Symbol Guard : Type}

/-- The actual fresh body and its exact ordinary probe have the same guard observation. -/
def Correct (valid : Guard → Prop) (body ordinary : Value Symbol Guard) : Prop :=
  profile valid body = profile valid ordinary

/-- Every actual completed Mu record retains its body-to-probe guard equality. -/
def Heap (valid : Guard → Prop) (state : State Symbol Guard) : Prop :=
  ∀ key entry body depth ordinary, state.nodeRecords key = some (.mu entry body depth ordinary) →
    Correct valid body ordinary

/-- Empty tables contain no completed-record obligation. -/
theorem empty_heap (valid : Guard → Prop) : Heap valid (empty (Symbol := Symbol) (Guard := Guard)) := by
  intro key entry body depth ordinary absent
  cases absent

/-- An effect with no new Mu record retains each exact earlier certificate. -/
theorem preserve (valid : Guard → Prop) (before after : State Symbol Guard)
    (heap : Heap valid before) (old : InternedShallowHeap.NoNewMu before after) : Heap valid after := by
  intro key entry body depth ordinary present
  exact heap key entry body depth ordinary (old key entry body depth ordinary present)

/-- First-writer publication installs a proved candidate or retains the exact earlier writer's law. -/
theorem complete_heap (valid : Guard → Prop) (smart : Bool) (entry : Interned NodeKey)
    (body depth ordinary : Value Symbol Guard) (state : State Symbol Guard)
    (heap : Heap valid state) (correct : Correct valid body ordinary) :
    Heap valid (InternedNestedRequestFacts.complete smart entry body depth ordinary state).state := by
  intro key actual actualBody actualDepth actualOrdinary present
  rcases record_cases state.nodeRecords (muKey depth ordinary) key (.mu entry body depth ordinary)
    (.mu actual actualBody actualDepth actualOrdinary) present with old | ⟨_, same⟩
  · exact heap key actual actualBody actualDepth actualOrdinary old
  · cases same
    exact correct

/-- A checked source outcome retains the actual stopping heap and verifies its literal successful result. -/
structure Checked (valid : Guard → Prop) (outcome : Outcome Symbol Guard Result) (post : Result → Prop) : Prop where
  /-- Complete earlier guard observations survive every stopping outcome. -/
  heap : Heap valid outcome.state
  /-- No successful result is inferred for a pending outcome. -/
  result : ∀ value after, outcome = .done value after → post value

/-- A pure result retains the current guard heap. -/
theorem done_checked (valid : Guard → Prop) (value : Result) (state : State Symbol Guard) (post : Result → Prop)
    (heap : Heap valid state) (holds : post value) : Checked valid (.done value state) post :=
  ⟨heap, fun _ _ same => by cases same; exact holds⟩

/-- An actual pending result retains earlier guard certificates without a result assertion. -/
theorem pending_checked (valid : Guard → Prop) (key : NodeKey) (state : State Symbol Guard) (post : Result → Prop)
    (heap : Heap valid state) : Checked valid (.pending key state) post :=
  ⟨heap, fun _ _ impossible => by cases impossible⟩

/-- Source sequencing uses only an actual earlier return and its produced guard heap. -/
theorem bind_checked (valid : Guard → Prop) (outcome : Outcome Symbol Guard First)
    (next : First → State Symbol Guard → Outcome Symbol Guard Result)
    (firstPost : First → Prop) (post : Result → Prop)
    (checked : Checked valid outcome firstPost)
    (later : ∀ value after, outcome = .done value after → Heap valid after → firstPost value →
      Checked valid (next value after) post) : Checked valid (outcome.bind next) post := by
  cases outcome with
  | pending key state => exact pending_checked valid key state post checked.heap
  | done value state => exact later value state rfl checked.heap (checked.result value state rfl)

end MicroCFTA.SourceCurrentConstrainedCapGuardHeap
