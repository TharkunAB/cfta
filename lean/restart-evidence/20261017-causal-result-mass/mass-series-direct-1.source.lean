import MicroCFTA.SourceCurrentAllocatedRecursiveMassBudget
import MicroCFTA.SourceRecursiveIntersectionMaybeMuCompletion

/-!
# Initial resources for serial generated optional binders

Each actual optional binder consumes the preceding returned body and heap.
One initial numeric payload bound determines every later bound and charge.
The all-outcome theorem retains pending prefixes. Initial semantic context
constructs a successful complete series. This series does not contain the
other instructions of a complete recursive intersection query.
-/
namespace MicroCFTA.SourceCurrentAllocatedRecursiveMassSeries
open InternedConstructorTemplates InternedProbeProvenance InternedNestedFacts
open InternedNestedConstruction (Outcome)
open InternedFreshOrdinaryContext (Context)
open SourceCurrentAllocatedRecursiveMassBudget (charge ceiling ceiling_ge)
local notation "mass" => InternedValueMass.value
local notation "Stored" => InternedValueMassHeap.Stored
local notation "maybeMu" => SourceRecursiveIntersectionMaybeMu.maybeMu
variable {Symbol Guard : Type}

/-- Feed each literal returned value and state into the next optional binder. -/
def run [DecidableEq (EdgeKey Symbol Guard)] : List (Nat × Nat) → Value Symbol Guard → State Symbol Guard → Outcome Symbol Guard (Value Symbol Guard)
  | [], body, before => .done body before
  | key :: rest, body, before => (maybeMu key body before).bind fun value after => run rest value after

/-- The initial bound and number of calls determine the final payload bound. -/
def massAfter : Nat → Nat → Nat
  | 0, bound => bound
  | count + 1, bound => massAfter count (ceiling bound)

/-- Sum every later numeric charge without reading a later heap or result. -/
def credit : Nat → Nat → Nat
  | 0, _ => 0
  | count + 1, bound => charge bound + credit count (ceiling bound)

/-- Every finite series retains its initial payload bound. -/
theorem massAfter_ge (count bound : Nat) : bound ≤ massAfter count bound := by
  induction count generalizing bound with
  | zero => exact Nat.le_refl _
  | succ count ih => exact Nat.le_trans (ceiling_ge bound) (ih (ceiling bound))

/-- Numeric payload schedules compose from their exact common bound. -/
theorem massAfter_add (first last bound : Nat) :
    massAfter (first + last) bound = massAfter last (massAfter first bound) := by
  induction first generalizing bound with
  | zero => simp only [Nat.zero_add, massAfter]
  | succ first ih =>
      change massAfter (first + last) (ceiling bound) = massAfter last (massAfter first (ceiling bound))
      exact ih (ceiling bound)

/-- Numeric constructor credits compose without later-entry counters. -/
theorem credit_add (first last bound : Nat) :
    credit (first + last) bound = credit first bound + credit last (massAfter first bound) := by
  induction first generalizing bound with
  | zero => simp only [Nat.zero_add, credit, massAfter]
  | succ first ih =>
      change charge bound + credit (first + last) (ceiling bound) =
        (charge bound + credit first (ceiling bound)) + credit last (massAfter first (ceiling bound))
      rw [ih]
      omega

/-- Every actual stopping outcome fits the one initial series budget and causal store bound. -/
theorem run_bound [DecidableEq (EdgeKey Symbol Guard)] (keys : List (Nat × Nat))
    (body : Value Symbol Guard) (before : State Symbol Guard) (bound : Nat)
    (facts : Facts before) (stored : Stored bound before) (available : Available before body) :
    Stored (massAfter keys.length bound) (run keys body before).state ∧
      (run keys body before).state.nodes.next ≤ before.nodes.next + credit keys.length bound ∧
      (run keys body before).state.edges.next ≤ before.edges.next + credit keys.length bound ∧
      Verified before (run keys body before) Available ∧
      ∀ value after, run keys body before = .done value after → mass value ≤ massAfter keys.length bound := by
  induction keys generalizing body before bound with
  | nil =>
      refine ⟨stored, Nat.le_refl _, Nat.le_refl _, pure_verified before facts body Available available, ?_⟩
      intro value after done
      cases done
      exact InternedValueMassHeap.available before stored body available
  | cons key rest ih =>
      have sizes := SourceCurrentAllocatedRecursiveMassBudget.stored_bound key body before bound facts stored available
      have counters := SourceCurrentAllocatedRecursiveMassBudget.allocation_bound key body before bound facts stored available
      have checked := SourceRecursiveIntersectionMaybeMu.verified key body before facts available
      cases first : maybeMu key body before with
      | pending key after =>
          simp only [first, Outcome.state] at sizes counters checked
          simp only [run, first, Outcome.bind, Outcome.state, List.length_cons, massAfter, credit]
          refine ⟨sizes.1.mono (massAfter_ge rest.length (ceiling bound)), by omega, by omega, checked, ?_⟩
          intro value final impossible
          cases impossible
      | done value middle =>
          simp only [first, Outcome.state] at sizes counters checked
          have nextAvailable := checked.result value middle rfl
          obtain ⟨lastStored, nodes, edges, lastChecked, returned⟩ :=
            ih value middle (ceiling bound) checked.facts sizes.1 nextAvailable
          simp only [run, first, Outcome.bind, List.length_cons, massAfter, credit]
          refine ⟨lastStored, by omega, by omega, ?_, returned⟩
          exact ⟨lastChecked.facts, grows_trans checked.growth lastChecked.growth,
            extends_trans checked.history lastChecked.history, lastChecked.result⟩

/-- Initial semantic input constructs each actual returned body and successful next call. -/
theorem finish [DecidableEq (EdgeKey Symbol Guard)] (keys : List (Nat × Nat))
    (body : Value Symbol Guard) (before : State Symbol Guard) (context : Context before environment)
    (available : Available before body) (heap : InternedFreshOrdinaryDepthHeap.Heap before)
    (covered : InternedRecordCoherence.Covered [] before) :
    ∃ value after, run keys body before = .done value after ∧ Context after environment ∧
      InternedFreshOrdinaryDepthHeap.Heap after ∧ InternedRecordCoherence.Covered [] after ∧ Available after value := by
  induction keys generalizing body before with
  | nil => exact ⟨body, before, rfl, context, heap, covered, available⟩
  | cons key rest ih =>
      obtain ⟨value, middle, done, nextContext, nextHeap, nextCovered, nextAvailable, _growth, _history⟩ :=
        SourceRecursiveIntersectionMaybeMu.complete_decoded key body before context available heap covered
      obtain ⟨result, after, tail, lastContext, lastHeap, lastCovered, lastAvailable⟩ :=
        ih value middle nextContext nextAvailable nextHeap nextCovered
      exact ⟨result, after, by simp only [run, done, Outcome.bind, tail],
        lastContext, lastHeap, lastCovered, lastAvailable⟩

/-- One computed initial source budget constructs the complete serial generated-binder execution. -/
theorem complete [DecidableEq (EdgeKey Symbol Guard)] (keys : List (Nat × Nat))
    (body : Value Symbol Guard) (before : State Symbol Guard) (context : Context before environment)
    (available : Available before body) (heap : InternedFreshOrdinaryDepthHeap.Heap before)
    (covered : InternedRecordCoherence.Covered [] before) :
    ∃ value after, run keys body before = .done value after ∧ Context after environment ∧
      InternedFreshOrdinaryDepthHeap.Heap after ∧ InternedRecordCoherence.Covered [] after ∧ Available after value ∧
      Stored (massAfter keys.length (InternedValueMassHeap.initialBound before)) after ∧
      after.nodes.next ≤ before.nodes.next + credit keys.length (InternedValueMassHeap.initialBound before) ∧
      after.edges.next ≤ before.edges.next + credit keys.length (InternedValueMassHeap.initialBound before) ∧
      mass value ≤ massAfter keys.length (InternedValueMassHeap.initialBound before) ∧
      Grows before after ∧ MergedPhysicalWarmup.Extends before.nodes.issued after.nodes.issued := by
  obtain ⟨value, after, done, lastContext, lastHeap, lastCovered, lastAvailable⟩ :=
    finish keys body before context available heap covered
  have bounds := run_bound keys body before (InternedValueMassHeap.initialBound before) context.normal.facts
    (InternedValueMassHeap.initial before context.normal.facts) available
  have returned := bounds.2.2.2.2 value after done
  simp only [done, Outcome.state] at bounds
  exact ⟨value, after, done, lastContext, lastHeap, lastCovered, lastAvailable, bounds.1,
    bounds.2.1, bounds.2.2.1, returned, bounds.2.2.2.1.growth, bounds.2.2.2.1.history⟩

end MicroCFTA.SourceCurrentAllocatedRecursiveMassSeries
