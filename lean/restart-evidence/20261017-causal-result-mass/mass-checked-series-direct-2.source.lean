import MicroCFTA.SourceCurrentAllocatedRecursiveMassSeries
import MicroCFTA.SourceCurrentAllocatedRecursiveAllocationTrace

/-!
# Checked serial optional binders from initial numeric resources

The actual checked instruction sequence consumes each preceding result.
Its constructor heap follows the complete source series. Native memo tables,
the domain cache, and equality operations retain their exact initial state.
Initial semantic context constructs the physical trace and its resource bound.
Other recursive-query instructions remain outside this sequence.
-/
namespace MicroCFTA.SourceCurrentAllocatedRecursiveMassCheckedSeries
open InternedConstructorTemplates InternedProbeProvenance InternedNestedFacts
open SourceRecursiveIntersectionCode SourceEqualityNativeDemand
open SourceCurrentAllocatedNativePhysicalCompletion (Good)
open SourceCurrentAllocatedNativePhysicalTraceCompletion (Trace)
open InternedNestedConstruction (Outcome)
open InternedFreshOrdinaryContext (Context)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Source" => InternedConstructorTemplates.State Symbol Guard

/-- Emit the literal optional-binder continuation for every key in source order. -/
def code : List (Nat × Nat) → Value Symbol Guard → Code Symbol Guard (Value Symbol Guard)
  | [], body => .pure body
  | key :: rest, body => .optionalBinder key body (fun value => code rest value)

/-- Replace only the constructor heap in the exact populated checked state. -/
def replaceHeap (before : Checked width) (heap : Source) : Checked width :=
  {before with native := {before.native with machine := {before.native.machine with heap := heap}}}

/-- These continuations emit no new raw edge annotations. -/
theorem code_fields (operations : SourceEqualityConstraintMemoAllocation.State)
    (keys : List (Nat × Nat)) (body : Value Symbol Guard) :
    SourceCurrentAllocatedNativeCodeFields.Fields operations (code keys body) := by
  induction keys generalizing body with
  | nil => trivial
  | cons key rest ih => exact fun value => ih value

/-- Constructor execution retains all native tables, domains, and equality operations exactly. -/
theorem same_tables (before : Checked width) (heap : Source) :
    (replaceHeap before heap).native.nodes = before.native.nodes ∧
      (replaceHeap before heap).native.edges = before.native.edges ∧
      (replaceHeap before heap).native.machine.domains = before.native.machine.domains ∧
      (replaceHeap before heap).operations = before.operations :=
  ⟨rfl, rfl, rfl, rfl⟩

variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]

/-- Each actual source return constructs the exact checked physical instruction trace. -/
theorem trace (keys : List (Nat × Nat)) (body : Value Symbol Guard) (before : Checked width)
    (value : Value Symbol Guard) (heap : Source) (facts : Facts before.native.machine.heap)
    (available : Available before.native.machine.heap body)
    (done : SourceCurrentAllocatedRecursiveMassSeries.run keys body before.native.machine.heap = .done value heap) :
    Trace keys.length (.code (code keys body)) before (.code (.pure value)) (replaceHeap before heap) := by
  induction keys generalizing body before value heap with
  | nil =>
      simp only [SourceCurrentAllocatedRecursiveMassSeries.run, InternedNestedConstruction.Outcome.done.injEq] at done
      rcases done with ⟨rfl, rfl⟩
      exact .refl _ _
  | cons key rest ih =>
      cases first : SourceRecursiveIntersectionMaybeMu.maybeMu key body before.native.machine.heap with
      | pending name after =>
          simp only [SourceCurrentAllocatedRecursiveMassSeries.run, first, Outcome.bind] at done
          cases done
      | done next current =>
          have checked := SourceRecursiveIntersectionMaybeMu.verified key body before.native.machine.heap facts available
          simp only [first, InternedNestedConstruction.Outcome.state] at checked
          have nextAvailable := checked.result next current rfl
          have tail : SourceCurrentAllocatedRecursiveMassSeries.run rest next current = .done value heap := by
            simpa only [SourceCurrentAllocatedRecursiveMassSeries.run, first, Outcome.bind] using done
          have later := ih next (replaceHeap before current) value heap checked.facts nextAvailable tail
          have one : step (.code (code (key :: rest) body)) before =
              .yielded (.code (code rest next)) (replaceHeap before current) := by
            simp only [code, step, SourceRecursiveIntersectionNative.step, first, lift,
              SourceRecursiveIntersectionThunks.advance, replaceHeap]
          have actual := Trace.cons (.code (code (key :: rest) body)) before (.code (code rest next))
            (replaceHeap before current) (.code (.pure value)) (replaceHeap before heap) rest.length available one
            (by simpa only [replaceHeap] using later)
          exact actual

/-- Initial source resources construct the complete checked series at the same populated state. -/
theorem complete (keys : List (Nat × Nat)) (body : Value Symbol Guard) (before : Checked width)
    (good : Good before) (context : Context before.native.machine.heap environment)
    (available : Available before.native.machine.heap body)
    (heap : InternedFreshOrdinaryDepthHeap.Heap before.native.machine.heap)
    (covered : InternedRecordCoherence.Covered [] before.native.machine.heap) :
    ∃ value finalHeap,
      Trace keys.length (.code (code keys body)) before (.code (.pure value)) (replaceHeap before finalHeap) ∧
      Good (replaceHeap before finalHeap) ∧
      InternedValueMassHeap.Stored
        (SourceCurrentAllocatedRecursiveMassSeries.massAfter keys.length (InternedValueMassHeap.initialBound before.native.machine.heap)) finalHeap ∧
      finalHeap.nodes.next ≤ before.native.machine.heap.nodes.next +
        SourceCurrentAllocatedRecursiveMassSeries.credit keys.length (InternedValueMassHeap.initialBound before.native.machine.heap) ∧
      finalHeap.edges.next ≤ before.native.machine.heap.edges.next +
        SourceCurrentAllocatedRecursiveMassSeries.credit keys.length (InternedValueMassHeap.initialBound before.native.machine.heap) ∧
      Context finalHeap environment ∧ InternedFreshOrdinaryDepthHeap.Heap finalHeap ∧
      InternedRecordCoherence.Covered [] finalHeap ∧ Available finalHeap value := by
  obtain ⟨value, finalHeap, done, lastContext, lastHeap, lastCovered, lastAvailable, stored, nodes, edges,
      _mass, _growth, _history⟩ :=
    SourceCurrentAllocatedRecursiveMassSeries.complete keys body before.native.machine.heap context available heap covered
  have actual := trace keys body before value finalHeap context.normal.facts available done
  have fields : SourceCurrentAllocatedNativeFieldClosure.Fields (.code (code keys body)) before :=
    code_fields before.operations keys body
  have retained := SourceCurrentAllocatedRecursiveAllocationTrace.prefix_bound actual good fields
  exact ⟨value, finalHeap, actual, retained.1, stored, nodes, edges, lastContext, lastHeap, lastCovered, lastAvailable⟩

end MicroCFTA.SourceCurrentAllocatedRecursiveMassCheckedSeries
