import MicroCFTA.SourceCurrentAllocatedRowReadNumeric
import MicroCFTA.SourceEqualityProjectionRead
import MicroCFTA.MergedComparisonCompletion

/-!
# Uniform initial resource bounds for recursive row reads

One causal bound covers the current heap mass and both issued counters.
The same pure reader fuel works at every such heap. Successful earlier
reads retain their exact rows and complete returned heap at that fuel.
-/
namespace MicroCFTA.SourceCurrentAllocatedRowReadUniform
open InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Edges)
open MergedColdReaderClosedInputs (ClosedEdges)
open SourceEqualityRequiredCache SourceEqualityRequiredSemanticCache
open SourceCurrentAllocatedRowReadNumeric (readFuel)
open MergedFreshOrdinaryExposure (nodeEdges)
open SourceCurrentAllocatedReaderControl (g)
variable {Symbol Guard : Type}

/-- Larger issued counters retain the reader fuel at the same causal mass. -/
theorem readFuel_mono (mass : Nat) {firstNodes lastNodes firstEdges lastEdges : Nat}
    (nodes : firstNodes ≤ lastNodes) (edges : firstEdges ≤ lastEdges) :
    readFuel firstNodes firstEdges mass ≤ readFuel lastNodes lastEdges mass := by
  unfold readFuel SourceCurrentAllocatedReaderNumeric.fuel
  apply HeightOrderControlled.majorant_mono g SourceCurrentAllocatedReaderControl.g_mono
    SourceCurrentAllocatedReaderControl.g_strict
  apply SourceCurrentAllocatedReaderControl.g_mono
  unfold SourceCurrentAllocatedReaderNumeric.initialControl
  omega

section Reads
variable [DecidableEq (EdgeKey Symbol Guard)]

/-- Current initial facts construct a complete row read at one uniform pure fuel. -/
theorem complete (value : Value Symbol Guard) (heap : State Symbol Guard) (bound : Nat)
    (semantic : SemanticReady heap) (available : Available heap value) (closed : value.free = [])
    (stored : InternedValueMassHeap.Stored bound heap)
    (nodes : heap.nodes.next ≤ bound) (edges : heap.edges.next ≤ bound) :
    ∃ rows after,
      nodeEdges (readFuel bound bound bound) value heap = .done rows after ∧
      SourceEqualityProjectionRead.Read value heap rows after ∧ Keeps heap after ∧ SemanticReady after ∧
      InternedValueMassHeap.Stored (readFuel bound bound bound) after ∧
      after.nodes.next ≤ readFuel bound bound bound ∧ after.edges.next ≤ readFuel bound bound bound ∧
      Edges after rows ∧ ClosedEdges rows ∧
      ∀ extra, nodeEdges (readFuel bound bound bound + extra) value heap = .done rows after := by
  obtain ⟨rows, after, done, actual, kept, ready, afterStored, afterNodes, afterEdges, resident, rowClosed, stable⟩ :=
    SourceCurrentAllocatedRowReadNumeric.complete value heap bound semantic available closed stored
  have increase := readFuel_mono bound nodes edges
  have uniform := stable (readFuel bound bound bound - readFuel heap.nodes.next heap.edges.next bound)
  have same : readFuel heap.nodes.next heap.edges.next bound +
      (readFuel bound bound bound - readFuel heap.nodes.next heap.edges.next bound) = readFuel bound bound bound := by omega
  rw [same] at uniform
  refine ⟨rows, after, uniform, actual, kept, ready, afterStored.mono increase,
    Nat.le_trans afterNodes increase, Nat.le_trans afterEdges increase, resident, rowClosed, ?_⟩
  intro extra
  exact (MergedFreshOrdinaryColdReplay.nodeEdges_stable _ extra value heap
    (by simp only [uniform, MergedSourceExposure.Finished])).trans uniform

/-- A successful earlier graph has the same exact return at the uniform initial fuel. -/
theorem of_read {value : Value Symbol Guard} {heap after : State Symbol Guard}
    {rows : List (EdgeValue Symbol Guard)} (actual : SourceEqualityProjectionRead.Read value heap rows after)
    (bound : Nat) (semantic : SemanticReady heap) (available : Available heap value) (closed : value.free = [])
    (stored : InternedValueMassHeap.Stored bound heap)
    (nodes : heap.nodes.next ≤ bound) (edges : heap.edges.next ≤ bound) :
    nodeEdges (readFuel bound bound bound) value heap = .done rows after ∧ Keeps heap after ∧ SemanticReady after ∧
      InternedValueMassHeap.Stored (readFuel bound bound bound) after ∧
      after.nodes.next ≤ readFuel bound bound bound ∧ after.edges.next ≤ readFuel bound bound bound ∧
      Edges after rows ∧ ClosedEdges rows ∧
      ∀ extra, nodeEdges (readFuel bound bound bound + extra) value heap = .done rows after := by
  obtain ⟨produced, final, done, checked, kept, ready, afterStored, afterNodes, afterEdges, resident, rowClosed, stable⟩ :=
    complete value heap bound semantic available closed stored nodes edges
  obtain ⟨rfl, rfl⟩ := checked.unique actual
  exact ⟨done, kept, ready, afterStored, afterNodes, afterEdges, resident, rowClosed, stable⟩

end Reads

/-- Every closed nonempty available operand has an identity below the current uniform bound. -/
theorem identity_bound (value : Value Symbol Guard) (heap : State Symbol Guard) (bound : Nat)
    (facts : InternedNestedFacts.Facts heap) (available : Available heap value) (closed : value.free = [])
    (nonempty : value.referenceOf ≠ .empty) (nodes : heap.nodes.next ≤ bound) :
    ∃ number, MergedSourceComparison.identity value = some number ∧ number < bound := by
  obtain ⟨number, found, issued⟩ := MergedComparisonCompletion.identity_closed value heap facts available closed nonempty
  exact ⟨number, found, Nat.lt_of_lt_of_le issued nodes⟩

/-- The full current ordered pair universe has at most the square of its identity bound. -/
theorem remainingPairs_length_le (bound : Nat) (above : List (Nat × Nat)) :
    (MergedComparisonCompletion.remainingPairs bound above).length ≤ bound * bound := by
  unfold MergedComparisonCompletion.remainingPairs
  apply Nat.le_trans (List.length_filter_le _ _)
  simp only [List.length_flatMap, List.length_map, List.length_range, List.map_const', List.sum_replicate_nat, Nat.le_refl]

end MicroCFTA.SourceCurrentAllocatedRowReadUniform
