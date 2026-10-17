import MicroCFTA.SourceCurrentAllocatedReaderNumeric
import MicroCFTA.SourceEqualityProjectionRead

/-!
# Complete recursive row reads at initial computable fuel

One controlled step pays the direct Mu unfold before any closure fallback.
The initial causal mass fixes the degree dimension. Full returned heaps and
rows fit a pure bound from initial counters and mass. No future successful
fuel, returned state, or resource certificate is supplied.
-/
namespace MicroCFTA.SourceCurrentAllocatedRowReadNumeric
open Cache InternedConstructorTemplates InternedProbeProvenance InternedRecordCoherence
open InternedNestedProvenance (Values Edges)
open InternedNestedConstruction (Outcome)
open SourceRecursiveIntersectionSemanticHeap (SemanticHeap)
open SourceCurrentAllocatedReaderControl (Config Good Fits g)
open SourceCurrentAllocatedReaderNumeric (initialControl fuel)
open MergedFreshOrdinaryExposure (collect nodeEdges)
open MergedSourceExposure (Result)
variable {Symbol Guard : Type}

/-- Initial numeric inputs pay one Mu probe and the complete closure fallback. -/
def readFuel (nodes edges mass : Nat) : Nat :=
  fuel mass (g (initialControl nodes edges mass 1))

variable [DecidableEq (EdgeKey Symbol Guard)]

/-- Full recursive row exposure constructs success and absolute bounds from initial numeric facts. -/
theorem complete_bound (value : Value Symbol Guard) (heap : State Symbol Guard) (mass : Nat)
    (semantic : SemanticHeap heap) (covered : Covered [] heap) (depth : InternedOpenDepthReadback.Heap heap)
    (available : Available heap value) (closed : value.free = []) (stored : InternedValueMassHeap.Stored mass heap) :
    ∃ rows after,
      nodeEdges (readFuel heap.nodes.next heap.edges.next mass) value heap = .done rows after ∧
      InternedValueMassHeap.Stored (readFuel heap.nodes.next heap.edges.next mass) after ∧
      after.nodes.next ≤ readFuel heap.nodes.next heap.edges.next mass ∧
      after.edges.next ≤ readFuel heap.nodes.next heap.edges.next mass := by
  let control := initialControl heap.nodes.next heap.edges.next mass 1
  let total := fuel mass (g control)
  have initialGood : Good mass (⟨heap, [], [value]⟩ : Config Symbol Guard) :=
    ⟨semantic, covered, depth, InternedValueMassBinderDepth.stored_bounded heap mass stored,
      by intro original member; cases List.mem_singleton.mp member; exact available,
      by intro original member; cases List.mem_singleton.mp member; exact closed⟩
  have initialFits : Fits control (⟨heap, [], [value]⟩ : Config Symbol Guard) :=
    SourceCurrentAllocatedReaderControl.initial_fits heap [] [value] mass stored initialGood.available
  have larger : control ≤ total := Nat.le_trans (Nat.le_of_lt (SourceCurrentAllocatedReaderControl.g_strict control))
    (HeightOrderControlled.majorant_ge g SourceCurrentAllocatedReaderControl.g_strict (mass + 1) (g control))
  have unchanged (rows : List (EdgeValue Symbol Guard))
      (done : nodeEdges total value heap = .done rows heap) :
      ∃ rows after, nodeEdges total value heap = .done rows after ∧
        InternedValueMassHeap.Stored total after ∧ after.nodes.next ≤ total ∧ after.edges.next ≤ total :=
    ⟨rows, heap, done, (initialFits.mono larger).stored, (initialFits.mono larger).nodes, (initialFits.mono larger).edges⟩
  have closure (current : State Symbol Guard)
      (good : Good mass (⟨current, [], [value]⟩ : Config Symbol Guard))
      (fits : Fits (g control) (⟨current, [], [value]⟩ : Config Symbol Guard)) :
      ∃ rows after, (collect total current [] [value]).canonical = .done rows after ∧
        InternedValueMassHeap.Stored total after ∧ after.nodes.next ≤ total ∧ after.edges.next ≤ total := by
    obtain ⟨count, rows, after, _actual, _countBound, _afterGood, afterFits, _empty, done, _stable⟩ :=
      SourceCurrentAllocatedReaderNumeric.control_complete mass (g control) ⟨current, [], [value]⟩ good fits
    exact ⟨canonicalEdges rows, after.heap, by simp only [done, Result.canonical],
      afterFits.stored, afterFits.nodes, afterFits.edges⟩
  cases value with
  | empty | reference => exact unchanged [] rfl
  | node entry rows level free => exact unchanged rows rfl
  | union entry members level free =>
      obtain ⟨rows, after, done, afterStored, nodes, edges⟩ := closure heap initialGood
        (initialFits.mono (Nat.le_of_lt (SourceCurrentAllocatedReaderControl.g_strict control)))
      exact ⟨rows, after, done, afterStored, nodes, edges⟩
  | mu entry body level ordinary =>
      obtain ⟨result, middle, unfolded, _context, _depth, _covered, _resultAvailable, growth, history⟩ :=
        InternedFreshOrdinaryStoredSubstitution.unfold_complete_decoded (.mu entry body level ordinary) heap
          semantic.1 available semantic.2 covered
      have step : SourceCurrentAllocatedReaderControl.Step
          (⟨heap, [], [.mu entry body level ordinary]⟩ : Config Symbol Guard)
          ⟨middle, [entry.identity], [result]⟩ := .mu_fresh (by simp) unfolded
      have producedGood := step.good initialGood
      have producedFits := step.fits initialGood initialFits
      have finalFits := producedFits.mono
        (HeightOrderControlled.majorant_ge g SourceCurrentAllocatedReaderControl.g_strict (mass + 1) (g control))
      have fallbackGood : Good mass (⟨middle, [], [.mu entry body level ordinary]⟩ : Config Symbol Guard) :=
        ⟨producedGood.semantic, producedGood.covered, producedGood.depth, producedGood.bounded,
          by intro original member; cases List.mem_singleton.mp member; exact available.grows heap middle growth history,
          by intro original member; cases List.mem_singleton.mp member; exact closed⟩
      have fallbackFits : Fits (g control) (⟨middle, [], [.mu entry body level ordinary]⟩ : Config Symbol Guard) :=
        ⟨producedFits.stored, producedFits.nodes, producedFits.edges,
          Nat.le_trans initialFits.work (Nat.le_of_lt (SourceCurrentAllocatedReaderControl.g_strict control))⟩
      obtain ⟨rows, after, done, afterStored, nodes, edges⟩ := closure middle fallbackGood fallbackFits
      cases result with
      | node resultEntry resultRows resultDepth resultFree =>
          exact ⟨resultRows, middle, by simp only [nodeEdges, unfolded], finalFits.stored, finalFits.nodes, finalFits.edges⟩
      | empty | reference | union | mu =>
          exact ⟨rows, after, by simpa only [nodeEdges, unfolded] using done, afterStored, nodes, edges⟩

/-- The same initial numeric read retains all semantic worker laws and every larger-fuel replay. -/
theorem complete (value : Value Symbol Guard) (heap : State Symbol Guard) (mass : Nat)
    (semantic : SourceEqualityRequiredSemanticCache.SemanticReady heap)
    (available : Available heap value) (closed : value.free = []) (stored : InternedValueMassHeap.Stored mass heap) :
    ∃ rows after,
      nodeEdges (readFuel heap.nodes.next heap.edges.next mass) value heap = .done rows after ∧
      SourceEqualityProjectionRead.Read value heap rows after ∧
      SourceEqualityRequiredCache.Keeps heap after ∧ SourceEqualityRequiredSemanticCache.SemanticReady after ∧
      InternedValueMassHeap.Stored (readFuel heap.nodes.next heap.edges.next mass) after ∧
      after.nodes.next ≤ readFuel heap.nodes.next heap.edges.next mass ∧
      after.edges.next ≤ readFuel heap.nodes.next heap.edges.next mass ∧
      Edges after rows ∧ MergedColdReaderClosedInputs.ClosedEdges rows ∧
      ∀ extra, nodeEdges (readFuel heap.nodes.next heap.edges.next mass + extra) value heap = .done rows after := by
  obtain ⟨rows, after, done, afterStored, nodes, edges⟩ := complete_bound value heap mass semantic.ready.semantic
    semantic.ready.covered semantic.ready.depth available closed stored
  have actual : SourceEqualityProjectionRead.Read value heap rows after := .done _ done
  have checked := actual.verified semantic available closed
  refine ⟨rows, after, done, actual, checked.1, checked.2.1, afterStored, nodes, edges, checked.2.2.1, checked.2.2.2, ?_⟩
  intro extra
  exact (MergedFreshOrdinaryColdReplay.nodeEdges_stable _ extra value heap
    (by simp only [done, MergedSourceExposure.Finished])).trans done

end MicroCFTA.SourceCurrentAllocatedRowReadNumeric
