import MicroCFTA.HeightOrderControlled
import MicroCFTA.InternedValueMassBinderDepth
import MicroCFTA.SourceCurrentAllocatedReaderConsumed

/-!
# Recursive collector completion from initial numeric resources

Actual consumed steps retain their physical premises and numeric control.
The controlled Mu-degree vector bounds their count from the initial state.
The resulting pure fuel reconstructs the same complete heap and rows.
No completed collector equation or future resource bound is an input.
-/
namespace MicroCFTA.SourceCurrentAllocatedReaderNumeric
open Cache InternedConstructorTemplates InternedProbeProvenance InternedRecordCoherence
open InternedNestedProvenance (Values)
open MergedColdReaderClosedInputs (ClosedValues)
open SourceRecursiveIntersectionSemanticHeap (SemanticHeap)
open SourceCurrentAllocatedReaderControl (Config Good Fits g)
open SourceCurrentAllocatedReaderConsumed (Run)
open MergedFreshOrdinaryExposure (collect)
variable {Symbol Guard : Type}

/-- Initial counters, payload mass, and literal occurrence count bound the first control. -/
def initialControl (nodes edges mass count : Nat) : Nat :=
  max (max nodes edges) (max mass (count * mass))

/-- Initial mass also bounds the number of Mu-degree coordinates. -/
def collectFuel (nodes edges mass count : Nat) : Nat :=
  HeightOrderControlled.majorant g (mass + 1) (initialControl nodes edges mass count)

/-- One fixed degree limit and initial control determine sufficient collector fuel. -/
def fuel (limit control : Nat) : Nat := HeightOrderControlled.majorant g (limit + 1) control

variable [DecidableEq (EdgeKey Symbol Guard)]

/-- Every actual finite collector prefix derives its complete controlled vector path. -/
theorem path_control {count limit : Nat} {before after : Config Symbol Guard}
    (actual : SourceCurrentAllocatedReaderConsumed.Path count before after) :
    ∀ control, Good limit before → Fits control before →
      ∃ finalControl, Good limit after ∧ Fits finalControl after ∧
        HeightOrderControlled.Path g (limit + 1)
          (HeightOrder.extend (SourceCurrentAllocatedReaderControl.measure limit before)) control
          (HeightOrder.extend (SourceCurrentAllocatedReaderControl.measure limit after)) finalControl count := by
  induction actual with
  | refl config =>
      intro control good fits
      refine ⟨control, good, fits, .refl ?_⟩
      intro index inside
      simpa only [HeightOrder.extend, dite_eq_left inside] using
        SourceCurrentAllocatedReaderControl.measure_le fits (⟨index, inside⟩ : Fin (limit + 1))
  | @step before middle after count step tail ih =>
      intro control good fits
      obtain ⟨finalControl, afterGood, afterFits, path⟩ :=
        ih (g control) (step.good good) (step.fits good fits)
      refine ⟨finalControl, afterGood, afterFits, .step ?_ (step.decreases good)
        (SourceCurrentAllocatedReaderControl.g_strict control) (Nat.le_refl _) path⟩
      intro index inside
      simpa only [HeightOrder.extend, dite_eq_left inside] using
        SourceCurrentAllocatedReaderControl.measure_le fits (⟨index, inside⟩ : Fin (limit + 1))

/-- Initial physical and numeric facts construct success at one pure sufficient fuel. -/
theorem control_complete (limit control : Nat) (before : Config Symbol Guard)
    (good : Good limit before) (fits : Fits control before) :
    ∃ count rows after,
      Run count before rows after ∧ count ≤ fuel limit control ∧ Good limit after ∧
      Fits (fuel limit control) after ∧ after.pending = [] ∧
      collect (fuel limit control) before.heap before.seen before.pending = .done rows after.heap ∧
      ∀ extra, collect (fuel limit control + extra) before.heap before.seen before.pending = .done rows after.heap := by
  obtain ⟨someFuel, rows, heap, done, _depth, _bounded⟩ := MergedFreshOrdinaryColdTermination.collect_complete
    limit before.heap good.semantic good.covered good.depth good.bounded before.seen before.pending good.available good.closed
  obtain ⟨count, finalSeen, _enough, actual⟩ := SourceCurrentAllocatedReaderConsumed.extract
    someFuel before.heap before.seen before.pending rows heap done
  obtain ⟨finalControl, afterGood, afterFits, path⟩ := path_control actual.path control good fits
  have enough := path.length_le SourceCurrentAllocatedReaderControl.g_mono SourceCurrentAllocatedReaderControl.g_strict
  have bounded := path.final_le SourceCurrentAllocatedReaderControl.g_mono SourceCurrentAllocatedReaderControl.g_strict
  exact ⟨count, rows, ⟨heap, finalSeen, []⟩, actual, enough, afterGood, afterFits.mono bounded,
    rfl, actual.stable _ enough, fun extra => actual.stable _ (Nat.le_trans enough (Nat.le_add_right _ _))⟩

/-- Initial causal mass constructs complete recursive collection with absolute numeric heap bounds. -/
theorem collect_complete (heap : State Symbol Guard) (seen : List Nat) (pending : List (Value Symbol Guard))
    (mass : Nat) (semantic : SemanticHeap heap) (covered : Covered [] heap)
    (depth : InternedOpenDepthReadback.Heap heap) (available : Values heap pending) (closed : ClosedValues pending)
    (stored : InternedValueMassHeap.Stored mass heap) :
    ∃ count rows after,
      Run count ⟨heap, seen, pending⟩ rows after ∧
      count ≤ collectFuel heap.nodes.next heap.edges.next mass pending.length ∧ Good mass after ∧
      Fits (collectFuel heap.nodes.next heap.edges.next mass pending.length) after ∧ after.pending = [] ∧
      collect (collectFuel heap.nodes.next heap.edges.next mass pending.length) heap seen pending = .done rows after.heap ∧
      ∀ extra, collect (collectFuel heap.nodes.next heap.edges.next mass pending.length + extra) heap seen pending = .done rows after.heap := by
  exact control_complete mass (initialControl heap.nodes.next heap.edges.next mass pending.length)
    ⟨heap, seen, pending⟩ ⟨semantic, covered, depth, InternedValueMassBinderDepth.stored_bounded heap mass stored, available, closed⟩
    (SourceCurrentAllocatedReaderControl.initial_fits heap seen pending mass stored available)

end MicroCFTA.SourceCurrentAllocatedReaderNumeric
