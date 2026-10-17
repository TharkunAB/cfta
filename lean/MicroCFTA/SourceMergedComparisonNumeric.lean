import MicroCFTA.SourceMergedComparisonReplayStages
import MicroCFTA.SourceCurrentAllocatedRowReadUniform
import MicroCFTA.SourceMergedComparisonMass
import MicroCFTA.SourceMergedComparisonStability

/-!
# General repaired comparisons at initial computable fuel

Exact unfold histories bound every reached heap from initial resources.
The resulting identity universe bounds fresh ancestors on each recursive
path. Ordered stage replay retains every original intermediate full heap.
The complete endpoint supplies its own successful execution and resource bound.
-/
namespace MicroCFTA.SourceMergedComparisonNumeric
open InternedConstructorTemplates InternedProbeProvenance
open SourceEqualityRequiredSemanticCache (SemanticReady)
open SourceCurrentAllocatedUnfoldHistory (History heapBound)
open SourceCurrentAllocatedRowReadNumeric (readFuel)
open SourceMergedComparisonEffects (bind_done read_graph Effect)
open MergedComparisonCompletion (remainingPairs remaining_mem remaining_cons_lt)
open MergedSourceComparison (Result identity)
open MergedFreshOrdinaryComparison (check allRows)
variable {Symbol Guard : Type}

/-- One initial heap ceiling supplies sufficient fuel for every reached row read. -/
def readerFuel (nodes edges mass : Nat) : Nat :=
  let bound := heapBound nodes edges mass
  readFuel bound bound bound

/-- One finite pair universe and a uniform row-read bound determine comparison fuel. -/
def comparisonFuel (nodes edges mass : Nat) : Nat :=
  let bound := heapBound nodes edges mass
  1 + bound * bound + readerFuel nodes edges mass

variable [DecidableEq (EdgeKey Symbol Guard)]

/-- Every actual reached read replays at the initial uniform fuel and all larger fuels. -/
theorem read_replay (origin : State Symbol Guard) (mass : Nat)
    (initial : SemanticReady origin) (stored : InternedValueMassHeap.Stored mass origin)
    (oldFuel : Nat) (value : Value Symbol Guard) (before : State Symbol Guard)
    (semantic : SemanticReady before) (available : Available before value) (closed : value.free = [])
    (reached : History origin before) (rows : List (EdgeValue Symbol Guard)) (after : State Symbol Guard)
    (done : MergedFreshOrdinaryExposure.read oldFuel value before = .done rows after)
    (newFuel : Nat) (enough : readerFuel origin.nodes.next origin.edges.next mass ≤ newFuel) :
    MergedFreshOrdinaryExposure.read newFuel value before = .done rows after := by
  let bound := heapBound origin.nodes.next origin.edges.next mass
  have fits := (reached.complete initial.ready.semantic initial.ready.covered initial.ready.depth stored).2
  obtain ⟨_uniform, _kept, _ready, _stored, _nodes, _edges, _resident, _closed, stable⟩ :=
    SourceCurrentAllocatedRowReadUniform.of_read (read_graph oldFuel value before rows after done)
      bound semantic available closed fits.stored fits.nodes fits.edges
  have same : readFuel bound bound bound + (newFuel - readFuel bound bound bound) = newFuel := by
    change readFuel bound bound bound ≤ newFuel at enough
    omega
  have replay := stable (newFuel - readFuel bound bound bound)
  rw [same] at replay
  simp only [MergedFreshOrdinaryExposure.read, replay]

/-- A successful actual comparison replays at the initial pair and row-read allowance. -/
theorem check_replay [DecidableEq Symbol] (origin : State Symbol Guard) (mass : Nat)
    (initial : SemanticReady origin) (stored : InternedValueMassHeap.Stored mass origin)
    (oldFuel : Nat) (clear : Guard → Bool) (above : List (Nat × Nat))
    (wide narrow : Value Symbol Guard) (before : State Symbol Guard) (semantic : SemanticReady before)
    (wideInput : Available before wide) (narrowInput : Available before narrow)
    (wideClosed : wide.free = []) (narrowClosed : narrow.free = []) (reached : History origin before)
    (answer : Bool) (after : State Symbol Guard) (done : check clear oldFuel above wide narrow before = .done answer after)
    (newFuel : Nat)
    (enough : (remainingPairs (heapBound origin.nodes.next origin.edges.next mass) above).length +
      readerFuel origin.nodes.next origin.edges.next mass ≤ newFuel) :
    check clear newFuel above wide narrow before = .done answer after := by
  let bound := heapBound origin.nodes.next origin.edges.next mass
  obtain ⟨good, fits⟩ := reached.complete initial.ready.semantic initial.ready.covered initial.ready.depth stored
  rw [check] at done ⊢
  by_cases narrowEmpty : narrow.referenceOf = .empty
  · simpa only [narrowEmpty, ↓reduceIte] using done
  simp only [narrowEmpty, ↓reduceIte] at done ⊢
  by_cases wideEmpty : wide.referenceOf = .empty
  · simpa only [wideEmpty, ↓reduceIte] using done
  simp only [wideEmpty, ↓reduceIte] at done ⊢
  by_cases same : wide.referenceOf = narrow.referenceOf
  · simpa only [same, ↓reduceIte] using done
  simp only [same, ↓reduceIte] at done ⊢
  obtain ⟨wideId, wideIdentity, wideBound⟩ := SourceCurrentAllocatedRowReadUniform.identity_bound
    wide before bound semantic.ready.semantic.1.normal.facts wideInput wideClosed wideEmpty fits.nodes
  obtain ⟨narrowId, narrowIdentity, narrowBound⟩ := SourceCurrentAllocatedRowReadUniform.identity_bound
    narrow before bound semantic.ready.semantic.1.normal.facts narrowInput narrowClosed narrowEmpty fits.nodes
  simp only [wideIdentity, narrowIdentity] at done ⊢
  by_cases visited : (wideId, narrowId) ∈ above
  · simpa only [visited, ↓reduceIte] using done
  simp only [visited, ↓reduceIte] at done ⊢
  have decreases := remaining_cons_lt bound above (wideId, narrowId)
    (remaining_mem bound above wideId narrowId wideBound narrowBound visited)
  cases oldFuel with
  | zero => cases done
  | succ oldFuel =>
      cases newFuel with
      | zero => change (remainingPairs bound above).length + _ ≤ 0 at enough; omega
      | succ newFuel =>
          obtain ⟨narrows, middle, readDone, later⟩ := (bind_done _ _ answer after).mp done
          have readFacts := (read_graph (oldFuel + 1) narrow before narrows middle readDone).verified semantic narrowInput narrowClosed
          have readRecorded := SourceMergedComparisonHistory.read_recorded mass (oldFuel + 1) narrow before
            semantic good.bounded narrowInput narrowClosed narrows middle readDone
          have recorded : SourceMergedComparisonHistory.Callback mass
              (check clear oldFuel ((wideId, narrowId) :: above)) :=
            SourceMergedComparisonHistory.check_recorded (Symbol := Symbol) mass clear oldFuel ((wideId, narrowId) :: above)
          have replay : SourceMergedComparisonReplayStages.CallbackReplay mass origin
              (check clear oldFuel ((wideId, narrowId) :: above))
              (check clear newFuel ((wideId, narrowId) :: above)) := by
            intro left right current currentSemantic _bounded leftInput rightInput leftClosed rightClosed reachedPrefix accepted final actual
            apply check_replay origin mass initial stored oldFuel clear ((wideId, narrowId) :: above)
              left right current currentSemantic leftInput rightInput leftClosed rightClosed reachedPrefix accepted final actual newFuel
            change (remainingPairs bound ((wideId, narrowId) :: above)).length + _ ≤ newFuel
            change (remainingPairs bound above).length + _ ≤ newFuel + 1 at enough
            omega
          have enoughRead : readerFuel origin.nodes.next origin.edges.next mass ≤ newFuel + 1 := by omega
          have readNew := read_replay origin mass initial stored (oldFuel + 1) narrow before semantic
            narrowInput narrowClosed reached narrows middle readDone (newFuel + 1) enoughRead
          have rowsNew := SourceMergedComparisonReplayStages.allRows_replay mass origin (oldFuel + 1) (newFuel + 1)
            clear _ _ recorded replay
            (fun value current currentSemantic _bounded available closed reachedPrefix rows final actual =>
              read_replay origin mass initial stored (oldFuel + 1) value current currentSemantic
                available closed reachedPrefix rows final actual (newFuel + 1) enoughRead)
            wide narrows middle readFacts.2.1 readRecorded.bounded (readFacts.1.available wide wideInput)
            readFacts.2.2.1 wideClosed readFacts.2.2.2 (reached.trans readRecorded.history) answer after later
          simpa only [readNew, Result.bind] using rowsNew
termination_by oldFuel

/-- Initial semantic facts and causal mass construct a complete comparison at pure computed fuel. -/
theorem check_complete [DecidableEq Symbol] (clear : Guard → Bool) (before : State Symbol Guard)
    (mass : Nat) (semantic : SemanticReady before) (stored : InternedValueMassHeap.Stored mass before)
    (above : List (Nat × Nat)) (wide narrow : Value Symbol Guard)
    (wideInput : Available before wide) (narrowInput : Available before narrow)
    (wideClosed : wide.free = []) (narrowClosed : narrow.free = []) :
    ∃ answer after,
      check clear (comparisonFuel before.nodes.next before.edges.next mass) above wide narrow before = .done answer after ∧
      Effect before after ∧
      SourceCurrentAllocatedUnfoldHistory.Fits (heapBound before.nodes.next before.edges.next mass) after ∧
      SourceMergedComparisonMass.Resources
        (SourceMergedComparisonMass.comparisonBound (comparisonFuel before.nodes.next before.edges.next mass) mass) before after ∧
      ∀ extra, check clear (comparisonFuel before.nodes.next before.edges.next mass + extra)
        above wide narrow before = .done answer after := by
  obtain ⟨someFuel, answer, after, stable, _effect⟩ := SourceMergedComparisonCompletion.check_complete clear before
    semantic above wide narrow wideInput narrowInput wideClosed narrowClosed
  have oldDone := stable someFuel (Nat.le_refl _)
  have done := check_replay before mass semantic stored someFuel clear above wide narrow before semantic
    wideInput narrowInput wideClosed narrowClosed (.refl before) answer after oldDone
    (comparisonFuel before.nodes.next before.edges.next mass) (by
      have pairs := SourceCurrentAllocatedRowReadUniform.remainingPairs_length_le
        (heapBound before.nodes.next before.edges.next mass) above
      dsimp only [comparisonFuel]
      omega)
  have recorded := SourceMergedComparisonHistory.check_recorded mass clear
    (comparisonFuel before.nodes.next before.edges.next mass) above wide narrow before semantic
    (InternedValueMassBinderDepth.stored_bounded before mass stored) wideInput narrowInput wideClosed narrowClosed answer after done
  have fits := (recorded.history.complete semantic.ready.semantic semantic.ready.covered semantic.ready.depth stored).2
  have resources := SourceMergedComparisonMass.check_bound
    clear (comparisonFuel before.nodes.next before.edges.next mass) above wide narrow before mass semantic stored
    wideInput narrowInput wideClosed narrowClosed answer after done
  exact ⟨answer, after, done, recorded.effect, fits, resources, fun extra =>
    (SourceMergedComparisonStability.check_stable clear _ extra above wide narrow before answer after done).trans done⟩

end MicroCFTA.SourceMergedComparisonNumeric
