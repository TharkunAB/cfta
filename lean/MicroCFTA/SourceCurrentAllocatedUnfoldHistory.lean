import MicroCFTA.SourceCurrentAllocatedReaderNumeric
import MicroCFTA.InternedFreshMuUnfoldBudget

/-!
# Initial bounds for actual closed unfolding histories

A history records successful repaired unfoldings at their exact heaps.
Heap-changing events decrease the unfinished Mu-degree vector. Exact heap
replays do not change the numeric control. The initial degree limit and
resource bound therefore bound all later heaps, independently of an outer
comparison fuel or the number of allocation-free replays.
-/
namespace MicroCFTA.SourceCurrentAllocatedUnfoldHistory
open Cache InternedConstructorTemplates InternedProbeProvenance InternedRecordCoherence
open InternedNestedConstruction (Outcome)
open SourceRecursiveIntersectionSemanticHeap (SemanticHeap)
open SourceCurrentAllocatedReaderControl (g)
variable {Symbol Guard : Type}

/-- Initial physical facts have no pending-list obligation. -/
abbrev Good (limit : Nat) (heap : State Symbol Guard) : Prop :=
  SourceCurrentAllocatedReaderControl.Good limit ⟨heap, [], []⟩

/-- One current bound covers stored payloads and both issued counters. -/
abbrev Fits (bound : Nat) (heap : State Symbol Guard) : Prop :=
  SourceCurrentAllocatedReaderControl.Fits bound ⟨heap, [], []⟩

/-- An event records one actual successful closed repaired unfolding. -/
inductive Event [DecidableEq (EdgeKey Symbol Guard)] : State Symbol Guard → State Symbol Guard → Prop where
  /-- The input is available and closed at this event's own starting heap. -/
  | unfold (value result : Value Symbol Guard) (available : Available before value) (closed : value.free = [])
      (done : InternedFreshOrdinaryStoredSubstitution.unfold value before = .done result after) : Event before after

/-- Finite histories retain exact full heaps at each sequential boundary. -/
inductive History [DecidableEq (EdgeKey Symbol Guard)] : State Symbol Guard → State Symbol Guard → Prop where
  /-- An empty history keeps the complete heap. -/
  | refl (heap : State Symbol Guard) : History heap heap
  /-- One actual unfolding precedes the remaining exact history. -/
  | step (event : Event before middle) (tail : History middle after) : History before after

/-- Sequential histories share the literal complete middle heap. -/
theorem History.trans [DecidableEq (EdgeKey Symbol Guard)] {before middle after : State Symbol Guard}
    (first : History before middle) (last : History middle after) : History before after := by
  induction first with
  | refl => exact last
  | step event tail ih => exact .step event (ih last)

private theorem singleton_good {limit : Nat} {heap : State Symbol Guard} {value : Value Symbol Guard}
    (good : Good limit heap) (available : Available heap value) (closed : value.free = []) :
    SourceCurrentAllocatedReaderControl.Good limit ⟨heap, [], [value]⟩ :=
  ⟨good.semantic, good.covered, good.depth, good.bounded,
    by intro item member; obtain rfl := List.mem_singleton.mp member; exact available,
    by intro item member; obtain rfl := List.mem_singleton.mp member; exact closed⟩

private theorem singleton_fits {bound : Nat} {heap : State Symbol Guard} {value : Value Symbol Guard}
    (fits : Fits bound heap) (available : Available heap value) :
    SourceCurrentAllocatedReaderControl.Fits bound ⟨heap, [], [value]⟩ := by
  have small := Nat.le_trans (SourceCurrentAllocatedReaderControl.weight_le_mass value)
    (InternedValueMassHeap.available heap fits.stored value available)
  exact ⟨fits.stored, fits.nodes, fits.edges, by simpa only [MergedColdReaderTermination.workWeight, Nat.add_zero] using small⟩

/-- One actual event retains every physical fact and the fixed degree limit. -/
theorem Event.good [DecidableEq (EdgeKey Symbol Guard)] {limit : Nat} {before after : State Symbol Guard}
    (event : Event before after) (good : Good limit before) : Good limit after := by
  cases event with
  | unfold value result available closed done =>
    cases value with
    | empty | reference | node | union =>
      have same : after = before := (Outcome.done.inj done).2.symm
      subst after
      exact good
    | mu entry body depth ordinary =>
      have step : SourceCurrentAllocatedReaderControl.Step
          (⟨before, [], [.mu entry body depth ordinary]⟩ : SourceCurrentAllocatedReaderControl.Config Symbol Guard)
          ⟨after, [entry.identity], [result]⟩ := .mu_fresh (by simp) done
      have checked := step.good (singleton_good good available closed)
      exact ⟨checked.semantic, checked.covered, checked.depth, checked.bounded,
        (by intro item member; cases member), (by intro item member; cases member)⟩

/-- One actual event derives its next resource bound from the current heap. -/
theorem Event.fits [DecidableEq (EdgeKey Symbol Guard)] {limit bound : Nat} {before after : State Symbol Guard}
    (event : Event before after) (good : Good limit before) (fits : Fits bound before) : Fits (g bound) after := by
  cases event with
  | unfold value result available closed done =>
    cases value with
    | empty | reference | node | union =>
      have same : after = before := (Outcome.done.inj done).2.symm
      subst after
      exact fits.mono (Nat.le_of_lt (SourceCurrentAllocatedReaderControl.g_strict bound))
    | mu entry body depth ordinary =>
      have step : SourceCurrentAllocatedReaderControl.Step
          (⟨before, [], [.mu entry body depth ordinary]⟩ : SourceCurrentAllocatedReaderControl.Config Symbol Guard)
          ⟨after, [entry.identity], [result]⟩ := .mu_fresh (by simp) done
      have checked := step.fits (singleton_good good available closed) (singleton_fits fits available)
      exact ⟨checked.stored, checked.nodes, checked.edges, Nat.zero_le _⟩

/-- Every event changes the unfinished vector or returns the identical heap. -/
theorem Event.progress [DecidableEq (EdgeKey Symbol Guard)] {limit : Nat} {before after : State Symbol Guard}
    (event : Event before after) (good : Good limit before) :
    InternedFreshMuUnfoldBudget.Progress limit before after := by
  cases event with
  | unfold value result available closed done =>
      exact InternedFreshMuUnfoldBudget.unfold_progress limit value before good.semantic good.covered
        good.depth good.bounded available closed result after done

/-- Count only unfinished canonical Mu records at each fixed degree. -/
noncomputable def measure [DecidableEq (EdgeKey Symbol Guard)] (limit : Nat) (heap : State Symbol Guard) : Fin limit → Nat :=
  fun index => InternedFreshMuUnfoldBudget.count heap index

/-- Every unfinished-degree count fits the current issued node counter bound. -/
theorem measure_le [DecidableEq (EdgeKey Symbol Guard)] {bound limit : Nat} {heap : State Symbol Guard} (fits : Fits bound heap)
    (index : Fin limit) : measure limit heap index ≤ bound := by
  have small := List.countP_le_length (l := List.range heap.nodes.next)
    (p := InternedFreshMuUnfoldBudget.unfinishedAt heap index)
  simp only [List.length_range] at small
  exact Nat.le_trans small fits.nodes

/-- Remove exact heap replays and derive a controlled path of changing events. -/
theorem History.path_control [DecidableEq (EdgeKey Symbol Guard)] {before after : State Symbol Guard} (actual : History before after)
    (limit bound : Nat) (good : Good limit before) (fits : Fits bound before) :
    ∃ count finalBound, Good limit after ∧ Fits finalBound after ∧
      HeightOrderControlled.Path g limit (HeightOrder.extend (measure limit before)) bound
        (HeightOrder.extend (measure limit after)) finalBound count := by
  induction actual generalizing bound with
  | refl heap =>
    refine ⟨0, bound, good, fits, .refl ?_⟩
    intro index inside
    simpa only [HeightOrder.extend, dite_eq_left inside] using measure_le fits (⟨index, inside⟩ : Fin limit)
  | @step before middle after event tail ih =>
    rcases event.progress good with decrease | same
    · obtain ⟨count, finalBound, afterGood, afterFits, path⟩ :=
        ih (g bound) (event.good good) (event.fits good fits)
      refine ⟨count + 1, finalBound, afterGood, afterFits, .step ?_ decrease
        (SourceCurrentAllocatedReaderControl.g_strict bound) (Nat.le_refl _) path⟩
      intro index inside
      simpa only [HeightOrder.extend, dite_eq_left inside] using measure_le fits (⟨index, inside⟩ : Fin limit)
    · subst middle
      exact ih bound good fits

/-- The initial degree limit and resources bound every finite history endpoint. -/
theorem History.bound [DecidableEq (EdgeKey Symbol Guard)] {limit bound : Nat} {before after : State Symbol Guard}
    (actual : History before after) (good : Good limit before) (fits : Fits bound before) :
    Good limit after ∧ Fits (HeightOrderControlled.majorant g limit bound) after := by
  obtain ⟨count, finalBound, afterGood, afterFits, path⟩ := actual.path_control limit bound good fits
  exact ⟨afterGood, afterFits.mono
    (path.final_le SourceCurrentAllocatedReaderControl.g_mono SourceCurrentAllocatedReaderControl.g_strict)⟩

/-- Initial issued counters and causal mass determine the first heap control. -/
def initialBound (nodes edges mass : Nat) : Nat := max (max nodes edges) mass

/-- Initial counters and causal mass bound any finite closed unfolding history. -/
def heapBound (nodes edges mass : Nat) : Nat :=
  HeightOrderControlled.majorant g mass (initialBound nodes edges mass)

/-- Initial semantic facts and causal mass derive the complete history endpoint bound. -/
theorem History.complete [DecidableEq (EdgeKey Symbol Guard)] {mass : Nat} {before after : State Symbol Guard} (actual : History before after)
    (semantic : SemanticHeap before) (covered : Covered [] before) (depth : InternedOpenDepthReadback.Heap before)
    (stored : InternedValueMassHeap.Stored mass before) :
    Good mass after ∧ Fits (heapBound before.nodes.next before.edges.next mass) after := by
  have good : Good mass before := ⟨semantic, covered, depth,
    InternedValueMassBinderDepth.stored_bounded before mass stored,
    (by intro item member; cases member), (by intro item member; cases member)⟩
  have fits : Fits (initialBound before.nodes.next before.edges.next mass) before :=
    ⟨stored.mono (by unfold initialBound; omega),
      (by change before.nodes.next ≤ initialBound before.nodes.next before.edges.next mass; unfold initialBound; omega),
      (by change before.edges.next ≤ initialBound before.nodes.next before.edges.next mass; unfold initialBound; omega),
      Nat.zero_le _⟩
  exact actual.bound good fits

end MicroCFTA.SourceCurrentAllocatedUnfoldHistory
