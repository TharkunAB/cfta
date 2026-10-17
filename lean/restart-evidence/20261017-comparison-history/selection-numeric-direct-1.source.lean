import MicroCFTA.SourceMergedComparisonNumeric
import MicroCFTA.SourceMergedSelectionMass

/-!
# Actual selection at initial computable comparison fuel

Every demanded comparison records its actual unfolding history. One initial
heap ceiling supplies comparison fuel for the whole ordered scan. The final
endpoint constructs its own successful selection and numerical resources.
-/
namespace MicroCFTA.SourceMergedSelectionNumeric
open InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open MergedColdReaderClosedInputs (ClosedValues)
open SourceEqualityRequiredSemanticCache (SemanticReady)
open SourceMergedComparisonEffects (Effect bind_done)
open SourceMergedComparisonHistory (Recorded pure_recorded check_recorded)
open SourceCurrentAllocatedUnfoldHistory (History heapBound)
open SourceMergedComparisonNumeric (comparisonFuel readerFuel)
open SourceMergedSelection (anyAccepts retain select)
open MergedSourceComparison (Result)
open InternedMuDepthInventory (Bounded)
variable {Symbol Guard : Type}

private theorem comparison_allowance (nodes edges mass newFuel : Nat)
    (enough : comparisonFuel nodes edges mass ≤ newFuel) :
    (MergedComparisonCompletion.remainingPairs (heapBound nodes edges mass) []).length +
      readerFuel nodes edges mass ≤ newFuel := by
  have pairs := SourceCurrentAllocatedRowReadUniform.remainingPairs_length_le (heapBound nodes edges mass) []
  dsimp only [comparisonFuel] at enough
  omega

private theorem unchanged [DecidableEq (EdgeKey Symbol Guard)] (limit : Nat)
    (before : State Symbol Guard) (semantic : SemanticReady before) (bounded : Bounded before limit) :
    Recorded limit before before := pure_recorded limit before semantic bounded true true before rfl

variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]

/-- A cover scan records false answers before the next original recursive operand. -/
theorem any_recorded (limit : Nat) (clear : Guard → Bool) (fuel : Nat)
    (narrow : Value Symbol Guard) (wides : List (Value Symbol Guard)) (before : State Symbol Guard)
    (semantic : SemanticReady before) (bounded : Bounded before limit)
    (narrowInput : Available before narrow) (wideInputs : Values before wides)
    (narrowClosed : narrow.free = []) (wideClosed : ClosedValues wides)
    (answer : Bool) (after : State Symbol Guard)
    (done : anyAccepts clear fuel narrow wides before = .done answer after) : Recorded limit before after := by
  induction wides generalizing before with
  | nil => exact pure_recorded limit before semantic bounded false answer after done
  | cons wide wides ih =>
      simp only [anyAccepts, narrowClosed, ite_true] at done
      obtain ⟨accepted, middle, first, later⟩ := (bind_done _ _ answer after).mp done
      have checked := check_recorded limit clear fuel [] wide narrow before semantic bounded
        (wideInputs _ List.mem_cons_self) narrowInput (wideClosed _ List.mem_cons_self) narrowClosed accepted middle first
      cases accepted with
      | true => exact checked.trans (pure_recorded limit middle checked.effect.2 checked.bounded true answer after later)
      | false => exact checked.trans (ih middle checked.effect.2 checked.bounded
          (checked.effect.1.available narrow narrowInput)
          (fun value member => checked.effect.1.available value (wideInputs value (List.mem_cons_of_mem _ member)))
          (fun value member => wideClosed value (List.mem_cons_of_mem _ member)) later)

/-- Actual retention composes only the comparisons it demands at their full returned heaps. -/
theorem retain_recorded (limit : Nat) (clear : Guard → Bool) (fuel : Nat)
    (recursive inputs : List (Value Symbol Guard)) (before : State Symbol Guard)
    (semantic : SemanticReady before) (bounded : Bounded before limit)
    (recInputs : Values before recursive) (recClosed : ClosedValues recursive)
    (available : Values before inputs) (closed : ClosedValues inputs)
    (result : List (Value Symbol Guard)) (after : State Symbol Guard)
    (done : retain clear fuel recursive inputs before = .done result after) : Recorded limit before after := by
  induction inputs generalizing before result after with
  | nil =>
      have equal := (Result.done.inj done).2
      cases equal
      exact unchanged limit before semantic bounded
  | cons child inputs ih =>
      rw [retain] at done
      split at done
      · obtain ⟨rest, middle, tail, returned⟩ := (bind_done _ _ result after).mp done
        have equal := (Result.done.inj returned).2
        cases equal
        exact ih before semantic bounded recInputs
          (fun value member => available value (List.mem_cons_of_mem _ member))
          (fun value member => closed value (List.mem_cons_of_mem _ member)) rest middle tail
      · obtain ⟨covered, middle, first, later⟩ := (bind_done _ _ result after).mp done
        have checked := any_recorded limit clear fuel child recursive before semantic bounded
          (available _ List.mem_cons_self) recInputs (closed _ List.mem_cons_self) recClosed covered middle first
        obtain ⟨rest, final, tail, returned⟩ := (bind_done _ _ result after).mp later
        have equal := (Result.done.inj returned).2
        cases equal
        exact checked.trans (ih middle checked.effect.2 checked.bounded
          (fun value member => checked.effect.1.available value (recInputs value member))
          (fun value member => checked.effect.1.available value (available value (List.mem_cons_of_mem _ member)))
          (fun value member => closed value (List.mem_cons_of_mem _ member)) rest final tail)

/-- Removing duplicate identities adds no heap effect or unfolding event. -/
theorem select_recorded (limit : Nat) (clear : Guard → Bool) (fuel : Nat)
    (inputs : List (Value Symbol Guard)) (before : State Symbol Guard)
    (semantic : SemanticReady before) (bounded : Bounded before limit)
    (available : Values before inputs) (closed : ClosedValues inputs)
    (result : List (Value Symbol Guard)) (after : State Symbol Guard)
    (done : select clear fuel inputs before = .done result after) : Recorded limit before after := by
  obtain ⟨retained, final, first, returned⟩ := (bind_done _ _ result after).mp done
  have equal := (Result.done.inj returned).2
  cases equal
  exact retain_recorded limit clear fuel (inputs.filter MergedPhysicalGroupColumns.closedMu) inputs before
    semantic bounded (fun value member => available value (List.mem_filter.mp member).1)
    (fun value member => closed value (List.mem_filter.mp member).1) available closed retained final first

/-- Every reached cover scan replays at the same initial comparison allowance. -/
theorem any_replay (origin : State Symbol Guard) (mass : Nat)
    (initial : SemanticReady origin) (stored : InternedValueMassHeap.Stored mass origin)
    (oldFuel newFuel : Nat) (clear : Guard → Bool)
    (enough : comparisonFuel origin.nodes.next origin.edges.next mass ≤ newFuel)
    (narrow : Value Symbol Guard) (wides : List (Value Symbol Guard)) (before : State Symbol Guard)
    (semantic : SemanticReady before) (narrowInput : Available before narrow) (wideInputs : Values before wides)
    (narrowClosed : narrow.free = []) (wideClosed : ClosedValues wides) (reached : History origin before)
    (answer : Bool) (after : State Symbol Guard)
    (done : anyAccepts clear oldFuel narrow wides before = .done answer after) :
    anyAccepts clear newFuel narrow wides before = .done answer after := by
  induction wides generalizing before with
  | nil => exact done
  | cons wide wides ih =>
      simp only [anyAccepts, narrowClosed, ite_true] at done ⊢
      obtain ⟨accepted, middle, first, later⟩ := (bind_done _ _ answer after).mp done
      have good := (reached.complete initial.ready.semantic initial.ready.covered initial.ready.depth stored).1
      have checked := check_recorded mass clear oldFuel [] wide narrow before semantic good.bounded
        (wideInputs _ List.mem_cons_self) narrowInput (wideClosed _ List.mem_cons_self) narrowClosed accepted middle first
      have replay := SourceMergedComparisonNumeric.check_replay origin mass initial stored oldFuel clear [] wide narrow
        before semantic (wideInputs _ List.mem_cons_self) narrowInput (wideClosed _ List.mem_cons_self) narrowClosed reached
        accepted middle first newFuel (comparison_allowance _ _ _ _ enough)
      cases accepted with
      | true => simpa only [replay, Result.bind, ite_true] using later
      | false =>
          have tail := ih middle checked.effect.2 (checked.effect.1.available narrow narrowInput)
            (fun value member => checked.effect.1.available value (wideInputs value (List.mem_cons_of_mem _ member)))
            (fun value member => wideClosed value (List.mem_cons_of_mem _ member)) (reached.trans checked.history) later
          simpa only [replay, Result.bind, Bool.false_eq_true, ite_false] using tail

/-- Retention replays every demanded scan without changing the original captured family. -/
theorem retain_replay (origin : State Symbol Guard) (mass : Nat)
    (initial : SemanticReady origin) (stored : InternedValueMassHeap.Stored mass origin)
    (oldFuel newFuel : Nat) (clear : Guard → Bool)
    (enough : comparisonFuel origin.nodes.next origin.edges.next mass ≤ newFuel)
    (recursive inputs : List (Value Symbol Guard)) (before : State Symbol Guard) (semantic : SemanticReady before)
    (recInputs : Values before recursive) (recClosed : ClosedValues recursive)
    (available : Values before inputs) (closed : ClosedValues inputs) (reached : History origin before)
    (result : List (Value Symbol Guard)) (after : State Symbol Guard)
    (done : retain clear oldFuel recursive inputs before = .done result after) :
    retain clear newFuel recursive inputs before = .done result after := by
  induction inputs generalizing before result after with
  | nil => exact done
  | cons child inputs ih =>
      rw [retain] at done ⊢
      split at done
      · rename_i recursiveChild
        rw [ite_eq_left recursiveChild]
        obtain ⟨rest, middle, tail, returned⟩ := (bind_done _ _ result after).mp done
        have replay := ih before semantic recInputs
          (fun value member => available value (List.mem_cons_of_mem _ member))
          (fun value member => closed value (List.mem_cons_of_mem _ member)) reached rest middle tail
        simpa only [replay, Result.bind] using returned
      · rename_i nonrecursive
        rw [ite_eq_right nonrecursive]
        obtain ⟨covered, middle, first, later⟩ := (bind_done _ _ result after).mp done
        have good := (reached.complete initial.ready.semantic initial.ready.covered initial.ready.depth stored).1
        have checked := any_recorded mass clear oldFuel child recursive before semantic good.bounded
          (available _ List.mem_cons_self) recInputs (closed _ List.mem_cons_self) recClosed covered middle first
        have replay := any_replay origin mass initial stored oldFuel newFuel clear enough child recursive before semantic
          (available _ List.mem_cons_self) recInputs (closed _ List.mem_cons_self) recClosed reached covered middle first
        obtain ⟨rest, final, tail, returned⟩ := (bind_done _ _ result after).mp later
        have restReplay := ih middle checked.effect.2
          (fun value member => checked.effect.1.available value (recInputs value member))
          (fun value member => checked.effect.1.available value (available value (List.mem_cons_of_mem _ member)))
          (fun value member => closed value (List.mem_cons_of_mem _ member)) (reached.trans checked.history) rest final tail
        simpa only [replay, restReplay, Result.bind] using returned

/-- An actual selection replays its exact output and full heap at initial uniform fuel. -/
theorem select_replay (origin : State Symbol Guard) (mass : Nat)
    (initial : SemanticReady origin) (stored : InternedValueMassHeap.Stored mass origin)
    (oldFuel newFuel : Nat) (clear : Guard → Bool)
    (enough : comparisonFuel origin.nodes.next origin.edges.next mass ≤ newFuel)
    (inputs : List (Value Symbol Guard)) (before : State Symbol Guard) (semantic : SemanticReady before)
    (available : Values before inputs) (closed : ClosedValues inputs) (reached : History origin before)
    (result : List (Value Symbol Guard)) (after : State Symbol Guard)
    (done : select clear oldFuel inputs before = .done result after) :
    select clear newFuel inputs before = .done result after := by
  obtain ⟨retained, final, first, returned⟩ := (bind_done _ _ result after).mp done
  have replay := retain_replay origin mass initial stored oldFuel newFuel clear enough
    (inputs.filter MergedPhysicalGroupColumns.closedMu) inputs before semantic
    (fun value member => available value (List.mem_filter.mp member).1)
    (fun value member => closed value (List.mem_filter.mp member).1) available closed reached retained final first
  simpa only [select, replay, Result.bind] using returned

/-- Initial counters and causal mass construct the complete selection and all larger-fuel replays. -/
theorem select_complete (clear : Guard → Bool) (inputs : List (Value Symbol Guard))
    (before : State Symbol Guard) (mass : Nat) (semantic : SemanticReady before)
    (stored : InternedValueMassHeap.Stored mass before) (available : Values before inputs) (closed : ClosedValues inputs) :
    ∃ result after,
      select clear (comparisonFuel before.nodes.next before.edges.next mass) inputs before = .done result after ∧
      Effect before after ∧ SourceCurrentAllocatedUnfoldHistory.Fits (heapBound before.nodes.next before.edges.next mass) after ∧
      SourceMergedComparisonMass.Resources
        (SourceMergedSelectionMass.selectionBound (comparisonFuel before.nodes.next before.edges.next mass) inputs.length mass) before after ∧
      ∀ extra, select clear (comparisonFuel before.nodes.next before.edges.next mass + extra) inputs before = .done result after := by
  obtain ⟨oldFuel, result, after, stable⟩ := SourceMergedSelectionCompletion.select_eventually clear inputs before semantic available closed
  have oldDone := stable oldFuel (Nat.le_refl _)
  have done := select_replay before mass semantic stored oldFuel
    (comparisonFuel before.nodes.next before.edges.next mass) clear (Nat.le_refl _)
    inputs before semantic available closed (.refl before) result after oldDone
  have recorded := select_recorded mass clear _ inputs before semantic
    (InternedValueMassBinderDepth.stored_bounded before mass stored) available closed result after done
  have fits := (recorded.history.complete semantic.ready.semantic semantic.ready.covered semantic.ready.depth stored).2
  exact ⟨result, after, done, recorded.effect, fits,
    SourceMergedSelectionMass.select_bound clear _ inputs before mass semantic stored available closed result after done,
    fun extra => select_replay before mass semantic stored oldFuel _ clear (Nat.le_add_right _ _)
      inputs before semantic available closed (.refl before) result after oldDone⟩

end MicroCFTA.SourceMergedSelectionNumeric
