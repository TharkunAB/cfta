import MicroCFTA.SourceMergedComparisonCompletion
import MicroCFTA.SourceMergedSelectionLanguage

/-!
# Finite general repaired child selection

Every demanded recursive comparison now has a stable finite bound.
Ordered retention combines those bounds at actual intermediate caches.
The final identity filter retains the exact successful value and cache.
-/
namespace MicroCFTA.SourceMergedSelectionCompletion
open InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open MergedColdReaderClosedInputs (ClosedValues)
open SourceEqualityRequiredCache SourceEqualityRequiredSemanticCache
open SourceMergedComparisonEffects
open MergedSourceComparison (Result)
open MergedComparisonCompletion (EventuallyDone eventually_done eventually_bind)
open SourceMergedSelection
variable {Symbol Guard : Type} [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]

/-- Every ordered original recursive-cover scan has a stable finite result and complete cache. -/
theorem any_eventually (clear : Guard → Bool) (narrow : Value Symbol Guard) (wides : List (Value Symbol Guard))
    (before : State Symbol Guard) (semantic : SemanticReady before) (narrowInput : Available before narrow) (wideInputs : Values before wides)
    (narrowClosed : narrow.free = []) (wideClosed : ClosedValues wides) :
    EventuallyDone (fun fuel => anyAccepts clear fuel narrow wides before) := by
  induction wides generalizing before with
  | nil => exact eventually_done false before
  | cons wide wides ih =>
      simp only [anyAccepts, narrowClosed, ite_true]
      apply eventually_bind
      · obtain ⟨bound, answer, after, done, _⟩ := SourceMergedComparisonCompletion.check_complete clear before semantic [] wide narrow
          (wideInputs _ List.mem_cons_self) narrowInput (wideClosed _ List.mem_cons_self) narrowClosed
        exact ⟨bound, answer, after, done⟩
      · intro fuel answer after done
        have checked := check_effect clear fuel [] wide narrow before semantic (wideInputs _ List.mem_cons_self) narrowInput
          (wideClosed _ List.mem_cons_self) narrowClosed answer after done
        cases answer with
        | true => exact eventually_done true after
        | false =>
            exact ih after checked.2 (checked.1.available narrow narrowInput)
              (fun value member => checked.1.available value (wideInputs value (List.mem_cons_of_mem _ member)))
              (fun value member => wideClosed value (List.mem_cons_of_mem _ member))

/-- Actual ordered retention has one stable finite result without a whole-filter completion premise. -/
theorem retain_eventually (clear : Guard → Bool) (recursive inputs : List (Value Symbol Guard))
    (before : State Symbol Guard) (semantic : SemanticReady before) (recInputs : Values before recursive) (recClosed : ClosedValues recursive)
    (available : Values before inputs) (closed : ClosedValues inputs) : EventuallyDone (fun fuel => retain clear fuel recursive inputs before) := by
  induction inputs generalizing before with
  | nil => exact eventually_done [] before
  | cons child inputs ih =>
      by_cases recursiveChild : MergedPhysicalGroupColumns.closedMu child = true
      · simp only [retain, ite_eq_left recursiveChild]
        apply eventually_bind
        · exact ih before semantic recInputs (fun value member => available value (List.mem_cons_of_mem _ member))
            (fun value member => closed value (List.mem_cons_of_mem _ member))
        · intro fuel values after done
          exact eventually_done (child :: values) after
      · simp only [retain, ite_eq_right recursiveChild]
        apply eventually_bind
        · exact any_eventually clear child recursive before semantic (available _ List.mem_cons_self) recInputs (closed _ List.mem_cons_self) recClosed
        · intro fuel covered middle done
          have checked := any_effect clear fuel child recursive before semantic (available _ List.mem_cons_self) recInputs
            (closed _ List.mem_cons_self) recClosed covered middle done
          apply eventually_bind
          · exact ih middle checked.2 (fun value member => checked.1.available value (recInputs value member))
              (fun value member => checked.1.available value (available value (List.mem_cons_of_mem _ member)))
              (fun value member => closed value (List.mem_cons_of_mem _ member))
          · intro bound retained after actual
            exact eventually_done (if covered then retained else child :: retained) after

/-- Every actual general selection has one stable finite value and full returned cache. -/
theorem select_eventually (clear : Guard → Bool) (inputs : List (Value Symbol Guard))
    (before : State Symbol Guard) (semantic : SemanticReady before) (available : Values before inputs) (closed : ClosedValues inputs) :
    EventuallyDone (fun fuel => select clear fuel inputs before) := by
  apply eventually_bind
  · exact retain_eventually clear (inputs.filter MergedPhysicalGroupColumns.closedMu) inputs before semantic
      (fun value member => available value (List.mem_filter.mp member).1)
      (fun value member => closed value (List.mem_filter.mp member).1) available closed
  · intro fuel retained after done
    exact eventually_done (distinctNodes retained) after

end MicroCFTA.SourceMergedSelectionCompletion
