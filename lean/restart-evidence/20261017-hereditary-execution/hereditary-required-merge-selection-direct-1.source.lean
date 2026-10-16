import MicroCFTA.SourceCurrentHereditaryComparison
import MicroCFTA.SourceCurrentMergedHeapEffects
import MicroCFTA.SourceMergedSelectionLanguage

/-!
# Causal Mu certificates through actual merge selection

The compared values carry local annotations and closed source inputs.
Actual comparisons retain the conditional Mu store. The ordered retention
filter copies original values. Other resident guards remain unrestricted.
-/
namespace MicroCFTA.SourceCurrentHereditarySelection
open InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open MergedColdReaderClosedInputs (ClosedValues)
open MergedPhysicalGroupColumns (closedMu)
open SourceEqualityRequiredCache SourceEqualityRequiredSemanticCache
open SourceEqualityAnnotationLanguage SourceCurrentHereditaryConstruction
open SourceMergedComparisonEffects (bind_done)
open SourceMergedSelection
open MergedSourceComparison (Result)
local notation "CostHeap" => InternedFreshOrdinaryCostHeap.Heap
variable {Symbol Guard : Type}

/-- The actual ordered cover scan retains the causal store at its exact stopping heap. -/
theorem anyAccepts [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (valid : Guard → Prop) (clear : Guard → Bool) (fuel : Nat)
    (narrow : Value Symbol Guard) (wides : List (Value Symbol Guard)) (before : State Symbol Guard)
    (semantic : SemanticReady before) (costs : CostHeap before)
    (narrowInput : Available before narrow) (wideInputs : Values before wides)
    (narrowClosed : narrow.free = []) (wideClosed : ClosedValues wides)
    (narrowAnnotated : Annotated valid narrow) (wideAnnotated : ∀ wide ∈ wides, Annotated valid wide)
    (stored : MuStored valid before) (answer : Bool) (after : State Symbol Guard)
    (done : SourceMergedSelection.anyAccepts clear fuel narrow wides before = .done answer after) :
    MuStored valid after := by
  induction wides generalizing before with
  | nil =>
      have same := Result.done.inj done
      cases same.2
      exact stored
  | cons wide wides ih =>
      simp only [SourceMergedSelection.anyAccepts, narrowClosed, ite_true] at done
      obtain ⟨accepted, middle, first, later⟩ := (bind_done _ _ answer after).mp done
      have nextStored := SourceCurrentHereditaryComparison.check valid clear fuel [] wide narrow before semantic costs
        (wideInputs _ List.mem_cons_self) narrowInput (wideClosed _ List.mem_cons_self) narrowClosed
        (wideAnnotated _ List.mem_cons_self) narrowAnnotated stored accepted middle first
      have effects := SourceCurrentMergedHeapEffects.check_effect (fun _ => True) clear fuel [] wide narrow before semantic costs
        (wideInputs _ List.mem_cons_self) narrowInput accepted middle first
      cases accepted with
      | true =>
          have same := Result.done.inj later
          cases same.2
          exact nextStored.stored
      | false =>
          exact ih middle effects.semantic effects.costs (effects.keeps.available narrow narrowInput)
            (fun value member => effects.keeps.available value (wideInputs value (List.mem_cons_of_mem _ member)))
            (fun value member => wideClosed value (List.mem_cons_of_mem _ member))
            (fun value member => wideAnnotated value (List.mem_cons_of_mem _ member)) nextStored.stored later

/-- Actual retention threads all completed comparison effects before the next original child. -/
theorem retain [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (valid : Guard → Prop) (clear : Guard → Bool) (fuel : Nat)
    (recursive inputs : List (Value Symbol Guard)) (before : State Symbol Guard)
    (semantic : SemanticReady before) (costs : CostHeap before)
    (recInputs : Values before recursive) (available : Values before inputs)
    (recClosed : ClosedValues recursive) (closed : ClosedValues inputs)
    (recAnnotated : ∀ value ∈ recursive, Annotated valid value)
    (annotated : ∀ value ∈ inputs, Annotated valid value) (stored : MuStored valid before)
    (retained : List (Value Symbol Guard)) (after : State Symbol Guard)
    (done : SourceMergedSelection.retain clear fuel recursive inputs before = .done retained after) :
    MuStored valid after := by
  induction inputs generalizing before retained after with
  | nil =>
      have same := Result.done.inj done
      cases same.2
      exact stored
  | cons child inputs ih =>
      rw [SourceMergedSelection.retain] at done
      split at done
      · obtain ⟨rest, middle, tail, returned⟩ := (bind_done _ _ retained after).mp done
        have same := Result.done.inj returned
        cases same.2
        exact ih before semantic costs recInputs (fun value member => available value (List.mem_cons_of_mem _ member))
          (fun value member => closed value (List.mem_cons_of_mem _ member))
          (fun value member => annotated value (List.mem_cons_of_mem _ member)) stored rest after tail
      · obtain ⟨covered, middle, first, later⟩ := (bind_done _ _ retained after).mp done
        have nextStored := anyAccepts valid clear fuel child recursive before semantic costs
          (available _ List.mem_cons_self) recInputs (closed _ List.mem_cons_self) recClosed
          (annotated _ List.mem_cons_self) recAnnotated stored covered middle first
        have effects := SourceCurrentMergedHeapEffects.anyAccepts_effect (fun _ => True) clear fuel child recursive before semantic costs
          (available _ List.mem_cons_self) recInputs covered middle first
        obtain ⟨rest, final, tail, returned⟩ := (bind_done _ _ retained after).mp later
        have same := Result.done.inj returned
        cases same.2
        exact ih middle effects.semantic effects.costs
          (fun value member => effects.keeps.available value (recInputs value member))
          (fun value member => effects.keeps.available value (available value (List.mem_cons_of_mem _ member)))
          (fun value member => closed value (List.mem_cons_of_mem _ member))
          (fun value member => annotated value (List.mem_cons_of_mem _ member)) nextStored rest after tail

/-- Actual selection retains the causal store and annotations of its original selected operands. -/
theorem select [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (valid : Guard → Prop) (clear : Guard → Bool) (fuel : Nat)
    (inputs : List (Value Symbol Guard)) (before : State Symbol Guard)
    (semantic : SemanticReady before) (costs : CostHeap before) (available : Values before inputs)
    (closed : ClosedValues inputs) (annotated : ∀ value ∈ inputs, Annotated valid value)
    (stored : MuStored valid before) (selected : List (Value Symbol Guard)) (after : State Symbol Guard)
    (done : SourceMergedSelection.select clear fuel inputs before = .done selected after) :
    MuStored valid after ∧ ∀ value ∈ selected, Annotated valid value := by
  obtain ⟨values, middle, filtered, returned⟩ := (bind_done _ _ selected after).mp done
  have nextStored := retain valid clear fuel (inputs.filter closedMu) inputs before semantic costs
    (fun value member => available value (List.mem_filter.mp member).1) available
    (fun value member => closed value (List.mem_filter.mp member).1) closed
    (fun value member => annotated value (List.mem_filter.mp member).1) annotated stored values middle filtered
  have same := Result.done.inj returned
  cases same.1
  cases same.2
  exact ⟨nextStored, fun value member => annotated value
    ((SourceMergedSelection.retain_members clear fuel (inputs.filter closedMu) inputs before values after filtered).1
      value (distinctNodes_member _ value member))⟩

end MicroCFTA.SourceCurrentHereditarySelection
