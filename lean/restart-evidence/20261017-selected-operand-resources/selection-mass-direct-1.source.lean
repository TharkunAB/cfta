import MicroCFTA.SourceMergedComparisonMass
import MicroCFTA.SourceMergedSelectionCompletion

/-!
# Numeric resources through actual recursive-cover selection

Each comparison derives its own read and constructor envelope. The initial
input length bounds the two ordered selection scans. The numeric envelope
still takes the supplied comparison fuel. No sufficient initial fuel or
fuel-independent selection resource bound is proved here.
-/
namespace MicroCFTA.SourceMergedSelectionMass
open InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open MergedColdReaderClosedInputs (ClosedValues)
open SourceEqualityRequiredCache SourceEqualityRequiredSemanticCache
open SourceMergedComparisonEffects (bind_done)
open SourceMergedComparisonMass (Resources iterate comparisonBound Monotone)
open SourceMergedSelection
local notation "Stored" => InternedValueMassHeap.Stored
variable {Symbol Guard : Type} [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]

/-- A selection performs at most one input-length cover scan per input. -/
def selectionBound (fuel count bound : Nat) : Nat :=
  iterate (fun current => iterate (comparisonBound fuel) count current) count bound

/-- Every selection envelope retains its initial causal bound. -/
theorem selectionBound_ge (fuel count bound : Nat) : bound ≤ selectionBound fuel count bound :=
  SourceMergedComparisonMass.iterate_ge (SourceMergedComparisonMass.iterate_ge
    (SourceMergedComparisonMass.comparisonBound_ge fuel) count) count bound

/-- Larger initial stores retain the same length and fuel envelope. -/
theorem selectionBound_mono (fuel count : Nat) : Monotone (selectionBound fuel count) :=
  SourceMergedComparisonMass.iterate_mono
    (SourceMergedComparisonMass.iterate_mono (SourceMergedComparisonMass.comparisonBound_mono fuel) count) count

/-- Larger input lengths retain both ordered scan bounds. -/
theorem selectionBound_count_mono (fuel : Nat) {first last : Nat} (enough : first ≤ last) (bound : Nat) :
    selectionBound fuel first bound ≤ selectionBound fuel last bound := by
  have mono := SourceMergedComparisonMass.comparisonBound_mono fuel
  have ge := SourceMergedComparisonMass.comparisonBound_ge fuel
  exact Nat.le_trans
    (SourceMergedComparisonMass.iterate_family_mono
      (SourceMergedComparisonMass.iterate_mono mono last)
      (fun current => SourceMergedComparisonMass.iterate_count_mono mono ge enough current) first bound)
    (SourceMergedComparisonMass.iterate_count_mono
      (SourceMergedComparisonMass.iterate_mono mono last)
      (SourceMergedComparisonMass.iterate_ge ge last) enough bound)

private theorem any_resources (clear : Guard → Bool) (fuel : Nat) (narrow : Value Symbol Guard)
    (wides : List (Value Symbol Guard)) (origin before : State Symbol Guard) (bound : Nat)
    (known : Resources bound origin before) (semantic : SemanticReady before)
    (narrowInput : Available before narrow) (wideInputs : Values before wides)
    (narrowClosed : narrow.free = []) (wideClosed : ClosedValues wides)
    (answer : Bool) (after : State Symbol Guard)
    (done : anyAccepts clear fuel narrow wides before = .done answer after) :
    Resources (iterate (comparisonBound fuel) wides.length bound) origin after := by
  induction wides generalizing before bound with
  | nil => cases done; exact known
  | cons wide wides ih =>
      simp only [anyAccepts, narrowClosed, ite_true] at done
      obtain ⟨accepted, middle, first, later⟩ := (bind_done _ _ answer after).mp done
      have produced := SourceMergedComparisonMass.check_resources clear fuel [] wide narrow origin before bound known semantic
        (wideInputs _ List.mem_cons_self) narrowInput (wideClosed _ List.mem_cons_self) narrowClosed accepted middle first
      have effects := SourceMergedComparisonEffects.check_effect clear fuel [] wide narrow before semantic
        (wideInputs _ List.mem_cons_self) narrowInput (wideClosed _ List.mem_cons_self) narrowClosed accepted middle first
      cases accepted with
      | true => cases later; exact produced.mono (SourceMergedComparisonMass.iterate_ge
          (SourceMergedComparisonMass.comparisonBound_ge fuel) _ _)
      | false =>
        exact ih middle _ produced effects.2 (effects.1.available narrow narrowInput)
          (fun value member => effects.1.available value (wideInputs value (List.mem_cons_of_mem _ member)))
          (fun value member => wideClosed value (List.mem_cons_of_mem _ member)) later

private theorem retain_resources (clear : Guard → Bool) (fuel : Nat)
    (recursive inputs : List (Value Symbol Guard)) (origin before : State Symbol Guard) (bound : Nat)
    (known : Resources bound origin before) (semantic : SemanticReady before)
    (recInputs : Values before recursive) (recClosed : ClosedValues recursive)
    (available : Values before inputs) (closed : ClosedValues inputs)
    (result : List (Value Symbol Guard)) (after : State Symbol Guard)
    (done : retain clear fuel recursive inputs before = .done result after) :
    Resources (iterate (fun current => iterate (comparisonBound fuel) recursive.length current) inputs.length bound) origin after := by
  induction inputs generalizing before bound result with
  | nil => cases done; exact known
  | cons child rest ih =>
      rw [retain] at done
      split at done
      · obtain ⟨retained, final, first, later⟩ := (bind_done _ _ result after).mp done
        have equal : final = after := (MergedSourceComparison.Result.done.inj later).2
        subst after
        exact (ih before bound known semantic recInputs recClosed
          (fun value member => available value (List.mem_cons_of_mem _ member))
          (fun value member => closed value (List.mem_cons_of_mem _ member)) retained final first).mono
          (SourceMergedComparisonMass.iterate_mono
            (SourceMergedComparisonMass.iterate_mono (SourceMergedComparisonMass.comparisonBound_mono fuel) recursive.length)
            _ (SourceMergedComparisonMass.iterate_ge (SourceMergedComparisonMass.comparisonBound_ge fuel) _ _))
      · obtain ⟨covered, middle, first, later⟩ := (bind_done _ _ result after).mp done
        have produced := any_resources clear fuel child recursive origin before bound known semantic
          (available _ List.mem_cons_self) recInputs (closed _ List.mem_cons_self) recClosed covered middle first
        have effects := any_effect clear fuel child recursive before semantic
          (available _ List.mem_cons_self) recInputs (closed _ List.mem_cons_self) recClosed covered middle first
        obtain ⟨retained, final, restDone, last⟩ := (bind_done _ _ result after).mp later
        have equal : final = after := (MergedSourceComparison.Result.done.inj last).2
        subst after
        exact ih middle _ produced effects.2
          (fun value member => effects.1.available value (recInputs value member)) recClosed
          (fun value member => effects.1.available value (available value (List.mem_cons_of_mem _ member)))
          (fun value member => closed value (List.mem_cons_of_mem _ member)) retained final restDone

/-- An actual successful selection derives mass and both supply bounds from initial facts. -/
theorem select_bound (clear : Guard → Bool) (fuel : Nat) (inputs : List (Value Symbol Guard))
    (before : State Symbol Guard) (bound : Nat) (semantic : SemanticReady before) (stored : Stored bound before)
    (available : Values before inputs) (closed : ClosedValues inputs)
    (result : List (Value Symbol Guard)) (after : State Symbol Guard)
    (done : select clear fuel inputs before = .done result after) :
    Resources (selectionBound fuel inputs.length bound) before after := by
  obtain ⟨retained, final, first, later⟩ := (bind_done _ _ result after).mp done
  have equal : final = after := (MergedSourceComparison.Result.done.inj later).2
  subst after
  have produced := retain_resources clear fuel (inputs.filter MergedPhysicalGroupColumns.closedMu) inputs before before bound
    (Resources.refl before bound stored) semantic
    (fun value member => available value (List.mem_filter.mp member).1)
    (fun value member => closed value (List.mem_filter.mp member).1) available closed retained final first
  exact produced.mono (SourceMergedComparisonMass.iterate_family_mono
    (SourceMergedComparisonMass.iterate_mono (SourceMergedComparisonMass.comparisonBound_mono fuel) inputs.length)
    (fun current => SourceMergedComparisonMass.iterate_count_mono
      (SourceMergedComparisonMass.comparisonBound_mono fuel) (SourceMergedComparisonMass.comparisonBound_ge fuel)
      (List.length_filter_le _ _) current) inputs.length bound)

/-- Existing finite completion constructs a return with its fuel-indexed resource envelope. -/
theorem select_complete (clear : Guard → Bool) (inputs : List (Value Symbol Guard))
    (before : State Symbol Guard) (bound : Nat) (semantic : SemanticReady before) (stored : Stored bound before)
    (available : Values before inputs) (closed : ClosedValues inputs) :
    ∃ fuel result after, select clear fuel inputs before = .done result after ∧
      Resources (selectionBound fuel inputs.length bound) before after := by
  obtain ⟨fuel, result, after, stable⟩ := SourceMergedSelectionCompletion.select_eventually clear inputs before semantic available closed
  have done := stable fuel (Nat.le_refl _)
  exact ⟨fuel, result, after, done, select_bound clear fuel inputs before bound semantic stored available closed result after done⟩

end MicroCFTA.SourceMergedSelectionMass
