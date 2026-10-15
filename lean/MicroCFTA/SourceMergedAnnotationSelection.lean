import MicroCFTA.SourceMergedSelection
import MicroCFTA.SourceMergedAnnotationComparison

/-!
# Physical annotations through actual merge child retention

Ordered recursive-cover queries preserve the annotation heap. Retention and
canonical identity filtering keep their exact returned cache. Original closed
input scopes advance only through the actual comparison histories.
-/
namespace MicroCFTA.SourceMergedAnnotationSelection
open InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open MergedColdReaderClosedInputs (ClosedValues)
open MergedPhysicalGroupColumns (closedMu)
open SourceEqualityRequiredCache SourceEqualityRequiredSemanticCache
open SourceMergedComparisonEffects (bind_done)
open SourceMergedAnnotationComparison
open SourceMergedSelection
open MergedSourceComparison (Result)

/-- Every completed recursive-cover scan retains annotations and actual cache histories. -/
theorem any_effect (annotation : Guard → Prop) [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] (clear : Guard → Bool) (fuel : Nat)
    (narrow : Value Symbol Guard) (wides : List (Value Symbol Guard)) (before : State Symbol Guard) (semantic : SemanticReady before)
    (narrowInput : Available before narrow) (wideInputs : Values before wides) (narrowClosed : narrow.free = []) (wideClosed : ClosedValues wides)
    (answer : Bool) (after : State Symbol Guard) (done : anyAccepts clear fuel narrow wides before = .done answer after) : Effect annotation before after := by
  induction wides generalizing before with
  | nil => exact pure_effect annotation before semantic false answer after done
  | cons wide wides ih =>
      simp only [anyAccepts, narrowClosed, ite_true] at done
      obtain ⟨accepted, middle, first, later⟩ := (bind_done _ _ answer after).mp done
      have effects := check_effect annotation clear fuel [] wide narrow before semantic (wideInputs _ List.mem_cons_self) narrowInput
        (wideClosed _ List.mem_cons_self) narrowClosed accepted middle first
      cases accepted with
      | true => exact effects.trans (pure_effect annotation middle effects.semantic true answer after later)
      | false => exact effects.trans (ih middle effects.semantic (effects.keeps.available narrow narrowInput)
          (fun value member => effects.keeps.available value (wideInputs value (List.mem_cons_of_mem _ member)))
          (fun value member => wideClosed value (List.mem_cons_of_mem _ member)) later)

/-- Successful actual filtering retains annotation heaps, semantic heaps, and both histories. -/
theorem retain_effect (annotation : Guard → Prop) [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] (clear : Guard → Bool) (fuel : Nat)
    (recursive inputs : List (Value Symbol Guard)) (before : State Symbol Guard) (semantic : SemanticReady before)
    (recInputs : Values before recursive) (recClosed : ClosedValues recursive) (available : Values before inputs) (closed : ClosedValues inputs)
    (retained : List (Value Symbol Guard)) (after : State Symbol Guard)
    (done : retain clear fuel recursive inputs before = .done retained after) : Effect annotation before after := by
  induction inputs generalizing before retained after with
  | nil =>
      have parts := Result.done.inj done
      cases parts.2
      exact ⟨pure_keeps _ semantic.ready, semantic, fun heap => heap⟩
  | cons child inputs ih =>
      rw [retain] at done
      split at done
      · obtain ⟨rest, middle, tail, returned⟩ := (bind_done _ _ retained after).mp done
        have parts := Result.done.inj returned
        cases parts.2
        exact ih before semantic recInputs (fun value member => available value (List.mem_cons_of_mem _ member))
          (fun value member => closed value (List.mem_cons_of_mem _ member)) rest after tail
      · obtain ⟨covered, middle, first, later⟩ := (bind_done _ _ retained after).mp done
        have effects := any_effect annotation clear fuel child recursive before semantic (available _ List.mem_cons_self) recInputs
          (closed _ List.mem_cons_self) recClosed covered middle first
        obtain ⟨rest, final, tail, returned⟩ := (bind_done _ _ retained after).mp later
        have parts := Result.done.inj returned
        cases parts.2
        exact effects.trans (ih middle effects.semantic (fun value member => effects.keeps.available value (recInputs value member))
          (fun value member => effects.keeps.available value (available value (List.mem_cons_of_mem _ member)))
          (fun value member => closed value (List.mem_cons_of_mem _ member)) rest after tail)

/-- The actual retention and identity filter preserve annotations at the returned cache. -/
theorem select_effect (annotation : Guard → Prop) [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (clear : Guard → Bool) (fuel : Nat) (inputs : List (Value Symbol Guard)) (before : State Symbol Guard)
    (semantic : SemanticReady before) (available : Values before inputs) (closed : ClosedValues inputs)
    (retained : List (Value Symbol Guard)) (after : State Symbol Guard)
    (done : select clear fuel inputs before = .done retained after) : Effect annotation before after := by
  obtain ⟨values, middle, filtered, returned⟩ := (bind_done _ _ retained after).mp done
  have checked := retain_effect annotation clear fuel (inputs.filter closedMu) inputs before semantic
    (fun value member => available value (List.mem_filter.mp member).1)
    (fun value member => closed value (List.mem_filter.mp member).1) available closed values middle filtered
  have parts := Result.done.inj returned
  cases parts.2
  exact checked

end MicroCFTA.SourceMergedAnnotationSelection
