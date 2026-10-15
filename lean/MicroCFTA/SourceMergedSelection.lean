import MicroCFTA.SourceMergedComparisonSoundness
import MicroCFTA.MergedPhysicalGroupColumns

/-!
# Actual child retention with general repaired comparisons

The source tries original closed Mu operands in order, retains closed Mu
children, and removes repeated identities after filtering. Every comparison
uses its actual repaired reads and returned constructor cache.
-/
namespace MicroCFTA.SourceMergedSelection
open InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open MergedColdReaderClosedInputs (ClosedValues)
open MergedPhysicalGroupColumns (closedMu)
open SourceEqualityRequiredCache SourceEqualityRequiredSemanticCache
open SourceMergedComparisonEffects
open MergedSourceComparison (Result)

/-- Try original recursive covers in source order with general repaired comparisons. -/
def anyAccepts [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] (clear : Guard → Bool) (fuel : Nat)
    (narrow : Value Symbol Guard) : List (Value Symbol Guard) → State Symbol Guard → Result Symbol Guard Bool
  | [], state => .done false state
  | wide :: rest, state => if narrow.free = [] then
      (MergedFreshOrdinaryComparison.check clear fuel [] wide narrow state).bind fun accepted after =>
        if accepted then .done true after else anyAccepts clear fuel narrow rest after
    else .done false state

/-- Preserve recursive children and filter other children through the original recursive operands. -/
def retain [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] (clear : Guard → Bool) (fuel : Nat)
    (recursive : List (Value Symbol Guard)) : List (Value Symbol Guard) → State Symbol Guard → Result Symbol Guard (List (Value Symbol Guard))
  | [], state => .done [] state
  | child :: rest, state => if closedMu child then
      (retain clear fuel recursive rest state).bind fun retained after => .done (child :: retained) after
    else (anyAccepts clear fuel child recursive state).bind fun covered after =>
      (retain clear fuel recursive rest after).bind fun retained final => .done (if covered then retained else child :: retained) final

/-- Remove repeated canonical identities after the actual ordered retention filter. -/
def select [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] (clear : Guard → Bool) (fuel : Nat)
    (inputs : List (Value Symbol Guard)) (state : State Symbol Guard) : Result Symbol Guard (List (Value Symbol Guard)) :=
  (retain clear fuel (inputs.filter closedMu) inputs state).bind fun retained after => .done (distinctNodes retained) after

/-- Every completed recursive-cover scan derives actual semantic heap and history preservation. -/
theorem any_effect [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] (clear : Guard → Bool) (fuel : Nat)
    (narrow : Value Symbol Guard) (wides : List (Value Symbol Guard)) (before : State Symbol Guard) (semantic : SemanticReady before)
    (narrowInput : Available before narrow) (wideInputs : Values before wides) (narrowClosed : narrow.free = []) (wideClosed : ClosedValues wides)
    (answer : Bool) (after : State Symbol Guard) (done : anyAccepts clear fuel narrow wides before = .done answer after) : Effect before after := by
  induction wides generalizing before with
  | nil => exact pure_effect before semantic false answer after done
  | cons wide wides ih =>
      simp only [anyAccepts, narrowClosed, ite_true] at done
      obtain ⟨accepted, middle, first, later⟩ := (bind_done _ _ answer after).mp done
      have effects := check_effect clear fuel [] wide narrow before semantic (wideInputs _ List.mem_cons_self) narrowInput
        (wideClosed _ List.mem_cons_self) narrowClosed accepted middle first
      cases accepted with
      | true => exact effects.trans (pure_effect middle effects.2 true answer after later)
      | false => exact effects.trans (ih middle effects.2 (effects.1.available narrow narrowInput)
          (fun value member => effects.1.available value (wideInputs value (List.mem_cons_of_mem _ member)))
          (fun value member => wideClosed value (List.mem_cons_of_mem _ member)) later)

/-- A successful retention filter returns only original children and retains every original closed Mu child. -/
theorem retain_members [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] (clear : Guard → Bool) (fuel : Nat)
    (recursive inputs : List (Value Symbol Guard)) (before : State Symbol Guard) (retained : List (Value Symbol Guard)) (after : State Symbol Guard)
    (done : retain clear fuel recursive inputs before = .done retained after) :
    (∀ value ∈ retained, value ∈ inputs) ∧ (∀ value ∈ inputs, closedMu value = true → value ∈ retained) := by
  induction inputs generalizing before retained after with
  | nil =>
      have parts := Result.done.inj done
      cases parts.1
      exact ⟨by simp, by simp⟩
  | cons child inputs ih =>
      rw [retain] at done
      split at done
      · rename_i recursiveChild
        obtain ⟨rest, middle, tail, returned⟩ := (bind_done _ _ retained after).mp done
        have parts := Result.done.inj returned
        cases parts.1; cases parts.2
        have facts := ih before rest after tail
        constructor
        · intro value member
          rcases List.mem_cons.mp member with rfl | member
          · exact List.mem_cons_self
          · exact List.mem_cons_of_mem _ (facts.1 value member)
        · intro value member marked
          rcases List.mem_cons.mp member with rfl | member
          · exact List.mem_cons_self
          · exact List.mem_cons_of_mem _ (facts.2 value member marked)
      · rename_i nonrecursive
        obtain ⟨covered, middle, first, later⟩ := (bind_done _ _ retained after).mp done
        obtain ⟨rest, final, tail, returned⟩ := (bind_done _ _ retained after).mp later
        have facts := ih middle rest final tail
        cases covered with
        | true =>
            have parts := Result.done.inj returned
            cases parts.1; cases parts.2
            constructor
            · exact fun value member => List.mem_cons_of_mem _ (facts.1 value member)
            · intro value member marked
              rcases List.mem_cons.mp member with rfl | member
              · exact False.elim (nonrecursive marked)
              · exact facts.2 value member marked
        | false =>
            have parts := Result.done.inj returned
            cases parts.1; cases parts.2
            constructor
            · intro value member
              rcases List.mem_cons.mp member with rfl | member
              · exact List.mem_cons_self
              · exact List.mem_cons_of_mem _ (facts.1 value member)
            · intro value member marked
              rcases List.mem_cons.mp member with rfl | member
              · exact List.mem_cons_self
              · exact List.mem_cons_of_mem _ (facts.2 value member marked)

/-- Successful actual filtering retains general semantic heaps and both histories. -/
theorem retain_effect [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] (clear : Guard → Bool) (fuel : Nat)
    (recursive inputs : List (Value Symbol Guard)) (before : State Symbol Guard) (semantic : SemanticReady before)
    (recInputs : Values before recursive) (recClosed : ClosedValues recursive) (available : Values before inputs) (closed : ClosedValues inputs)
    (retained : List (Value Symbol Guard)) (after : State Symbol Guard)
    (done : retain clear fuel recursive inputs before = .done retained after) : Effect before after := by
  induction inputs generalizing before retained after with
  | nil =>
      have parts := Result.done.inj done
      cases parts.2
      exact ⟨pure_keeps _ semantic.ready, semantic⟩
  | cons child inputs ih =>
      rw [retain] at done
      split at done
      · obtain ⟨rest, middle, tail, returned⟩ := (bind_done _ _ retained after).mp done
        have parts := Result.done.inj returned
        cases parts.2
        exact ih before semantic recInputs (fun value member => available value (List.mem_cons_of_mem _ member))
          (fun value member => closed value (List.mem_cons_of_mem _ member)) rest after tail
      · obtain ⟨covered, middle, first, later⟩ := (bind_done _ _ retained after).mp done
        have effects := any_effect clear fuel child recursive before semantic (available _ List.mem_cons_self) recInputs
          (closed _ List.mem_cons_self) recClosed covered middle first
        obtain ⟨rest, final, tail, returned⟩ := (bind_done _ _ retained after).mp later
        have parts := Result.done.inj returned
        cases parts.2
        exact effects.trans (ih middle effects.2 (fun value member => effects.1.available value (recInputs value member))
          (fun value member => effects.1.available value (available value (List.mem_cons_of_mem _ member)))
          (fun value member => closed value (List.mem_cons_of_mem _ member)) rest after tail)

end MicroCFTA.SourceMergedSelection
