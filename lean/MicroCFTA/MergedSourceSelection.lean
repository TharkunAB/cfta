import MicroCFTA.MergedComparisonCompletion
import MicroCFTA.MergedPhysicalGroupColumns

/-!
# Ordered child retention with actual comparison effects

Each nonrecursive child tries the original closed Mu operands in order.
A successful comparison removes that child. Failed comparisons retain
their cache effects. Identity removal follows the completed filter.
-/
namespace MicroCFTA.MergedSourceSelection
open InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance InternedNestedFacts InternedNestedProvenance
open MergedPhysicalWarmup MergedSourceComparison MergedComparisonFacts MergedComparisonCompletion
open MergedColdReaderClosedInputs MergedPhysicalGroupColumns
open InternedFreshProbeKeys

/-- Try recursive covers in order and retain each comparison's exact cache. -/
def anyAccepts [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Symbol]
    (clear : Guard → Bool) (fuel : Nat) (narrow : Value Symbol Guard) :
    List (Value Symbol Guard) → State Symbol Guard → Result Symbol Guard Bool
  | [], state => .done false state
  | wide :: rest, state =>
      if narrow.free = [] then
        (check clear fuel [] wide narrow state).bind fun accepted after =>
          if accepted then .done true after else anyAccepts clear fuel narrow rest after
      else .done false state

/-- Retain closed Mu operands and children for which all original Mu comparisons fail. -/
def retain [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Symbol]
    (clear : Guard → Bool) (fuel : Nat) (recursive : List (Value Symbol Guard)) :
    List (Value Symbol Guard) → State Symbol Guard → Result Symbol Guard (List (Value Symbol Guard))
  | [], state => .done [] state
  | child :: rest, state =>
      if closedMu child then
        (retain clear fuel recursive rest state).bind fun retained after => .done (child :: retained) after
      else
        (anyAccepts clear fuel child recursive state).bind fun covered after =>
          (retain clear fuel recursive rest after).bind fun retained final =>
            .done (if covered then retained else child :: retained) final

/-- Complete the source filter before removing repeated canonical identities. -/
def select [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Symbol]
    (clear : Guard → Bool) (fuel : Nat) (inputs : List (Value Symbol Guard))
    (state : State Symbol Guard) : Result Symbol Guard (List (Value Symbol Guard)) :=
  (retain clear fuel (inputs.filter closedMu) inputs state).bind fun retained after =>
    .done (distinctNodes retained) after

/-- Every demanded recursive comparison preserves the original source invariants. -/
theorem any_verified [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Symbol]
    (clear : Guard → Bool) (fuel : Nat) (narrow : Value Symbol Guard) (wides : List (Value Symbol Guard))
    (state : State Symbol Guard) (facts : Facts state) (prepared : Prepared state)
    (narrowInput : Available state narrow) (wideInputs : Values state wides) (wideClosed : ClosedValues wides) :
    Verified state (anyAccepts clear fuel narrow wides state) := by
  induction wides generalizing state with
  | nil => exact done_verified state facts false
  | cons wide rest ih =>
      rw [anyAccepts]
      split
      · rename_i closed
        have checked := check_verified clear fuel [] wide narrow state facts prepared
          (wideInputs wide List.mem_cons_self) narrowInput (wideClosed wide List.mem_cons_self) closed
        apply bind_verified state _ _ checked
        intro accepted after done
        have effect := checked.effect done
        cases accepted with
        | true => exact done_verified after effect.facts true
        | false =>
            exact ih after effect.facts (prepared.preserve effect.unchanged)
              (narrowInput.grows state after effect.growth effect.history)
              (fun value member => (wideInputs value (List.mem_cons_of_mem _ member)).grows state after effect.growth effect.history)
              (fun value member => wideClosed value (List.mem_cons_of_mem _ member))
      · exact done_verified state facts false

/-- Ordered filtering preserves effects from each discarded or retained child. -/
theorem retain_verified [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Symbol]
    (clear : Guard → Bool) (fuel : Nat) (recursive inputs : List (Value Symbol Guard))
    (state : State Symbol Guard) (facts : Facts state) (prepared : Prepared state)
    (recInputs : Values state recursive) (recClosed : ClosedValues recursive) (available : Values state inputs) :
    Verified state (retain clear fuel recursive inputs state) := by
  induction inputs generalizing state with
  | nil => exact done_verified state facts []
  | cons child rest ih =>
      rw [retain]
      split
      · have tail := ih state facts prepared recInputs (fun value member => available value (List.mem_cons_of_mem _ member))
        apply bind_verified state _ _ tail
        intro values after done
        exact done_verified after (tail.effect done).facts (child :: values)
      · have checked := any_verified clear fuel child recursive state facts prepared (available child List.mem_cons_self) recInputs recClosed
        apply bind_verified state _ _ checked
        intro covered after done
        have effect := checked.effect done
        have tail := ih after effect.facts (prepared.preserve effect.unchanged)
          (fun value member => (recInputs value member).grows state after effect.growth effect.history)
          (fun value member => (available value (List.mem_cons_of_mem _ member)).grows state after effect.growth effect.history)
        apply bind_verified after _ _ tail
        intro values final tailDone
        exact done_verified final (tail.effect tailDone).facts _

/-- A closed Mu selected from the source inputs supplies the comparator's closed wide operand. -/
theorem recursive_closed (inputs : List (Value Symbol Guard)) : ClosedValues (inputs.filter closedMu) := by
  intro value member
  have marked := (List.mem_filter.mp member).2
  cases value with
  | empty | reference | node | union => simp [closedMu] at marked
  | mu entry body depth ordinary => exact List.isEmpty_iff.mp marked

/-- On actual source inputs, recursive-list membership is exactly the closed Mu predicate. -/
theorem recursive_member (inputs : List (Value Symbol Guard)) (state : State Symbol Guard)
    (facts : Facts state) (available : Values state inputs) (child : Value Symbol Guard) (member : child ∈ inputs) :
    child.referenceOf ∈ (inputs.filter closedMu).map Value.referenceOf ↔ closedMu child = true := by
  constructor
  · intro included
    obtain ⟨other, selected, same⟩ := List.mem_map.mp included
    have equal := resident_reference_injective state facts.coherent other child
      (available other (List.mem_filter.mp selected).1).resident (available child member).resident same
    exact equal ▸ (List.mem_filter.mp selected).2
  · intro recursive
    exact List.mem_map.mpr ⟨child, List.mem_filter.mpr ⟨member, recursive⟩, rfl⟩

/-- Filtering returns only original records, regardless of comparison answers. -/
theorem retain_subset [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Symbol]
    (clear : Guard → Bool) (fuel : Nat) (recursive inputs : List (Value Symbol Guard))
    (state : State Symbol Guard) (retained : List (Value Symbol Guard)) (after : State Symbol Guard)
    (done : retain clear fuel recursive inputs state = .done retained after) :
    ∀ value ∈ retained, value ∈ inputs := by
  induction inputs generalizing state retained after with
  | nil => cases done; simp
  | cons child rest ih =>
      by_cases recursiveChild : closedMu child = true
      · cases tail : retain clear fuel recursive rest state with
        | failed => simp [retain, recursiveChild, tail, Result.bind] at done
        | done values final =>
            have equal : child :: values = retained ∧ final = after := by
              simpa only [retain, ite_eq_left recursiveChild, tail, Result.bind, Result.done.injEq] using done
            rcases equal with ⟨rfl, rfl⟩
            intro value member
            rcases List.mem_cons.mp member with same | member
            · exact List.mem_cons.mpr (Or.inl same)
            · exact List.mem_cons_of_mem _ (ih state values final tail value member)
      · cases checked : anyAccepts clear fuel child recursive state with
        | failed => simp [retain, recursiveChild, checked, Result.bind] at done
        | done covered middle =>
            cases tail : retain clear fuel recursive rest middle with
            | failed => simp [retain, recursiveChild, checked, tail, Result.bind] at done
            | done values final =>
                have equal : (if covered then values else child :: values) = retained ∧ final = after := by
                  simpa only [retain, ite_eq_right recursiveChild, checked, tail, Result.bind, Result.done.injEq] using done
                rcases equal with ⟨rfl, rfl⟩
                intro value member
                cases covered with
                | true => exact List.mem_cons_of_mem _ (ih middle values final tail value member)
                | false =>
                    rcases List.mem_cons.mp member with same | member
                    · exact List.mem_cons.mpr (Or.inl same)
                    · exact List.mem_cons_of_mem _ (ih middle values final tail value member)

/-- Ordered identity removal cannot add a child absent from the original source column. -/
theorem select_subset [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Symbol]
    (clear : Guard → Bool) (fuel : Nat) (inputs : List (Value Symbol Guard))
    (state : State Symbol Guard) (retained : List (Value Symbol Guard)) (after : State Symbol Guard)
    (done : select clear fuel inputs state = .done retained after) :
    ∀ value ∈ retained, value ∈ inputs := by
  cases filtered : retain clear fuel (inputs.filter closedMu) inputs state with
  | failed => simp [select, filtered, Result.bind] at done
  | done values final =>
      have equal : distinctNodes values = retained ∧ final = after := by
        simpa only [select, filtered, Result.bind, Result.done.injEq] using done
      rcases equal with ⟨rfl, rfl⟩
      exact fun value member => retain_subset clear fuel _ inputs state values final filtered value
        (distinctNodes_member values value member)

/-- Final identity removal leaves all verified cache effects unchanged. -/
theorem select_verified [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Symbol]
    (clear : Guard → Bool) (fuel : Nat) (inputs : List (Value Symbol Guard))
    (state : State Symbol Guard) (facts : Facts state) (prepared : Prepared state) (available : Values state inputs) :
    Verified state (select clear fuel inputs state) := by
  have checked := retain_verified clear fuel (inputs.filter closedMu) inputs state facts prepared
    (fun value member => available value (List.mem_filter.mp member).1) (recursive_closed inputs) available
  apply bind_verified state _ _ checked
  intro retained after done
  exact done_verified after (checked.effect done).facts _

/-- Every ordered finite cover search has an exact stable successful bound. -/
theorem any_eventually [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Symbol]
    (clear : Guard → Bool) (narrow : Value Symbol Guard) (wides : List (Value Symbol Guard))
    (state : State Symbol Guard) (facts : Facts state) (prepared : Prepared state)
    (narrowInput : Available state narrow) (wideInputs : Values state wides) (wideClosed : ClosedValues wides) :
    EventuallyDone (fun fuel => anyAccepts clear fuel narrow wides state) := by
  induction wides generalizing state with
  | nil => exact eventually_done false state
  | cons wide rest ih =>
      by_cases closed : narrow.free = []
      · simp only [anyAccepts, ite_eq_left closed]
        apply eventually_bind
        · exact check_eventually (nodeInventory state) clear state facts prepared
            (MergedComparisonColdMeasure.covers_initial state facts) [] wide narrow
            (wideInputs wide List.mem_cons_self) narrowInput (wideClosed wide List.mem_cons_self) closed
        · intro fuel accepted after done
          have effect := (check_verified clear fuel [] wide narrow state facts prepared
            (wideInputs wide List.mem_cons_self) narrowInput (wideClosed wide List.mem_cons_self) closed).effect done
          cases accepted with
          | true => exact eventually_done true after
          | false =>
              exact ih after effect.facts (prepared.preserve effect.unchanged)
                (narrowInput.grows state after effect.growth effect.history)
                (fun value member => (wideInputs value (List.mem_cons_of_mem _ member)).grows state after effect.growth effect.history)
                (fun value member => wideClosed value (List.mem_cons_of_mem _ member))
      · simpa only [anyAccepts, ite_eq_right closed] using eventually_done false state

/-- The finite child filter completes in source order with a stable exact cache. -/
theorem retain_eventually [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Symbol]
    (clear : Guard → Bool) (recursive inputs : List (Value Symbol Guard))
    (state : State Symbol Guard) (facts : Facts state) (prepared : Prepared state)
    (recInputs : Values state recursive) (recClosed : ClosedValues recursive) (available : Values state inputs) :
    EventuallyDone (fun fuel => retain clear fuel recursive inputs state) := by
  induction inputs generalizing state with
  | nil => exact eventually_done [] state
  | cons child rest ih =>
      by_cases recursiveChild : closedMu child = true
      · simp only [retain, ite_eq_left recursiveChild]
        apply eventually_bind
        · exact ih state facts prepared recInputs (fun value member => available value (List.mem_cons_of_mem _ member))
        · intro fuel retained after done
          exact eventually_done (child :: retained) after
      · simp only [retain, ite_eq_right recursiveChild]
        apply eventually_bind
        · exact any_eventually clear child recursive state facts prepared (available child List.mem_cons_self) recInputs recClosed
        · intro fuel covered after done
          have effect := (any_verified clear fuel child recursive state facts prepared
            (available child List.mem_cons_self) recInputs recClosed).effect done
          apply eventually_bind
          · exact ih after effect.facts (prepared.preserve effect.unchanged)
              (fun value member => (recInputs value member).grows state after effect.growth effect.history)
              (fun value member => (available value (List.mem_cons_of_mem _ member)).grows state after effect.growth effect.history)
          · intro bound retained final tailDone
            exact eventually_done (if covered then retained else child :: retained) final

/-- Actual cold selection completes without a warmup or a recursive-comparison premise. -/
theorem select_complete [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Symbol]
    (clear : Guard → Bool) (inputs : List (Value Symbol Guard))
    (state : State Symbol Guard) (facts : Facts state) (prepared : Prepared state) (available : Values state inputs) :
    ∃ bound retained after, (∀ fuel, bound ≤ fuel → select clear fuel inputs state = .done retained after) ∧
      Verified state (.done retained after) ∧ Prepared after := by
  have stable : EventuallyDone (fun fuel => select clear fuel inputs state) := by
    apply eventually_bind
    · exact retain_eventually clear (inputs.filter closedMu) inputs state facts prepared
        (fun value member => available value (List.mem_filter.mp member).1) (recursive_closed inputs) available
    · intro fuel retained after done
      exact eventually_done (distinctNodes retained) after
  obtain ⟨bound, retained, after, done⟩ := stable
  dsimp only at done
  have checked := select_verified clear bound inputs state facts prepared available
  rw [done bound (Nat.le_refl _)] at checked
  exact ⟨bound, retained, after, done, checked, prepared.preserve checked.unchanged⟩

end MicroCFTA.MergedSourceSelection
