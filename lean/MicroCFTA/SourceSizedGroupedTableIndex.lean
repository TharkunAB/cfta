import MicroCFTA.SourceSizedGroupedPlain
import MicroCFTA.SourceSizedGroupedRecurrence

/-!
# Finite observations of the source grouped table index

Each unfolding uses the source state body and its actual count and selector
combinators. An absent minimum key returns the empty index before the body
reads child fields. A query supplies its unfolding bound from its size.

Independent class unfoldings specify the resulting field observations.
The paid source recurrence reads only smaller child sizes. Its strict
dependency proves that size plus one unfoldings suffice, including cycles.
Class lists do not construct the count or selector fields.

The missing-key property is an internal source-table condition. The actual
computed minimum adapter can derive it from successful preparation. This
module does not prove sparse-series or fromMinimum correspondence, lazy
sharing, machine index conversions, or total native execution cost.
-/
namespace MicroCFTA.SourceSizedGroupedTableIndex
open Language RecursiveSize SizedRank SourceSizedDecided
open RecursiveJoinFields (ValueIndex)
open SourceSizedGroupedIndex (Correct emptyIndex stateIndex)

variable {State Symbol : Type}

/-- Unfold the projected source table with its minimum-presence gate first. -/
def evaluate : Nat → (State → Bool) → (State → List (Row State Symbol (List (List Nat)))) →
    State → ValueIndex (Term Symbol)
  | 0, _, _, _ => emptyIndex
  | fuel + 1, known, rows, state =>
      if known state then stateIndex (evaluate fuel known rows) (rows state) else emptyIndex

/-- Independent ordered classes of the same gated source unfoldings. -/
def unrolled : Nat → (State → Bool) → (State → List (Row State Symbol (List (List Nat)))) →
    State → Nat → List (Term Symbol)
  | 0, _, _, _, _ => []
  | fuel + 1, known, rows, state, size =>
      if known state then SourceSizedGroupedClasses.classOf (unrolled fuel known rows) (rows state) size else []

/-- The actual minimum table must exclude only states with no grouped members. -/
def MissingEmpty (known : State → Bool) (rows : State → List (Row State Symbol (List (List Nat)))) : Prop :=
  ∀ state, known state = false → ∀ size, SourceSizedGroupedClasses.classes rows size state = []

private theorem classOf_zero (classes : State → Nat → List (Term Symbol))
    (rows : List (Row State Symbol (List (List Nat)))) :
    SourceSizedGroupedClasses.classOf classes rows 0 = [] := by
  apply List.flatMap_eq_nil_iff.mpr
  intro row _
  exact SourceSizedGroupedRecurrence.rowClass_zero classes row.label row.children row.constraint

private theorem unrolled_zero (fuel : Nat) (known : State → Bool)
    (rows : State → List (Row State Symbol (List (List Nat)))) (state : State) :
    unrolled fuel known rows state 0 = [] := by
  cases fuel with
  | zero => rfl
  | succ fuel =>
      cases present : known state with
      | false => simp only [unrolled, present, Bool.false_eq_true, ite_false]
      | true => simpa only [unrolled, present, ite_true] using classOf_zero (unrolled fuel known rows) (rows state)

/-- Each finite source unfolding has its exact independent count and selector law. -/
theorem evaluate_correct (fuel : Nat) (known : State → Bool)
    (rows : State → List (Row State Symbol (List (List Nat)))) (state : State) :
    Correct (evaluate fuel known rows state) (unrolled fuel known rows state) := by
  induction fuel generalizing state with
  | zero => exact SourceSizedGroupedIndex.empty_correct
  | succ fuel ih =>
      change Correct (evaluate (fuel + 1) known rows state)
        (fun size => unrolled (fuel + 1) known rows state size)
      cases present : known state with
      | false =>
          simpa only [evaluate, unrolled, present, Bool.false_eq_true, ite_false] using
            (SourceSizedGroupedIndex.empty_correct (Value := Term Symbol))
      | true =>
          simpa only [evaluate, unrolled, present, ite_true] using
            SourceSizedGroupedPlain.state_correct (evaluate fuel known rows) (unrolled fuel known rows) ih (rows state)

/-- Every finite unfolding has zero source count at node size zero. -/
theorem evaluate_zero_count (fuel : Nat) (known : State → Bool)
    (rows : State → List (Row State Symbol (List (List Nat)))) (state : State) :
    (evaluate fuel known rows state).counts 0 = 0 := by
  rw [(evaluate_correct fuel known rows state).counts, unrolled_zero]
  rfl

/-- The strict paid child-size dependency determines every sufficiently unfolded class. -/
theorem unrolled_eq_classes (fuel : Nat) (known : State → Bool)
    (rows : State → List (Row State Symbol (List (List Nat)))) (missing : MissingEmpty known rows)
    (size : Nat) (state : State) (enough : size + 1 ≤ fuel) :
    unrolled fuel known rows state size = SourceSizedGroupedClasses.classes rows size state := by
  induction fuel generalizing size state with
  | zero => omega
  | succ fuel ih =>
      cases present : known state with
      | false =>
          simp only [unrolled, present, Bool.false_eq_true, ite_false]
          exact (missing state present size).symm
      | true =>
          simp only [unrolled, present, ite_true]
          cases size with
          | zero =>
              rw [SourceSizedGroupedClasses.classes_zero]
              exact classOf_zero (unrolled fuel known rows) (rows state)
          | succ remaining =>
              rw [SourceSizedGroupedRecurrence.classes_succ]
              apply SourceSizedGroupedRecurrence.classOf_congr
              intro child childSize smaller
              exact ih childSize child (by omega)

/-- Enough source unfoldings give the checked count without constructing class products. -/
theorem evaluate_count (fuel : Nat) (known : State → Bool)
    (rows : State → List (Row State Symbol (List (List Nat)))) (missing : MissingEmpty known rows)
    (size : Nat) (state : State) (enough : size + 1 ≤ fuel) :
    (evaluate fuel known rows state).counts size = (SourceSizedGroupedClasses.classes rows size state).length := by
  rw [(evaluate_correct fuel known rows state).counts,
    unrolled_eq_classes fuel known rows missing size state enough]

/-- A counted source selection has the exact checked grouped class position. -/
theorem evaluate_select (fuel : Nat) (known : State → Bool)
    (rows : State → List (Row State Symbol (List (List Nat)))) (missing : MissingEmpty known rows)
    (size rank : Nat) (state : State) (enough : size + 1 ≤ fuel)
    (bounded : rank < (evaluate fuel known rows state).counts size) :
    (evaluate fuel known rows state).select ⟨size, rank⟩ =
      (SourceSizedGroupedClasses.classes rows size state)[rank]? := by
  rw [(evaluate_correct fuel known rows state).select ⟨size, rank⟩ bounded,
    unrolled_eq_classes fuel known rows missing size state enough]

/-- Supply the finite source unfolding bound from the query size alone. -/
def indexAt (known : State → Bool) (rows : State → List (Row State Symbol (List (List Nat))))
    (size : Nat) (state : State) : ValueIndex (Term Symbol) := evaluate (size + 1) known rows state

/-- Read the source count field at its requested class size. -/
def countAt (known : State → Bool) (rows : State → List (Row State Symbol (List (List Nat))))
    (size : Nat) (state : State) : Nat := (indexAt known rows size state).counts size

/-- Retain the source fromTable class-count guard before the selector read. -/
def selectAt (known : State → Bool) (rows : State → List (Row State Symbol (List (List Nat))))
    (size rank : Nat) (state : State) : Option (Term Symbol) :=
  let index := indexAt known rows size state
  if rank < index.counts size then index.select ⟨size, rank⟩ else none

/-- The bound computed from the request yields the checked count in the same order. -/
theorem countAt_eq (known : State → Bool) (rows : State → List (Row State Symbol (List (List Nat))))
    (missing : MissingEmpty known rows) (size : Nat) (state : State) :
    countAt known rows size state = (SourceSizedGroupedClasses.classes rows size state).length :=
  evaluate_count (size + 1) known rows missing size state (Nat.le_refl _)

/-- The guarded source selector agrees with the checked class at every natural rank. -/
theorem selectAt_eq (known : State → Bool) (rows : State → List (Row State Symbol (List (List Nat))))
    (missing : MissingEmpty known rows) (size rank : Nat) (state : State) :
    selectAt known rows size rank state = (SourceSizedGroupedClasses.classes rows size state)[rank]? := by
  unfold selectAt
  dsimp only
  split
  · rename_i bounded
    exact evaluate_select (size + 1) known rows missing size rank state (Nat.le_refl _) bounded
  · rename_i outside
    have bound : (SourceSizedGroupedClasses.classes rows size state).length ≤ rank := by
      have counts := countAt_eq known rows missing size state
      change (indexAt known rows size state).counts size = _ at counts
      omega
    exact (List.getElem?_eq_none bound).symm

/-- Out-of-class source ranks are rejected by the actual count guard. -/
theorem selectAt_none_iff (known : State → Bool)
    (rows : State → List (Row State Symbol (List (List Nat)))) (missing : MissingEmpty known rows)
    (size rank : Nat) (state : State) :
    selectAt known rows size rank state = none ↔ countAt known rows size state ≤ rank := by
  rw [selectAt_eq known rows missing, List.getElem?_eq_none_iff, countAt_eq known rows missing]

/-- Increasing the finite unfolding bound preserves every checked count observation. -/
theorem count_stable (first second : Nat) (known : State → Bool)
    (rows : State → List (Row State Symbol (List (List Nat)))) (missing : MissingEmpty known rows)
    (size : Nat) (state : State) (firstEnough : size + 1 ≤ first) (secondEnough : size + 1 ≤ second) :
    (evaluate first known rows state).counts size = (evaluate second known rows state).counts size := by
  rw [evaluate_count first known rows missing size state firstEnough,
    evaluate_count second known rows missing size state secondEnough]

/-- Increasing the unfolding bound preserves each counted source selector observation. -/
theorem select_stable (first second : Nat) (known : State → Bool)
    (rows : State → List (Row State Symbol (List (List Nat)))) (missing : MissingEmpty known rows)
    (size rank : Nat) (state : State) (firstEnough : size + 1 ≤ first) (secondEnough : size + 1 ≤ second)
    (bounded : rank < (evaluate first known rows state).counts size) :
    (evaluate first known rows state).select ⟨size, rank⟩ =
      (evaluate second known rows state).select ⟨size, rank⟩ := by
  have secondBound : rank < (evaluate second known rows state).counts size := by
    rw [← count_stable first second known rows missing size state firstEnough secondEnough]
    exact bounded
  rw [evaluate_select first known rows missing size rank state firstEnough bounded,
    evaluate_select second known rows missing size rank state secondEnough secondBound]

end MicroCFTA.SourceSizedGroupedTableIndex
