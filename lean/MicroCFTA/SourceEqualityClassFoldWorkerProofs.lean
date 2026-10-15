import MicroCFTA.SourceEqualityClassFoldWorker

/-!
# Source class fold function and graph agreement

Checked successful workers retain actual source fold graphs. Complete
graphs derive finite bounds for all five edit and target stages. Every
larger tuple returns the identical forest and entire native state.
-/
namespace MicroCFTA.SourceEqualityClassFoldWorkerProofs
open InternedConstructorTemplates SourceEqualityClassFoldGraph SourceEqualityClassFoldWorker

/-- A completed sequence contains the exact returned first stage and its literal continuation. -/
theorem bind_done (first : Result width Symbol Guard A) (next : A → NativeState width Symbol Guard → Result width Symbol Guard B)
    (result : B) (after : NativeState width Symbol Guard) :
    first.bind next = .done result after ↔ ∃ value middle, first = .done value middle ∧ next value middle = .done result after := by
  cases first with
  | done value state =>
      constructor
      · intro done; exact ⟨value, state, rfl, done⟩
      · rintro ⟨actual, middle, same, done⟩; cases same; exact done
  | incomplete => simp [Result.bind]

/-- Five finite bounds give identical completed forests and native states at every larger tuple. -/
def StableRun (evaluation : Nat → Nat → Nat → Nat → Nat → Result width Symbol Guard A) (result : A) (after : NativeState width Symbol Guard) : Prop :=
  ∃ edit projection head comparison native, ∀ e p h c n,
    edit ≤ e → projection ≤ p → head ≤ h → comparison ≤ c → native ≤ n → evaluation e p h c n = .done result after

/-- Adjacent stable source stages compose at their literal intermediate native state. -/
theorem bind_stable (first : Nat → Nat → Nat → Nat → Nat → Result width Symbol Guard A)
    (next : Nat → Nat → Nat → Nat → Nat → A → NativeState width Symbol Guard → Result width Symbol Guard B)
    (value : A) (middle : NativeState width Symbol Guard) (result : B) (after : NativeState width Symbol Guard)
    (one : StableRun first value middle) (two : StableRun (fun e p h c n => next e p h c n value middle) result after) :
    StableRun (fun e p h c n => (first e p h c n).bind (next e p h c n)) result after := by
  obtain ⟨e, p, h, c, n, done⟩ := one
  obtain ⟨laterE, laterP, laterH, laterC, laterN, nextDone⟩ := two
  refine ⟨max e laterE, max p laterP, max h laterH, max c laterC, max n laterN, ?_⟩
  intro a b d f g ee ep eh ec en
  simp only [done a b d f g (Nat.le_trans (Nat.le_max_left _ _) ee) (Nat.le_trans (Nat.le_max_left _ _) ep)
    (Nat.le_trans (Nat.le_max_left _ _) eh) (Nat.le_trans (Nat.le_max_left _ _) ec) (Nat.le_trans (Nat.le_max_left _ _) en), Result.bind,
    nextDone a b d f g (Nat.le_trans (Nat.le_max_right _ _) ee) (Nat.le_trans (Nat.le_max_right _ _) ep)
      (Nat.le_trans (Nat.le_max_right _ _) eh) (Nat.le_trans (Nat.le_max_right _ _) ec) (Nat.le_trans (Nat.le_max_right _ _) en)]

variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat}
variable (emptyGuard : Guard) (conjoin : Guard → Guard → Guard) (clear : Guard → Bool) (top : Guard)

/-- Successful checked class execution retains its fresh-slot simultaneous edit graph. -/
theorem class_graph (e p h c n : Nat) (record : SourceEqualityClassOrder.Record) (values : List (Value Symbol Guard))
    (before : NativeState width Symbol Guard) (ranges : ClassRanges emptyGuard conjoin clear top record values before)
    (results : List (Value Symbol Guard)) (after : NativeState width Symbol Guard)
    (done : classEdit emptyGuard conjoin clear top e p h c n record values before = .done results after) :
    Class emptyGuard conjoin clear top record values before results after := by
  cases actual : SourceEqualitySharedEditWorker.editAll emptyGuard conjoin clear top record values e p h c n
      (SourceEqualityClassEdits.edits record.paths id) values (SourceEqualitySharedTargetState.initial before) with
  | done output shared =>
      simp only [classEdit, actual] at done
      have parts := Result.done.inj done
      cases parts.1; cases parts.2
      exact .edit (SourceEqualitySharedEditAPI.list_graph emptyGuard conjoin clear top record values e p h c n _ values _ ranges _ shared actual)
  | pending | unresolved | exhausted | target | native => simp only [classEdit, actual] at done; cases done

/-- Successful checked right-fold execution contains every literal completed tail and fresh class. -/
theorem fold_graph (e p h c n : Nat) (records : List SourceEqualityClassOrder.Record) (values : List (Value Symbol Guard))
    (before : NativeState width Symbol Guard) (ranges : Ranges emptyGuard conjoin clear top records values before)
    (results : List (Value Symbol Guard)) (after : NativeState width Symbol Guard)
    (done : fold emptyGuard conjoin clear top e p h c n records values before = .done results after) :
    Fold emptyGuard conjoin clear top records values before results after := by
  induction records generalizing values before results after with
  | nil =>
      have parts := Result.done.inj done
      cases parts.1; cases parts.2; exact .nil
  | cons record records ih =>
      cases ranges with
      | cons tail head =>
          obtain ⟨middle, next, first, last⟩ := (bind_done _ _ results after).mp done
          have tailTrace := ih values before tail middle next first
          exact .cons tailTrace (class_graph emptyGuard conjoin clear top e p h c n record middle next (head middle next tailTrace) results after last)

/-- Checked successful pass execution gives the fold followed by its single final propagation. -/
theorem pass_graph (e p h c n : Nat) (records : List SourceEqualityClassOrder.Record) (values : List (Value Symbol Guard))
    (before : NativeState width Symbol Guard) (ranges : Ranges emptyGuard conjoin clear top records values before)
    (results : List (Value Symbol Guard)) (after : NativeState width Symbol Guard)
    (done : pass emptyGuard conjoin clear top e p h c n records values before = .done results after) :
    Pass emptyGuard conjoin clear top records values before results after := by
  obtain ⟨middle, next, first, last⟩ := (bind_done _ _ results after).mp done
  have parts := Result.done.inj last
  cases parts.1; cases parts.2
  exact .done (fold_graph emptyGuard conjoin clear top e p h c n records values before ranges middle _ first)

/-- Every completed fresh class supplies finite bounds for identical output and full native state. -/
theorem class_stable {record values before results after}
    (trace : Class (Symbol := Symbol) (width := width) emptyGuard conjoin clear top record values before results after) :
    StableRun (fun e p h c n => classEdit emptyGuard conjoin clear top e p h c n record values before) results after := by
  cases trace with
  | edit actual =>
      obtain ⟨e, p, h, c, n, stable⟩ := SourceEqualitySharedEditWorkerComplete.list_stable emptyGuard conjoin clear top record values actual
      refine ⟨e, p, h, c, n, ?_⟩
      intro a b d f g ee ep eh ec en
      have repeated := stable a b d f g ee ep eh ec en
      change SourceEqualitySharedEditWorker.editAll emptyGuard conjoin clear top record values a b d f g _ values _ = _ at repeated
      simp only [classEdit, repeated]

/-- Complete source folds execute identically at every larger independent bound tuple. -/
theorem fold_stable {records values before results after}
    (trace : Fold (Symbol := Symbol) (width := width) emptyGuard conjoin clear top records values before results after) :
    StableRun (fun e p h c n => fold emptyGuard conjoin clear top e p h c n records values before) results after := by
  induction trace with
  | nil => exact ⟨0, 0, 0, 0, 0, by intros; rfl⟩
  | cons tail head ih => exact bind_stable _ _ _ _ _ _ ih (class_stable emptyGuard conjoin clear top head)

/-- Final propagation has no additional work bound or native-state effect. -/
theorem pass_stable {records values before results after}
    (trace : Pass (Symbol := Symbol) (width := width) emptyGuard conjoin clear top records values before results after) :
    StableRun (fun e p h c n => pass emptyGuard conjoin clear top e p h c n records values before) results after := by
  cases trace with
  | done fold =>
      obtain ⟨e, p, h, c, n, stable⟩ := fold_stable emptyGuard conjoin clear top fold
      exact ⟨e, p, h, c, n, by intro a b d f g ee ep eh ec en; simp only [pass, stable a b d f g ee ep eh ec en, Result.bind]⟩

end MicroCFTA.SourceEqualityClassFoldWorkerProofs
