import MicroCFTA.SourceCurrentMemoClassWorker
import MicroCFTA.SourceCurrentMemoSharedEditWorkerComplete

/-!
# Completed class worker correspondence and stable bounds

Checked successful workers derive the actual memo-aware class graphs.
Actual finite graphs derive six independent sufficient bounds. Every larger
tuple retains the same result forest, native state, and completed merge table.
No cache invariant or recursive completion law is supplied for that direction.
-/
namespace MicroCFTA.SourceCurrentMemoClassWorkerProofs
open InternedConstructorTemplates SourceCurrentMemoClassPass SourceCurrentMemoClassWorker
open SourceCurrentMemoMergeGraph (Memo)
local notation "Native" => SourceRecursiveIntersectionThunks.State

/-- A completed bind contains its exact first result, both returned states, and continuation. -/
theorem bind_done_iff (first : Outcome width Symbol Guard A)
    (next : A → Native width Symbol Guard → Memo Symbol Guard → Outcome width Symbol Guard B)
    (result : B) (after : Native width Symbol Guard) (saved : Memo Symbol Guard) :
    first.bind next = .done result after saved ↔
      ∃ value middle current, first = .done value middle current ∧ next value middle current = .done result after saved := by
  cases first with
  | done value native memo =>
      constructor
      · intro done; exact ⟨value, native, memo, rfl, done⟩
      · rintro ⟨_, _, _, same, done⟩; cases same; exact done
  | incomplete => simp [Outcome.bind]

/-- Six independent bounds retain the exact result and both final states at every larger tuple. -/
def StableRun (evaluation : Nat → Nat → Nat → Nat → Nat → Nat → Outcome width Symbol Guard A)
    (result : A) (after : Native width Symbol Guard) (saved : Memo Symbol Guard) : Prop :=
  ∃ edit projection read merge selection native, ∀ e p h w c n,
    edit ≤ e → projection ≤ p → read ≤ h → merge ≤ w → selection ≤ c → native ≤ n →
      evaluation e p h w c n = .done result after saved

/-- Adjacent stable stages compose at their exact intermediate native state and merge table. -/
theorem bind_stable (first : Nat → Nat → Nat → Nat → Nat → Nat → Outcome width Symbol Guard A)
    (next : Nat → Nat → Nat → Nat → Nat → Nat → A → Native width Symbol Guard → Memo Symbol Guard → Outcome width Symbol Guard B)
    (value : A) (middle : Native width Symbol Guard) (current : Memo Symbol Guard)
    (result : B) (after : Native width Symbol Guard) (saved : Memo Symbol Guard)
    (one : StableRun first value middle current)
    (two : StableRun (fun e p h w c n => next e p h w c n value middle current) result after saved) :
    StableRun (fun e p h w c n => (first e p h w c n).bind (next e p h w c n)) result after saved := by
  obtain ⟨e, p, h, w, c, n, done⟩ := one
  obtain ⟨laterE, laterP, laterH, laterW, laterC, laterN, nextDone⟩ := two
  refine ⟨max e laterE, max p laterP, max h laterH, max w laterW, max c laterC, max n laterN, ?_⟩
  intro a b d f g k ee ep eh ew ec en
  simp only [done a b d f g k
    (Nat.le_trans (Nat.le_max_left _ _) ee) (Nat.le_trans (Nat.le_max_left _ _) ep)
    (Nat.le_trans (Nat.le_max_left _ _) eh) (Nat.le_trans (Nat.le_max_left _ _) ew)
    (Nat.le_trans (Nat.le_max_left _ _) ec) (Nat.le_trans (Nat.le_max_left _ _) en), Outcome.bind,
    nextDone a b d f g k
      (Nat.le_trans (Nat.le_max_right _ _) ee) (Nat.le_trans (Nat.le_max_right _ _) ep)
      (Nat.le_trans (Nat.le_max_right _ _) eh) (Nat.le_trans (Nat.le_max_right _ _) ew)
      (Nat.le_trans (Nat.le_max_right _ _) ec) (Nat.le_trans (Nat.le_max_right _ _) en)]

/-- Independent stable bounds give one sufficient common bound without an extra algorithm premise. -/
theorem uniform {evaluation : Nat → Nat → Nat → Nat → Nat → Nat → Outcome width Symbol Guard A}
    {result : A} {after : Native width Symbol Guard} {saved : Memo Symbol Guard}
    (stable : StableRun evaluation result after saved) :
    ∃ bound, ∀ fuel, bound ≤ fuel → evaluation fuel fuel fuel fuel fuel fuel = .done result after saved := by
  obtain ⟨e, p, h, w, c, n, done⟩ := stable
  refine ⟨max e (max p (max h (max w (max c n)))), ?_⟩
  intro fuel enough
  apply done <;> omega

variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat}
variable (emptyGuard : Guard) (conjoin : Guard → Guard → Guard) (clear : Guard → Bool) (top : Guard)

/-- Successful checked class execution derives the actual graph with its returned merge table. -/
theorem class_graph (e p h w c n : Nat) (record : SourceEqualityClassOrder.Record)
    (values : List (Value Symbol Guard)) (before : Native width Symbol Guard) (memo : Memo Symbol Guard)
    (ranges : ClassRanges emptyGuard conjoin clear top record values before memo)
    (results : List (Value Symbol Guard)) (after : Native width Symbol Guard) (saved : Memo Symbol Guard)
    (done : classEdit emptyGuard conjoin clear top e p h w c n record values before memo = .done results after saved) :
    Class emptyGuard conjoin clear top record values before memo results after saved := by
  cases actual : SourceCurrentMemoSharedEditWorker.editAll emptyGuard conjoin clear top record values e p h w c n
      (SourceEqualityClassEdits.edits record.paths id) values (SourceCurrentMemoSharedTargetState.initial before memo) with
  | done output shared =>
      simp only [classEdit, actual] at done
      have parts := Outcome.done.inj done
      cases parts.1; cases parts.2.1; cases parts.2.2
      exact .edit (SourceCurrentMemoSharedEditWorkerSound.list_graph emptyGuard conjoin clear top record values
        e p h w c n _ values _ ranges _ shared actual)
  | failed => simp only [classEdit, actual] at done; cases done

/-- Successful checked folds retain every actual tail and its exact returned memo table. -/
theorem fold_graph (e p h w c n : Nat) (records : List SourceEqualityClassOrder.Record)
    (values : List (Value Symbol Guard)) (before : Native width Symbol Guard) (memo : Memo Symbol Guard)
    (ranges : Ranges emptyGuard conjoin clear top records values before memo)
    (results : List (Value Symbol Guard)) (after : Native width Symbol Guard) (saved : Memo Symbol Guard)
    (done : fold emptyGuard conjoin clear top e p h w c n records values before memo = .done results after saved) :
    Fold emptyGuard conjoin clear top records values before memo results after saved := by
  induction records generalizing values before memo results after saved with
  | nil =>
      have parts := Outcome.done.inj done
      cases parts.1; cases parts.2.1; cases parts.2.2; exact .nil
  | cons record records ih =>
      cases ranges with
      | cons tail head =>
          obtain ⟨middle, next, current, first, last⟩ := (bind_done_iff _ _ results after saved).mp done
          have actualTail := ih values before memo tail middle next current first
          exact .cons actualTail (class_graph emptyGuard conjoin clear top e p h w c n record middle next current
            (head middle next current actualTail) results after saved last)

/-- Successful checked pass execution derives the complete fold and its one final empty propagation. -/
theorem pass_graph (e p h w c n : Nat) (records : List SourceEqualityClassOrder.Record)
    (values : List (Value Symbol Guard)) (before : Native width Symbol Guard) (memo : Memo Symbol Guard)
    (ranges : Ranges emptyGuard conjoin clear top records values before memo)
    (results : List (Value Symbol Guard)) (after : Native width Symbol Guard) (saved : Memo Symbol Guard)
    (done : pass emptyGuard conjoin clear top e p h w c n records values before memo = .done results after saved) :
    Pass emptyGuard conjoin clear top records values before memo results after saved := by
  obtain ⟨middle, next, current, first, last⟩ := (bind_done_iff _ _ results after saved).mp done
  have parts := Outcome.done.inj last
  cases parts.1; cases parts.2.1; cases parts.2.2
  exact .done (fold_graph emptyGuard conjoin clear top e p h w c n records values before memo ranges middle _ _ first)

/-- A completed fresh class supplies stable bounds for its exact output and both returned states. -/
theorem class_stable {record values before memo results after saved}
    (actual : Class (Symbol := Symbol) (width := width) emptyGuard conjoin clear top record values before memo results after saved) :
    StableRun (fun e p h w c n => classEdit emptyGuard conjoin clear top e p h w c n record values before memo) results after saved := by
  cases actual with
  | edit actual =>
      obtain ⟨e, p, h, w, c, n, stable⟩ :=
        SourceCurrentMemoSharedEditWorkerComplete.list_stable emptyGuard conjoin clear top record values actual
      refine ⟨e, p, h, w, c, n, ?_⟩
      intro a b d f g k ee ep eh ew ec en
      have repeated := stable a b d f g k ee ep eh ew ec en
      change SourceCurrentMemoSharedEditWorker.editAll emptyGuard conjoin clear top record values a b d f g k _ values _ = _ at repeated
      simp only [classEdit, repeated]

/-- Completed class right folds derive stable execution with their actual returned merge table. -/
theorem fold_stable {records values before memo results after saved}
    (actual : Fold (Symbol := Symbol) (width := width) emptyGuard conjoin clear top records values before memo results after saved) :
    StableRun (fun e p h w c n => fold emptyGuard conjoin clear top e p h w c n records values before memo) results after saved := by
  induction actual with
  | nil => exact ⟨0, 0, 0, 0, 0, 0, by intros; rfl⟩
  | cons tail head ih => exact bind_stable _ _ _ _ _ _ _ _ ih (class_stable emptyGuard conjoin clear top head)

/-- Final empty propagation retains the same stable bounds, native state, and merge table. -/
theorem pass_stable {records values before memo results after saved}
    (actual : Pass (Symbol := Symbol) (width := width) emptyGuard conjoin clear top records values before memo results after saved) :
    StableRun (fun e p h w c n => pass emptyGuard conjoin clear top e p h w c n records values before memo) results after saved := by
  cases actual with
  | done actual =>
      obtain ⟨e, p, h, w, c, n, stable⟩ := fold_stable emptyGuard conjoin clear top actual
      refine ⟨e, p, h, w, c, n, ?_⟩
      intro a b d f g k ee ep eh ew ec en
      simp only [pass, stable a b d f g k ee ep eh ew ec en, Outcome.bind]

/-- One derived common bound executes the exact completed pass at every larger common fuel. -/
theorem pass_uniform {records values before memo results after saved}
    (actual : Pass (Symbol := Symbol) (width := width) emptyGuard conjoin clear top records values before memo results after saved) :
    ∃ bound, ∀ fuel, bound ≤ fuel →
      pass emptyGuard conjoin clear top fuel fuel fuel fuel fuel fuel records values before memo = .done results after saved :=
  uniform (pass_stable emptyGuard conjoin clear top actual)

end MicroCFTA.SourceCurrentMemoClassWorkerProofs
