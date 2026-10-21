import MicroCFTA.SourceCurrentMemoMergeGraph
import MicroCFTA.InternedEmptyNormalization

/-!
# Empty support through actual Merge calls

The completed Empty key can return only Empty. Actual instructions preserve
this law. Hits use the same stored entry. Misses check the actual body and
retain the first winner. No semantic or physical storage premise is needed.
-/
namespace MicroCFTA.SourceCurrentMergeEmptySupport
open InternedConstructorTemplates SourceCurrentMemoMergeGraph
variable {Symbol Guard : Type}

/-- Every completed result at the tagged Empty key is Empty. -/
def EmptySafe (memo : Memo Symbol Guard) : Prop :=
  ∀ entry, memo (Value.empty : Value Symbol Guard).referenceOf = some entry →
    entry.result = .empty

/-- An empty completed table satisfies the Empty support law. -/
theorem empty_safe : EmptySafe (empty : Memo Symbol Guard) := by
  intro entry impossible
  cases impossible

private theorem remember_safe {memo : Memo Symbol Guard} (safe : EmptySafe memo)
    (input candidate : Value Symbol Guard) (candidateSafe : input = .empty → candidate = .empty) :
    EmptySafe (remember memo input candidate) := by
  intro entry found
  rcases remember_cases memo input candidate _ entry found with old | ⟨key, same⟩
  · exact safe entry old
  · subst entry
    exact candidateSafe ((InternedEmptyNormalization.reference_empty input).mp key.symm)

variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]

private theorem run_safe {clear : Guard → Bool} {top : Guard} {code : Code Symbol Guard Output}
    {before after : State Symbol Guard} {memo saved : Memo Symbol Guard} {output : Output}
    (actual : Run clear top code before memo output after saved) :
    EmptySafe memo → EmptySafe saved := by
  induction actual using Run.rec
      (motive_2 := fun input _ memo output _ saved _ =>
        EmptySafe memo → EmptySafe saved ∧ (input = .empty → output = .empty)) with
  | pure | work | select => exact id
  | request actual ih => exact fun safe => (ih safe).1
  | bind first later ihFirst ihLater => exact fun safe => ihLater (ihFirst safe)
  | hit found =>
      intro safe
      refine ⟨safe, ?_⟩
      intro same
      subst same
      exact safe _ found
  | @miss memo input before candidate after current absent actual ih =>
      intro safe
      have candidateSafe : input = .empty → candidate = .empty := by
        intro same
        subst same
        exact (Run.pure_iff.mp actual).1
      have completed := remember_safe (ih safe) input candidate candidateSafe
      refine ⟨completed, ?_⟩
      intro same
      exact completed _ (by simpa only [same] using winner_found current input candidate)

/-- Actual completed instructions preserve the law at their exact returned table. -/
theorem run {clear : Guard → Bool} {top : Guard} {code : Code Symbol Guard Output}
    {before after : State Symbol Guard} {memo saved : Memo Symbol Guard} {output : Output}
    (actual : Run clear top code before memo output after saved) (safe : EmptySafe memo) :
    EmptySafe saved := run_safe actual safe

/-- Actual hits and misses return Empty for an Empty input under the same table law. -/
theorem call {clear : Guard → Bool} {top : Guard} {input output : Value Symbol Guard}
    {before after : State Symbol Guard} {memo saved : Memo Symbol Guard}
    (actual : Call clear top input before memo output after saved) (safe : EmptySafe memo) :
    EmptySafe saved ∧ (input = .empty → output = .empty) := by
  have finalSafe := run (.request actual) safe
  refine ⟨finalSafe, ?_⟩
  intro same
  obtain ⟨entry, found, returned⟩ := actual.present
  exact returned.trans (finalSafe entry (by simpa only [same] using found))

end MicroCFTA.SourceCurrentMergeEmptySupport
