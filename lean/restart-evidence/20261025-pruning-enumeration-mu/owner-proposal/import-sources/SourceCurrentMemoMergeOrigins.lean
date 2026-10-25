import MicroCFTA.SourceCurrentMemoMergeGraph
import MicroCFTA.InternedRecordCoherence

/-!
# Historical producers of recursive memo-aware merge results

Every completed entry retains an actual execution of its recursive body.
The body uses the new memo-aware requests. It is not an uncached replay.
Initial empty tables supply no result. Literal first-writer completion
retains earlier producers. This provenance statement does not by itself
establish language coverage or the lazy publication/runtime bridge.
-/
namespace MicroCFTA.SourceCurrentMemoMergeOrigins
open Cache InternedConstructorTemplates SourceCurrentMemoMergeGraph
open InternedRecordCoherence (record_cases)

variable {Symbol Guard : Type} [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]

/-- A producer records the literal completed recursive body and its original table. -/
def Origin (clear : Guard → Bool) (top : Guard) (input output : Value Symbol Guard) : Prop :=
  ∃ before memo after saved, Run clear top (body top input) before memo output after saved

/-- Each stored original has its actual tagged key and a completed memo-aware producer. -/
def Produced (clear : Guard → Bool) (top : Guard) (memo : Memo Symbol Guard) : Prop :=
  ∀ key entry, memo key = some entry → entry.original.referenceOf = key ∧ Origin clear top entry.original entry.result

/-- An initial empty completed table has no unsupported producer. -/
theorem produced_empty (clear : Guard → Bool) (top : Guard) : Produced (Symbol := Symbol) clear top empty := by
  intro key entry impossible
  cases impossible

/-- A first-writer completion retains earlier producers and records the actual new body result. -/
theorem produced_remember {clear : Guard → Bool} {top : Guard} {memo : Memo Symbol Guard}
    (produced : Produced clear top memo) (input output : Value Symbol Guard) (origin : Origin clear top input output) :
    Produced clear top (remember memo input output) := by
  intro key entry found
  rcases record_cases memo input.referenceOf key ⟨input, output⟩ entry found with old | ⟨same, entrySame⟩
  · exact produced key entry old
  · subst entry
    exact ⟨same.symm, origin⟩

/-- Every actual completed instruction preserves the producer history of the result table. -/
theorem run_produced {clear : Guard → Bool} {top : Guard} {code : Code Symbol Guard Output}
    {before after : State Symbol Guard} {memo saved : Memo Symbol Guard} {output : Output}
    (actual : Run clear top code before memo output after saved) :
    Produced clear top memo → Produced clear top saved := by
  exact Run.rec
      (motive_1 := fun {_} _ _ memo _ _ saved _ => Produced clear top memo → Produced clear top saved)
      (motive_2 := fun _ _ memo _ _ saved _ => Produced clear top memo → Produced clear top saved)
      (fun _ _ _ => id)
      (fun _ _ _ => id)
      (fun _ _ => id)
      (fun _ ih => ih)
      (fun _ _ first later produced => later (first produced))
      (fun _ => id)
      (fun _ body ih produced => produced_remember (ih produced) _ _ ⟨_, _, _, _, body⟩)
      actual

/-- Actual recursive cache calls retain historical producers through hits and first-writer misses. -/
theorem call_produced {clear : Guard → Bool} {top : Guard} {input output : Value Symbol Guard}
    {before after : State Symbol Guard} {memo saved : Memo Symbol Guard}
    (actual : Call clear top input before memo output after saved) :
    Produced clear top memo → Produced clear top saved :=
  run_produced (.request actual)

/-- Every completed request returns a record that its final table actually stores. -/
theorem call_returned {clear : Guard → Bool} {top : Guard} {input output : Value Symbol Guard}
    {before after : State Symbol Guard} {memo saved : Memo Symbol Guard}
    (actual : Call clear top input before memo output after saved) :
    ∃ entry, saved input.referenceOf = some entry ∧ entry.result = output := by
  cases actual with
  | hit found => exact ⟨_, found, rfl⟩
  | miss => exact ⟨_, winner_found _ _ _, rfl⟩

/-- A cold actual call derives all final producer histories and the returned winner's physical key. -/
theorem cold_produced {clear : Guard → Bool} {top : Guard} {input output : Value Symbol Guard}
    {before after : State Symbol Guard} {saved : Memo Symbol Guard}
    (actual : Call clear top input before empty output after saved) :
    Produced clear top saved ∧ ∃ entry, saved input.referenceOf = some entry ∧ entry.result = output ∧
      entry.original.referenceOf = input.referenceOf ∧ Origin clear top entry.original output := by
  have produced := call_produced actual (produced_empty clear top)
  obtain ⟨entry, found, same⟩ := call_returned actual
  have origin := produced _ entry found
  exact ⟨produced, entry, found, same, origin.1, same ▸ origin.2⟩

end MicroCFTA.SourceCurrentMemoMergeOrigins
