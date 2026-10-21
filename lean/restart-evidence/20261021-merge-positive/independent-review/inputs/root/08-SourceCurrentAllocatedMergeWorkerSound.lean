import MicroCFTA.SourceCurrentAllocatedMergeWorker

/-!
# Completed worker observations derive the allocated graph

Soundness follows the literal bounded interpreter. Each completed bind
retains its actual prefix state and merge table. Failed observations do
not become graph completion receipts. No physical or language invariant
is needed for this operational correspondence.
-/
namespace MicroCFTA.SourceCurrentAllocatedMergeWorkerSound
open InternedConstructorTemplates SourceCurrentAllocatedMergeGraph SourceCurrentAllocatedMergeWorker
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula

/-- A completed bind identifies its exact completed prefix and returned table. -/
theorem bind_done_iff (first : Outcome Input) (next : Input → State → Memo → Outcome Output)
    (output : Output) (after : State) (saved : Memo) :
    first.bind next = .done output after saved ↔
      ∃ value middle current, first = .done value middle current ∧ next value middle current = .done output after saved := by
  cases first with
  | done value state memo =>
      constructor
      · intro actual
        exact ⟨value, state, memo, rfl, actual⟩
      · rintro ⟨_, _, _, same, actual⟩
        cases same
        exact actual
  | failed =>
      constructor
      · intro impossible
        cases impossible
      · rintro ⟨_, _, _, impossible, _⟩
        cases impossible

private theorem sound [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (clear : Guard → Bool) (fuel : Nat) :
    (∀ {Output : Type} (code : Code Output) before memo output after saved selectionFuel,
      execute clear fuel selectionFuel code before memo = .done output after saved →
        Run clear code before memo output after saved) ∧
    (∀ (input : Value Symbol Guard) before memo output after saved selectionFuel,
      call clear fuel selectionFuel input before memo = .done output after saved →
        Call clear input before memo output after saved) := by
  induction fuel with
  | zero =>
      constructor
      · intro _ code before memo output after saved selectionFuel impossible
        cases impossible
      · intro input before memo output after saved selectionFuel impossible
        cases impossible
  | succ fuel ih =>
      constructor
      · intro Output code before memo output after saved selectionFuel done
        cases code with
        | pure value =>
            simp only [execute] at done
            cases done
            exact .pure _ _ _
        | work job =>
            simp only [execute] at done
            cases done
            exact .work _ _ _
        | topRow symbol children =>
            simp only [execute] at done
            cases done
            exact .topRow _ _ _ _
        | select inputs =>
            simp only [execute] at done
            cases selected : SourceMergedSelection.select clear selectionFuel inputs before.heap with
            | done values heap =>
                simp only [selected] at done
                cases done
                exact .select selectionFuel selected
            | failed =>
                simp only [selected] at done
                cases done
        | request input =>
            exact .request (ih.2 input before memo output after saved selectionFuel done)
        | bind first next =>
            obtain ⟨value, middle, current, firstDone, laterDone⟩ :=
              (bind_done_iff _ _ output after saved).mp done
            exact .bind (ih.1 first before memo value middle current selectionFuel firstDone)
              (ih.1 (next value) middle current output after saved selectionFuel laterDone)
      · intro input before memo output after saved selectionFuel done
        cases found : memo input.referenceOf with
        | some entry =>
            simp only [call, found] at done
            cases done
            exact .hit found
        | none =>
            simp only [call, found] at done
            obtain ⟨candidate, state, current, bodyDone, returned⟩ := (bind_done_iff _ _ output after saved).mp done
            cases returned
            exact .miss found (ih.1 (body input) before memo candidate _ current selectionFuel bodyDone)

/-- Every completed instruction returns the same output, allocated state, and merge table in Run. -/
theorem execute_sound [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {clear : Guard → Bool} {code : Code Output} {before after : State} {memo saved : Memo} {output : Output}
    {fuel selectionFuel : Nat} (done : execute clear fuel selectionFuel code before memo = .done output after saved) :
    Run clear code before memo output after saved := (sound clear fuel).1 code before memo output after saved selectionFuel done

/-- Every completed request derives its literal completed hit or allocated recursive miss. -/
theorem call_sound [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {clear : Guard → Bool} {input output : Value Symbol Guard} {before after : State} {memo saved : Memo}
    {fuel selectionFuel : Nat} (done : call clear fuel selectionFuel input before memo = .done output after saved) :
    Call clear input before memo output after saved := (sound clear fuel).2 input before memo output after saved selectionFuel done

end MicroCFTA.SourceCurrentAllocatedMergeWorkerSound
