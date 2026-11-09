import MicroCFTA.SourceCurrentConjunctionRequirementRowsSemantics
import MicroCFTA.SourceCurrentConjunctionRequirementRowsPublication
import MicroCFTA.SourceCurrentConjunctionRequirementRowsFrame
import MicroCFTA.SourceCurrentConjunctionRequirementRowsEffects

/-!
# Coupled origins through actual row publication

The actual selected publication supplies one descriptor batch and one raw
tail. Both origin lists extend with those same witnesses. Old other spine
handles retain their exact cells. Cached and exhausted observations append
nothing. This proof does not combine independent origin and trace choices.
-/
namespace MicroCFTA.SourceCurrentConjunctionRequirementRowsSemanticsStep
open InternedConstructorTemplates (EdgeValue)
open SourceCurrentConjunctionRequirementRows (Spine lookupSpine descriptors Outcome Handles)
open SourceCurrentConjunctionRequirementRowsSemantics (Spec Invariant)
open SourceCurrentConjunctionRowsAllocation (Ready)
variable {Symbol Formula : Type}
local notation "Guard" => SourceSymbolicIndex.Constraint Formula
local notation "Tuple" => List (EdgeValue Symbol Guard)
local notation "Cell" => SourceCurrentConjunctionRequirementCells.Cell Symbol Formula
local notation "Storage" => SourceCurrentConjunctionRequirementRows.State Symbol Formula
local notation "observe" => SourceCurrentConjunctionRequirementRows.nextRow

private theorem pending_source {origins : List Cell} {sources : List (List Tuple)} {before : Storage}
    {target : Nat} {tuples : List Tuple} (invariant : Invariant origins sources before)
    (found : lookupSpine target before = some (.pending tuples)) : sources[target]? = some tuples := by
  have inside : target < sources.length := by
    rw [invariant.length]
    exact (List.getElem?_eq_some_iff.mp found).1
  have sourceFound : sources[target]? = some sources[target] := List.getElem?_eq_getElem inside
  have spec := invariant.spines target sources[target] (.pending tuples) sourceFound found
  change tuples = sources[target] at spec
  simpa only [← spec] using sourceFound

private theorem other_spec {target : Nat} {before after : Storage} {result : Option (Handles × Nat)}
    {origins : List Cell} {sources : List (List Tuple)}
    (actual : observe target before = .done result after) (invariant : Invariant origins sources before)
    (addedOrigins : List Cell) (addedSources : List (List Tuple))
    {handle : Nat} {original : List Tuple} {spine : Spine Symbol Formula}
    (different : handle ≠ target) (sourceFound : sources[handle]? = some original)
    (spineFound : lookupSpine handle after = some spine) :
    Spec (origins ++ addedOrigins) (sources ++ addedSources) original spine := by
  have inside : handle < before.spines.length := by
    rw [← invariant.length]
    exact (List.getElem?_eq_some_iff.mp sourceFound).1
  have prior : lookupSpine handle before = some before.spines[handle] := List.getElem?_eq_getElem inside
  have retained := SourceCurrentConjunctionRequirementRowsFrame.nextRow_other target before handle
    before.spines[handle] different prior
  rw [actual] at retained
  change lookupSpine handle after = some before.spines[handle] at retained
  have same : spine = before.spines[handle] := Option.some.inj (spineFound.symm.trans retained)
  rw [same]
  exact Spec.weaken (invariant.spines handle original before.spines[handle] sourceFound prior)
    addedOrigins addedSources

/-- A successful actual row observation extends both origin lists with its same selected publication. -/
theorem nextRow {target : Nat} {before after : Storage} {result : Option (Handles × Nat)}
    {origins : List Cell} {sources : List (List Tuple)}
    (actual : observe target before = .done result after) (ready : Ready before.requirements.physical)
    (raw : SourceCurrentConjunctionRequirementRowsEffects.SpineInputs before)
    (closed : SourceCurrentConjunctionRequirementRowsClosed.SpineClosed before)
    (invariant : Invariant origins sources before) :
    ∃ addedOrigins addedSources, Invariant (origins ++ addedOrigins) (sources ++ addedSources) after := by
  cases found : lookupSpine target before with
  | none =>
      rw [SourceCurrentConjunctionRequirementRows.nextRow_missing target before found] at actual
      cases actual
  | some spine =>
      cases spine with
      | done cached =>
          rw [SourceCurrentConjunctionRequirementRows.nextRow_hit target cached before found] at actual
          have returned := Outcome.done.inj actual
          have same : after = before := returned.2.symm
          subst after
          exact ⟨[], [], by simpa only [List.append_nil] using invariant⟩
      | pending tuples =>
          have sourceAt := pending_source invariant found
          have publication := (SourceCurrentConjunctionRequirementRowsPublication.nextRow_publication
            target before origins tuples found ready
            (raw (.pending tuples) (List.mem_of_getElem? found))
            (closed (.pending tuples) (List.mem_of_getElem? found)) invariant.cells).2
          rw [actual] at publication
          cases result with
          | none =>
              obtain ⟨rejected, refined, _, _, spineLength⟩ := publication
              refine ⟨[], [], ?_⟩
              simp only [List.append_nil]
              refine ⟨refined, invariant.length.trans spineLength.symm, ?_⟩
              intro handle original current sourceFound spineFound
              by_cases selected : handle = target
              · subst handle
                have sameSource : original = tuples := Option.some.inj (sourceFound.symm.trans sourceAt)
                have published := SourceCurrentConjunctionRequirementPublication.nextRow_done
                  target before after none actual
                have sameSpine : current = .done none := Option.some.inj (spineFound.symm.trans published)
                rw [sameSpine, sameSource]
                exact rejected
              · have retained := other_spec actual invariant [] [] selected sourceFound spineFound
                simpa only [List.append_nil] using retained
          | some pair =>
              rcases pair with ⟨handles, tail⟩
              obtain ⟨skipped, chosen, rest, _, _, _, _, constraints, split, rejected, _, _, _, live,
                ordered, refined, _, registered, tailIndex, tailPresent, headPresent, _, _, spineLength⟩ := publication
              refine ⟨descriptors chosen constraints, [rest], refined, ?_, ?_⟩
              · simp only [List.length_append, List.length_singleton, invariant.length, spineLength]
              · intro handle original current sourceFound spineFound
                by_cases old : handle < sources.length
                · have originalFound : sources[handle]? = some original := by
                    simpa only [List.getElem?_append_left old] using sourceFound
                  by_cases selected : handle = target
                  · subst handle
                    have sameSource : original = tuples := Option.some.inj (originalFound.symm.trans sourceAt)
                    have sameSpine : current = .done (some (handles, tail)) :=
                      Option.some.inj (spineFound.symm.trans headPresent)
                    rw [sameSpine, sameSource]
                    refine ⟨skipped, chosen, rest, constraints, before.requirements.cells.length,
                      split, rejected, live, ordered, ?_, ?_⟩
                    · intro index cell descriptor
                      exact (registered index cell descriptor).2
                    · rw [tailIndex, ← invariant.length]
                      simp
                  · exact other_spec actual invariant (descriptors chosen constraints) [rest]
                      selected originalFound spineFound
                · have inside := (List.getElem?_eq_some_iff.mp sourceFound).1
                  have atEnd : handle = sources.length := by
                    simp only [List.length_append, List.length_singleton] at inside
                    omega
                  subst handle
                  have sameSource : rest = original := by simpa using sourceFound
                  have tailAtEnd : tail = sources.length := tailIndex.trans invariant.length.symm
                  have fresh : lookupSpine sources.length after = some (.pending rest) := by
                    rw [← tailAtEnd]
                    exact tailPresent
                  have sameSpine : current = .pending rest := Option.some.inj (spineFound.symm.trans fresh)
                  rw [sameSpine]
                  exact sameSource

end MicroCFTA.SourceCurrentConjunctionRequirementRowsSemanticsStep
