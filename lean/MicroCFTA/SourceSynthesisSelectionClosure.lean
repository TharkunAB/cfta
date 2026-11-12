import MicroCFTA.SourceSynthesisSelections
import Init.Data.List.Perm

/-!
# Closure of actual source selections under take and drop

The proofs retain the literal GHC-order subsequence and permutation workers.
They preserve occurrences when values or names repeat. The source's closed
root lookup theorem remains unchanged. These laws close child keys formed
from actual resolver winners. They do not identify those winners with the
supplied row slices or prove source-table construction totality.
-/
namespace MicroCFTA.SourceSynthesisSelectionClosure
open SourceSynthesisSelections

variable {α β : Type}

private theorem fold_subsequences_member (value : α) (entries : List (List α)) (output : List α) :
    output ∈ entries.foldr (fun selected later => selected :: (value :: selected) :: later) [] ↔
      ∃ selected ∈ entries, output = selected ∨ output = value :: selected := by
  induction entries with
  | nil => simp
  | cons first rest ih =>
      change output ∈ first :: (value :: first) ::
        rest.foldr (fun selected later => selected :: (value :: selected) :: later) [] ↔ _
      conv => lhs; rw [List.mem_cons, List.mem_cons, ih]
      constructor
      · rintro (same | same | ⟨selected, member, chosen⟩)
        · exact ⟨first, List.mem_cons_self, .inl same⟩
        · exact ⟨first, List.mem_cons_self, .inr same⟩
        · exact ⟨selected, List.mem_cons_of_mem _ member, chosen⟩
      · rintro ⟨selected, member, chosen⟩
        rcases List.mem_cons.mp member with rfl | member
        · rcases chosen with same | same
          · exact .inl same
          · exact .inr (.inl same)
        · exact .inr (.inr ⟨selected, member, chosen⟩)

/-- The literal source subsequences are exactly the occurrence-preserving sublists. -/
theorem subsequences_spec (inputs selected : List α) :
    selected ∈ subsequences inputs ↔ selected.Sublist inputs := by
  induction inputs generalizing selected with
  | nil => simp [subsequences, nonEmptySubsequences]
  | cons first rest ih =>
      constructor
      · intro member
        rw [subsequences, nonEmptySubsequences] at member
        rcases List.mem_cons.mp member with rfl | member
        · exact List.nil_sublist _
        · rcases List.mem_cons.mp member with rfl | member
          · exact (List.nil_sublist rest).cons_cons first
          · obtain ⟨tail, included, chosen⟩ := (fold_subsequences_member first _ selected).mp member
            have part := (ih tail).mp (List.mem_cons_of_mem _ included)
            rcases chosen with rfl | rfl
            · exact part.cons first
            · exact part.cons_cons first
      · intro part
        rcases List.sublist_cons_iff.mp part with skipped | ⟨tail, rfl, included⟩
        · have member := (ih selected).mpr skipped
          rcases List.mem_cons.mp member with rfl | member
          · exact nil_mem_subsequences _
          · rw [subsequences, nonEmptySubsequences]
            apply List.mem_cons_of_mem
            apply List.mem_cons_of_mem
            exact (fold_subsequences_member first _ selected).mpr ⟨selected, member, .inl rfl⟩
        · have member := (ih tail).mpr included
          rcases List.mem_cons.mp member with rfl | member
          · rw [subsequences, nonEmptySubsequences]
            exact List.mem_cons_of_mem _ List.mem_cons_self
          · rw [subsequences, nonEmptySubsequences]
            apply List.mem_cons_of_mem
            apply List.mem_cons_of_mem
            exact (fold_subsequences_member first _ (first :: tail)).mpr ⟨tail, member, .inr rfl⟩

private theorem interleaveAux_fst (value : α) (suffix selected : List α)
    (initial : List α → β) (later : List β) :
    (interleaveAux value suffix initial selected later).1 = selected ++ suffix := by
  induction selected generalizing initial with
  | nil => rfl
  | cons first rest ih => simp only [interleaveAux, ih, List.cons_append]

private theorem interleaveAux_member (value : α) (suffix selected : List α)
    (initial : List α → β) (later : List β) (output : β) :
    output ∈ (interleaveAux value suffix initial selected later).2 ↔
      output ∈ later ∨ ∃ before after, selected = before ++ after ∧ after ≠ [] ∧
        output = initial (before ++ value :: (after ++ suffix)) := by
  induction selected generalizing initial with
  | nil => simp [interleaveAux]
  | cons first rest ih =>
      rw [interleaveAux]
      simp only [interleaveAux_fst, List.mem_cons, ih]
      constructor
      · rintro (same | member | ⟨before, after, restEq, nonempty, same⟩)
        · exact .inr ⟨[], first :: rest, rfl, by simp, same⟩
        · exact .inl member
        · exact .inr ⟨first :: before, after, congrArg (List.cons first) restEq, nonempty, same⟩
      · rintro (member | ⟨before, after, selectedEq, nonempty, same⟩)
        · exact .inr (.inl member)
        · cases before with
          | nil =>
              have afterEq : first :: rest = after := selectedEq
              subst after
              exact .inl same
          | cons head tail =>
              have parts := List.cons.inj selectedEq
              have headEq := parts.1
              subst head
              exact .inr (.inr ⟨tail, after, parts.2, nonempty, same⟩)

private theorem interleave_member (value : α) (suffix selected : List α)
    (later : List (List α)) (output : List α) :
    output ∈ interleave value suffix selected later ↔
      output ∈ later ∨ ∃ before after, selected = before ++ after ∧ after ≠ [] ∧
        output = before ++ value :: (after ++ suffix) := by
  exact interleaveAux_member value suffix selected id later output

private theorem fold_interleave_member (value : α) (suffix : List α)
    (entries later : List (List α)) (output : List α) :
    output ∈ entries.foldr (interleave value suffix) later ↔
      output ∈ later ∨ ∃ selected ∈ entries, ∃ before after,
        selected = before ++ after ∧ after ≠ [] ∧ output = before ++ value :: (after ++ suffix) := by
  induction entries with
  | nil => simp
  | cons first rest ih =>
      change output ∈ interleave value suffix first (rest.foldr (interleave value suffix) later) ↔ _
      rw [interleave_member, ih]
      constructor
      · rintro ((member | ⟨selected, included, inserted⟩) | inserted)
        · exact .inl member
        · exact .inr ⟨selected, List.mem_cons_of_mem _ included, inserted⟩
        · exact .inr ⟨first, List.mem_cons_self, inserted⟩
      · rintro (member | ⟨selected, included, inserted⟩)
        · exact .inl (.inl member)
        · rcases List.mem_cons.mp included with rfl | included
          · exact .inr inserted
          · exact .inl (.inr ⟨selected, included, inserted⟩)

private theorem permutations_spec_aux (size : Nat) :
    ∀ inputs output : List α, inputs.length = size →
      (output ∈ permutations inputs ↔ output.Perm inputs) := by
  induction size using Nat.strongRecOn with
  | ind size ih =>
      intro inputs output sizeEq
      have worker : ∀ suffix accumulated : List α, suffix.length + accumulated.length = size →
          (∀ result, result ∈ perms suffix accumulated → result.Perm (accumulated ++ suffix)) ∧
          (∀ result, result.Perm (accumulated ++ suffix) →
            (∃ front, front.Perm accumulated ∧ result = front ++ suffix) ∨
              result ∈ perms suffix accumulated) := by
        intro suffix
        induction suffix with
        | nil =>
            intro accumulated _sameSize
            constructor
            · intro result member
              rw [perms] at member
              cases member
            · intro result permuted
              exact .inl ⟨result, by simpa only [List.append_nil] using permuted, by simp⟩
        | cons value rest recursiveIH =>
            intro accumulated sameSize
            have shorter : accumulated.length < size := by simp only [List.length_cons] at sameSize; omega
            have accumulatedSpec (selected : List α) :
                selected ∈ permutations accumulated ↔ selected.Perm accumulated :=
              ih accumulated.length shorter accumulated selected rfl
            have recursive := recursiveIH (value :: accumulated) (by
              simp only [List.length_cons] at sameSize ⊢
              omega)
            constructor
            · intro result member
              rw [perms, fold_interleave_member] at member
              rcases member with later | ⟨selected, included, before, after, selectedEq, _nonempty, resultEq⟩
              · have permuted := recursive.1 result later
                exact permuted.trans (List.perm_middle (a := value) (l₁ := accumulated) (l₂ := rest)).symm
              · have selectedPerm := (accumulatedSpec selected).mp included
                rw [selectedEq] at selectedPerm
                subst result
                have moved : (before ++ value :: (after ++ rest)).Perm
                    (value :: ((before ++ after) ++ rest)) := by
                  simpa only [List.append_assoc] using
                    (List.perm_middle (a := value) (l₁ := before) (l₂ := after ++ rest))
                exact (moved.trans ((selectedPerm.append_right rest).cons value)).trans
                  (List.perm_middle (a := value) (l₁ := accumulated) (l₂ := rest)).symm
            · intro result permuted
              have moved : result.Perm ((value :: accumulated) ++ rest) :=
                permuted.trans (List.perm_middle (a := value) (l₁ := accumulated) (l₂ := rest))
              rcases recursive.2 result moved with ⟨front, frontPerm, resultEq⟩ | later
              · have present : value ∈ front := frontPerm.symm.subset List.mem_cons_self
                obtain ⟨before, after, frontEq⟩ := List.append_of_mem present
                have selectedPerm : (before ++ value :: after).Perm (value :: accumulated) := by
                  rw [← frontEq]
                  exact frontPerm
                have removed : (before ++ after).Perm accumulated :=
                  ((List.perm_middle (a := value) (l₁ := before) (l₂ := after)).symm.trans selectedPerm).cons_inv
                cases after with
                | nil =>
                    refine .inl ⟨before, ?_, ?_⟩
                    · simpa only [List.append_nil] using removed
                    · simp only [resultEq, frontEq, List.append_assoc, List.cons_append, List.nil_append]
                | cons first remaining =>
                    apply Or.inr
                    rw [perms, fold_interleave_member]
                    refine .inr ⟨before ++ first :: remaining, (accumulatedSpec _).mpr removed,
                      before, first :: remaining, rfl, by simp, ?_⟩
                    simp only [resultEq, frontEq, List.append_assoc, List.cons_append]
              · apply Or.inr
                rw [perms, fold_interleave_member]
                exact .inl later
      have checked := worker inputs [] (by simpa only [List.length_nil, Nat.add_zero] using sizeEq)
      constructor
      · intro member
        rw [permutations] at member
        rcases List.mem_cons.mp member with rfl | member
        · exact .refl _
        · exact checked.1 output member
      · intro permuted
        rcases checked.2 output permuted with ⟨front, frontPerm, same⟩ | member
        · have empty := frontPerm.eq_nil
          subst front
          have outputEq : output = inputs := same
          subst output
          exact self_mem_permutations inputs
        · rw [permutations]
          exact List.mem_cons_of_mem _ member

/-- The literal source permutation worker enumerates exactly the List.Perm relation. -/
theorem permutations_spec (inputs output : List α) :
    output ∈ permutations inputs ↔ output.Perm inputs :=
  permutations_spec_aux inputs.length inputs output rfl

/-- An actual selection permutes one occurrence-preserving sublist of the input. -/
theorem selections_spec (inputs selected : List (String × α)) :
    selected ∈ selections inputs ↔ ∃ subset, subset.Sublist inputs ∧ selected.Perm subset := by
  constructor
  · intro member
    obtain ⟨subset, included, permuted⟩ := List.mem_flatMap.mp member
    exact ⟨subset, (subsequences_spec inputs subset).mp included,
      (permutations_spec subset selected).mp permuted⟩
  · rintro ⟨subset, included, permuted⟩
    exact mem_selections inputs subset selected ((subsequences_spec inputs subset).mpr included)
      ((permutations_spec subset selected).mpr permuted)

/-- Every sublist of an actual selection is another actual source selection. -/
theorem selections_sublist_closed (inputs winner child : List (String × α))
    (member : winner ∈ selections inputs) (part : child.Sublist winner) :
    child ∈ selections inputs := by
  obtain ⟨subset, subsetPart, permuted⟩ := (selections_spec inputs winner).mp member
  obtain ⟨picked, pickedPerm, pickedPart⟩ := List.exists_perm_sublist part permuted
  exact (selections_spec inputs child).mpr ⟨picked, pickedPart.trans subsetPart, pickedPerm.symm⟩

/-- Taking any prefix of an actual selection retains an actual table key. -/
theorem take_mem_selections (inputs winner : List (String × α))
    (member : winner ∈ selections inputs) (offset : Nat) : winner.take offset ∈ selections inputs :=
  selections_sublist_closed inputs winner (winner.take offset) member (List.take_sublist offset winner)

/-- Dropping any prefix of an actual selection retains an actual table key. -/
theorem drop_mem_selections (inputs winner : List (String × α))
    (member : winner ∈ selections inputs) (offset : Nat) : winner.drop offset ∈ selections inputs :=
  selections_sublist_closed inputs winner (winner.drop offset) member (List.drop_sublist offset winner)

/-- Both recursive names-only keys resolve after splitting an actual last winner. -/
theorem resolveSelection_take_drop (inputs : List (String × α)) (names : List String)
    (winner : List (String × α)) (resolved : resolveSelection inputs names = some winner) (offset : Nat) :
    (∃ leftWinner, resolveSelection inputs ((winner.take offset).map Prod.fst) = some leftWinner) ∧
    (∃ rightWinner, resolveSelection inputs ((winner.drop offset).map Prod.fst) = some rightWinner) := by
  have member := (resolveSelection_spec inputs names winner resolved).1
  exact ⟨resolveSelection_exists inputs (winner.take offset) (take_mem_selections inputs winner member offset),
    resolveSelection_exists inputs (winner.drop offset) (drop_mem_selections inputs winner member offset)⟩

end MicroCFTA.SourceSynthesisSelectionClosure
