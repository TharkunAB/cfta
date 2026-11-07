import MicroCFTA.SourceSizedApiLaws

/-!
# Exact optimized queries from root-local uniqueness

The source can check unambiguity after trimming to one root. Other original
states can remain ambiguous. The optimized API at that root needs distinct
run classes only at that root.

Reference classes form a subsequence of raw run enumeration, including
when guards remove terms. Plain guards and one distinct root class make
that subsequence equal to the complete class. Ranking uses uniqueness
only in the requested root class. No child or global uniqueness is assumed.

The source trim and Boolean gate must still derive root-local uniqueness.
This module does not prove the complete current Sized dispatch or a native
execution bound.
-/
namespace MicroCFTA.SourceSizedRootQueryLaws
open Language RecursiveSize SizedRank SourceSizedDispatcher SourceSizedCandidates

private theorem flatMap_sublist {A B : Type} {before after : List A}
    (sublist : before.Sublist after) (first second : A → List B)
    (each : ∀ item ∈ after, (first item).Sublist (second item)) :
    (before.flatMap first).Sublist (after.flatMap second) := by
  induction after generalizing before with
  | nil => cases sublist; exact .slnil
  | cons item rest ih =>
      cases sublist with
      | cons _ tail =>
          exact (ih tail (fun value present => each value (List.mem_cons_of_mem item present))).trans
            (List.sublist_append_right (second item) (rest.flatMap second))
      | cons_cons _ tail =>
          exact (each item (by simp)).append
            (ih tail (fun value present => each value (List.mem_cons_of_mem item present)))

private theorem dedup_sublist {A : Type} [DecidableEq A] (seen values : List A) :
    (RefinementValidation.dedup seen values).Sublist values := by
  induction values generalizing seen with
  | nil => exact .slnil
  | cons first rest ih =>
      simp only [RefinementValidation.dedup]
      split
      · exact (ih seen).cons first
      · exact (ih (first :: seen)).cons_cons first

private theorem go_sublist {State Symbol : Type}
    (first second : State → Nat → List (Term Symbol)) (states : List State) (remaining : Nat)
    (included : ∀ state size, size ≤ remaining → (first state size).Sublist (second state size)) :
    (go first states remaining).Sublist (go second states remaining) := by
  induction states generalizing remaining with
  | nil => exact .refl _
  | cons current before ih =>
      simp only [go]
      apply flatMap_sublist (.refl _)
      intro left present
      have bound : left ≤ remaining := by have := List.mem_range.mp present; omega
      apply flatMap_sublist
        (ih left (fun state size within => included state size (Nat.le_trans within bound)))
      intro arguments _
      exact (included current (remaining - left) (Nat.sub_le _ _)).map (fun term => term :: arguments)

private theorem candidates_sublist {State Symbol : Type}
    (first second : State → Nat → List (Term Symbol)) (label : Symbol)
    (children : List State) (size : Nat)
    (included : ∀ state childSize, childSize < size →
      (first state childSize).Sublist (second state childSize)) :
    (candidates first label children size).Sublist (candidates second label children size) := by
  cases size with
  | zero => exact .refl _
  | succ remaining =>
      exact (go_sublist first second children.reverse remaining
        (fun state childSize within => included state childSize (by omega))).map
          (fun arguments => Term.node label arguments.reverse)

private theorem enumerate_candidates {State Symbol : Type} (rows : Automaton State Symbol)
    (remaining : Nat) (state : State) :
    RecursiveSize.enumerate rows (remaining + 1) state =
      (rows state).flatMap fun edge =>
        candidates (fun child childSize => RecursiveSize.enumerate rows childSize child)
          edge.label edge.children (remaining + 1) := by
  rw [TablePosition.enumerate_rootForests]
  apply TablePosition.flatMap_congr
  intro edge _
  rw [candidates_succ, TablePosition.rootForests_eq, TablePosition.rooted]

/-- Reference guard filtering and duplicate removal retain the raw run order. -/
theorem classes_sublist_enumerate {State Symbol : Type} [DecidableEq Symbol]
    (rows : Automaton State Symbol) (size : Nat) (state : State) :
    (SourceSizedReference.classes rows size state).Sublist (RecursiveSize.enumerate rows size state) := by
  induction size using Nat.strongRecOn generalizing state with
  | ind size ih =>
      cases size with
      | zero =>
          rw [SourceSizedReference.classes_zero, enumerate_zero]
          exact .refl _
      | succ remaining =>
          rw [SourceSizedReference.classes_succ, SourceSizedReference.classOf, enumerate_candidates]
          apply (dedup_sublist [] _).trans
          apply flatMap_sublist (.refl _)
          intro edge _
          apply List.filter_sublist.trans
          apply candidates_sublist
          intro child childSize smaller
          exact ih childSize smaller child

/-- One distinct root class gives exact reference order without child uniqueness. -/
theorem classes_eq_enumerate_at {State Symbol : Type} [DecidableEq Symbol]
    (rows : Automaton State Symbol) (plain : Decoder.Plain rows) (root : State) (size : Nat)
    (distinct : (RecursiveSize.enumerate rows size root).Nodup) :
    SourceSizedReference.classes rows size root = RecursiveSize.enumerate rows size root := by
  apply (classes_sublist_enumerate rows size root).eq_of_length_le
  apply distinct.length_le_of_subset
  intro term present
  exact (SourceSizedReference.mem_classes_iff rows size root term).mpr
    ((RecursiveSize.mem_enumerate_iff rows plain size root term).mp present)

/-- Distinctness in the replayed root class recovers that class position. -/
theorem termPosition_of_replay_at {State Symbol : Type} [DecidableEq Symbol]
    (rows : Automaton State Symbol) (plain : Decoder.Plain rows) (root : State)
    (position : Position) (term : Term Symbol)
    (distinct : (RecursiveSize.enumerate rows position.size root).Nodup)
    (replayed : replayPosition rows root position = some term) :
    termPosition rows root term = some position := by
  letI : DecidableEq (Term Symbol) := SizedRank.termDecidableEq
  rw [replayPosition, decode_compileAt] at replayed
  obtain ⟨valid, same⟩ := List.getElem?_eq_some_iff.mp replayed
  have sized := (RecursiveSize.mem_enumerate_iff rows plain position.size root term).mp
    (List.mem_of_getElem? replayed)
  rw [termPosition, sized.2]
  have ranked := rankOf_get (RecursiveSize.enumerate rows position.size root)
    distinct position.rank valid
  rw [same] at ranked
  rw [ranked]
  cases position
  rfl

/-- Bottom-up ranking needs distinct classes only at the queried root. -/
theorem positionsOf_eq_termPosition {State Symbol : Type} [DecidableEq Symbol]
    (rows : Automaton State Symbol) (plain : Decoder.Plain rows) (root : State)
    (distinct : ∀ size, (RecursiveSize.enumerate rows size root).Nodup) (term : Term Symbol) :
    TablePosition.positionsOf rows term root = termPosition rows root term := by
  cases computed : TablePosition.positionsOf rows term root with
  | some position =>
      exact (termPosition_of_replay_at rows plain root position term (distinct position.size)
        (TablePosition.positionsOf_replay rows term root position computed)).symm
  | none =>
      cases reference : termPosition rows root term with
      | none => rfl
      | some position =>
          have accepted := (termPosition_exists_iff rows plain root term).mp ⟨position, reference⟩
          obtain ⟨result, found⟩ := TablePosition.positionsOf_complete rows term root accepted
          rw [computed] at found
          cases found

/-- Root-local run uniqueness identifies the complete optimized and reference APIs. -/
theorem optimizedApi_eq_reference {State Symbol : Type} [DecidableEq Symbol]
    (rows : Automaton State Symbol) (plain : Decoder.Plain rows) (root : State)
    (distinct : ∀ size, (RecursiveSize.enumerate rows size root).Nodup) :
    optimizedApi rows root = referenceApi rows root := by
  have reference (size : Nat) := classes_eq_enumerate_at rows plain root size (distinct size)
  change Api.mk _ _ _ _ = Api.mk _ _ _ _
  congr 1
  · funext size
    rw [SourceSizedDispatch.terms_exact, reference_terms_toNat, reference]
  · funext size
    dsimp only [optimizedApi, referenceApi, SourceSizedQueries.countSigned]
    rw [countAt_correct, reference_terms_toNat, reference]
  · funext size rank
    dsimp only [optimizedApi, referenceApi, SourceSizedQueries.unrankSigned]
    rw [SourceSizedDispatch.select_exact, reference_terms_toNat, reference]
    by_cases negative : rank < 0
    · simp [negative, show ¬0 ≤ rank by omega]
    · simp [negative, show 0 ≤ rank by omega]
  · funext term
    change TablePosition.positionsOf rows term root = _
    rw [positionsOf_eq_termPosition rows plain root distinct, termPosition, ← reference]
    rfl

/-- Root-local uniqueness gives every exact signed query law for the root language. -/
theorem optimized_exact {State Symbol : Type} [DecidableEq Symbol]
    (rows : Automaton State Symbol) (plain : Decoder.Plain rows) (root : State)
    (distinct : ∀ size, (RecursiveSize.enumerate rows size root).Nodup)
    (language : Term Symbol → Prop) (correct : ∀ term, Accepts rows root term ↔ language term) :
    SourceSizedApiLaws.Exact (optimizedApi rows root) language := by
  rw [optimizedApi_eq_reference rows plain root distinct]
  exact SourceSizedApiLaws.reference rows root language correct

end MicroCFTA.SourceSizedRootQueryLaws
