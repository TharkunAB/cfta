import MicroCFTA.SourceSizedTrimRunClasses
import MicroCFTA.SourceSizedStructuralKeys

/-!
# Raw run multiplicity under row permutations

Changing each state's transition order permutes each complete raw size
class. It does not add or remove runs. This result allows arbitrary guards
and needs no plainness or uniqueness premise.

Root-local uniqueness therefore survives the actual canonical row sort.
The source trim and Boolean unambiguity gate must still derive the input
root's uniqueness. Native storage and resource bounds remain separate.
-/
namespace MicroCFTA.SourceSizedRunPermutation
open Language RecursiveSize SourceSizedCandidates SourceSizedDecided SourceSizedFiniteKeys Std

private theorem flatMap_permutation {A B : Type} (items : List A) (first second : A → List B)
    (same : ∀ item ∈ items, (first item).Perm (second item)) :
    (items.flatMap first).Perm (items.flatMap second) := by
  induction items with
  | nil => exact .nil
  | cons item rest ih =>
      exact (same item (by simp)).append
        (ih (fun value present => same value (List.mem_cons_of_mem item present)))

private theorem go_permutation {State Symbol : Type}
    (first second : State → Nat → List (Term Symbol)) (states : List State) (remaining : Nat)
    (same : ∀ state size, size ≤ remaining → (first state size).Perm (second state size)) :
    (go first states remaining).Perm (go second states remaining) := by
  induction states generalizing remaining with
  | nil => exact .refl _
  | cons current before ih =>
      simp only [go]
      apply flatMap_permutation
      intro left present
      have bound : left ≤ remaining := by have := List.mem_range.mp present; omega
      have prefixes := ih left (fun state size within => same state size (Nat.le_trans within bound))
      apply (List.Perm.flatMap_right
        (fun arguments => (first current (remaining - left)).map (fun term => term :: arguments)) prefixes).trans
      apply flatMap_permutation
      intro arguments _
      exact (same current (remaining - left) (Nat.sub_le _ _)).map (fun term => term :: arguments)

private theorem candidates_permutation {State Symbol : Type}
    (first second : State → Nat → List (Term Symbol)) (label : Symbol)
    (children : List State) (size : Nat)
    (same : ∀ state childSize, childSize < size → (first state childSize).Perm (second state childSize)) :
    (candidates first label children size).Perm (candidates second label children size) := by
  cases size with
  | zero => exact .refl _
  | succ remaining =>
      exact (go_permutation first second children.reverse remaining
        (fun state childSize within => same state childSize (by omega))).map
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

/-- Per-state transition permutations preserve each raw run class's multiplicity. -/
theorem enumerate_permutation {State Symbol : Type} (first second : Automaton State Symbol)
    (rowPermutation : ∀ state, (first state).Perm (second state)) (size : Nat) (state : State) :
    (RecursiveSize.enumerate first size state).Perm (RecursiveSize.enumerate second size state) := by
  induction size using Nat.strongRecOn generalizing state with
  | ind size ih =>
      cases size with
      | zero => rw [enumerate_zero, enumerate_zero]
      | succ remaining =>
          rw [enumerate_candidates, enumerate_candidates]
          apply (List.Perm.flatMap_right
            (fun edge => candidates (fun child childSize => RecursiveSize.enumerate first childSize child)
              edge.label edge.children (remaining + 1)) (rowPermutation state)).trans
          apply flatMap_permutation
          intro edge _
          apply candidates_permutation
          intro child childSize smaller
          exact ih childSize smaller child

/-- A root size class is distinct before row reordering exactly when it is distinct afterward. -/
theorem enumerate_nodup_iff {State Symbol : Type} (first second : Automaton State Symbol)
    (rowPermutation : ∀ state, (first state).Perm (second state)) (size : Nat) (state : State) :
    (RecursiveSize.enumerate first size state).Nodup ↔
      (RecursiveSize.enumerate second size state).Nodup :=
  (enumerate_permutation first second rowPermutation size state).nodup_iff

/-- Root-local uniqueness transfers through every per-state row permutation. -/
theorem root_unique {State Symbol : Type} (first second : Automaton State Symbol)
    (rowPermutation : ∀ state, (first state).Perm (second state)) (root : State)
    (unique : ∀ size, (RecursiveSize.enumerate second size root).Nodup) :
    ∀ size, (RecursiveSize.enumerate first size root).Nodup :=
  fun size => (enumerate_nodup_iff first second rowPermutation size root).mpr (unique size)

variable {State Symbol Payload : Type} [DecidableEq State] [Ord State]
  [DecidableEq Symbol] [Ord Symbol]

/-- The actual canonical sort preserves every raw original-table run with its multiplicity. -/
theorem nativeSorted_enumerate (table : Table State Symbol Payload) (root : State)
    (success : SourceFTAValidation.validateRows root (interpreted table (fun _ _ => true)) =
      .ok (interpreted table (fun _ _ => true)))
    (holds : Payload → Term Symbol → Bool) (size : Nat) (state : State) :
    (RecursiveSize.enumerate (automaton (SourceSizedStructuralKeys.nativeSorted table root success) holds)
      size state).Perm
        (RecursiveSize.enumerate (automaton (SourceSizedFiniteKeys.lookup table) holds) size state) :=
  enumerate_permutation _ _
    (fun current => (SourceSizedStructuralKeys.nativeSorted_perm table root success current).map (Row.edge holds))
    size state

/-- Canonical sorting needs only original root uniqueness for the optimized count table. -/
theorem nativeSorted_root_unique (table : Table State Symbol Payload) (root : State)
    (success : SourceFTAValidation.validateRows root (interpreted table (fun _ _ => true)) =
      .ok (interpreted table (fun _ _ => true)))
    (holds : Payload → Term Symbol → Bool)
    (unique : ∀ size,
      (RecursiveSize.enumerate (automaton (SourceSizedFiniteKeys.lookup table) holds) size root).Nodup) :
    ∀ size,
      (RecursiveSize.enumerate (automaton (SourceSizedStructuralKeys.nativeSorted table root success) holds)
        size root).Nodup :=
  fun size => (nativeSorted_enumerate table root success holds size root).nodup_iff.mpr (unique size)

end MicroCFTA.SourceSizedRunPermutation
