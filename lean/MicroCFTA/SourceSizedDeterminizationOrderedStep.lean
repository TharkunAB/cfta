import MicroCFTA.SourceSizedDeterminizationStep
import MicroCFTA.CanonicalClasses

/-!
# Ordered token and tuple readback for determinization

The source iterates its token map in symbol/arity order. Within each
token it reads the tuple set in ascending order. This module constructs
those two finite readbacks and relates the emitted sequence to the
existing round. It retains each tuple once. The final target-map grouping
is a separate operation.
-/
namespace MicroCFTA.SourceSizedDeterminizationOrderedStep
open Language SourceSizedDeterminizationKernel SourceSizedDeterminizationFrontier Std
attribute [local instance] lexOrd

variable {State Symbol : Type} [DecidableEq State] [DecidableEq Symbol]
  [Ord State] [Ord Symbol]

/-- Read token-map keys in ascending symbol and arity order. -/
def tokens (states : List State) (rows : Automaton State Symbol) : List (Symbol × Nat) :=
  (SourceSizedDeterminizationStep.tokens states rows).mergeSort
    fun first second => (compare first second).isLE

/-- Read the set of tuples generated from all members of one token group. -/
def tupleSet (states : List State) (rows : Automaton State Symbol)
    (fresh : List (List State)) (holding : State → List (List State)) (known : List (List State))
    (wanted : Symbol × Nat) : List (List (List State)) :=
  CanonicalClasses.sortedSet
    ((SourceSizedDeterminizationStep.seeds states rows wanted).flatMap (tuples fresh holding known))

/-- The ordered source round reads token keys, then that token's tuple set. -/
def round (states : List State) (rows : Automaton State Symbol)
    (fresh : List (List State)) (holding : State → List (List State)) (known : List (List State)) :
    List (Choice State Symbol) :=
  (tokens states rows).flatMap fun wanted =>
    (tupleSet states rows fresh holding known wanted).map fun keys => (wanted.1, keys)

omit [DecidableEq State] [Ord State] in
/-- Token-map sorting retains exactly the original token inventory. -/
theorem tokens_perm (states : List State) (rows : Automaton State Symbol) :
    (tokens states rows).Perm (SourceSizedDeterminizationStep.tokens states rows) :=
  List.mergeSort_perm _ _

omit [DecidableEq State] [Ord State] in
/-- The source token map reads its symbol/arity keys in ascending order. -/
theorem tokens_ordered [TransOrd Symbol] (states : List State) (rows : Automaton State Symbol) :
    (tokens states rows).Pairwise (fun first second => (compare first second).isLE = true) := by
  apply List.pairwise_mergeSort
  · intro first second third before after
    exact TransOrd.isLE_trans before after
  · intro first second
    have swap := OrientedOrd.eq_swap (a := first) (b := second)
    cases left : compare first second <;> cases right : compare second first <;> simp_all

omit [Ord Symbol] in
/-- Tuple-set readback is a permutation of the deduplicated generated tuples. -/
theorem tupleSet_perm (states : List State) (rows : Automaton State Symbol)
    (fresh : List (List State)) (holding : State → List (List State)) (known : List (List State))
    (wanted : Symbol × Nat) :
    (tupleSet states rows fresh holding known wanted).Perm
      (((SourceSizedDeterminizationStep.seeds states rows wanted).flatMap
        (tuples fresh holding known)).eraseDups) := by
  apply (List.perm_ext_iff_of_nodup (CanonicalClasses.sortedSet_nodup _)
    (SymbolicDriver.eraseDups_nodup _)).mpr
  intro keys
  simp only [CanonicalClasses.mem_sortedSet, List.mem_eraseDups]

omit [Ord Symbol] in
/-- The source tuple set reads its child-subset tuples in ascending order. -/
theorem tupleSet_ordered [TransOrd State] (states : List State) (rows : Automaton State Symbol)
    (fresh : List (List State)) (holding : State → List (List State)) (known : List (List State))
    (wanted : Symbol × Nat) :
    (tupleSet states rows fresh holding known wanted).Pairwise
      (fun first second => (compare first second).isLE = true) :=
  CanonicalClasses.sortedSet_ordered _

private theorem flatMap_permutation {A B : Type} (items : List A) (first second : A → List B)
    (same : ∀ item, (first item).Perm (second item)) :
    (items.flatMap first).Perm (items.flatMap second) := by
  induction items with
  | nil => exact .nil
  | cons item rest ih =>
      exact (same item).append ih

/-- Native token and tuple sorting permutes the existing complete round. -/
theorem round_perm (states : List State) (rows : Automaton State Symbol)
    (fresh : List (List State)) (holding : State → List (List State)) (known : List (List State)) :
    (round states rows fresh holding known).Perm
      (SourceSizedDeterminizationStep.round states rows fresh holding known) := by
  let bucket := fun wanted : Symbol × Nat =>
    (tupleSet states rows fresh holding known wanted).map fun keys => (wanted.1, keys)
  have first := List.Perm.flatMap_right bucket (tokens_perm states rows)
  apply first.trans
  apply flatMap_permutation
  intro wanted
  exact (tupleSet_perm states rows fresh holding known wanted).map _

/-- Ordered emission retains precisely the existing generated choices. -/
theorem mem_round (states : List State) (rows : Automaton State Symbol)
    (fresh : List (List State)) (holding : State → List (List State)) (known : List (List State))
    (choice : Choice State Symbol) :
    choice ∈ round states rows fresh holding known ↔
      choice ∈ SourceSizedDeterminizationStep.round states rows fresh holding known :=
  (round_perm states rows fresh holding known).mem_iff

/-- Sorting never repeats a generated symbol and child tuple. -/
theorem round_distinct (states : List State) (rows : Automaton State Symbol)
    (fresh : List (List State)) (holding : State → List (List State)) (known : List (List State)) :
    (round states rows fresh holding known).Nodup :=
  (round_perm states rows fresh holding known).nodup_iff.mpr
    (SourceSizedDeterminizationStep.round_distinct states rows fresh holding known)

end MicroCFTA.SourceSizedDeterminizationOrderedStep
