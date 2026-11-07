import MicroCFTA.SourceSizedDeterminizationZipTarget

/-!
# Literal target readback from ordered original owners

The source reads original owners from `Map.keys`. That list is distinct
and ascending. Each kernel target filters that list. Its set readback
therefore retains the same list, including its order.

The generated source zip target equals the kernel target under these
input properties. No uniform symbol arity is required. This module does
not prove the native map's representation or the complete public route.
-/
namespace MicroCFTA.SourceSizedDeterminizationTargetReadback
open Language SourceSizedDeterminizationKernel Std

/-- Ascending set readback retains any distinct list that is already ordered. -/
theorem sortedSet_eq_self {State : Type} [DecidableEq State] [Ord State]
    [TransOrd State] [LawfulEqOrd State] (states : List State) (distinct : states.Nodup)
    (ordered : states.Pairwise fun first second => (compare first second).isLE = true) :
    CanonicalClasses.sortedSet states = states := by
  have antisymm : ∀ first second : State,
      (compare first second).isLE = true → (compare second first).isLE = true → first = second := by
    intro first second before after
    apply LawfulEqOrd.eq_of_compare
    exact Ordering.eq_eq_of_isLE_of_isLE_swap before
      (by simpa only [← OrientedOrd.eq_swap] using after)
  apply List.Perm.eq_of_pairwise (fun first second _ _ => antisymm first second)
    (CanonicalClasses.sortedSet_ordered states) ordered
  exact (List.perm_ext_iff_of_nodup (CanonicalClasses.sortedSet_nodup states) distinct).mpr
    (fun state => CanonicalClasses.mem_sortedSet states state)

variable {State Symbol : Type} [DecidableEq State] [DecidableEq Symbol]

/-- A target cannot repeat an owner when the original owner list is distinct. -/
theorem target_nodup (states : List State) (rows : Automaton State Symbol)
    (symbol : Symbol) (keys : List (List State)) (distinct : states.Nodup) :
    (target states rows symbol keys).Nodup :=
  distinct.filter _

/-- A target retains the original owner's ascending order. -/
theorem target_ordered [Ord State] (states : List State) (rows : Automaton State Symbol)
    (symbol : Symbol) (keys : List (List State))
    (ordered : states.Pairwise fun first second => (compare first second).isLE = true) :
    (target states rows symbol keys).Pairwise
      (fun first second => (compare first second).isLE = true) :=
  ordered.filter _

/-- Set construction preserves the literal kernel target from ordered distinct owners. -/
theorem target_readback [Ord State] [TransOrd State] [LawfulEqOrd State]
    (states : List State) (rows : Automaton State Symbol)
    (symbol : Symbol) (keys : List (List State)) (distinct : states.Nodup)
    (ordered : states.Pairwise fun first second => (compare first second).isLE = true) :
    CanonicalClasses.sortedSet (target states rows symbol keys) = target states rows symbol keys :=
  sortedSet_eq_self (target states rows symbol keys)
    (target_nodup states rows symbol keys distinct) (target_ordered states rows symbol keys ordered)

/-- At the token's arity, source set readback equals the literal kernel target. -/
theorem sourceTarget_readback [Ord State] [TransOrd State] [LawfulEqOrd State]
    (states : List State) (rows : Automaton State Symbol)
    (wanted : Symbol × Nat) (keys : List (List State)) (arity : keys.length = wanted.2)
    (distinct : states.Nodup)
    (ordered : states.Pairwise fun first second => (compare first second).isLE = true) :
    SourceSizedDeterminizationZipTarget.sourceTarget states rows wanted keys =
      target states rows wanted.1 keys :=
  (SourceSizedDeterminizationZipTarget.sourceTarget_eq states rows wanted keys arity).trans
    (target_readback states rows wanted.1 keys distinct ordered)

/-- Every generated tuple gives literal source and kernel target equality. -/
theorem generated_source_target_eq [Ord State] [TransOrd State] [LawfulEqOrd State]
    (states : List State) (rows : Automaton State Symbol)
    (distinct : states.Nodup)
    (ordered : states.Pairwise fun first second => (compare first second).isLE = true)
    (fresh : List (List State)) (holding : State → List (List State)) (known : List (List State))
    (wanted : Symbol × Nat) (keys : List (List State))
    (member : keys ∈ SourceSizedDeterminizationOrderedStep.tupleSet states rows fresh holding known wanted) :
    SourceSizedDeterminizationZipTarget.sourceTarget states rows wanted keys =
      target states rows wanted.1 keys :=
  (SourceSizedDeterminizationZipTarget.generated_target_eq
    states rows fresh holding known wanted keys member).trans
    (target_readback states rows wanted.1 keys distinct ordered)

/-- Canonical original owner preparation derives all target readback properties. -/
theorem canonical_target_readback [Ord State] [TransOrd State] [LawfulEqOrd State]
    (states : List State) (rows : Automaton State Symbol)
    (symbol : Symbol) (keys : List (List State)) :
    CanonicalClasses.sortedSet (target (CanonicalClasses.sortedSet states) rows symbol keys) =
      target (CanonicalClasses.sortedSet states) rows symbol keys :=
  target_readback (CanonicalClasses.sortedSet states) rows symbol keys
    (CanonicalClasses.sortedSet_nodup states) (CanonicalClasses.sortedSet_ordered states)

/-- Canonical original owners give literal source target equality for generated tuples. -/
theorem canonical_generated_source_target_eq [Ord State] [TransOrd State] [LawfulEqOrd State]
    (states : List State) (rows : Automaton State Symbol)
    (fresh : List (List State)) (holding : State → List (List State)) (known : List (List State))
    (wanted : Symbol × Nat) (keys : List (List State))
    (member : keys ∈ SourceSizedDeterminizationOrderedStep.tupleSet
      (CanonicalClasses.sortedSet states) rows fresh holding known wanted) :
    SourceSizedDeterminizationZipTarget.sourceTarget (CanonicalClasses.sortedSet states) rows wanted keys =
      target (CanonicalClasses.sortedSet states) rows wanted.1 keys :=
  generated_source_target_eq (CanonicalClasses.sortedSet states) rows
    (CanonicalClasses.sortedSet_nodup states) (CanonicalClasses.sortedSet_ordered states)
    fresh holding known wanted keys member

end MicroCFTA.SourceSizedDeterminizationTargetReadback
