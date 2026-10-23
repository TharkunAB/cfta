import MicroCFTA.EnumerationDriver
import MicroCFTA.EnumerationCPSChecked

namespace MicroCFTA.EnumerationUntilBridge

open Fragments EnumerationState EnumerationCorrectness EnumerationDriver
open EnumerationCPSChecked (successes mem_successes)

local instance : Monad List where
  pure value := [value]
  bind values continuation := values.flatMap continuation

local instance : LawfulMonad List where
  map_const := rfl
  id_map := by intro α xs; simp [Functor.map]
  seqLeft_eq := by
    intros
    simp [SeqLeft.seqLeft, Seq.seq, Functor.map, List.flatMap_map, ← List.map_eq_flatMap]
    simp only [List.map_const']
  seqRight_eq := by
    intros
    simp only [SeqRight.seqRight, Seq.seq, Functor.map, List.flatMap_map]
    simp
  pure_seq := by intros; simp [Seq.seq, Functor.map, pure]
  bind_pure_comp := by intros; simp [bind, pure, Functor.map, ← List.map_eq_flatMap]
  bind_map := by intros; rfl
  pure_bind := by intros; simp [pure, bind]
  bind_assoc := by intros; exact List.flatMap_assoc

/-- Binding preserves the order and multiplicity of successful rows. -/
theorem successes_bind (action : EnumerateM Symbol Guard α)
    (next : α → EnumerateM Symbol Guard β) (before : State Symbol Guard) :
    successes (ExceptT.run ((action >>= next) before)) =
      (successes (ExceptT.run (action before))).flatMap
        (fun pair => successes (ExceptT.run (next pair.1 pair.2))) := by
  rw [run_bind]
  generalize ExceptT.run (action before) = rows
  induction rows with
  | nil => rfl
  | cons row rows ih =>
      simp only [successes] at ih
      cases row <;> simp [successes, ih, List.filterMap_append]

/-- A pure action has one successful row with the original state. -/
theorem successes_pure (value : α) (before : State Symbol Guard) :
    successes (ExceptT.run ((pure value : EnumerateM Symbol Guard α) before)) = [(value, before)] := rfl

/-- Equal continuations on each actual successful branch give equal successful rows. -/
theorem successes_bind_congr (action : EnumerateM Symbol Guard α)
    (left right : α → EnumerateM Symbol Guard β) (before : State Symbol Guard)
    (same : ∀ value after, Success action before value after →
      successes (ExceptT.run (left value after)) = successes (ExceptT.run (right value after))) :
    successes (ExceptT.run ((action >>= left) before)) =
      successes (ExceptT.run ((action >>= right) before)) := by
  rw [successes_bind, successes_bind]
  generalize rowsEq : successes (ExceptT.run (action before)) = rows
  have memberSame : ∀ pair ∈ rows,
      successes (ExceptT.run (left pair.1 pair.2)) = successes (ExceptT.run (right pair.1 pair.2)) := by
    intro pair member
    apply same pair.1 pair.2
    exact (mem_successes _ _ _).mp (rowsEq.symm ▸ member)
  clear rowsEq
  induction rows with
  | nil => rfl
  | cons first rest ih =>
      simp only [List.flatMap_cons]
      rw [memberSame first (by simp), ih (fun pair member => memberSame pair (by simp [member]))]

/-- An action with no successful branch has an empty successful projection. -/
theorem successes_empty (action : EnumerateM Symbol Guard α) (before : State Symbol Guard)
    (absent : ∀ value after, ¬Success action before value after) :
    successes (ExceptT.run (action before)) = [] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro pair member
  exact absent pair.1 pair.2 ((mem_successes _ _ _).mp member)

end MicroCFTA.EnumerationUntilBridge
