import MicroCFTA.SourcePruningEnumerationRendering
import MicroCFTA.EnumerationExecution

/-!
# Stable fuel bounds for actual native rendering

Every successful native rendering keeps its exact output and final state.
A larger fuel bound retains the same successful execution.
-/
namespace MicroCFTA.SourcePruningEnumerationRendering
open Language Fragments EnumerationState EnumerationCorrectness EnumerationExecution
local notation "Symbol" => SourcePruningTemplates.Symbol
variable {NativeGuard EnumGuard : Type}

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

/-- Concrete fragment rendering retains its exact term and compression state. -/
theorem expandFragment_moreFuel (heap : InternedConstructorTemplates.State Symbol NativeGuard) (marker : Symbol) (fuel extra : Nat)
    (fragment : Fragment Symbol) :
    Retains (expandFragment (EnumGuard := EnumGuard) heap marker fuel fragment) (expandFragment (EnumGuard := EnumGuard) heap marker (fuel + extra) fragment) := by
  induction fuel generalizing fragment with
  | zero =>
      intro before value after success
      exact (success_failure .fuelExhausted before after value success).elim
  | succ fuel ih =>
      rw [Nat.succ_add]
      cases fragment with
      | node symbol children =>
          simp only [expandFragment]
          exact retains_bind _ _ _ _ (retains_mapM _ _ ih children) (fun _ => retains_refl _)
      | hole uv =>
          simp only [expandFragment]
          apply retains_bind _ _ _ _ (by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using getValue_moreFuel (fuel + 1) extra uv)
          intro value
          cases value with
          | eliminated => exact retains_refl _
          | enumerated fragment => exact ih fragment
          | unenumerated node scs => cases node <;> exact retains_refl _

/-- Root rendering retains its exact term and compression state. -/
theorem expandUVar_moreFuel (heap : InternedConstructorTemplates.State Symbol NativeGuard) (marker : Symbol) (fuel extra uv : Nat) :
    Retains (expandUVar (EnumGuard := EnumGuard) heap marker fuel uv) (expandUVar (EnumGuard := EnumGuard) heap marker (fuel + extra) uv) := by
  unfold expandUVar
  apply retains_bind _ _ _ _ (by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using getValue_moreFuel (fuel + 1) extra uv)
  intro value
  cases value with
  | eliminated => exact retains_refl _
  | enumerated fragment => exact expandFragment_moreFuel heap marker fuel extra fragment
  | unenumerated node scs => cases node <;> exact retains_refl _

/-- Native root and residual rendering retain the same result at every larger bound. -/
theorem render_moreFuel (heap : InternedConstructorTemplates.State Symbol NativeGuard)
    (marker : Symbol) (fuel extra uv : Nat) :
    Retains (render (EnumGuard := EnumGuard) heap marker fuel uv)
      (render heap marker (fuel + extra) uv) := by
  unfold render
  apply retains_bind _ _ _ _ (expandUVar_moreFuel heap marker fuel extra uv)
  intro term
  apply retains_bind _ _ _ _ (retains_refl _)
  intro current
  apply retains_bind _ _ _ _ ?_ (fun _ => retains_refl _)
  exact retains_mapM _ _ (fun obligation =>
    retains_bind _ _ _ _ (expandFragment_moreFuel heap marker fuel extra obligation.2)
      (fun _ => retains_refl _)) current.obligations

end MicroCFTA.SourcePruningEnumerationRendering
