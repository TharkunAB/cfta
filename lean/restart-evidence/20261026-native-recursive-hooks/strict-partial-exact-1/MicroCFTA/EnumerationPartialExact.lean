import MicroCFTA.EnumerationPartialObservation

namespace MicroCFTA.EnumerationPartialExact
open Language Fragments EnumerationState EnumerationCorrectness EnumerationSchedule

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

variable {Symbol Guard α β : Type}

private theorem pure_exact (value result : α) (before after : State Symbol Guard)
    (success : Success (pure value) before result after) :
    ExceptT.run ((pure value : EnumerateM Symbol Guard α) before) = [.ok (result, after)] := by
  obtain ⟨rfl, rfl⟩ := (success_pure value result before after).mp success
  rfl

private theorem mapM_exact (action : α → EnumerateM Symbol Guard β) (inputs : List α)
    (step : ∀ input before output after, Success (action input) before output after →
      ExceptT.run (action input before) = [.ok (output, after)])
    (before after : State Symbol Guard) (outputs : List β)
    (success : Success (inputs.mapM action) before outputs after) :
    ExceptT.run ((inputs.mapM action) before) = [.ok (outputs, after)] := by
  induction inputs generalizing before after outputs with
  | nil => exact pure_exact [] outputs before after success
  | cons input rest ih =>
      rw [List.mapM_cons] at success ⊢
      obtain ⟨output, middle, first, continued⟩ := (success_bind _ _ _ _ _).mp success
      obtain ⟨tail, last, remaining, finished⟩ := (success_bind _ _ _ _ _).mp continued
      rw [bind_single _ _ _ _ _ (step input before output middle first)]
      rw [bind_single _ _ _ _ _ (ih middle last tail remaining)]
      exact pure_exact (output :: tail) outputs last after finished

/-- An actual successful representative read has one exact raw result. -/
theorem representative_success_exact (fuel uv : Nat) (before after : State Symbol Guard)
    (root : Nat) (success : Success (representative fuel uv) before root after) :
    ExceptT.run (representative fuel uv before) = [.ok (root, after)] := by
  obtain ⟨found, lookup, rfl, rfl⟩ := (representative_success fuel uv before after root).mp success
  exact representative_exact fuel uv before found lookup

/-- An actual successful value read has one exact raw result without a totality premise. -/
theorem getValue_exact (fuel uv : Nat) (before after : State Symbol Guard)
    (value : UVarValue Symbol) (success : Success (getValue fuel uv) before value after) :
    ExceptT.run (getValue fuel uv before) = [.ok (value, after)] := by
  obtain ⟨found, lookup, stored, rfl⟩ := (getValue_success fuel uv before after value).mp success
  unfold getValue
  rw [bind_single _ _ _ _ _ (representative_exact fuel uv before found lookup)]
  change (match before.values[found.representative]? with
    | none => [Except.error Error.invalidSlot]
    | some observed => [.ok (observed, {before with representatives := found.forest})]) = _
  rw [stored]

/-- An actual successful partial render has one exact raw term and final state. -/
theorem expandPartial_exact (graph : Graph Symbol Guard) (fuel : Nat)
    (fragment : Fragment Symbol) (before after : State Symbol Guard)
    (term : Term (PartialSymbol Symbol))
    (success : Success (expandPartial graph fuel fragment) before term after) :
    ExceptT.run (expandPartial graph fuel fragment before) = [.ok (term, after)] := by
  induction fuel generalizing fragment before after term with
  | zero => exact (success_failure .fuelExhausted before after term success).elim
  | succ fuel ih =>
      cases fragment with
      | node symbol children =>
          change Success (children.mapM (expandPartial graph fuel) >>= fun terms =>
            pure (.node (.concrete symbol) terms)) before term after at success
          change ExceptT.run ((children.mapM (expandPartial graph fuel) >>= fun terms =>
            pure (.node (.concrete symbol) terms)) before) = [.ok (term, after)]
          obtain ⟨terms, middle, traversed, finished⟩ := (success_bind _ _ _ _ _).mp success
          have exactChildren := mapM_exact (expandPartial graph fuel) children
            (fun child previous output next reading => ih child previous next output reading)
            before middle terms traversed
          rw [bind_single _ _ _ _ _ exactChildren]
          exact pure_exact (.node (.concrete symbol) terms) term middle after finished
      | hole uv =>
          change Success (getValue (fuel + 1) uv >>= fun value => match value with
            | .enumerated stored => expandPartial graph fuel stored
            | .unenumerated (some node) [] => match graph.node node with
              | .recursive _ => pure (.node .truncated [])
              | _ => pure (.node (.hole uv) [])
            | _ => pure (.node (.hole uv) [])) before term after at success
          change ExceptT.run ((getValue (fuel + 1) uv >>= fun value => match value with
            | .enumerated stored => expandPartial graph fuel stored
            | .unenumerated (some node) [] => match graph.node node with
              | .recursive _ => pure (.node .truncated [])
              | _ => pure (.node (.hole uv) [])
            | _ => pure (.node (.hole uv) [])) before) = [.ok (term, after)]
          obtain ⟨value, middle, reading, finished⟩ := (success_bind _ _ _ _ _).mp success
          rw [bind_single _ _ _ _ _ (getValue_exact (fuel + 1) uv before middle value reading)]
          cases value with
          | eliminated => exact pure_exact _ term middle after finished
          | enumerated stored => exact ih stored middle after term finished
          | unenumerated node scs =>
              cases node with
              | none => exact pure_exact _ term middle after finished
              | some node =>
                  cases scs with
                  | cons first rest => exact pure_exact _ term middle after finished
                  | nil =>
                      cases view : graph.node node <;> simp only [view] at finished ⊢ <;>
                        exact pure_exact _ term middle after finished

end MicroCFTA.EnumerationPartialExact
