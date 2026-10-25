import MicroCFTA.EnumerationPartialObservation

/-!
# Allocated holes in partial renderings

Successful partial rendering preserves storage safety. Every returned hole
names a slot below the unchanged allocation counter.
-/
namespace MicroCFTA.EnumerationPartialBounds
open Language Fragments EnumerationState EnumerationCorrectness EnumerationSchedule
open EnumerationDriver EnumerationCompressionFrame EnumerationExecution

variable {Symbol Guard : Type}

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

mutual
  /-- Every hole in a partial term names an allocated slot. -/
  def TermBound (limit : Nat) : Term (PartialSymbol Symbol) → Prop
    | .node symbol children =>
        (match symbol with
          | .hole uv => uv < limit
          | _ => True) ∧ TermsBound limit children

  /-- Every partial term in the list has allocated holes. -/
  def TermsBound (limit : Nat) : List (Term (PartialSymbol Symbol)) → Prop
    | [] => True
    | child :: rest => TermBound limit child ∧ TermsBound limit rest
end

/-- A list bound also bounds each member. -/
theorem termsBound_member (limit : Nat) (children : List (Term (PartialSymbol Symbol)))
    (bounded : TermsBound limit children) (child : Term (PartialSymbol Symbol))
    (member : child ∈ children) : TermBound limit child := by
  induction children with
  | nil => cases member
  | cons first rest ih =>
      rcases List.mem_cons.mp member with rfl | present
      · exact bounded.1
      · exact ih bounded.2 present

/-- A successful partial render preserves safety and bounds every returned hole. -/
theorem expandPartial_bounded (graph : Graph Symbol Guard) (fuel : Nat)
    (fragment : Fragment Symbol) (before after : State Symbol Guard)
    (term : Term (PartialSymbol Symbol)) (safe : Safe before)
    (allocated : FragmentBound before.counter fragment)
    (success : Success (expandPartial graph fuel fragment) before term after) :
    RenderStable before after ∧ TermBound after.counter term := by
  induction fuel generalizing fragment before after term with
  | zero => exact (success_failure .fuelExhausted before after term success).elim
  | succ fuel ih =>
      cases fragment with
      | node symbol children =>
          change Success (children.mapM (expandPartial graph fuel) >>= fun terms =>
            pure (.node (.concrete symbol) terms)) before term after at success
          obtain ⟨terms, middle, traversed, final⟩ := (success_bind _ _ _ _ _).mp success
          have traversal : ∀ (inputs : List (Fragment Symbol))
              (initial last : State Symbol Guard) (outputs : List (Term (PartialSymbol Symbol))),
              Safe initial → FragmentsBound initial.counter inputs →
              Success (inputs.mapM (expandPartial graph fuel)) initial outputs last →
              RenderStable initial last ∧ TermsBound last.counter outputs := by
            intro inputs
            induction inputs with
            | nil =>
                intro initial last outputs valid _bounded rendered
                obtain ⟨rfl, rfl⟩ := (success_pure [] outputs initial last).mp rendered
                exact ⟨.refl initial valid, trivial⟩
            | cons input rest tailIH =>
                intro initial last outputs valid bounded rendered
                rw [List.mapM_cons] at rendered
                obtain ⟨output, current, first, continued⟩ := (success_bind _ _ _ _ _).mp rendered
                obtain ⟨firstStable, firstBound⟩ :=
                  ih input initial current output valid bounded.1 first
                obtain ⟨remaining, finished, restSuccess, finalPure⟩ :=
                  (success_bind _ _ _ _ _).mp continued
                have restBound : FragmentsBound current.counter rest := by
                  rw [firstStable.counter]
                  exact bounded.2
                obtain ⟨lastStable, lastBound⟩ :=
                  tailIH current finished remaining firstStable.safe restBound restSuccess
                obtain ⟨rfl, rfl⟩ :=
                  (success_pure (output :: remaining) outputs finished last).mp finalPure
                refine ⟨firstStable.trans lastStable, ?_⟩
                exact ⟨by rw [lastStable.counter]; exact firstBound, lastBound⟩
          obtain ⟨stable, bounded⟩ := traversal children before middle terms safe allocated traversed
          obtain ⟨rfl, rfl⟩ :=
            (success_pure (.node (.concrete symbol) terms) term middle after).mp final
          exact ⟨stable, trivial, bounded⟩
      | hole uv =>
          change Success (getValue (fuel + 1) uv >>= fun value => match value with
            | .enumerated stored => expandPartial graph fuel stored
            | .unenumerated (some node) [] => match graph.node node with
              | .recursive _ => pure (.node .truncated [])
              | _ => pure (.node (.hole uv) [])
            | _ => pure (.node (.hole uv) [])) before term after at success
          obtain ⟨value, middle, reading, final⟩ := (success_bind _ _ _ _ _).mp success
          obtain ⟨readStable, valueBound⟩ :=
            getValue_storage (fuel + 1) uv before middle value safe allocated reading
          have holeBound : TermBound (Symbol := Symbol) middle.counter (.node (.hole uv) []) := by
            refine ⟨?_, trivial⟩
            rw [readStable.counter]
            exact allocated
          cases value with
          | eliminated =>
              obtain ⟨rfl, rfl⟩ := (success_pure _ term middle after).mp final
              exact ⟨readStable, holeBound⟩
          | enumerated stored =>
              obtain ⟨stable, bounded⟩ :=
                ih stored middle after term readStable.safe valueBound final
              exact ⟨readStable.trans stable, bounded⟩
          | unenumerated node scs =>
              cases node with
              | none =>
                  obtain ⟨rfl, rfl⟩ := (success_pure _ term middle after).mp final
                  exact ⟨readStable, holeBound⟩
              | some node =>
                  cases scs with
                  | cons first rest =>
                      obtain ⟨rfl, rfl⟩ := (success_pure _ term middle after).mp final
                      exact ⟨readStable, holeBound⟩
                  | nil =>
                      cases view : graph.node node with
                      | recursive body =>
                          simp only [view] at final
                          obtain ⟨rfl, rfl⟩ := (success_pure _ term middle after).mp final
                          exact ⟨readStable, trivial, trivial⟩
                      | empty | alternatives _ | unresolved _ =>
                          simp only [view] at final
                          obtain ⟨rfl, rfl⟩ := (success_pure _ term middle after).mp final
                          exact ⟨readStable, holeBound⟩

end MicroCFTA.EnumerationPartialBounds
