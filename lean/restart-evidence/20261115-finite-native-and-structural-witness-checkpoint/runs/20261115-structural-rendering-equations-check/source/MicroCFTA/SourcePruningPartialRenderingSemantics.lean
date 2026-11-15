import MicroCFTA.SourcePruningPartialMatchSemantics
import MicroCFTA.EnumerationPartialObservation
import MicroCFTA.SourcePruningEnumerationNativeLanguage

/-!
# Original assignment completions of actual partial rendering

Stored fragment equations interpret actual reads and raw holes.
Truncation remains opaque and can have any assigned complete term.
-/
namespace MicroCFTA.SourcePruningPartialRenderingSemantics
open Language Fragments EnumerationState EnumerationCorrectness EnumerationCompressionFrame
open SourcePruningPartialMatch
local notation "Symbol" => SourcePruningTemplates.Symbol
variable {Guard : Type}

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

/-- UF aliases and stored fragments determine the structural equations. -/
def StoredEquations (assignment : Nat → Term Symbol) (state : State Symbol Guard) : Prop :=
  UnionFind.Satisfies state.representatives assignment ∧
    ∀ uv fragment, state.values[uv]? = some (.enumerated fragment) →
      fill assignment fragment = assignment uv

/-- A read frame preserves UF aliases and every stored fragment equation. -/
theorem storedEquations_frame (assignment : Nat → Term Symbol)
    (before after : State Symbol Guard) (frame : Frame before after) :
    StoredEquations assignment after ↔ StoredEquations assignment before := by
  have forestSame : UnionFind.Satisfies after.representatives assignment ↔
      UnionFind.Satisfies before.representatives assignment := by
    constructor
    · intro satisfied left right related
      exact satisfied left right
        ((SourcePruningEnumerationNativeLanguage.frame_sameClass before after frame left right).mpr related)
    · intro satisfied left right related
      exact satisfied left right
        ((SourcePruningEnumerationNativeLanguage.frame_sameClass before after frame left right).mp related)
  simp only [StoredEquations, frame.values, forestSame]

/-- A full semantic model includes the structural equations. -/
theorem satisfies_storedEquations (language : NodeLanguage Symbol)
    (meaning : Guard → Term Symbol → Prop) (assignment : Nat → Term Symbol)
    (state : State Symbol Guard) (satisfied : Satisfies language meaning assignment state) :
    StoredEquations assignment state := by
  refine ⟨satisfied.1.1, ?_⟩
  intro uv fragment stored
  simpa only [EnumerationCorrectness.heap, stored, Option.getD_some, slot, slotSatisfies]
    using satisfied.1.2 uv

/-- Stored equations suffice to complete the actual partial rendering. -/
theorem expandPartial_completes_of_stored_equations (graph : Graph Symbol Guard)
    (assignment : Nat → Term Symbol) (fuel : Nat) (fragment : Fragment Symbol)
    (before after : State Symbol Guard) (observedTerm : Term (PartialSymbol Symbol))
    (total : UnionFind.Total before.representatives)
    (satisfied : StoredEquations assignment before)
    (success : Success (expandPartial graph fuel fragment) before observedTerm after) :
    Completes assignment observedTerm (fill assignment fragment) := by
  induction fuel generalizing fragment before after observedTerm with
  | zero => exact (success_failure .fuelExhausted before after observedTerm success).elim
  | succ fuel ih =>
      cases fragment with
      | node symbol children =>
          change Success (children.mapM (expandPartial graph fuel) >>= fun terms =>
            pure (.node (.concrete symbol) terms)) before observedTerm after at success
          obtain ⟨partials, middle, traversed, final⟩ := (success_bind _ _ _ _ _).mp success
          obtain ⟨rfl, rfl⟩ := (success_pure _ observedTerm middle after).mp final
          have completed : ∀ (children : List (Fragment Symbol))
              (before after : State Symbol Guard) (partials : List (Term (PartialSymbol Symbol))),
              UnionFind.Total before.representatives → StoredEquations assignment before →
              Success (children.mapM (expandPartial graph fuel)) before partials after →
              All₂ (Completes assignment) partials (children.map (fill assignment)) := by
            intro children
            induction children with
            | nil =>
                intro before after partials _total _satisfied traversed
                obtain ⟨rfl, _same⟩ := (success_pure [] partials before after).mp traversed
                exact .nil
            | cons child rest restIH =>
                intro before after partials total satisfied traversed
                rw [List.mapM_cons] at traversed
                obtain ⟨first, middle, firstRead, continued⟩ := (success_bind _ _ _ _ _).mp traversed
                obtain ⟨remaining, last, restRead, final⟩ := (success_bind _ _ _ _ _).mp continued
                obtain ⟨rfl, _same⟩ := (success_pure (first :: remaining) partials last after).mp final
                have frame := EnumerationObservations.expandPartial_frame graph fuel child before middle first total firstRead
                have middleSatisfied := (storedEquations_frame assignment before middle frame).mpr satisfied
                exact .cons (ih child before middle first total satisfied firstRead)
                  (restIH middle last remaining (frame.total total) middleSatisfied restRead)
          simpa only [fill] using (Completes.concrete symbol partials (children.map (fill assignment))
            (completed children before after partials total satisfied traversed))
      | hole uv =>
          simp only [expandPartial] at success
          obtain ⟨value, middle, reading, final⟩ := (success_bind _ _ _ _ _).mp success
          obtain ⟨frame, root, size, path, _afterPath, stored⟩ :=
            getValue_frame (fuel + 1) uv before middle value total reading
          cases value with
          | enumerated fragment =>
              have equation : fill assignment fragment = assignment uv := by
                have rootEquation : fill assignment fragment = assignment root := by
                  exact satisfied.2 root fragment stored
                exact rootEquation.trans (satisfied.1 uv root (UnionFind.sameClass_root path)).symm
              have middleSatisfied := (storedEquations_frame assignment before middle frame).mpr satisfied
              have completed := ih fragment middle after observedTerm (frame.total total) middleSatisfied final
              simpa only [fill, equation] using completed
          | eliminated =>
              obtain ⟨rfl, _same⟩ := (success_pure _ observedTerm middle after).mp final
              simpa only [fill] using (Completes.hole (assignment := assignment) uv)
          | unenumerated node scs =>
              cases node with
              | none =>
                  obtain ⟨rfl, _same⟩ := (success_pure _ observedTerm middle after).mp final
                  simpa only [fill] using (Completes.hole (assignment := assignment) uv)
              | some node =>
                  cases scs with
                  | cons first rest =>
                      obtain ⟨rfl, _same⟩ := (success_pure _ observedTerm middle after).mp final
                      simpa only [fill] using (Completes.hole (assignment := assignment) uv)
                  | nil =>
                      cases view : graph.node node <;> simp only [view] at final
                      all_goals
                        obtain ⟨rfl, _same⟩ := (success_pure _ observedTerm middle after).mp final
                        first
                        | simpa only [fill] using (Completes.hole (assignment := assignment) uv)
                        | simpa only [fill] using (Completes.truncated (assignment := assignment) [] (assignment uv))

/-- Actual partial rendering represents the same original completed fragment. -/
theorem expandPartial_completes (graph : Graph Symbol Guard)
    (language : NodeLanguage Symbol) (meaning : Guard → Term Symbol → Prop)
    (assignment : Nat → Term Symbol) (fuel : Nat) (fragment : Fragment Symbol)
    (before after : State Symbol Guard) (observedTerm : Term (PartialSymbol Symbol))
    (total : UnionFind.Total before.representatives)
    (satisfied : Satisfies language meaning assignment before)
    (success : Success (expandPartial graph fuel fragment) before observedTerm after) :
    Completes assignment observedTerm (fill assignment fragment) := by
  exact expandPartial_completes_of_stored_equations graph assignment fuel fragment before after
    observedTerm total (satisfies_storedEquations language meaning assignment before satisfied) success

end MicroCFTA.SourcePruningPartialRenderingSemantics

#check @MicroCFTA.SourcePruningPartialRenderingSemantics.storedEquations_frame
#print axioms MicroCFTA.SourcePruningPartialRenderingSemantics.storedEquations_frame
#check @MicroCFTA.SourcePruningPartialRenderingSemantics.satisfies_storedEquations
#print axioms MicroCFTA.SourcePruningPartialRenderingSemantics.satisfies_storedEquations
#check @MicroCFTA.SourcePruningPartialRenderingSemantics.expandPartial_completes_of_stored_equations
#print axioms MicroCFTA.SourcePruningPartialRenderingSemantics.expandPartial_completes_of_stored_equations
#check @MicroCFTA.SourcePruningPartialRenderingSemantics.expandPartial_completes
#print axioms MicroCFTA.SourcePruningPartialRenderingSemantics.expandPartial_completes
