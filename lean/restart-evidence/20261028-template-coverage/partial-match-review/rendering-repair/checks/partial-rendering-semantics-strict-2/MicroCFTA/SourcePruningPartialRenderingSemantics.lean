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

/-- Actual partial rendering represents the same original completed fragment. -/
theorem expandPartial_completes (graph : Graph Symbol Guard)
    (language : NodeLanguage Symbol) (meaning : Guard → Term Symbol → Prop)
    (assignment : Nat → Term Symbol) (fuel : Nat) (fragment : Fragment Symbol)
    (before after : State Symbol Guard) (observedTerm : Term (PartialSymbol Symbol))
    (total : UnionFind.Total before.representatives)
    (satisfied : Satisfies language meaning assignment before)
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
              UnionFind.Total before.representatives → Satisfies language meaning assignment before →
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
                have middleSatisfied := (SourcePruningEnumerationNativeLanguage.satisfies_frame language meaning
                  assignment before middle frame).mpr satisfied
                exact .cons (ih child before middle first total satisfied firstRead)
                  (restIH middle last remaining (frame.total total) middleSatisfied restRead)
          exact .concrete symbol partials (children.map (fill assignment))
            (completed children before middle partials total satisfied traversed)
      | hole uv =>
          simp only [expandPartial] at success
          obtain ⟨value, middle, reading, final⟩ := (success_bind _ _ _ _ _).mp success
          obtain ⟨frame, root, size, path, _afterPath, stored⟩ :=
            getValue_frame (fuel + 1) uv before middle value total reading
          cases value with
          | enumerated fragment =>
              have equation : fill assignment fragment = assignment uv := by
                have rootEquation : fill assignment fragment = assignment root := by
                  simpa only [EnumerationCorrectness.heap, stored, Option.getD_some, slot, slotSatisfies]
                    using satisfied.1.2 root
                exact rootEquation.trans (satisfied.1.1 uv root (UnionFind.sameClass_root path)).symm
              have middleSatisfied := (SourcePruningEnumerationNativeLanguage.satisfies_frame language meaning
                assignment before middle frame).mpr satisfied
              have completed := ih fragment middle after observedTerm (frame.total total) middleSatisfied final
              simpa only [fill, equation] using completed
          | eliminated =>
              obtain ⟨rfl, _same⟩ := (success_pure _ observedTerm middle after).mp final
              exact .hole uv
          | unenumerated node scs =>
              cases node with
              | none =>
                  obtain ⟨rfl, _same⟩ := (success_pure _ observedTerm middle after).mp final
                  exact .hole uv
              | some node =>
                  cases scs with
                  | cons first rest =>
                      obtain ⟨rfl, _same⟩ := (success_pure _ observedTerm middle after).mp final
                      exact .hole uv
                  | nil =>
                      cases view : graph.node node <;> simp only [view] at final
                      all_goals
                        obtain ⟨rfl, _same⟩ := (success_pure _ observedTerm middle after).mp final
                        first | exact .hole uv | exact .truncated [] (assignment uv)

end MicroCFTA.SourcePruningPartialRenderingSemantics
