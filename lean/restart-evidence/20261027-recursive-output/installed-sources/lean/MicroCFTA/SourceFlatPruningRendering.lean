import MicroCFTA.EnumerationFlatPartial
import MicroCFTA.SourcePruningEnumerationRendering

/-!
# Native rendering with direct representative reads

The renderer uses the heap of the emitted output. Structural fuel remains
explicit. A recursive boundary retains the source marker behavior.
-/
namespace MicroCFTA.SourceFlatPruningRendering
open Language Fragments EnumerationFlatState EnumerationFlatReplay
open SourcePruningEnumerationNodes
local notation "Symbol" => SourcePruningTemplates.Symbol
variable {NativeGuard EnumGuard : Type}
attribute [local instance] SourcePruningEnumerationTerminalPrefix.terminalPrefixMonadList
  SourcePruningEnumerationTerminalPrefix.terminalPrefixLawfulMonadList

/-- Render a fragment through direct roots and actual native handle lookup. -/
def expandFragment (heap : InternedConstructorTemplates.State Symbol NativeGuard) (marker : Symbol) :
    Nat → Fragment Symbol → Action Symbol EnumGuard (Term Symbol)
  | 0, _ => failure .fuelExhausted
  | fuel + 1, .node symbol children => do
      pure (.node symbol (← children.mapM (expandFragment heap marker fuel)))
  | fuel + 1, .hole uv => do
      match ← getValue uv with
      | .enumerated fragment => expandFragment heap marker fuel fragment
      | .unenumerated (some handle) _ =>
          match lookupNode heap handle with
          | none => failure .unresolvedReference
          | some value =>
              if MergedOrdinaryHeight.recursiveBoundary value then pure (.node marker [])
              else failure .unfinishedFragment
      | _ => failure .unfinishedFragment

/-- Render a stored root and retain the source rejection branches. -/
def expandUVar (heap : InternedConstructorTemplates.State Symbol NativeGuard) (marker : Symbol)
    (fuel uv : Nat) : Action Symbol EnumGuard (Term Symbol) := do
  match ← getValue uv with
  | .enumerated fragment => expandFragment heap marker fuel fragment
  | .unenumerated (some handle) _ =>
      match lookupNode heap handle with
      | none => failure .unresolvedReference
      | some value =>
          if MergedOrdinaryHeight.recursiveBoundary value then pure (.node marker []) else reject
  | _ => reject

/-- Render the root and all residuals at the same native heap. -/
def render (heap : InternedConstructorTemplates.State Symbol NativeGuard) (marker : Symbol)
    (fuel uv : Nat) : Action Symbol EnumGuard (Term Symbol × List (EnumGuard × Term Symbol)) := do
  let term ← expandUVar heap marker fuel uv
  let pending ← (← get).obligations.mapM fun obligation => do
    pure (obligation.1, ← expandFragment heap marker fuel obligation.2)
  pure (term, pending)

private theorem failure_replays (error : EnumerationState.Error) :
    Replays (failure error : Action Symbol EnumGuard α) (EnumerationState.failure error) := by
  intro _ earlier value after _ observed
  exact (EnumerationCorrectness.success_failure error earlier after value observed).elim

private theorem reject_replays :
    Replays (reject : Action Symbol EnumGuard α) EnumerationState.reject := by
  intro _ _ _ _ _ observed
  exact (List.not_mem_nil observed).elim

/-- Every successful original fragment rendering has the same term and a related final core. -/
theorem expandFragment_replays (heap : InternedConstructorTemplates.State Symbol NativeGuard)
    (marker : Symbol) (fuel : Nat) (fragment : Fragment Symbol) :
    Replays (expandFragment (EnumGuard := EnumGuard) heap marker fuel fragment)
      (SourcePruningEnumerationRendering.expandFragment heap marker fuel fragment) := by
  induction fuel generalizing fragment with
  | zero => exact failure_replays .fuelExhausted
  | succ fuel ih =>
      cases fragment with
      | node symbol children =>
          exact bind_replays _ _ _ _ (mapM_replays _ _ (fun child => ih child) children)
            (fun terms => pure_replays (Term.node symbol terms))
      | hole uv =>
          apply bind_replays _ _ _ _ (EnumerationFlatPartial.getValue_replays (fuel + 1) uv)
          intro value
          cases value with
          | eliminated => exact failure_replays .unfinishedFragment
          | enumerated fragment => exact ih fragment
          | unenumerated node scs =>
              cases node with
              | none => exact failure_replays .unfinishedFragment
              | some handle =>
                  dsimp only
                  cases lookupNode heap handle with
                  | none => exact failure_replays .unresolvedReference
                  | some value =>
                      by_cases boundary : MergedOrdinaryHeight.recursiveBoundary value = true
                      · simpa only [boundary, Bool.false_eq_true, ↓reduceIte] using
                          (pure_replays (Guard := EnumGuard) (Term.node marker []))
                      · simpa only [boundary, Bool.false_eq_true, ↓reduceIte] using
                          (failure_replays (EnumGuard := EnumGuard) (α := Term Symbol) .unfinishedFragment)

/-- Every successful original root rendering retains its term and related final core. -/
theorem expandUVar_replays (heap : InternedConstructorTemplates.State Symbol NativeGuard)
    (marker : Symbol) (fuel uv : Nat) :
    Replays (expandUVar (EnumGuard := EnumGuard) heap marker fuel uv)
      (SourcePruningEnumerationRendering.expandUVar heap marker fuel uv) := by
  apply bind_replays _ _ _ _ (EnumerationFlatPartial.getValue_replays (fuel + 1) uv)
  intro value
  cases value with
  | eliminated => exact reject_replays
  | enumerated fragment => exact expandFragment_replays heap marker fuel fragment
  | unenumerated node scs =>
      cases node with
      | none => exact reject_replays
      | some handle =>
          dsimp only
          cases lookupNode heap handle with
          | none => exact failure_replays .unresolvedReference
          | some value =>
              by_cases boundary : MergedOrdinaryHeight.recursiveBoundary value = true
              · simpa only [boundary, Bool.false_eq_true, ↓reduceIte] using
                  (pure_replays (Guard := EnumGuard) (Term.node marker []))
              · simpa only [boundary, Bool.false_eq_true, ↓reduceIte] using (reject_replays (EnumGuard := EnumGuard) (α := Term Symbol))

end MicroCFTA.SourceFlatPruningRendering
