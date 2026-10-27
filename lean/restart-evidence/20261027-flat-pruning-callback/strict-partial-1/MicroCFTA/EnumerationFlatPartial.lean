import MicroCFTA.EnumerationFlatReplay

/-!
# Partial rendering with direct representative reads

Structural rendering fuel remains explicit. Recursive boundaries retain the
existing truncated marker. Raw holes retain their original variable IDs.
-/

namespace MicroCFTA.EnumerationFlatPartial

open Language Fragments EnumerationFlatState EnumerationFlatReplay

variable {Symbol Guard : Type}

attribute [local instance] SourcePruningEnumerationTerminalPrefix.terminalPrefixMonadList
  SourcePruningEnumerationTerminalPrefix.terminalPrefixLawfulMonadList

/-- Read the current direct root and its stored value without old lookup fuel. -/
theorem getValue_replays (fuel uv : Nat) :
    Replays (Symbol := Symbol) (Guard := Guard)
      (getValue uv) (EnumerationState.getValue fuel uv) := by
  apply bind_replays _ _ _ _ (representative_replays fuel uv)
  intro root flat earlier value after related observed
  cases stored : earlier.values[root]? with
  | none => simp [EnumerationCorrectness.Success, EnumerationState.rawValue, stored] at observed
  | some found =>
      have same : value = found ∧ after = earlier := by
        simpa [EnumerationCorrectness.Success, EnumerationState.rawValue, stored] using observed
      obtain ⟨rfl, rfl⟩ := same
      exact ⟨flat, by simp [rawValue, related.values, stored], related⟩

/-- Render the same partial term with structural fuel and direct slot reads. -/
def expandPartial (graph : EnumerationState.Graph Symbol Guard) : Nat → Fragment Symbol →
    Action Symbol Guard (Term (EnumerationState.PartialSymbol Symbol))
  | 0, _ => failure .fuelExhausted
  | fuel + 1, .node symbol children => do
      pure (.node (.concrete symbol) (← children.mapM (expandPartial graph fuel)))
  | fuel + 1, .hole uv => do
      match ← getValue uv with
      | .enumerated fragment => expandPartial graph fuel fragment
      | .unenumerated (some node) [] =>
          match graph.node node with
          | .recursive _ => pure (.node .truncated [])
          | _ => pure (.node (.hole uv) [])
      | _ => pure (.node (.hole uv) [])

/-- Every successful old rendering has the same partial term and related core. -/
theorem expandPartial_replays (graph : EnumerationState.Graph Symbol Guard)
    (fuel : Nat) (fragment : Fragment Symbol) :
    Replays (expandPartial graph fuel fragment) (EnumerationState.expandPartial graph fuel fragment) := by
  induction fuel generalizing fragment with
  | zero =>
      intro flat earlier value after _ observed
      simp [EnumerationCorrectness.Success, EnumerationState.expandPartial,
        EnumerationState.failure] at observed
  | succ fuel ih =>
      cases fragment with
      | node symbol children =>
          exact bind_replays _ _ _ _
            (mapM_replays _ _ (fun child => ih child) children)
            (fun terms => pure_replays (.node (.concrete symbol) terms))
      | hole uv =>
          apply bind_replays _ _ _ _ (getValue_replays (fuel + 1) uv)
          intro value
          cases value with
          | enumerated fragment => exact ih fragment
          | eliminated => exact pure_replays _
          | unenumerated node scs =>
              cases node with
              | none => exact pure_replays _
              | some node =>
                  cases scs with
                  | cons first rest => exact pure_replays _
                  | nil => cases graph.node node <;> exact pure_replays _

end MicroCFTA.EnumerationFlatPartial
