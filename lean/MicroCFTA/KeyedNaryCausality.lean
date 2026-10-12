import MicroCFTA.KeyedNaryInverse

/-!
# Source equations of the mutually recursive keyed inverse

An occurrence dispatches to its own key. The complete member boundary
strictly reduces the requested forest. Increasing adequate fuel changes
no candidate row, checked flag, or source order.
-/
namespace MicroCFTA.KeyedNaryCausality
open Language GeneratorCombinators IntegerTermViews SizedRank
open RecursiveCallbackTermination KeyedNaryFields KeyedNaryInverse

/-- No key member boundary can occur in a height-zero request. -/
theorem unwrap_zero (code : Nat) (wanted : List (EngineTerm Symbol)) (bound : forestHeight wanted ≤ 0) :
    KeyedTermBoundary.unwrap code wanted = none := by
  cases found : KeyedTermBoundary.unwrap code wanted with
  | none => rfl
  | some child =>
      have descent := KeyedTermBoundary.unwrap_height code wanted child found
      omega

/-- Adequate fuel preserves the entire per-key candidate list, including false flags. -/
theorem fuel_stable [DecidableEq Symbol] (code : Key → Nat) (callbacks : LeafCallbacks Symbol)
    (program : Key → Body Key Root Symbol Root) (first second : Nat) (key : Key)
    (view : View) (wanted : List (EngineTerm Symbol))
    (firstEnough : forestHeight wanted ≤ first) (secondEnough : forestHeight wanted ≤ second) :
    fuelPositions code callbacks program first key view wanted =
      fuelPositions code callbacks program second key view wanted := by
  induction first generalizing second key view wanted with
  | zero =>
      have absent := unwrap_zero (code key) wanted firstEnough
      cases second <;> simp [fuelPositions, KeyedTermBoundary.positions, absent]
  | succ first ih =>
      cases second with
      | zero =>
          have absent := unwrap_zero (code key) wanted secondEnough
          simp [fuelPositions, KeyedTermBoundary.positions, absent]
      | succ second =>
          cases found : KeyedTermBoundary.unwrap (code key) wanted with
          | none => simp [fuelPositions, KeyedTermBoundary.positions, found]
          | some child =>
              have descent := KeyedTermBoundary.unwrap_height (code key) wanted child found
              have roots : ∀ childKey, RecursiveNaryCausality.Agree (forestHeight [child])
                  (rootField code program (fuelPositions code callbacks program first) childKey)
                  (rootField code program (fuelPositions code callbacks program second) childKey) := by
                intro childKey
                refine ⟨rfl, ?_⟩
                intro childView requested small
                exact ih second childKey childView requested (by omega) (by omega)
              have same := (compiled_agree callbacks _ _ roots (program key)).2 .whole [child] (Nat.le_refl _)
              simpa only [fuelPositions, KeyedTermBoundary.positions, found] using same

/-- The terminating family inverse satisfies the original simultaneous source callback equation. -/
theorem positions_equation [DecidableEq Symbol] (code : Key → Nat) (callbacks : LeafCallbacks Symbol)
    (program : Key → Body Key Root Symbol Root) (key : Key) (view : View) (wanted : List (EngineTerm Symbol)) :
    KeyedNaryInverse.positions code callbacks program key view wanted =
      KeyedTermBoundary.positions (code key)
        (compile callbacks (rootField code program (KeyedNaryInverse.positions code callbacks program)) (program key))
        view wanted := by
  change fuelPositions code callbacks program (forestHeight wanted) key view wanted = _
  cases height : forestHeight wanted with
  | zero =>
      have absent := unwrap_zero (code key) wanted (by omega)
      simp [fuelPositions, KeyedTermBoundary.positions, absent]
  | succ fuel =>
      cases found : KeyedTermBoundary.unwrap (code key) wanted with
      | none => simp [fuelPositions, KeyedTermBoundary.positions, found]
      | some child =>
          have descent := KeyedTermBoundary.unwrap_height (code key) wanted child found
          have roots : ∀ childKey, RecursiveNaryCausality.Agree (forestHeight [child])
              (rootField code program (fuelPositions code callbacks program fuel) childKey)
              (rootField code program (KeyedNaryInverse.positions code callbacks program) childKey) := by
            intro childKey
            refine ⟨rfl, ?_⟩
            intro childView requested small
            exact fuel_stable code callbacks program fuel (forestHeight requested) childKey childView requested
              (by omega) (Nat.le_refl _)
          have same := (compiled_agree callbacks _ _ roots (program key)).2 .whole [child] (Nat.le_refl _)
          simpa only [fuelPositions, KeyedTermBoundary.positions, found] using same

/-- Every source view dispatches a well-formed member to exactly its selected key's body. -/
theorem positions_member [DecidableEq Symbol] (code : Key → Nat) (callbacks : LeafCallbacks Symbol)
    (program : Key → Body Key Root Symbol Root) (key : Key) (view : View) (child : EngineTerm Symbol) :
    KeyedNaryInverse.positions code callbacks program key view [KeyedTermBoundary.atKeyTerm (code key) child] =
      (compile callbacks (rootField code program (KeyedNaryInverse.positions code callbacks program)) (program key)).positions
        .whole [child] := by
  rw [positions_equation]
  simp only [KeyedTermBoundary.positions, (KeyedTermBoundary.unwrap_some _ _ child).mpr rfl]

/-- Wrong keys and malformed family member boundaries return no candidates. -/
theorem positions_rejects [DecidableEq Symbol] (code : Key → Nat) (callbacks : LeafCallbacks Symbol)
    (program : Key → Body Key Root Symbol Root) (key : Key) (view : View) (wanted : List (EngineTerm Symbol))
    (absent : KeyedTermBoundary.unwrap (code key) wanted = none) :
    KeyedNaryInverse.positions code callbacks program key view wanted = [] := by
  rw [positions_equation]
  simp only [KeyedTermBoundary.positions, absent]

end MicroCFTA.KeyedNaryCausality
