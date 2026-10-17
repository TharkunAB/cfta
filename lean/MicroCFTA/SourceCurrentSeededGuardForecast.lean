import MicroCFTA.SourceCurrentGeneratedQueryGuardResources
import MicroCFTA.SourceCurrentConstrainedCapSeededForecast

/-!
# Initial guard schedules for first-seeded queries

Projection retains the entry alphabet. Each native query extends the
alphabet at its predicted profile. The recurrence follows the actual head,
tail, and query order. It does not inspect a future heap.
-/
namespace MicroCFTA.SourceCurrentSeededGuardForecast
open SourceCurrentAllocatedNativeResourceForecast (Profile)
open SourceCurrentConstrainedCapSeededForecast (projectionProfile foldProfile)
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "queryAlphabet" => SourceCurrentGeneratedQueryGuardResources.forecast

/-- Predict each native alphabet at the exact profile scheduled after its recursive tail. -/
noncomputable def foldAlphabet (alphabet : List Guard) (count : Nat) (seed : List Int) :
    List (List Int) → Profile → List Guard
  | [], _ => alphabet
  | path :: rest, profile =>
      let projected := projectionProfile path count profile
      queryAlphabet (foldAlphabet alphabet count seed rest projected) (foldProfile count seed rest projected)

/-- The original first path stays the final seed of the guard schedule. -/
noncomputable def finalAlphabet (alphabet : List Guard) (count : Nat) :
    List (List Int) → Profile → List Guard
  | [], _ => alphabet
  | seed :: rest, profile => foldAlphabet alphabet count seed rest profile

/-- A singleton fold performs only its seed projection and retains the alphabet. -/
theorem fold_nil (alphabet : List Guard) (count : Nat) (seed : List Int) (profile : Profile) :
    foldAlphabet alphabet count seed [] profile = alphabet := rfl

/-- The first projection precedes the tail and its final native query. -/
theorem fold_cons (alphabet : List Guard) (count : Nat) (seed path : List Int)
    (rest : List (List Int)) (profile : Profile) :
    foldAlphabet alphabet count seed (path :: rest) profile =
      queryAlphabet (foldAlphabet alphabet count seed rest (projectionProfile path count profile))
        (foldProfile count seed rest (projectionProfile path count profile)) := rfl

/-- Every scheduled fold retains every entry guard. -/
theorem fold_ge (alphabet : List Guard) (count : Nat) (seed : List Int)
    (paths : List (List Int)) (profile : Profile) : alphabet ⊆ foldAlphabet alphabet count seed paths profile := by
  induction paths generalizing profile with
  | nil => exact fun _ member => member
  | cons path rest ih =>
      intro guard member
      exact SourceCurrentGeneratedQueryGuardResources.forecast_ge _ _ (ih _ member)

/-- The final query retains every guard in its actual tail schedule. -/
theorem fold_tail_le (alphabet : List Guard) (count : Nat) (seed path : List Int)
    (rest : List (List Int)) (profile : Profile) :
    foldAlphabet alphabet count seed rest (projectionProfile path count profile) ⊆
      foldAlphabet alphabet count seed (path :: rest) profile :=
  SourceCurrentGeneratedQueryGuardResources.forecast_ge _ _

/-- Inclusion of entry alphabets is retained through the same fixed profile schedule. -/
theorem fold_mono {first last : List Guard} (increase : first ⊆ last) (count : Nat)
    (seed : List Int) (paths : List (List Int)) (profile : Profile) :
    foldAlphabet first count seed paths profile ⊆ foldAlphabet last count seed paths profile := by
  induction paths generalizing profile with
  | nil => exact increase
  | cons path rest ih =>
      exact SourceCurrentNativeGuardAlphabet.advance_mono (ih _) _

/-- Every complete first-seeded schedule retains every entry guard. -/
theorem final_ge (alphabet : List Guard) (count : Nat) (paths : List (List Int)) (profile : Profile) :
    alphabet ⊆ finalAlphabet alphabet count paths profile := by
  cases paths with
  | nil => exact fun _ member => member
  | cons seed rest => exact fold_ge _ _ _ _ _

/-- Initial alphabet inclusion is retained through the same first-seeded schedule. -/
theorem final_mono {first last : List Guard} (increase : first ⊆ last) (count : Nat)
    (paths : List (List Int)) (profile : Profile) :
    finalAlphabet first count paths profile ⊆ finalAlphabet last count paths profile := by
  cases paths with
  | nil => exact increase
  | cons seed rest => exact fold_mono increase _ _ _ _

end MicroCFTA.SourceCurrentSeededGuardForecast
