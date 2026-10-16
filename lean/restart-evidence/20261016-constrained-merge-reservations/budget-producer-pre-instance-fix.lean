import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryMergeBudgetBody
import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryMergeProfileProducer

/-!
# Constructor budgets from actual recursive merge calls

The proof follows the actual Run and Call graph.
Each miss counts its complete body before it reads the first winner.
A warm hit performs no constructor Work.
Profile facts come from the proved profile producer on the same graph.
-/
namespace MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryMergeBudgetProducer
open Cache InternedConstructorTemplates InternedProbeProvenance
open SourceCurrentMemoMergeGraph
open SourceEqualityRequiredSemanticCache (SemanticReady)
open MergedOrdinaryHeight (height)
namespace Physical
export SourceCurrentMemoMergeEffects (Stored Effect effect_refl)
end Physical
namespace Profiles
export SourceCurrentAllocatedFiniteOrdinaryMergeProfileCache (Stored)
end Profiles
namespace BudgetCode
export SourceCurrentAllocatedFiniteOrdinaryMergeBudgetCode (Budget Certificate Contract Certified)
end BudgetCode
namespace Numbers
export SourceCurrentAllocatedFiniteOrdinaryMergeBudgetNumbers (nodeBudget edgeBudget)
end Numbers
local notation "CostHeap" => InternedFreshOrdinaryCostHeap.Heap
variable {Symbol Guard : Type}

/-- Actual instructions retain both stored invariants and discharge their local budget. -/
theorem run_budget [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {clear : Guard → Bool} {top : Guard} {code : Code Symbol Guard Output}
    {before after : State Symbol Guard} {memo saved : Memo Symbol Guard} {output : Output}
    (actual : Run clear top code before memo output after saved) :
    ∀ (post : State Symbol Guard → Output → Prop), SemanticReady before → CostHeap before →
      Physical.Stored before memo → Profiles.Stored memo → BudgetCode.Certified clear code before post →
      Physical.Effect before after ∧ Physical.Stored after saved ∧ Profiles.Stored saved ∧ post after output := by
  induction actual using Run.rec
      (motive_2 := fun input before memo output after saved _ =>
        SemanticReady before → CostHeap before → Physical.Stored before memo → Profiles.Stored memo →
        Available before input → Physical.Effect before after ∧ Physical.Stored after saved ∧
          Profiles.Stored saved ∧ BudgetCode.Contract input before output after) with
  | pure value state memo =>
      intro post semantic costs physical profiles checked
      exact ⟨Physical.effect_refl _ semantic costs, physical, profiles, checked⟩
  | work job state memo =>
      intro post semantic costs physical profiles checked
      exact ⟨checked.1, physical.grows checked.1.keeps, profiles, checked.2⟩
  | select fuel done =>
      intro post semantic costs physical profiles checked
      have original := SourceCurrentMergedHeapEffects.select_effect (fun _ => True) _ fuel _ _
        semantic costs checked.1 _ _ done
      have effect : Physical.Effect _ _ := ⟨original.keeps, original.semantic, original.costs⟩
      exact ⟨effect, physical.grows effect.keeps, profiles, checked.2.2 fuel _ _ done effect⟩
  | request actual ih =>
      intro post semantic costs physical profiles checked
      obtain ⟨effect, physicalAfter, profilesAfter, returned⟩ := ih semantic costs physical profiles checked.1
      exact ⟨effect, physicalAfter, profilesAfter, checked.2 _ _ effect returned⟩
  | bind first later ihFirst ihLater =>
      intro post semantic costs physical profiles checked
      obtain ⟨intermediate, firstChecked, nextChecked⟩ := checked
      obtain ⟨firstEffect, firstPhysical, firstProfiles, valid⟩ :=
        ihFirst intermediate semantic costs physical profiles firstChecked
      obtain ⟨laterEffect, laterPhysical, laterProfiles, returned⟩ :=
        ihLater post firstEffect.semantic firstEffect.costs firstPhysical firstProfiles
          (nextChecked _ _ firstEffect valid)
      exact ⟨firstEffect.trans laterEffect, laterPhysical, laterProfiles, returned⟩
  | hit found =>
      rename_i semantic costs physical profiles available
      have profile := SourceCurrentAllocatedFiniteOrdinaryMergeProfileProducer.call_profile
        (clear := clear) (top := top) (.hit found) semantic costs physical profiles available
      refine ⟨profile.1, profile.2.1, profile.2.2.1, profile.2.2.2, ?_⟩
      intro rows arity bound _ _
      exact SourceCurrentAllocatedFiniteOrdinaryMergeBudgetCode.Budget.mono
        (SourceCurrentAllocatedFiniteOrdinaryMergeBudgetCode.Budget.refl _) (Nat.zero_le _) (Nat.zero_le _)
  | @miss memo input before candidate after current absent actual ih =>
      rename_i semantic costs physical profiles available
      have profile := SourceCurrentAllocatedFiniteOrdinaryMergeProfileProducer.call_profile
        (clear := clear) (top := top) (.miss absent actual) semantic costs physical profiles available
      refine ⟨profile.1, profile.2.1, profile.2.2.1, profile.2.2.2, ?_⟩
      intro rows arity bound inputProfile bounded
      have bodyBudget := SourceCurrentAllocatedFiniteOrdinaryMergeBudgetBody.body_certified
        clear top input before semantic costs available rows arity inputProfile
      obtain ⟨_, _, _, budget⟩ := ih _ semantic costs physical profiles bodyBudget
      exact SourceCurrentAllocatedFiniteOrdinaryMergeBudgetCode.Budget.mono budget
        (SourceCurrentAllocatedFiniteOrdinaryMergeBudgetNumbers.node_mono rows arity bounded)
        (SourceCurrentAllocatedFiniteOrdinaryMergeBudgetNumbers.edge_mono rows arity bounded)

/-- A completed call derives its actual constructor trace and universal input-only budgets. -/
theorem call_budget [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {clear : Guard → Bool} {top : Guard} {input output : Value Symbol Guard}
    {before after : State Symbol Guard} {memo saved : Memo Symbol Guard}
    (actual : Call clear top input before memo output after saved)
    (semantic : SemanticReady before) (costs : CostHeap before)
    (physical : Physical.Stored before memo) (profiles : Profiles.Stored memo)
    (available : Available before input) :
    Physical.Effect before after ∧ Physical.Stored after saved ∧ Profiles.Stored saved ∧
      BudgetCode.Contract input before output after :=
  run_budget (.request actual) (fun after output => BudgetCode.Contract input before output after)
    semantic costs physical profiles ⟨available, fun _ _ _ returned => returned⟩

/-- A cold table derives both stored invariants and budgets without supplied entry certificates. -/
theorem cold [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {clear : Guard → Bool} {top : Guard} {input output : Value Symbol Guard}
    {before after : State Symbol Guard} {saved : Memo Symbol Guard}
    (actual : Call clear top input before empty output after saved)
    (semantic : SemanticReady before) (costs : CostHeap before) (available : Available before input) :
    Physical.Effect before after ∧ Physical.Stored after saved ∧ Profiles.Stored saved ∧
      BudgetCode.Contract input before output after :=
  call_budget actual semantic costs (SourceCurrentMemoMergeEffects.stored_empty before)
    SourceCurrentAllocatedFiniteOrdinaryMergeProfileCache.empty_stored available

end MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryMergeBudgetProducer
