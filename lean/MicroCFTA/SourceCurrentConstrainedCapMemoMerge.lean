import MicroCFTA.SourceCurrentConstrainedCapMemoMergeCode
import MicroCFTA.SourceCurrentHereditaryMerge

/-!
# Finite constraint depths through actual memo-aware Merge calls

Each completed entry retains a conditional law for its complete original.
The mutual graph proves each candidate before it publishes completion.
The final reread uses the actual first winner at the returned table.
These results preserve supplied completed graphs. They do not construct them.
-/
namespace MicroCFTA.SourceCurrentConstrainedCapMemoMerge
open Cache InternedConstructorTemplates InternedProbeProvenance
open SourceEqualityRequiredSemanticCache (SemanticReady)
open SourceCurrentMemoMergeGraph
open SourceCurrentMemoMergeEffects (Effect)
open SourceCurrentConstrainedCap (Cap)
namespace Local
export SourceCurrentConstrainedCapMemoMergeCode (Certificate Contract Certified)
end Local
local notation "CostHeap" => InternedFreshOrdinaryCostHeap.Heap
variable {Symbol Guard : Type}

/-- Each actual completed entry retains every finite depth of its captured original. -/
def Stored (valid : Guard → Prop) (memo : Memo Symbol Guard) : Prop :=
  ∀ key entry, memo key = some entry → Local.Certificate valid entry.original entry.result

/-- An empty completed table needs no conditional depth law. -/
theorem stored_empty (valid : Guard → Prop) : Stored valid (empty : Memo Symbol Guard) := by
  intro key entry found
  cases found

/-- Universal finite-depth laws include the earlier hereditary annotation laws. -/
theorem Stored.hereditary {valid : Guard → Prop} {memo : Memo Symbol Guard}
    (stored : Stored valid memo) : SourceCurrentHereditaryMerge.Stored valid memo := by
  intro key entry found annotated
  exact (stored key entry found 0 (.plain 0 annotated)).annotated rfl

/-- Completion preserves old laws and checks the actual new candidate. -/
theorem stored_remember {valid : Guard → Prop} {memo : Memo Symbol Guard}
    (stored : Stored valid memo) (input candidate : Value Symbol Guard)
    (certificate : Local.Certificate valid input candidate) :
    Stored valid (remember memo input candidate) := by
  intro key entry found
  rcases remember_cases memo input candidate key entry found with old | ⟨_, same⟩
  · exact stored key entry old
  · subst entry
    exact certificate

/-- Physical readback identifies the whole captured original of a warm hit. -/
theorem hit_certificate
    {valid : Guard → Prop} {heap : State Symbol Guard} {memo : Memo Symbol Guard}
    {input : Value Symbol Guard} {entry : Entry Symbol Guard}
    (semantic : SemanticReady heap) (available : Available heap input)
    (physical : SourceCurrentMemoMergeEffects.Stored heap memo) (stored : Stored valid memo)
    (found : memo input.referenceOf = some entry) :
    entry.original = input ∧ Local.Certificate valid input entry.result := by
  classical
  have same := (SourceCurrentMemoMergeEffects.hit_original semantic available physical found).1
  exact ⟨same, same ▸ stored _ entry found⟩

/-- The actual winner uses its old law or the new candidate law before completion. -/
theorem winner_certificate
    {valid : Guard → Prop} {heap : State Symbol Guard} {memo : Memo Symbol Guard}
    {input candidate : Value Symbol Guard}
    (semantic : SemanticReady heap) (available : Available heap input)
    (physical : SourceCurrentMemoMergeEffects.Stored heap memo) (stored : Stored valid memo)
    (certificate : Local.Certificate valid input candidate) :
    (winner memo input candidate).original = input ∧
      Local.Certificate valid input (winner memo input candidate).result ∧
      Stored valid (remember memo input candidate) := by
  classical
  have completed := stored_remember stored input candidate certificate
  have original : (winner memo input candidate).original = input := by
    cases found : memo input.referenceOf with
    | none => rw [(remember_absent memo input candidate found).2]
    | some entry =>
        rw [(winner_existing memo input candidate entry found).2]
        exact (SourceCurrentMemoMergeEffects.hit_original semantic available physical found).1
  have law := completed _ _ (winner_found memo input candidate)
  rw [original] at law
  exact ⟨original, law, completed⟩

/-- A losing candidate cannot replace an earlier winner or its captured law. -/
theorem winner_existing_certificate {valid : Guard → Prop} {memo : Memo Symbol Guard}
    (stored : Stored valid memo) (input candidate : Value Symbol Guard) (entry : Entry Symbol Guard)
    (found : memo input.referenceOf = some entry) :
    remember memo input candidate = memo ∧ winner memo input candidate = entry ∧
      Local.Certificate valid entry.original entry.result :=
  ⟨(winner_existing memo input candidate entry found).1,
    (winner_existing memo input candidate entry found).2, stored _ entry found⟩

/-- Actual instructions preserve both tables and discharge their own local postcondition. -/
theorem run [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (valid : Guard → Prop) {clear : Guard → Bool} {top : Guard} (topValid : valid top)
    {code : Code Symbol Guard Output} {before after : State Symbol Guard}
    {memo saved : Memo Symbol Guard} {output : Output}
    (actual : Run clear top code before memo output after saved) :
    ∀ (post : State Symbol Guard → Output → Prop), SemanticReady before → CostHeap before →
      SourceCurrentMemoMergeEffects.Stored before memo → Stored valid memo →
      Local.Certified valid clear code before post →
      Effect before after ∧ SourceCurrentMemoMergeEffects.Stored after saved ∧
        Stored valid saved ∧ post after output := by
  induction actual using Run.rec
      (motive_2 := fun input before memo output after saved _ =>
        SemanticReady before → CostHeap before → SourceCurrentMemoMergeEffects.Stored before memo →
        Stored valid memo → Available before input →
        Effect before after ∧ SourceCurrentMemoMergeEffects.Stored after saved ∧
          Stored valid saved ∧ Local.Contract valid input before output after) with
  | pure value state memo =>
      intro post semantic costs physical caps checked
      exact ⟨SourceCurrentMemoMergeEffects.effect_refl _ semantic costs, physical, caps, checked⟩
  | work job state memo =>
      intro post semantic costs physical caps checked
      exact ⟨checked.1, physical.grows checked.1.keeps, caps, checked.2⟩
  | select fuel done =>
      intro post semantic costs physical caps checked
      have original := SourceCurrentMergedHeapEffects.select_effect (fun _ => True) _ fuel _ _
        semantic costs checked.1 _ _ done
      have effect : Effect _ _ := ⟨original.keeps, original.semantic, original.costs⟩
      exact ⟨effect, physical.grows effect.keeps, caps, checked.2.2 fuel _ _ done effect⟩
  | request actual ih =>
      intro post semantic costs physical caps checked
      obtain ⟨effect, physicalAfter, capsAfter, returned⟩ := ih semantic costs physical caps checked.1
      exact ⟨effect, physicalAfter, capsAfter, checked.2 _ _ effect returned⟩
  | bind first later ihFirst ihLater =>
      intro post semantic costs physical caps checked
      obtain ⟨intermediate, firstChecked, nextChecked⟩ := checked
      obtain ⟨firstEffect, firstPhysical, firstCaps, intermediateValid⟩ :=
        ihFirst intermediate semantic costs physical caps firstChecked
      obtain ⟨laterEffect, laterPhysical, laterCaps, returned⟩ :=
        ihLater post firstEffect.semantic firstEffect.costs firstPhysical firstCaps
          (nextChecked _ _ firstEffect intermediateValid)
      exact ⟨firstEffect.trans laterEffect, laterPhysical, laterCaps, returned⟩
  | hit found =>
      rename_i semantic costs physical caps available
      obtain ⟨_, result, closed⟩ := SourceCurrentMemoMergeEffects.hit_original semantic available physical found
      have certificate := (hit_certificate semantic available physical caps found).2
      exact ⟨SourceCurrentMemoMergeEffects.effect_refl _ semantic costs, physical, caps,
        ⟨result, closed⟩, certificate⟩
  | @miss memo input before candidate after current absent actual ih =>
      rename_i semantic costs physical caps available
      have checked := SourceCurrentConstrainedCapMemoMergeCode.lift_certified valid clear
        (body top input) before _
        (SourceCurrentMemoMergeEffects.body_certified clear top input before semantic costs available)
      obtain ⟨effect, physicalAfter, capsAfter, candidatePhysical⟩ :=
        ih _ semantic costs physical caps checked
      have candidateCertificate : Local.Certificate valid input candidate :=
        (ih _ semantic costs physical caps
          (SourceCurrentConstrainedCapMemoMergeCode.body_certified valid clear top topValid
            input before semantic costs available)).2.2.2
      have inputAvailable := effect.keeps.available input available
      have completed := SourceCurrentMemoMergeEffects.stored_remember physicalAfter input candidate
        inputAvailable candidatePhysical.1 candidatePhysical.2
      have winner := winner_certificate effect.semantic inputAvailable physicalAfter capsAfter candidateCertificate
      obtain ⟨_, result, closed⟩ := SourceCurrentMemoMergeEffects.hit_original effect.semantic
        inputAvailable completed (winner_found current input candidate)
      exact ⟨effect, completed, winner.2.2, ⟨result, closed⟩, winner.2.1⟩

/-- A completed call derives a universal certificate for its exact returned winner. -/
theorem call [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (valid : Guard → Prop) {clear : Guard → Bool} {top : Guard} (topValid : valid top)
    {input output : Value Symbol Guard} {before after : State Symbol Guard}
    {memo saved : Memo Symbol Guard}
    (actual : Call clear top input before memo output after saved) (semantic : SemanticReady before)
    (costs : CostHeap before) (physical : SourceCurrentMemoMergeEffects.Stored before memo)
    (caps : Stored valid memo) (available : Available before input) :
    Effect before after ∧ SourceCurrentMemoMergeEffects.Stored after saved ∧ Stored valid saved ∧
      Local.Contract valid input before output after :=
  run valid topValid (.request actual) (fun after output => Local.Contract valid input before output after)
    semantic costs physical caps ⟨available, fun _ _ _ returned => returned⟩

/-- A cold completed call constructs both stored invariants from their empty tables. -/
theorem cold [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (valid : Guard → Prop) {clear : Guard → Bool} {top : Guard} (topValid : valid top)
    {input output : Value Symbol Guard} {before after : State Symbol Guard} {saved : Memo Symbol Guard}
    (actual : Call clear top input before empty output after saved) (semantic : SemanticReady before)
    (costs : CostHeap before) (available : Available before input) :
    Effect before after ∧ SourceCurrentMemoMergeEffects.Stored after saved ∧ Stored valid saved ∧
      Local.Contract valid input before output after :=
  call valid topValid actual semantic costs (SourceCurrentMemoMergeEffects.stored_empty before)
    (stored_empty valid) available

/-- Every admitted finite depth survives the actual returned heap and completed table. -/
theorem retained [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (valid : Guard → Prop) {clear : Guard → Bool} {top : Guard} (topValid : valid top)
    {input output : Value Symbol Guard} {before after : State Symbol Guard}
    {memo saved : Memo Symbol Guard}
    (actual : Call clear top input before memo output after saved) (semantic : SemanticReady before)
    (costs : CostHeap before) (physical : SourceCurrentMemoMergeEffects.Stored before memo)
    (caps : Stored valid memo) (available : Available before input) (depth : Nat)
    (bounded : Cap valid depth input) :
    Effect before after ∧ SourceCurrentMemoMergeEffects.Stored after saved ∧ Stored valid saved ∧
      SourceCurrentMemoMergeEffects.Contract input before output after ∧ Cap valid depth output := by
  obtain ⟨effect, physicalAfter, capsAfter, returned⟩ :=
    call valid topValid actual semantic costs physical caps available
  exact ⟨effect, physicalAfter, capsAfter, returned.1, returned.2 depth bounded⟩

end MicroCFTA.SourceCurrentConstrainedCapMemoMerge
