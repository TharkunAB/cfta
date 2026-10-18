import MicroCFTA.SourceCurrentEqualityOperationFixed
import MicroCFTA.EqualityModel

/-!
# Initial finite path domains for actual inherited combinations

Source saturation can increase path height above both operand heights.
The initial path gaps, anchors and child-index alphabet give a larger
finite domain for each actual combination. These bounds use that call's
initial operands. They do not bound an unbounded sequence of new row inputs.
-/
namespace MicroCFTA.SourceCurrentInheritedGainDomain
open EqualityNormalize EqualitySaturation EqualityTermination
open SourceEqualityClassOrder SourceEqualityConstraintAllocation
local notation "Operations" => SourceEqualityConstraintMemoAllocation.State
local notation "Valid" => SourceEqualityConstraintMemoAllocation.Valid
local notation "Grows" => SourceEqualityConstraintMemoAllocation.Grows
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula

/-- One initial normalization input determines a finite domain for every returned path. -/
def domain (classes : Constraints) : List Path :=
  saturationDomain (complete (prepare classes))

/-- Initial path gaps and anchors give a numeric height bound for this normalization. -/
def heightBound (classes : Constraints) : Nat :=
  let initial := complete (prepare classes)
  initialGap initial * ((members initial).length + 1)

private theorem fix_within (gap : Nat) (anchors : List Path) (alphabet : List Nat)
    (fuel : Nat) (classes output : Constraints) (normal : NormalState classes)
    (segmented : SegmentedState gap classes) (anchored : Anchored anchors classes)
    (allowed : UsesAlphabet alphabet classes) (actual : fixMaybe fuel classes = .normalized output) :
    Within (words alphabet (gap * (anchors.length + 1))) output := by
  induction fuel generalizing classes with
  | zero => cases actual
  | succ fuel ih =>
      cases stepped : congruenceStep classes with
      | none => simp only [fixMaybe,stepped] at actual; cases actual
      | some next =>
          by_cases stable : next = classes
          · subst next
            have same : output = classes := by simpa only [fixMaybe,stepped,ite_true] using actual.symm
            subst output
            exact bounded_state gap anchors alphabet classes normal
              (congruenceStep_invariants classes classes normal.1 stepped).2 segmented anchored allowed
          · have recursive : fixMaybe fuel next = .normalized output := by
              simpa only [fixMaybe,stepped,stable,ite_false] using actual
            exact ih next (step_normal classes next normal.1 stepped)
              (step_segmented gap classes next segmented stepped)
              (step_anchored anchors classes next normal.1 anchored stepped)
              (step_alphabet alphabet classes next allowed stepped) recursive

private theorem height_of_within (classes output : Constraints) (within : Within (domain classes) output) :
    EqualityModel.depth output.flatten ≤ heightBound classes := by
  apply (EqualityModel.maxOn_le List.length _ _).mpr
  intro path member
  have known : path ∈ members output := by simpa only [members,List.mem_eraseDups] using member
  exact ((words_correct (initialAlphabet (complete (prepare classes))) (heightBound classes) path).mp
    (within path known)).1

/-- Actual source normalization retains only paths in its initial finite domain and height bound. -/
theorem normalize (classes output : Constraints) (actual : SourceCompactGuards.normalize classes = some output) :
    Within (domain classes) output ∧ EqualityModel.depth output.flatten ≤ heightBound classes := by
  have completed := actual
  unfold SourceCompactGuards.normalize at completed
  rw [SourceCompactGuards.arrayNormalize_eq] at completed
  cases result : mkEqConstraints (normalizationBound classes) classes with
  | timeout | contradiction => simp only [result,SymbolicEqualityBridge.resultClasses] at completed; cases completed
  | normalized next =>
      have same : next = output := Option.some.inj completed
      subst next
      have initialNormal := complete_normal (prepare classes) (prepare_active classes)
      have within := fix_within (initialGap (complete (prepare classes)))
        (members (complete (prepare classes))) (initialAlphabet (complete (prepare classes)))
        (normalizationBound classes) (complete (prepare classes)) output initialNormal
        (initially_segmented _) (initially_anchored _ initialNormal.1) (initially_allowed _) result
      exact ⟨within,height_of_within classes output within⟩

private theorem combine_classes (first second : Option Constraints) (output : Constraints)
    (actual : SourceCompactGuards.combineEqualities first second = some output) :
    Within (domain (first.getD [] ++ second.getD [])) output ∧
      EqualityModel.depth output.flatten ≤ heightBound (first.getD [] ++ second.getD []) := by
  cases first with
  | none => cases actual
  | some first =>
      cases second with
      | none => cases actual
      | some second =>
          cases first with
          | nil =>
              cases second with
              | nil =>
                  cases actual
                  exact ⟨by intro path impossible; cases impossible,Nat.zero_le _⟩
              | cons head tail => exact normalize _ _ actual
          | cons head tail => cases second <;> exact normalize _ _ actual

/-- Initial ready operands construct the actual cold or warm result with a finite path carrier. -/
theorem combine (first second : Value) (before : Operations) (valid : Valid before)
    (firstReady : Ready before.constraints first) (secondReady : Ready before.constraints second) :
    ∃ result,
      (SourceEqualityConstraintMemoAllocation.combine first second before).1 = .ok result ∧
      Valid (SourceEqualityConstraintMemoAllocation.combine first second before).2 ∧
      Ready (SourceEqualityConstraintMemoAllocation.combine first second before).2.constraints result ∧
      Grows before (SourceEqualityConstraintMemoAllocation.combine first second before).2 ∧
      ∀ records, result.payload = some records →
        let inputs := (SourceEqualityInheritedPayload.classes first.payload).getD [] ++
          (SourceEqualityInheritedPayload.classes second.payload).getD []
        Within (domain inputs) (records.map Record.paths) ∧
          EqualityModel.depth (records.flatMap Record.paths) ≤ heightBound inputs := by
  obtain ⟨result,actual,finalValid,ready,payload,growth⟩ :=
    SourceEqualityConstraintMemoAllocation.combine_correct first second before valid firstReady secondReady
  refine ⟨result,actual,finalValid,ready,growth,?_⟩
  intro records live
  have classes := SourceEqualityConstraintAllocation.read_classes _
    (SourceEqualityGuardReadback.combine_cached _ _) result.payload payload
  have source : SourceCompactGuards.combineEqualities
      (SourceEqualityInheritedPayload.classes first.payload) (SourceEqualityInheritedPayload.classes second.payload) =
        some (records.map Record.paths) := by
    simpa only [live,SourceEqualityInheritedPayload.classes,Option.map_some] using classes.symm
  have bounded := combine_classes _ _ _ source
  exact ⟨bounded.1,by simpa only [List.flatten_map] using bounded.2⟩

/-- Initial inherited and field data construct a bounded actual full accessor and combination prefix. -/
theorem inherited_prefix (original : Guard) (input : Value) (before : Operations) (valid : Valid before)
    (ready : Ready before.constraints input) (field : SourceCurrentConjunctionEquality.FieldAvailable before original) :
    ∃ result,
      (SourceCurrentAllocatedInheritedPrefix.run original input before).1 = .ok (some result) ∧
      Valid (SourceCurrentAllocatedInheritedPrefix.run original input before).2 ∧
      Ready (SourceCurrentAllocatedInheritedPrefix.run original input before).2.constraints result ∧
      Grows before (SourceCurrentAllocatedInheritedPrefix.run original input before).2 ∧
      ∀ records, result.payload = some records →
        let inputs := (SourceEqualityInheritedPayload.classes input.payload).getD [] ++
          (SourceCompactGuards.sourceEqualities original).getD []
        Within (domain inputs) (records.map Record.paths) ∧
          EqualityModel.depth (records.flatMap Record.paths) ≤ heightBound inputs := by
  cases input with
  | contradiction =>
      exact ⟨.contradiction,rfl,valid,ready,SourceEqualityConstraintMemoAllocation.grows_refl _,
        by intro records impossible; cases impossible⟩
  | live identity records =>
      obtain ⟨own,loaded,accessorValid,ownReady,classes,_,accessorGrowth⟩ :=
        SourceCurrentConjunctionEquality.accessor_correct original before valid field
      obtain ⟨result,actual,finalValid,resultReady,growth,bounded⟩ := combine (.live identity records) own _
        accessorValid (ready.grows accessorGrowth.constraint_growth) ownReady
      rw [SourceCurrentAllocatedInheritedPrefix.run_combine original identity records before own loaded]
      refine ⟨result,by simp only [actual,Except.map],finalValid,resultReady,
        SourceCurrentConjunctionEquality.grows_trans accessorGrowth growth,?_⟩
      intro outputs live
      simpa only [classes] using bounded outputs live

end MicroCFTA.SourceCurrentInheritedGainDomain
