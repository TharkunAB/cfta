import MicroCFTA.SourceCurrentOuterInheritedDescent
import MicroCFTA.SourceEqualityNormalizationReceipt
import MicroCFTA.SourceEqualityOriginalFieldOrigins

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
            have same : output = classes := RunResult.normalized.inj (by simpa only [fixMaybe,stepped,ite_true] using actual.symm)
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
      have same : next = output := Option.some.inj (by simpa only [result,SymbolicEqualityBridge.resultClasses] using completed)
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
                  refine ⟨?_,Nat.zero_le _⟩
                  intro path impossible
                  change path ∈ ([] : List Path) at impossible
                  cases impossible
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
  exact ⟨bounded.1,bounded.2⟩

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

set_option linter.all true
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.proofs true
set_option pp.proofs.threshold 254
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000
set_option maxRecDepth 30000
set_option maxHeartbeats 5000000
set_option cbv.maxSteps 10000000

namespace MicroCFTA.InheritedGainDomainKernels
open SourceEqualityConstraintAllocation SourceEqualityClassOrder
open SourceCurrentOuterInheritedDescent (pathHeight)
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
private theorem array_small (classes : EqualityNormalize.Constraints) :
    SourceCompactGuards.arrayNormalize classes = SourceEqualityNormalizationReceipt.observed 16 classes :=
  SourceEqualityNormalizationReceipt.observed_eq 16 classes
attribute [local cbv_eval] array_small
private def inheritedGuard : Guard := ⟨some [[[0],[1,0]],[[2],[3,0]]],.top⟩
private def ownGuard : Guard := ⟨some [[[1],[2]]],.top⟩
private def first := construct inheritedGuard.equalities Cache.emptyState
private def inherited : Value := match first.1 with | .ok value => value | _ => .contradiction
private def second := construct ownGuard.equalities first.2
private def own : Value := match second.1 with | .ok value => value | _ => .contradiction
private def before := SourceEqualityConstraintMemoAllocation.initial second.2
private noncomputable def accessor := SourceCurrentConjunctionEquality.accessor ownGuard before
private noncomputable def actual := SourceCurrentAllocatedInheritedPrefix.run ownGuard inherited before
private noncomputable def combined : Value := match actual.1 with | .ok (some value) => value | _ => .contradiction
private noncomputable def inputs : EqualityNormalize.Constraints :=
  (SourceEqualityInheritedPayload.classes inherited.payload).getD [] ++
    (SourceCompactGuards.sourceEqualities ownGuard).getD []
private theorem inherited_cached : SourceEqualityGuardReadback.Cached inheritedGuard.equalities := by
  intro classes same
  cases same
  exact SourceEqualityGuardReadback.normalized
    (show EqualityNormalize.mkEqConstraints 2 [[[0],[1,0]],[[2],[3,0]]] = .normalized [[[0],[1,0]],[[2],[3,0]]] by cbv)
private theorem own_cached : SourceEqualityGuardReadback.Cached ownGuard.equalities := by
  intro classes same
  cases same
  exact SourceEqualityGuardReadback.normalized
    (show EqualityNormalize.mkEqConstraints 2 [[[1],[2]]] = .normalized [[[1],[2]]] by cbv)
private theorem first_done : first = (.ok inherited,first.2) := by cbv
private theorem second_done : second = (.ok own,second.2) := by cbv
private theorem first_info : Cache.Valid first.2 ∧ Ready first.2 inherited := by
  obtain ⟨value,after,done,valid,ready,_,_,_⟩ := construct_complete inheritedGuard.equalities inherited_cached Cache.emptyState Cache.empty_valid
  obtain ⟨same,state⟩ := Prod.mk.inj (done.symm.trans first_done)
  cases Except.ok.inj same
  cases state
  exact ⟨valid,ready⟩
private theorem second_info : Cache.Valid second.2 ∧ Ready second.2 own ∧ Cache.Steps first.2 second.2 := by
  obtain ⟨value,after,done,valid,ready,steps,_,_⟩ := construct_complete ownGuard.equalities own_cached first.2 first_info.1
  obtain ⟨same,state⟩ := Prod.mk.inj (done.symm.trans second_done)
  cases Except.ok.inj same
  cases state
  exact ⟨valid,ready,steps⟩
private theorem inherited_ready : Ready before.constraints inherited := first_info.2.grows (Cache.steps_table_extends second_info.2.2)
private theorem field : SourceCurrentConjunctionEquality.FieldAvailable before ownGuard := by
  have origin := SourceEqualityOriginalFieldOrigins.of_construct ownGuard first.2 first_info.1 own second.2 second_done
  obtain ⟨loaded,done,_,_,_⟩ := SourceEqualityOriginalFieldOrigins.Origin.load ownGuard second.2 own_cached origin
  exact ⟨own_cached,loaded,done⟩
private theorem valid : SourceEqualityConstraintMemoAllocation.Valid before :=
  SourceEqualityConstraintMemoAllocation.initial_valid _ second_info.1
private theorem actual_done : actual.1 = .ok (some combined) := by cbv
private theorem input_fixed : SourceCurrentEqualityOperationFixed.FixedPayload inherited.payload := by
  intro records live
  cbv at live
  cases live
  cbv
private theorem own_fixed : SourceCurrentEqualityOperationFixed.FixedPayload own.payload := by
  intro records live
  cbv at live
  cases live
  cbv
private theorem bounded : ∀ records, combined.payload = some records →
    EqualitySaturation.Within (SourceCurrentInheritedGainDomain.domain inputs) (records.map Record.paths) ∧
      EqualityModel.depth (records.flatMap Record.paths) ≤ SourceCurrentInheritedGainDomain.heightBound inputs := by
  obtain ⟨result,done,_,_,_,bound⟩ := SourceCurrentInheritedGainDomain.inherited_prefix ownGuard inherited before valid inherited_ready field
  have same := Option.some.inj (Except.ok.inj (done.symm.trans actual_done))
  exact same ▸ bound
private theorem proof :
    SourceEqualityConstraintMemoAllocation.Valid before ∧ Ready before.constraints inherited ∧ Ready before.constraints own ∧
      SourceCurrentEqualityOperationFixed.FixedPayload inherited.payload ∧ SourceCurrentEqualityOperationFixed.FixedPayload own.payload ∧
      SourceCurrentConjunctionEquality.FieldAvailable before ownGuard ∧ accessor.1 = .ok (some own) ∧
      actual.1 = .ok (some combined) ∧ pathHeight inherited = 2 ∧ pathHeight own = 1 ∧ pathHeight combined = 3 ∧
      ∀ records, combined.payload = some records →
        EqualitySaturation.Within (SourceCurrentInheritedGainDomain.domain inputs) (records.map Record.paths) ∧
          EqualityModel.depth (records.flatMap Record.paths) ≤ SourceCurrentInheritedGainDomain.heightBound inputs := by
  exact ⟨valid,inherited_ready,second_info.2.1,input_fixed,own_fixed,field,by cbv,actual_done,by cbv,by cbv,by cbv,bounded⟩

/-- A shallower fixed own field activates an inherited dependency while the initial finite domain still bounds the actual result. -/
theorem shallower_own_gain :
    SourceEqualityConstraintMemoAllocation.Valid before ∧ Ready before.constraints inherited ∧ Ready before.constraints own ∧
      SourceCurrentEqualityOperationFixed.FixedPayload inherited.payload ∧ SourceCurrentEqualityOperationFixed.FixedPayload own.payload ∧
      SourceCurrentConjunctionEquality.FieldAvailable before ownGuard ∧ accessor.1 = .ok (some own) ∧
      actual.1 = .ok (some combined) ∧ pathHeight inherited = 2 ∧ pathHeight own = 1 ∧ pathHeight combined = 3 ∧
      ∀ records, combined.payload = some records →
        EqualitySaturation.Within (SourceCurrentInheritedGainDomain.domain inputs) (records.map Record.paths) ∧
          EqualityModel.depth (records.flatMap Record.paths) ≤ SourceCurrentInheritedGainDomain.heightBound inputs := proof

end MicroCFTA.InheritedGainDomainKernels
