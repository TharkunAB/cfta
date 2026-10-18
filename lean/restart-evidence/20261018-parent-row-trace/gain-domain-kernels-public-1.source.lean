import MicroCFTA.SourceCurrentInheritedGainDomain
import MicroCFTA.SourceCurrentOuterInheritedDescent
import MicroCFTA.SourceEqualityNormalizationReceipt
import MicroCFTA.SourceEqualityOriginalFieldOrigins

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

#check @MicroCFTA.InheritedGainDomainKernels.shallower_own_gain
#print MicroCFTA.InheritedGainDomainKernels.shallower_own_gain
#print axioms MicroCFTA.InheritedGainDomainKernels.shallower_own_gain
