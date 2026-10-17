import MicroCFTA.SourceRecursiveIntersectionCompileInstructionCredit
import MicroCFTA.SourceEqualityNativeCheckedInstructionCredit
import MicroCFTA.SourceCurrentAllocatedRecursiveRequestStep
import MicroCFTA.SourceEqualityNativeDemandBodyYield
import MicroCFTA.SourceCurrentAllocatedNativePhysicalCompletion

/-!
# Instruction credit through actual checked native steps

Every yielded step consumes at least one credit. A native miss retains its
captured finish frame. Checked edge demand reserves its actual body effect.
Warm returns use the same continuation at the same physical result.
-/
namespace MicroCFTA.SourceCurrentAllocatedNativeInstructionStep
open Cache InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceRecursiveIntersectionInputView IntersectSchedule SourceEqualityNativeDemand
open SourceCurrentAllocatedNativePhysicalCompletion (Good)
open SourceCurrentAllocatedNativeFieldClosure (Fields)
open SourceRecursiveIntersectionInstructionProfile (budget sourceBranching)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Credit" => SourceRecursiveIntersectionInstructionCredit.At
variable {width : Nat} {A : Type}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]

/-- A demanded edge body pays its own effect, child code, and exact continuation. -/
def ControlAt (source : InternedConstructorTemplates.State Symbol Guard)
    (holds : Guard → Language.Term Symbol → Bool) (control : Control A) (before : Checked width)
    (amount : Nat) (post : Machine Symbol Guard → A → Prop) : Prop :=
  match control with
  | .code code => Credit source holds (sourceBranching source) code before.native.machine amount post
  | .edgeBody request next => EdgeReady before.native.machine request ∧ EdgeScope source request ∧
      ∃ (complete : Completes (view source holds) (SourceRecursiveIntersectionNative.edgeSemantic holds request)) (rest : Nat),
        2 + sourceBranching source * budget (sourceBranching source)
          (requiredFuel (view source holds) (SourceRecursiveIntersectionNative.edgeSemantic holds request) complete - 1) + rest ≤ amount ∧
        ∀ value after, SourceRecursiveIntersectionKernel.Valid after → Extension before.native.machine after →
          EdgeResident after.heap value → Credit source holds (sourceBranching source) (next value) after rest post

/-- Extra credit retains the same checked control. -/
theorem ControlAt.mono (source : InternedConstructorTemplates.State Symbol Guard)
    (holds : Guard → Language.Term Symbol → Bool) (control : Control A) (before : Checked width)
    {first last : Nat} (certificate : ControlAt source holds control before first post) (enough : first ≤ last) :
    ControlAt source holds control before last post := by
  cases control with
  | code code => exact SourceRecursiveIntersectionInstructionCredit.mono code _ certificate enough
  | edgeBody request next =>
      obtain ⟨ready, scope, complete, rest, paid, continuation⟩ := certificate
      exact ⟨ready, scope, complete, rest, Nat.le_trans paid enough, continuation⟩

/-- Every actual yielded instruction consumes credit without changing its protected continuation. -/
theorem yielded (source : InternedConstructorTemplates.State Symbol Guard) (facts : InternedNestedFacts.Facts source)
    (holds : Guard → Language.Term Symbol → Bool) (control next : Control A) (before after : Checked width)
    (amount : Nat) (post : Machine Symbol Guard → A → Prop)
    (good : Good before) (physical : SourceCurrentAllocatedNativePhysicalExecution.Inputs control before)
    (fields : Fields control before) (sourceGrowth : Grows source before.native.machine.heap)
    (sourceHistory : Extends source.nodes.issued before.native.machine.heap.nodes.issued)
    (certificate : ControlAt source holds control before amount post)
    (one : step control before = .yielded next after) :
    ∃ remaining, remaining + 1 ≤ amount ∧ ControlAt source holds next after remaining post := by
  have effects := SourceCurrentAllocatedNativePhysicalCompletion.step_invariants control before good physical fields
  have current : Good after := by simpa only [one, Outcome.state] using effects.1
  have growth : Extension before.native.machine after.native.machine := by
    simpa only [one, Outcome.state] using effects.2.1
  cases control with
  | edgeBody request continuation =>
      obtain ⟨ready, scope, complete, rest, enough, resume⟩ := certificate
      obtain ⟨body, pureBody, same⟩ := SourceEqualityNativeDemandBodyYield.yielded_unbind request continuation before after next one
      subst next
      have emitted := SourceEqualityNativeCheckedInstructionCredit.body_at source facts holds request scope complete
        before after body good.native.machine ready pureBody
      let childCredit := sourceBranching source * budget (sourceBranching source)
        (requiredFuel (view source holds) (SourceRecursiveIntersectionNative.edgeSemantic holds request) complete - 1)
      refine ⟨(1 + childCredit) + rest, by dsimp only [childCredit]; omega, ?_⟩
      apply SourceRecursiveIntersectionInstructionCredit.bind body continuation after.native.machine
        (1 + childCredit) rest current.native.machine _ post emitted.2
      intro value final finalValid later resident
      exact resume value final finalValid (growth.trans later) resident
  | code code =>
      cases code with
      | pure | fail => cases one
      | work job continuation =>
          obtain ⟨rest, enough, resume⟩ := certificate
          obtain ⟨rfl, rfl⟩ := Outcome.yielded.inj one
          exact ⟨rest, enough, resume _ _ current.native.machine growth rfl⟩
      | enter domain left right first second continuation =>
          obtain ⟨rest, enough, resume⟩ := certificate
          obtain ⟨rfl, rfl⟩ := Outcome.yielded.inj one
          exact ⟨rest, enough, resume current.native.machine growth⟩
      | read name continuation =>
          obtain ⟨rest, enough, resume⟩ := certificate
          obtain ⟨rfl, rfl⟩ := Outcome.yielded.inj one
          exact ⟨rest, enough, resume⟩
      | optionalBinder key body continuation =>
          obtain ⟨available, rest, enough, resume⟩ := certificate
          have checked := construction_checked before.native.machine good.native.machine _ Available
            (SourceRecursiveIntersectionMaybeMu.verified key body before.native.machine.heap good.native.machine.1 available)
          cases done : SourceRecursiveIntersectionMaybeMu.maybeMu key body before.native.machine.heap with
          | pending pending heap =>
              simp only [step, SourceRecursiveIntersectionNative.step, done, lift] at one
              cases one
          | done value heap =>
              simp only [step, SourceRecursiveIntersectionNative.step, done, lift] at one
              obtain ⟨rfl, rfl⟩ := Outcome.yielded.inj one
              have present := checked.result value {before.native.machine with heap := heap}
                (by simp only [done, construction])
              exact ⟨rest, enough, resume value _ current.native.machine growth present⟩
      | node request continuation =>
          obtain ⟨ready, cost, rest, charged, enough, resume⟩ := certificate
          obtain ⟨scope, complete, paid⟩ := charged
          let rank := requiredFuel (view source holds) (SourceRecursiveIntersectionNative.nodeSemantic request) complete
          let childCredit := sourceBranching source * budget (sourceBranching source) (rank - 1)
          have positive : 0 < rank := requiredFuel_positive _ _ complete
          have rankStep : rank - 1 + 1 = rank := by omega
          have total : budget (sourceBranching source) rank = 4 + childCredit := by
            rw [← rankStep, SourceRecursiveIntersectionInstructionProfile.budget_succ]
          have covered : 4 + childCredit + rest ≤ amount := by rw [← total] at *; omega
          obtain ⟨machine, _, branches⟩ := SourceCurrentAllocatedRecursiveRequestStep.node_yielded request continuation before
            next after good.native ready physical.2 one
          rcases branches with ⟨rfl, sameBefore⟩ | ⟨value, rfl, available⟩ | ⟨handle, rfl, _⟩
          · subst after
            have compiled := SourceRecursiveIntersectionCompileInstructionCredit.compileNode source facts holds request scope complete
              before.native.machine good.native.machine ready sourceGrowth sourceHistory
            refine ⟨(2 + childCredit) + rest, by omega, ?_⟩
            apply SourceRecursiveIntersectionInstructionCredit.bind _ continuation before.native.machine
              (2 + childCredit) rest good.native.machine _ post compiled
            intro value final finalValid later available
            exact resume value final finalValid later available
          · exact ⟨rest, by omega, resume value after.native.machine current.native.machine growth available⟩
          · have compiled := SourceRecursiveIntersectionCompileInstructionCredit.compileNode source facts holds request scope complete
              after.native.machine current.native.machine (by rw [machine]; exact ready)
              (by rw [machine]; exact sourceGrowth) (by rw [machine]; exact sourceHistory)
            refine ⟨(2 + childCredit) + (rest + 1), by omega, ?_⟩
            apply SourceRecursiveIntersectionInstructionCredit.bind _ _ after.native.machine
              (2 + childCredit) (rest + 1) current.native.machine _ post compiled
            intro value final finalValid later available
            exact ⟨rest, Nat.le_refl _, resume value final finalValid (growth.trans later) available⟩
      | edge request continuation =>
          obtain ⟨ready, cost, rest, charged, enough, resume⟩ := certificate
          obtain ⟨scope, complete, paid⟩ := charged
          let rank := requiredFuel (view source holds) (SourceRecursiveIntersectionNative.edgeSemantic holds request) complete
          let childCredit := sourceBranching source * budget (sourceBranching source) (rank - 1)
          have positive : 0 < rank := requiredFuel_positive _ _ complete
          have rankStep : rank - 1 + 1 = rank := by omega
          have total : budget (sourceBranching source) rank = 4 + childCredit := by
            rw [← rankStep, SourceRecursiveIntersectionInstructionProfile.budget_succ]
          have covered : 4 + childCredit + rest ≤ amount := by rw [← total] at *; omega
          obtain ⟨machine, _, branches⟩ := SourceCurrentAllocatedRecursiveRequestStep.edge_yielded request continuation before
            next after good.native ready physical.2 one
          rcases branches with ⟨value, rfl, resident⟩ | ⟨handle, rfl, _⟩
          · exact ⟨rest, by omega, resume value after.native.machine current.native.machine growth resident⟩
          · refine ⟨(2 + childCredit) + (rest + 1), by omega, ?_⟩
            refine ⟨by rw [machine]; exact ready, scope, complete, rest + 1, Nat.le_refl _, ?_⟩
            intro value final finalValid later resident
            exact ⟨rest, Nat.le_refl _, resume value final finalValid (growth.trans later) resident⟩
      | finishNode handle value continuation | finishEdge handle value continuation =>
          obtain ⟨rest, enough, resume⟩ := certificate
          obtain ⟨rfl, rfl⟩ := Outcome.yielded.inj one
          exact ⟨rest, enough, resume⟩

end MicroCFTA.SourceCurrentAllocatedNativeInstructionStep
