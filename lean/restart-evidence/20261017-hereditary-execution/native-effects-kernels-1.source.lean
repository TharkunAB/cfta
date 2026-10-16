import MicroCFTA.SourceCurrentHereditaryNativeEffectsEdge
import MicroCFTA.SourceCurrentHereditaryNativeEffectsCompile
import MicroCFTA.SourceCurrentAllocatedNativeCodeProgress

set_option linter.all true
set_option pp.explicit true
set_option pp.proofs true
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000
set_option format.width 200

namespace MicroCFTA.HereditaryNativeEffectsChecks
open Cache InternedConstructorTemplates InternedProbeProvenance InternedNestedFacts InternedEdgeResidency
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceEqualityAnnotationLanguage
open SourceCurrentHereditaryConstruction (MuStored)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Plain" => fun guard : Guard => SourceMemoGate.plain guard = true
local instance : DecidableEq (SourceGuards.Guard FullSyntax.Formula) := SourceEqualityPCSNativeEdge.guardDecidableEq
variable [DecidableEq (EdgeKey Symbol Guard)]

/-- A mismatched actual body emits its sentinel and its literal work derives residency and local annotation. -/
theorem mismatch_constructs_annotated (source : InternedConstructorTemplates.State Symbol Guard)
    (request : EdgeRequest Symbol Guard) (before : Checked width)
    (valid : SourceRecursiveIntersectionKernel.Valid before.native.machine)
    (stored : MuStored Plain before.native.machine.heap)
    (mismatch : request.left.children.length ≠ request.right.children.length) :
    let job := makeEdge request.left.entry.key.symbol (SourceEqualityConstraintConstructors.top (Formula := FullSyntax.Formula)) [.empty]
    let output := run job before.native.machine.heap
    let final : Machine Symbol Guard := {before.native.machine with heap := output.2}
    SourceEqualityNativeDemand.body request .pure before =
      .yielded (.code (SourceEqualityNativeCheckedCode.sentinel request.left))
        {before with operations := SourceEqualityMkEdgeAllocation.emptyField before.operations} ∧
      SourceRecursiveIntersectionKernel.work job before.native.machine = .done output.1 final ∧
      MuStored Plain final.heap ∧ EdgeResident final.heap output.1 ∧ SourceCurrentHereditaryConstructors.Edge Plain output.1 := by
  dsimp only
  let job := makeEdge request.left.entry.key.symbol (SourceEqualityConstraintConstructors.top (Formula := FullSyntax.Formula)) [.empty]
  let output := run job before.native.machine.heap
  let final : Machine Symbol Guard := {before.native.machine with heap := output.2}
  have done : SourceRecursiveIntersectionKernel.work job before.native.machine = .done output.1 final := rfl
  have safe := (SourceCurrentAllocatedNativeCodeProgress.sentinel_certified request.left before.native.machine valid).1
  have finalValid : SourceRecursiveIntersectionKernel.Valid final := safe.1
  have growth : Extension before.native.machine final := safe.2.1
  have certificate := SourceCurrentHereditaryNativeEffectsEdge.sentinel_certified Plain source
    request.left before.native.machine valid SourceCurrentUnconstrainedGuardClosure.top_plain
  have produced := SourceCurrentHereditaryNativeEffects.work_stored Plain job certificate.1 before.native.machine stored output.1 final done
  have returned := certificate.2 output.1 final done finalValid growth produced
  refine ⟨?_, done, produced, returned⟩
  rw [SourceEqualityNativeDemand.body_mismatch request .pure before mismatch]
  simp only [SourceEqualityNativeDemand.sentinel, SourceEqualityNativeDemand.code_bind_pure]

/-- An actual ready nullary branch emits no child callback and derives its own constructor result annotation. -/
theorem nullary_ready_constructs_annotated (source : InternedConstructorTemplates.State Symbol Guard)
    (request : EdgeRequest Symbol Guard) (before : Checked width)
    (good : SourceCurrentAllocatedNativePhysicalCompletion.Good before)
    (stored : MuStored Plain before.native.machine.heap)
    (ready : EdgeReady before.native.machine request)
    (bindings : SourceCurrentHereditaryNativeScope.Bindings Plain source request.domain.key)
    (left : SourceCurrentHereditaryConstructors.Edge Plain request.left)
    (right : SourceCurrentHereditaryConstructors.Edge Plain request.right)
    (leftEmpty : request.left.children = []) (rightEmpty : request.right.children = [])
    (first second combined : SourceEqualityConjoinAllocation.Constraint FullSyntax.Formula)
    (firstLoad : SourceEqualityConstraintFieldLookup.load request.left.entry.key.constraint before.operations.constraints = .ok (some first))
    (secondLoad : SourceEqualityConstraintFieldLookup.load request.right.entry.key.constraint before.operations.constraints = .ok (some second))
    (combinedDone : (SourceEqualityIntersectionEdgeAllocation.run GuardStructuralOrder.le first second 0 0 before.operations).1 =
      .ok (.ready combined)) :
    let after : Checked width := {before with operations :=
      (SourceEqualityIntersectionEdgeAllocation.run GuardStructuralOrder.le first second 0 0 before.operations).2}
    let job := makeEdge request.left.entry.key.symbol (SourceEqualityConjoinAllocation.readback combined) []
    let output := run job after.native.machine.heap
    let final : Machine Symbol Guard := {after.native.machine with heap := output.2}
    SourceEqualityNativeDemand.body request .pure before = .yielded (.code (.work job .pure)) after ∧
      SourceRecursiveIntersectionKernel.work job after.native.machine = .done output.1 final ∧
      MuStored Plain final.heap ∧ EdgeResident final.heap output.1 ∧ SourceCurrentHereditaryConstructors.Edge Plain output.1 := by
  dsimp only
  let after : Checked width := {before with operations :=
    (SourceEqualityIntersectionEdgeAllocation.run GuardStructuralOrder.le first second 0 0 before.operations).2}
  let job := makeEdge request.left.entry.key.symbol (SourceEqualityConjoinAllocation.readback combined) []
  let output := run job after.native.machine.heap
  let final : Machine Symbol Guard := {after.native.machine with heap := output.2}
  have yielded : SourceEqualityNativeDemand.body request .pure before = .yielded (.code (.work job .pure)) after := by
    simp only [SourceEqualityNativeDemand.body, leftEmpty, rightEmpty, List.length_nil, ne_eq, not_true_eq_false,
      ↓reduceIte, firstLoad, secondLoad, combinedDone, SourceEqualityNativeDemand.code_bind_pure,
      SourceEqualityNativeCheckedCode.children]
    rfl
  have certificate := SourceCurrentHereditaryNativeEffectsEdge.body_certified source request before after
    (.work job .pure) good stored ready bindings left right yielded
  have physical := SourceCurrentAllocatedNativeCodeProgress.body_certified request before after (.work job .pure)
    good.native.machine ready yielded
  have done : SourceRecursiveIntersectionKernel.work job after.native.machine = .done output.1 final := rfl
  have finalValid : SourceRecursiveIntersectionKernel.Valid final := by simpa only [done, Result.state] using physical.1.1
  have growth : Extension after.native.machine final := by simpa only [done, Result.state] using physical.1.2.1
  have produced := SourceCurrentHereditaryNativeEffects.work_stored Plain job certificate.1 after.native.machine stored output.1 final done
  exact ⟨yielded, done, produced, certificate.2 output.1 final done finalValid growth produced⟩

/-- A prepared local binder constructs its own result and reuses that exact complete payload. -/
theorem prepared_binder_then_warm (annotation : Guard → Prop) (source : InternedConstructorTemplates.State Symbol Guard)
    (key : Nat × Nat) (body : Value Symbol Guard) (before : Machine Symbol Guard)
    (valid : SourceRecursiveIntersectionKernel.Valid before) (stored : MuStored annotation before.heap)
    (available : Available before.heap body) (annotated : Annotated annotation body)
    (covered : InternedRecordCoherence.Covered [] before.heap)
    (prepared : InternedStoredClosedMuCompletion.PreparedWithoutMu body) :
    ∃ value after,
      construction (SourceRecursiveIntersectionMaybeMu.maybeMu key body before.heap) before = .done value after ∧
      MuStored annotation after.heap ∧ Annotated annotation value ∧
      construction (SourceRecursiveIntersectionMaybeMu.maybeMu key body after.heap) after = .done value after ∧
      SourceCurrentHereditaryNativeEffects.Certified annotation source (.optionalBinder key body .pure) after
        (fun final result => Available final.heap result ∧ Annotated annotation result) := by
  obtain ⟨value, heap, done, facts, _returned, growth, history⟩ :=
    SourceRecursiveIntersectionMaybeMu.complete key body before.heap valid.1 available covered prepared
  let after : Machine Symbol Guard := {before with heap := heap}
  have actual : construction (SourceRecursiveIntersectionMaybeMu.maybeMu key body before.heap) before = .done value after := by
    simp only [done, construction, after]
  obtain ⟨afterStored, valueAnnotated⟩ := SourceCurrentHereditaryNativeEffects.optionalBinder_result
    annotation key body before valid stored available annotated value after actual
  have replay := SourceRecursiveIntersectionMaybeMu.replay key body before.heap heap heap valid.1 available value done (Cache.grows_refl _)
  have warm : construction (SourceRecursiveIntersectionMaybeMu.maybeMu key body after.heap) after = .done value after := by
    simpa only [replay, construction] using (rfl : SourceRecursiveIntersectionKernel.Result.done value after = .done value after)
  have afterValid : SourceRecursiveIntersectionKernel.Valid after := ⟨facts, valid.2⟩
  have bodyAvailable := available.grows before.heap heap growth history
  exact ⟨value, after, actual, afterStored, valueAnnotated, warm,
    SourceCurrentHereditaryNativeEffects.optional_binder_certified annotation source key body after afterValid afterStored bodyAvailable annotated⟩

#print axioms mismatch_constructs_annotated
#check @mismatch_constructs_annotated
#print axioms nullary_ready_constructs_annotated
#check @nullary_ready_constructs_annotated
#print axioms prepared_binder_then_warm
#check @prepared_binder_then_warm
end MicroCFTA.HereditaryNativeEffectsChecks
