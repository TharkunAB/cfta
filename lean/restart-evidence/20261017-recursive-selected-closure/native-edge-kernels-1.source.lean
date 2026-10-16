import MicroCFTA.SourceCurrentHereditaryNativeEdge
import MicroCFTA.SourceCurrentAllocatedNativeCodeProgress

set_option linter.all true
set_option pp.explicit true
set_option pp.proofs true
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000
set_option format.width 200

namespace MicroCFTA.HereditaryNativeEdgeIndependent
open Cache InternedConstructorTemplates InternedProbeProvenance InternedNestedFacts InternedEdgeResidency
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceEqualityAnnotationLanguage
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Plain" => fun guard : Guard => SourceMemoGate.plain guard = true
variable [DecidableEq (EdgeKey Symbol Guard)]

/-- A mismatched actual body emits its sentinel and its literal work derives residency and local annotation. -/
theorem mismatch_constructs_annotated (source : InternedConstructorTemplates.State Symbol Guard)
    (request : EdgeRequest Symbol Guard) (before : Checked width)
    (valid : SourceRecursiveIntersectionKernel.Valid before.native.machine)
    (mismatch : request.left.children.length ≠ request.right.children.length) :
    let job := makeEdge request.left.entry.key.symbol SourceEqualityConstraintConstructors.top [.empty]
    let output := run job before.native.machine.heap
    let final : Machine Symbol Guard := {before.native.machine with heap := output.2}
    SourceEqualityNativeDemand.body request .pure before =
      .yielded (.code (SourceEqualityNativeCheckedCode.sentinel request.left))
        {before with operations := SourceEqualityMkEdgeAllocation.emptyField before.operations} ∧
      SourceRecursiveIntersectionKernel.work job before.native.machine = .done output.1 final ∧
      EdgeResident final.heap output.1 ∧ SourceCurrentHereditaryConstructors.Edge Plain output.1 := by
  dsimp only
  let job := makeEdge request.left.entry.key.symbol SourceEqualityConstraintConstructors.top [.empty]
  let output := run job before.native.machine.heap
  let final : Machine Symbol Guard := {before.native.machine with heap := output.2}
  have done : SourceRecursiveIntersectionKernel.work job before.native.machine = .done output.1 final := rfl
  have safe := (SourceCurrentAllocatedNativeCodeProgress.sentinel_certified request.left before.native.machine valid).1
  have finalValid : SourceRecursiveIntersectionKernel.Valid final := by simpa only [done, Result.state] using safe.1
  have growth : Extension before.native.machine final := by simpa only [done, Result.state] using safe.2.1
  have certificate := SourceCurrentHereditaryNativeEdge.sentinel_certified Plain source (fun _ => True)
    request.left before.native.machine valid SourceCurrentUnconstrainedGuardClosure.top_plain
  have returned := certificate output.1 final done finalValid growth trivial
  refine ⟨?_, done, returned⟩
  rw [SourceEqualityNativeDemand.body_mismatch request .pure before mismatch]
  simp only [SourceEqualityNativeDemand.sentinel, SourceEqualityNativeDemand.code_bind_pure]

/-- An actual ready nullary branch emits no child callback and derives its own constructor result annotation. -/
theorem nullary_ready_constructs_annotated (source : InternedConstructorTemplates.State Symbol Guard)
    (request : EdgeRequest Symbol Guard) (before : Checked width)
    (good : SourceCurrentAllocatedNativePhysicalCompletion.Good before)
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
      EdgeResident final.heap output.1 ∧ SourceCurrentHereditaryConstructors.Edge Plain output.1 := by
  dsimp only
  let after : Checked width := {before with operations :=
    (SourceEqualityIntersectionEdgeAllocation.run GuardStructuralOrder.le first second 0 0 before.operations).2}
  let job := makeEdge request.left.entry.key.symbol (SourceEqualityConjoinAllocation.readback combined) []
  let output := run job after.native.machine.heap
  let final : Machine Symbol Guard := {after.native.machine with heap := output.2}
  have yielded : SourceEqualityNativeDemand.body request .pure before = .yielded (.code (.work job .pure)) after := by
    simp only [SourceEqualityNativeDemand.body, leftEmpty, rightEmpty, List.length_nil, ne_eq, not_true_eq_false,
      ↓reduceIte, firstLoad, secondLoad, combinedDone, SourceEqualityNativeDemand.code_bind_pure]
    rfl
  have certificate := SourceCurrentHereditaryNativeEdge.body_certified source (fun _ => True) request before after
    (.work job .pure) good trivial ready bindings left right yielded
  have physical := SourceCurrentAllocatedNativeCodeProgress.body_certified request before after (.work job .pure)
    good.native.machine ready yielded
  have done : SourceRecursiveIntersectionKernel.work job after.native.machine = .done output.1 final := rfl
  have finalValid : SourceRecursiveIntersectionKernel.Valid final := by simpa only [done, Result.state] using physical.1.1
  have growth : Extension after.native.machine final := by simpa only [done, Result.state] using physical.1.2.1
  exact ⟨yielded, done, certificate output.1 final done finalValid growth trivial⟩

#print axioms mismatch_constructs_annotated
#check @mismatch_constructs_annotated
#print axioms nullary_ready_constructs_annotated
#check @nullary_ready_constructs_annotated
end MicroCFTA.HereditaryNativeEdgeIndependent
