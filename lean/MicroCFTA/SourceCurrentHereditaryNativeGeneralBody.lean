import MicroCFTA.SourceCurrentHereditaryNativeEffectsEdge

/-!
# Operand-local annotations through actual checked native row bodies

Actual loads retain both original full guards. The ready branch returns
their actual source conjunction. The rejected branches return Top. These
facts support any annotation predicate closed under Top and conjunction.
Physical checks and the incoming conditional Mu store remain explicit.
-/
namespace MicroCFTA.SourceCurrentHereditaryNativeGeneralBody
open Cache InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceEqualityAnnotationLanguage SourceCurrentHereditaryNativeScope
open SourceCurrentHereditaryNativeEffects
open SourceCurrentHereditaryNativeEffectsEdge (children_certified sentinel_certified)
open SourceCurrentHereditaryConstruction (MuStored)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Allocated" => SourceEqualityConjoinAllocation.Constraint FullSyntax.Formula
local instance : DecidableEq (SourceGuards.Guard FullSyntax.Formula) := SourceEqualityPCSNativeEdge.guardDecidableEq

/-- Actual loaded ready guards retain an annotation closed under source conjunction. -/
theorem loaded_ready_valid (annotation : Guard → Prop)
    (conjoinClosed : ∀ first second, annotation first → annotation second →
      annotation (SourceEqualityPCSNativeEdge.conjoin first second))
    (left right : Guard) (first second : Allocated) (firstArity secondArity : Nat)
    (before : SourceEqualityConstraintMemoAllocation.State)
    (valid : SourceEqualityConstraintMemoAllocation.Valid before)
    (leftCached : SourceEqualityGuardReadback.Cached left.equalities)
    (rightCached : SourceEqualityGuardReadback.Cached right.equalities)
    (leftLoad : SourceEqualityConstraintFieldLookup.load left before.constraints = .ok (some first))
    (rightLoad : SourceEqualityConstraintFieldLookup.load right before.constraints = .ok (some second))
    (leftValid : annotation left) (rightValid : annotation right) (result : Allocated)
    (done : (SourceEqualityIntersectionEdgeAllocation.run GuardStructuralOrder.le first second
      firstArity secondArity before).1 = .ok (.ready result)) :
    annotation (SourceEqualityConjoinAllocation.readback result) := by
  obtain ⟨firstReady, firstReadback⟩ := SourceEqualityConstraintFieldLookup.load_ready left
    before.constraints valid.constraints leftCached first leftLoad
  obtain ⟨secondReady, secondReadback⟩ := SourceEqualityConstraintFieldLookup.load_ready right
    before.constraints valid.constraints rightCached second rightLoad
  obtain ⟨branch, completed, mapped, _, _, _⟩ :=
    SourceEqualityIntersectionEdgeAllocation.run_correct GuardStructuralOrder.le first second
      firstArity secondArity before valid firstReady secondReady
  have equal : branch = .ready result := Except.ok.inj (completed.symm.trans done)
  subst branch
  simp only [SourceEqualityIntersectionEdgeAllocation.Branch.map,
    SourceEqualityIntersectionEdgeAllocation.source] at mapped
  split at mapped
  · cases mapped
  · split at mapped
    · have same := SourceEqualityIntersectionEdgeAllocation.Branch.ready.inj mapped
      rw [same, firstReadback, secondReadback]
      exact conjoinClosed left right leftValid rightValid
    · cases mapped

/-- Each actual yielded body derives its own row annotation and constructor effects. -/
theorem body_certified [DecidableEq (EdgeKey Symbol Guard)]
    (annotation : Guard → Prop)
    (validTop : annotation SourceEqualityConstraintConstructors.top)
    (conjoinClosed : ∀ first second, annotation first → annotation second →
      annotation (SourceEqualityPCSNativeEdge.conjoin first second))
    (source : InternedConstructorTemplates.State Symbol Guard)
    (request : EdgeRequest Symbol Guard) (before after : Checked width)
    (code : Code Symbol Guard (EdgeValue Symbol Guard))
    (good : SourceCurrentAllocatedNativePhysicalCompletion.Good before)
    (represented : MuStored annotation before.native.machine.heap) (ready : EdgeReady before.native.machine request)
    (bindings : Bindings annotation source request.domain.key)
    (left : SourceCurrentHereditaryConstructors.Edge annotation request.left)
    (right : SourceCurrentHereditaryConstructors.Edge annotation request.right)
    (yielded : SourceEqualityNativeDemand.body request .pure before = .yielded (.code code) after) :
    Certified annotation source code after.native.machine
      (fun final value => EdgeResident final.heap value ∧
        SourceCurrentHereditaryConstructors.Edge annotation value) := by
  have same : after.native = before.native := by
    simpa only [yielded, SourceEqualityNativeDemand.Outcome.state] using
      SourceEqualityNativeDemandOperations.body_native request .pure before
  rw [same]
  by_cases arity : request.left.children.length = request.right.children.length
  · have matched : ¬ request.left.children.length ≠ request.right.children.length := by omega
    simp only [SourceEqualityNativeDemand.body, ite_eq_right matched] at yielded
    cases firstLoaded : SourceEqualityConstraintFieldLookup.load request.left.entry.key.constraint before.operations.constraints with
    | error message => simp only [firstLoaded] at yielded; cases yielded
    | ok first =>
        cases first with
        | none => simp only [firstLoaded] at yielded; cases yielded
        | some first =>
            simp only [firstLoaded] at yielded
            cases secondLoaded : SourceEqualityConstraintFieldLookup.load request.right.entry.key.constraint before.operations.constraints with
            | error message => simp only [secondLoaded] at yielded; cases yielded
            | ok second =>
                cases second with
                | none => simp only [secondLoaded] at yielded; cases yielded
                | some second =>
                    simp only [secondLoaded] at yielded
                    have firstCached := (good.fields _ _ ready.2.1).1
                    have secondCached := (good.fields _ _ ready.2.2).1
                    have firstReady := (SourceEqualityConstraintFieldLookup.load_ready _ _ good.operations.constraints
                      firstCached first firstLoaded).1
                    have secondReady := (SourceEqualityConstraintFieldLookup.load_ready _ _ good.operations.constraints
                      secondCached second secondLoaded).1
                    obtain ⟨branch, done, _, _⟩ := SourceEqualityIntersectionEdgeAllocation.run_correct
                      GuardStructuralOrder.le first second request.left.children.length request.right.children.length
                      before.operations good.operations firstReady secondReady
                    cases branch with
                    | mismatch | rejected =>
                        simp only [done, SourceEqualityNativeDemand.sentinel, SourceEqualityNativeDemand.code_bind_pure] at yielded
                        cases yielded
                        exact sentinel_certified _ source request.left _ good.native.machine
                          validTop
                    | ready combined =>
                        have combinedValid := loaded_ready_valid annotation conjoinClosed request.left.entry.key.constraint request.right.entry.key.constraint
                          first second request.left.children.length request.right.children.length before.operations good.operations
                          firstCached secondCached firstLoaded secondLoaded left.1 right.1 combined done
                        simp only [done, SourceEqualityNativeDemand.code_bind_pure] at yielded
                        cases yielded
                        exact children_certified _ source request combined _ good.native.machine represented ready
                          bindings left right combinedValid
  · simp only [SourceEqualityNativeDemand.body, ite_eq_left arity, SourceEqualityNativeDemand.sentinel,
      SourceEqualityNativeDemand.code_bind_pure] at yielded
    cases yielded
    exact sentinel_certified _ source request.left _ good.native.machine
      validTop


end MicroCFTA.SourceCurrentHereditaryNativeGeneralBody
