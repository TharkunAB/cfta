import MicroCFTA.SourceEqualityPartialNativeHeap
import MicroCFTA.SourceEqualityNativeDemandMismatchReceipt
import MicroCFTA.SourceEqualityNativeDemandRejectedReceipt

/-!
# Completed stopped native calls inside recursive memo scope

Actual stopped branches derive their constructor and operation receipts.
These receipts preserve the current recursive memo and both native memo
families. No reached-path plan or future soundness fact is supplied for
the mismatch branch.
-/
namespace MicroCFTA.SourceEqualityPartialNativeStopped
open InternedConstructorTemplates SourceRecursiveIntersectionThunks SourceEqualityNativeDemand
open SourceEqualityPartialNativeDemand
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Worker" => SourceEqualityPartialMemoWorker.State
local notation "Operations" => SourceEqualityConstraintMemoAllocation.State

/-- A fresh mismatch call derives native validity and preserves all surrounding result cells. -/
theorem mismatch_sound [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (holds : Guard → Language.Term Symbol → Bool) (ambient : InternedGuardedLanguage.Env Symbol)
    (request : EdgeRequest Symbol Guard) (operations : Operations) (worker : Worker width)
    (valid : SourceEqualityConstraintMemoAllocation.Valid operations) (same : worker.constraints = operations.constraints)
    (sound : SourceEqualityPartialMemoSound.Sound holds ambient worker)
    (nativeValid : SourceEqualityNativeDemandProvenance.Valid holds worker.native)
    (ready : SourceEqualityRequiredCache.Ready worker.native.machine.heap)
    (inputs : EdgeReady worker.native.machine request)
    (safe : SourceRecursiveIntersectionEdgeMemo.KeySafe width request.domain request.left request.right)
    (mismatch : request.left.children.length ≠ request.right.children.length)
    (missing : worker.native.edges.table
      (SourceRecursiveIntersectionEdgeMemo.requestKey width request.domain request.left request.right) = none) :
    ∃ result after, execute 5 (.code (.edge request .pure)) (input operations worker) = .done result after ∧
      SourceEqualityConstraintMemoAllocation.Valid after.operations ∧
      SourceEqualityConstraintMemoAllocation.Grows operations after.operations ∧
      SourceEqualityNativeDemandProvenance.Valid holds after.native ∧
      SourceEqualityNativeDemandProvenance.EdgeProduced (width := width) holds after.native.machine request result ∧
      SourceEqualityPartialMemoFrame.Frame (SourceEqualityPartialMemoFrame.stateTables worker)
        (SourceEqualityPartialMemoFrame.stateTables (returned worker (.done result after))) ∧
      SourceEqualityPartialMemoSound.Sound holds ambient (returned worker (.done result after)) := by
  let before := input operations worker
  obtain ⟨result, after, done, afterValid, produced, keeps, _, _⟩ :=
    SourceEqualityNativeDemandMismatchReceipt.mismatch_miss_native_valid holds request before nativeValid ready inputs safe mismatch missing
  have exactRun := mismatch_miss_complete request before mismatch missing
  have afterOperations : after.operations = SourceEqualityMkEdgeAllocation.emptyField operations := by
    have sameResult := Outcome.done.inj (done.symm.trans exactRun)
    exact congrArg State.operations sameResult.2
  have allocated := SourceEqualityMkEdgeAllocation.emptyField_correct operations valid
  have operationValid : SourceEqualityConstraintMemoAllocation.Valid after.operations := by
    rw [afterOperations]
    exact allocated.1
  have growth : SourceEqualityConstraintMemoAllocation.Grows operations after.operations := by
    rw [afterOperations]
    exact allocated.2.1
  have outer := SourceEqualityPartialNativeHeap.observed_sound holds ambient worker operations (.done result after)
    same sound growth keeps
  exact ⟨result, after, done, operationValid, growth, afterValid, produced, outer⟩

/-- Actual fresh checked rejection derives both native receipts and current outer memo soundness. -/
theorem rejected_sound [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (ambient : InternedGuardedLanguage.Env Symbol) (request : EdgeRequest Symbol Guard)
    (operations : Operations) (worker : Worker width)
    (first second : SourceEqualityConjoinAllocation.Constraint FullSyntax.Formula)
    (valid : SourceEqualityConstraintMemoAllocation.Valid operations) (same : worker.constraints = operations.constraints)
    (sound : SourceEqualityPartialMemoSound.Sound (SourceEqualityPCSGuard.holds formulas solver) ambient worker)
    (nativeValid : SourceEqualityNativeDemandProvenance.Valid (SourceEqualityPCSGuard.holds formulas solver) worker.native)
    (ready : SourceEqualityRequiredCache.Ready worker.native.machine.heap)
    (inputs : EdgeReady worker.native.machine request)
    (safe : SourceRecursiveIntersectionEdgeMemo.KeySafe width request.domain request.left request.right)
    (leftCached : SourceEqualityGuardReadback.Cached request.left.entry.key.constraint.equalities)
    (rightCached : SourceEqualityGuardReadback.Cached request.right.entry.key.constraint.equalities)
    (arity : request.left.children.length = request.right.children.length)
    (left : SourceEqualityConstraintFieldLookup.load request.left.entry.key.constraint operations.constraints = .ok (some first))
    (right : SourceEqualityConstraintFieldLookup.load request.right.entry.key.constraint operations.constraints = .ok (some second))
    (rejected : (SourceEqualityIntersectionEdgeAllocation.run GuardStructuralOrder.le first second
      request.left.children.length request.right.children.length operations).1 = .ok .rejected)
    (missing : worker.native.edges.table
      (SourceRecursiveIntersectionEdgeMemo.requestKey width request.domain request.left request.right) = none) :
    ∃ result after, execute 5 (.code (.edge request .pure)) (input operations worker) = .done result after ∧
      SourceEqualityConstraintMemoAllocation.Valid after.operations ∧
      SourceEqualityConstraintMemoAllocation.Grows operations after.operations ∧
      SourceEqualityNativeDemandProvenance.Valid (SourceEqualityPCSGuard.holds formulas solver) after.native ∧
      SourceEqualityNativeDemandProvenance.EdgeProduced (width := width)
        (SourceEqualityPCSGuard.holds formulas solver) after.native.machine request result ∧
      SourceEqualityPartialMemoFrame.Frame (SourceEqualityPartialMemoFrame.stateTables worker)
        (SourceEqualityPartialMemoFrame.stateTables (returned worker (.done result after))) ∧
      SourceEqualityPartialMemoSound.Sound (SourceEqualityPCSGuard.holds formulas solver) ambient
        (returned worker (.done result after)) := by
  let before := input operations worker
  obtain ⟨result, after, done, afterValid, produced, keeps, _, _, _, operationValid, growth⟩ :=
    SourceEqualityNativeDemandRejectedReceipt.rejected_native_valid formulas solver request before first second
      nativeValid valid ready inputs safe leftCached rightCached arity left right rejected (edge_miss_starts request before missing)
  have outer := SourceEqualityPartialNativeHeap.observed_sound (SourceEqualityPCSGuard.holds formulas solver) ambient
    worker operations (.done result after) same sound growth keeps
  exact ⟨result, after, done, operationValid, growth, afterValid, produced, outer⟩

end MicroCFTA.SourceEqualityPartialNativeStopped
