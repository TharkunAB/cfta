import MicroCFTA.SourceCurrentAllocatedLocalPlain
import MicroCFTA.SourceCurrentAllocatedParentWorkerActual

/-!
# Full local range plans for empty effective own equalities

The actual allocated prefix can reach only an empty class list. Its Scan
is nil and its positional retained list is nil. Thus the full finite
class-pass range plan follows without a future execution or result law.
No forest closedness or positive worker bound is required.
-/
namespace MicroCFTA.SourceCurrentAllocatedLocalPlainRanges
open EqualityNormalize InternedConstructorTemplates
open SourceCurrentAllocatedLocalPlain (OwnEmpty)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Allocated" => SourceEqualityConjoinAllocation.Constraint FullSyntax.Formula
local notation "EqValue" => SourceEqualityConstraintAllocation.Value
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Fourth" => SourceCurrentEmptinessMemo.Memo
local notation "Memo" => SourceCurrentMemoMergeGraph.Memo Symbol Guard
local notation "EqReady" => SourceEqualityConstraintAllocation.Ready
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
  [DecidableEq (Value Symbol Guard)] {width : Nat}

/-- Nil Scan and exact positional retention derive the full finite continuation plan. -/
theorem nil_ranges (budget : Nat) (values : List (Value Symbol Guard))
    (before : Checked width) (fourth : Fourth) (memo : Memo) :
    SourceCurrentConjunctionScanClassPass.Ranges budget [] values before fourth memo := by
  refine ⟨trivial, ?_⟩
  intro selected middle saved actual kept retained fuel readFuel requiredValues heap done
  cases actual
  cases retained
  exact .nil

/-- Actual prefix allocation derives the full local finite range plan. -/
theorem ranges (budget : Nat) (loaded : Allocated) (inherited : EqValue)
    (values : List (Value Symbol Guard)) (before : Checked width) (fourth : Fourth) (memo : Memo)
    (valid : SourceEqualityConstraintMemoAllocation.Valid before.operations)
    (storedReady : EqReady before.operations.constraints loaded.stored)
    (inheritedReady : EqReady before.operations.constraints inherited) (plain : OwnEmpty loaded) :
    SourceCurrentAllocatedLocalReduction.Ranges budget loaded inherited values before fourth memo := by
  intro records actual
  rcases SourceCurrentAllocatedLocalPlain.prefix_cases loaded inherited before.operations
      valid storedReady inheritedReady plain with unchanged | erased | live
  · cases unchanged.symm.trans actual
  · cases erased.symm.trans actual
  · have same := SourceEqualityPrecheck.Branch.classes.inj (Except.ok.inj (live.symm.trans actual))
    subst records
    exact nil_ranges budget values (SourceCurrentAllocatedPrecheck.state before loaded inherited) fourth memo

/-- A current successful load supplies stored readiness and the effective own-empty test. -/
theorem loaded_ranges (budget : Nat) (original : Guard) (loaded : Allocated) (inherited : EqValue)
    (values : List (Value Symbol Guard)) (before : Checked width) (fourth : Fourth) (memo : Memo)
    (valid : SourceEqualityConstraintMemoAllocation.Valid before.operations)
    (cached : SourceEqualityGuardReadback.Cached original.equalities)
    (found : SourceEqualityConstraintFieldLookup.load original before.operations.constraints = .ok (some loaded))
    (inheritedReady : EqReady before.operations.constraints inherited)
    (plain : SourceCompactGuards.sourceEqualities original = some []) :
    SourceCurrentAllocatedLocalReduction.Ranges budget loaded inherited values before fourth memo := by
  obtain ⟨ownEmpty, storedReady⟩ := SourceCurrentAllocatedLocalPlain.of_load
    original before.operations valid cached loaded found plain
  exact ranges budget loaded inherited values before fourth memo valid storedReady inheritedReady ownEmpty

/-- Resident annotations derive the parent plan only at an actual live field load. -/
theorem resident_ranges (budget : Nat) (request : SourceCurrentAllocatedPartialState.EdgeRequest)
    (before : Caller width) (ready : SourceCurrentConjunctionClassScan.Ready before.checked)
    (resident : InternedEdgeResidency.EdgeResident before.checked.native.machine.heap request.value)
    (inheritedReady : EqReady before.checked.operations.constraints request.inherited)
    (plain : SourceEqualityMkEdgeAllocation.contradictory request.value.entry.key.constraint = false →
      SourceCompactGuards.sourceEqualities request.value.entry.key.constraint = some []) :
    SourceCurrentAllocatedParentWorkerActual.ResidentRanges budget request before := by
  intro live loaded found
  exact loaded_ranges budget request.value.entry.key.constraint loaded request.inherited request.value.children
    before.checked before.fourth before.merge ready.good.operations
    (ready.good.fields request.value.entry.key request.value resident).1 found inheritedReady (plain live)

end MicroCFTA.SourceCurrentAllocatedLocalPlainRanges
