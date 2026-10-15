import MicroCFTA.SourceEqualityDemandTargetWorkerComplete
import MicroCFTA.SourceEqualityClassTarget

/-!
# Finite stable actual targets for original equality-class paths

Demand graphs and checked successful execution agree in both directions.
Completed targets have one value and full returned native state. Original
class paths retain equality-satisfying subterms through actual construction.
-/
namespace MicroCFTA.SourceEqualityClassTargetAPI
open Language InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open MergedColdReaderClosedInputs (ClosedValues)
open SourceEqualityRequiredCache SourceEqualityNativeScoped SourceEqualityDemandTarget SourceEqualityDemandTargetComplete
open SourceEqualityDemandTargetWorkerComplete
open EqualityNormalize
open InternedGuardedLanguage (meaning)

/-- Complete demand graphs and checked successful target executions agree in both directions. -/
theorem execution_iff [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (emptyGuard : Guard) (conjoin : Guard → Guard → Guard) (clear : Guard → Bool) (top : Guard)
    (values : List (Value Symbol Guard)) (paths : List (List Int)) (before : SourceRecursiveIntersectionThunks.State width Symbol Guard)
    (ranges : TargetRanges emptyGuard conjoin clear top values paths before) (result : Value Symbol Guard) (after : SourceRecursiveIntersectionThunks.State width Symbol Guard) :
    Target emptyGuard conjoin clear top values paths before result after ↔ ∃ p h c n,
      SourceEqualityDemandTargetWorker.target emptyGuard conjoin clear top p h c n values paths before = .done result after := by
  constructor
  · intro trace
    obtain ⟨p, h, c, n, stable⟩ := target_stable trace
    exact ⟨p, h, c, n, stable p h c n (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _)⟩
  · rintro ⟨p, h, c, n, done⟩
    exact SourceEqualityDemandTargetWorkerSound.target_graph emptyGuard conjoin clear top p h c n values paths before ranges result after done

/-- Stable completed target executions have one value and full actual native state. -/
theorem stable_unique {evaluation : Nat → Nat → Nat → Nat → SourceEqualityDemandTargetWorker.Result width Symbol Guard A}
    {first second : A} {afterFirst afterSecond : SourceRecursiveIntersectionThunks.State width Symbol Guard}
    (left : StableRun evaluation first afterFirst) (right : StableRun evaluation second afterSecond) : first = second ∧ afterFirst = afterSecond := by
  obtain ⟨p, h, c, n, one⟩ := left
  obtain ⟨laterP, laterH, laterC, laterN, two⟩ := right
  exact SourceEqualityDemandTargetWorker.Result.done.inj ((one (max p laterP) (max h laterH) (max c laterC) (max n laterN)
    (Nat.le_max_left _ _) (Nat.le_max_left _ _) (Nat.le_max_left _ _) (Nat.le_max_left _ _)).symm.trans
    (two (max p laterP) (max h laterH) (max c laterC) (max n laterN)
      (Nat.le_max_right _ _) (Nat.le_max_right _ _) (Nat.le_max_right _ _) (Nat.le_max_right _ _)))

/-- Complete target graphs have one target and full returned native state. -/
theorem unique [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {emptyGuard : Guard} {conjoin : Guard → Guard → Guard} {clear : Guard → Bool} {top : Guard}
    {values : List (Value Symbol Guard)} {paths : List (List Int)} {first second : Value Symbol Guard}
    {before afterFirst afterSecond : SourceRecursiveIntersectionThunks.State width Symbol Guard}
    (left : Target emptyGuard conjoin clear top values paths before first afterFirst)
    (right : Target emptyGuard conjoin clear top values paths before second afterSecond) : first = second ∧ afterFirst = afterSecond :=
  stable_unique (target_stable left) (target_stable right)

/-- Original coherent class paths derive finite stable demanded target execution and retained equality subterms. -/
theorem class_complete [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (emptyGuard : Guard) (conjoin : Guard → Guard → Guard) (clear : Guard → Bool) (top : Guard)
    (record : SourceEqualityClassOrder.Record) (coherent : SourceEqualityClassOrder.Coherent record) (active : Nontrivial record.paths)
    (path : Path) (member : path ∈ record.paths) (values : List (Value Symbol Guard))
    (base : InternedConstructorTemplates.State Symbol Guard) (known : Values base values) (closed : ClosedValues values)
    (before : SourceRecursiveIntersectionThunks.State width Symbol Guard) (retained : Keeps base before.machine.heap)
    (ready : IdleReady emptyGuard conjoin before)
    (ranges : TargetRanges emptyGuard conjoin clear top values (SourceEqualityClassTarget.operandPaths record.paths path) before)
    (holds : Guard → Term Symbol → Bool) (ambient : InternedGuardedLanguage.Env Symbol)
    (clearTrue : ∀ guard, clear guard = true → ∀ term, holds guard term = true) (topTrue : ∀ term, holds top term = true)
    (conjoined : ∀ first second term, holds (conjoin first second) term = (holds first term && holds second term)) :
    ∃ target after, Target emptyGuard conjoin clear top values (SourceEqualityClassTarget.operandPaths record.paths path) before target after ∧
      IdleReady emptyGuard conjoin after ∧ Keeps base after.machine.heap ∧ Available after.machine.heap target ∧ target.free = [] ∧
      StableRun (fun p h c n => SourceEqualityDemandTargetWorker.target emptyGuard conjoin clear top p h c n values
        (SourceEqualityClassTarget.operandPaths record.paths path) before) target after ∧
      ∀ symbol terms part, All₂ (meaning holds ambient) values terms → ClassSat (.node symbol terms) record.paths →
        (Term.node symbol terms).atPath path = some part → meaning holds ambient target part := by
  obtain ⟨target, after, trace, finalReady, keeps, available, resultClosed, included⟩ := SourceEqualityClassTarget.target_complete
    emptyGuard conjoin clear top record coherent active path member values base known closed before retained ready ranges holds ambient clearTrue topTrue conjoined
  exact ⟨target, after, trace, finalReady, keeps, available, resultClosed, target_stable trace, included⟩

end MicroCFTA.SourceEqualityClassTargetAPI
