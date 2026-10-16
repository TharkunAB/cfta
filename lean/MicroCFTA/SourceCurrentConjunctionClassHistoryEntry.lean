import MicroCFTA.SourceCurrentClassHistoryEntry
import MicroCFTA.SourceCurrentConjunctionClassScanCompletion

/-!
# Current conjunction scans from covered original allocation history

The same covered history and actual original build derive the initial
checked state, semantic heap, stored costs, loaded fields, and empty native
scope invariant. Finite current scans need no historical Scan premise.

The native and operation tables start empty over the retained interner.
Selected-path availability and reached word bounds remain explicit.
Exact seeded-query language and runtime correspondence remain separate.
-/
namespace MicroCFTA.SourceCurrentConjunctionClassHistoryEntry
open Cache Language EqualityNormalize InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks
open SourceEqualityOriginalAllocationHistory
open SourceCurrentAllocatedNativeEffects (physical)
open SourceCurrentConjunctionClassScan (Scan Ready)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Key" => SourceEqualityPartialConstraintKey.Key
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Memo" => SourceCurrentEmptinessMemo.Memo
local notation "operations" => SourceEqualityConstraintMemoAllocation.initial
local notation "Effects" => SourceCurrentConjunctionRowsAllocation.Effects
variable {initialCache finalCache : Cache.State Key} {originals : List Guard}

/-- Covered construction derives every initial checked Scan invariant in the literal state. -/
theorem constructed [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (width : Nat) (history : History initialCache finalCache originals) (valid : Cache.Valid initialCache)
    (expression : InternedNestedConstruction.Syntax Symbol Guard)
    (covered : ∀ original ∈ SourceEqualityConstraintOrigins.guards expression, original ∈ originals)
    (value : Value Symbol Guard) (heap : State Symbol Guard)
    (built : InternedFreshOrdinaryConstruction.build expression [] empty = .done value heap) :
    Ready (⟨initial width ⟨heap, Cache.emptyState⟩, operations finalCache⟩ : Checked width) ∧
      Available heap value ∧ value.free = [] ∧ SourceRecursiveIntersectionInputView.Original value := by
  have actual := SourceCurrentAllocatedNativeOriginalHistory.constructed width history valid
    expression covered value heap built
  have initialFields := SourceCurrentClassHistoryEntry.constructed width history valid
    expression covered value heap built
  exact ⟨⟨actual.1, actual.2.1, initialFields.2.2.1,
    SourceCurrentAllocatedNativeScopeCache.initial_scoped width ⟨heap, Cache.emptyState⟩,
    SourceRecursiveIntersectionNative.idle_initial ⟨heap, Cache.emptyState⟩⟩, actual.2.2⟩

/-- Actual covered construction and reached ranges derive a finite current scan with no initial-ready premise. -/
theorem finite [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    [DecidableEq (Value Symbol Guard)]
    (width : Nat) (history : History initialCache finalCache originals) (valid : Cache.Valid initialCache)
    (expression : InternedNestedConstruction.Syntax Symbol Guard)
    (covered : ∀ original ∈ SourceEqualityConstraintOrigins.guards expression, original ∈ originals)
    (value : Value Symbol Guard) (heap : State Symbol Guard)
    (built : InternedFreshOrdinaryConstruction.build expression [] empty = .done value heap)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (budget : Nat) (unconstrained reaches : Value Symbol Guard → Bool)
    (values : List (Value Symbol Guard)) (classes : Constraints) (memo : Memo)
    (available : Values heap values) (proper : ∀ paths ∈ classes, ∀ path ∈ paths, path ≠ [])
    (correct : SourceCurrentEmptinessMemo.Correct formulas solver heap memo)
    (ranges : SourceCurrentConjunctionClassScanCompletion.Ranges budget unconstrained reaches values classes
      (⟨initial width ⟨heap, Cache.emptyState⟩, operations finalCache⟩ : Checked width) memo) :
    ∃ outcome selected after saved,
      Scan budget unconstrained reaches values classes
        (⟨initial width ⟨heap, Cache.emptyState⟩, operations finalCache⟩ : Checked width)
        memo outcome selected after saved ∧
      Ready after ∧ Effects ⟨heap, operations finalCache⟩ (physical after) ∧
      Values after.native.machine.heap values ∧
      SourceCurrentEmptinessMemo.Correct formulas solver after.native.machine.heap saved ∧
      SourceCurrentEmptinessMemo.Extends memo saved :=
  SourceCurrentConjunctionClassScanCompletion.finite formulas solver budget unconstrained reaches values classes
    ⟨initial width ⟨heap, Cache.emptyState⟩, operations finalCache⟩ memo
    (constructed width history valid expression covered value heap built).1 available proper correct ranges

/-- An empty fourth memo derives its own initial correctness for the same finite current scan. -/
theorem cold_finite [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    [DecidableEq (Value Symbol Guard)]
    (width : Nat) (history : History initialCache finalCache originals) (valid : Cache.Valid initialCache)
    (expression : InternedNestedConstruction.Syntax Symbol Guard)
    (covered : ∀ original ∈ SourceEqualityConstraintOrigins.guards expression, original ∈ originals)
    (value : Value Symbol Guard) (heap : State Symbol Guard)
    (built : InternedFreshOrdinaryConstruction.build expression [] empty = .done value heap)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (budget : Nat) (unconstrained reaches : Value Symbol Guard → Bool)
    (values : List (Value Symbol Guard)) (classes : Constraints)
    (available : Values heap values) (proper : ∀ paths ∈ classes, ∀ path ∈ paths, path ≠ [])
    (ranges : SourceCurrentConjunctionClassScanCompletion.Ranges budget unconstrained reaches values classes
      (⟨initial width ⟨heap, Cache.emptyState⟩, operations finalCache⟩ : Checked width)
      SourceCurrentEmptinessMemo.empty) :
    ∃ outcome selected after saved,
      Scan budget unconstrained reaches values classes
        (⟨initial width ⟨heap, Cache.emptyState⟩, operations finalCache⟩ : Checked width)
        SourceCurrentEmptinessMemo.empty outcome selected after saved ∧
      Ready after ∧ Effects ⟨heap, operations finalCache⟩ (physical after) ∧
      Values after.native.machine.heap values ∧
      SourceCurrentEmptinessMemo.Correct formulas solver after.native.machine.heap saved ∧
      SourceCurrentEmptinessMemo.Extends SourceCurrentEmptinessMemo.empty saved :=
  finite width history valid expression covered value heap built formulas solver budget unconstrained reaches
    values classes SourceCurrentEmptinessMemo.empty available proper
    (SourceCurrentEmptinessMemo.empty_correct formulas solver heap) ranges

end MicroCFTA.SourceCurrentConjunctionClassHistoryEntry
