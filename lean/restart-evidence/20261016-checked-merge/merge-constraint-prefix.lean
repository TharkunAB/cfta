import MicroCFTA.SourceCurrentConjunctionClassScan
import MicroCFTA.SourceCurrentAllocatedNativeInventoryState
import MicroCFTA.SourceCurrentMemoMergeLanguage
import MicroCFTA.SourceCurrentMemoMergeQueryMemos

/-!
# Allocated merge calls in the current checked state

The actual merge graph advances the constructor heap and equality operations.
Both native tables and the domain cache remain in the same checked state.
Generated results enter the input inventory when a later query requests them.
The completed selection primitive and its runtime demand adapter remain separate.
-/
namespace MicroCFTA.SourceCurrentAllocatedMerge
open Cache Language InternedConstructorTemplates InternedProbeProvenance
open SourceCurrentAllocatedNativeEffects (physical)
open SourceCurrentAllocatedQueryMemo (advancePhysical advance_extension)
open SourceCurrentConjunctionClassScan (Ready)
open SourceCurrentAllocatedNativeInventoryState (Inventory At)
open SourceCurrentMemoMergeEffects (Stored)
open SourceCurrentMemoMergeLanguage (Covers CacheCovers)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Physical" => SourceCurrentConjunctionRowsAllocation.State Symbol FullSyntax.Formula
local notation "Memo" => SourceCurrentMemoMergeGraph.Memo Symbol Guard
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Valid" => EndpointMemoGateTrace.Valid
local notation "top" => SourceEqualityConstraintConstructors.top (Formula := FullSyntax.Formula)
variable {width : Nat}

/-- The source comparison accepts only the literal unconstrained raw field. -/
noncomputable def literalClear (constraint : Guard) : Bool := by
  classical
  exact decide (constraint = top)

/-- The independent PCS interpretation accepts Top without a storage premise. -/
theorem top_true (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (term : Term Symbol) :
    SourceEqualityPCSGuard.holds formulas solver top term = true := by
  rw [SourceEqualityPCSGuard.public_eq formulas solver top
    (SourceEqualityGuardReadback.active SourceEqualityConstraintConstructors.top_cached)]
  exact SourceEqualityConstraintConstructors.top_true formulas solver term

/-- A literal source clear test derives independent constraint truth. -/
theorem literalClear_true (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (constraint : Guard)
    (cleared : literalClear constraint = true) (term : Term Symbol) :
    SourceEqualityPCSGuard.holds formulas solver constraint term = true := by
  classical
  have same : constraint = top := of_decide_eq_true cleared
  subst constraint
  exact top_true formulas solver term

/-- A normalized clear guard need not be the literal source Top field. -/
theorem normalized_clear_boundary :
    SourceMemoGate.plain (⟨some [], .and []⟩ : Guard) = true ∧
      literalClear (⟨some [], .and []⟩ : Guard) = false := by
  constructor
  · rfl
  · simp [literalClear, SourceEqualityConstraintConstructors.top]


end MicroCFTA.SourceCurrentAllocatedMerge
