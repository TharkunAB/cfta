import MicroCFTA.SourceCurrentConjunctionClassHistoryEntry

#print axioms MicroCFTA.SourceCurrentConjunctionClassHistoryEntry.constructed
#print axioms MicroCFTA.SourceCurrentConjunctionClassHistoryEntry.finite
#print axioms MicroCFTA.SourceCurrentConjunctionClassHistoryEntry.cold_finite
#check MicroCFTA.SourceCurrentConjunctionClassHistoryEntry.constructed
#check MicroCFTA.SourceCurrentConjunctionClassHistoryEntry.finite
#check MicroCFTA.SourceCurrentConjunctionClassHistoryEntry.cold_finite

namespace MicroCFTA.SourceCurrentConjunctionClassHistoryEntryProbes
open Cache InternedConstructorTemplates InternedProbeProvenance
open SourceRecursiveIntersectionThunks SourceEqualityOriginalAllocationHistory
open SourceCurrentConjunctionClassScan (Ready)
open SourceCurrentConjunctionClassHistoryEntry
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Key" => SourceEqualityPartialConstraintKey.Key
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "ops" => SourceEqualityConstraintMemoAllocation.initial
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
variable (width : Nat) {first final : Cache.State Key} {originals : List Guard}
variable (history : History first final originals) (valid : Cache.Valid first)
variable (expression : InternedNestedConstruction.Syntax Symbol Guard)
variable (covered : ∀ original ∈ SourceEqualityConstraintOrigins.guards expression, original ∈ originals)
variable (value : Value Symbol Guard) (heap : State Symbol Guard)
variable (built : InternedFreshOrdinaryConstruction.build expression [] empty = .done value heap)

-- One actual construction derives Ready at the complete literal checked state.
example : Ready (⟨initial width ⟨heap, Cache.emptyState⟩, ops final⟩ : Checked width) :=
  (constructed width history valid expression covered value heap built).1

-- The same build derives its result availability without a supplied readback.
example : Available heap value := (constructed width history valid expression covered value heap built).2.1

-- Closedness is derived from the actual original build.
example : value.free = [] := (constructed width history valid expression covered value heap built).2.2.1

-- Generated initial Original is derived from physical coherence and closedness.
example : SourceRecursiveIntersectionInputView.Original value :=
  (constructed width history valid expression covered value heap built).2.2.2

-- The actual final interner is retained; the operations start at its literal initial state.
example : (⟨initial width ⟨heap, Cache.emptyState⟩, ops final⟩ : Checked width).operations = ops final := rfl

-- Empty fourth memo derives correctness at any reached constructor heap.
example (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula) :
    SourceCurrentEmptinessMemo.Correct formulas solver heap SourceCurrentEmptinessMemo.empty :=
  SourceCurrentEmptinessMemo.empty_correct formulas solver heap

-- The empty original expression requires no fabricated field-allocation history.
example : Ready (⟨initial width ⟨empty, Cache.emptyState⟩, ops Cache.emptyState⟩ : Checked width) :=
  (constructed width (History.start Cache.emptyState) Cache.empty_valid .empty
    (by intro field member; cases member) .empty empty (by simp [InternedFreshOrdinaryConstruction.build])).1
end MicroCFTA.SourceCurrentConjunctionClassHistoryEntryProbes
