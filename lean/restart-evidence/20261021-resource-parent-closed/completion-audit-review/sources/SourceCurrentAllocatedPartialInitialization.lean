import MicroCFTA.SourceCurrentAllocatedPartialInvariant
import MicroCFTA.SourceCurrentConjunctionClassHistoryEntry

/-!
# Constructed initial state for the current root caller

Covered original construction derives the heap and its loaded fields.
The empty inherited equality value uses the retained interner's actual
allocation result. The modeled native, operation, and result tables start
empty. This module does not assert a reset of source global caches.
General caller progress and concrete CAF initialization remain separate.
-/
namespace MicroCFTA.SourceCurrentAllocatedPartialInitialization
open Cache InternedConstructorTemplates InternedProbeProvenance
open SourceEqualityOriginalAllocationHistory
open SourceCurrentAllocatedNativeInventoryState (Inventory)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Key" => SourceEqualityPartialConstraintKey.Key
local notation "EqValue" => SourceEqualityConstraintAllocation.Value
local notation "OpState" => SourceEqualityConstraintMemoAllocation.State
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "EqReady" => SourceEqualityConstraintAllocation.Ready
local notation "Context" => SourceCurrentAllocatedPartialInvariant.Context

/-- The empty inherited value retains the actual canonical identity. -/
def emptyValue (cache : Cache.State Key) : EqValue :=
  (SourceEqualityConstraintAllocation.intern (some []) cache).1

/-- Empty equality allocation retains the supplied physical interner. -/
def operations (cache : Cache.State Key) : OpState :=
  SourceEqualityMkEdgeAllocation.emptyField (SourceEqualityConstraintMemoAllocation.initial cache)

/-- A checked initial state uses the actual returned empty-equality interner. -/
def checked (width : Nat) (cache : Cache.State Key) (heap : State Symbol Guard) : Checked width :=
  ⟨SourceRecursiveIntersectionThunks.initial width ⟨heap, Cache.emptyState⟩, operations cache⟩

/-- The logical cold caller has separate empty merge, fourth, and result tables. -/
def caller (width : Nat) (cache : Cache.State Key) (heap : State Symbol Guard) : Caller width :=
  SourceCurrentAllocatedPartialState.initial (checked width cache heap)
    SourceCurrentMemoMergeGraph.empty SourceCurrentEmptinessMemo.empty

/-- The three global memo families start with no saved entries. -/
def globals : EndpointMemoGateTrace.Memos :=
  ⟨InternedFreshOrdinaryUnfoldMemo.empty, SourceEndpointMemo.empty⟩

/-- Empty allocation returns a live value with exactly the empty payload. -/
theorem emptyValue_live (cache : Cache.State Key) :
    ∃ identity, emptyValue cache = .live identity [] :=
  ⟨(Cache.intern cache (SourceEqualityPartialConstraintKey.key [])).1.identity, rfl⟩

/-- The retained interner and actual empty allocation derive inherited readiness. -/
theorem operations_correct (cache : Cache.State Key) (valid : Cache.Valid cache) :
    SourceEqualityConstraintMemoAllocation.Valid (operations cache) ∧
      SourceEqualityConstraintMemoAllocation.Grows
        (SourceEqualityConstraintMemoAllocation.initial cache) (operations cache) ∧
      EqReady (operations cache).constraints (emptyValue cache) :=
  SourceEqualityMkEdgeAllocation.emptyField_correct _
    (SourceEqualityConstraintMemoAllocation.initial_valid cache valid)

variable [DecidableEq (EdgeKey Symbol Guard)]

/-- Actual closed construction computes a singleton source inventory. -/
def inventory (expression : InternedNestedConstruction.Syntax Symbol Guard)
    (value : Value Symbol Guard) (heap : State Symbol Guard)
    (built : InternedFreshOrdinaryConstruction.build expression [] empty = .done value heap) : Inventory := by
  have verified := InternedFreshOrdinaryFacts.closed_verified expression
  have facts : InternedNestedFacts.Facts heap := by
    simpa only [built, InternedNestedConstruction.Outcome.state] using verified.facts
  have available := verified.result value heap built
  have closed := InternedFreshOrdinarySourceFreeNames.closed_free_empty expression value heap built
  have original := SourceRecursiveIntersectionOriginalOutput.closed_original
    value heap facts.coherent available closed
  refine ⟨heap, facts, [value], ?_, ?_, ?_⟩
  · intro root member
    have same := List.mem_singleton.mp member
    subst root
    exact original
  · intro root member
    have same := List.mem_singleton.mp member
    subst root
    exact available
  · intro root member
    have same := List.mem_singleton.mp member
    subst root
    exact closed

/-- The computed inventory uses the literal constructed source heap. -/
theorem inventory_source (expression : InternedNestedConstruction.Syntax Symbol Guard)
    (value : Value Symbol Guard) (heap : State Symbol Guard)
    (built : InternedFreshOrdinaryConstruction.build expression [] empty = .done value heap) :
    (inventory expression value heap built).source = heap := rfl

/-- The computed inventory contains the original root once. -/
theorem inventory_roots (expression : InternedNestedConstruction.Syntax Symbol Guard)
    (value : Value Symbol Guard) (heap : State Symbol Guard)
    (built : InternedFreshOrdinaryConstruction.build expression [] empty = .done value heap) :
    (inventory expression value heap built).roots = [value] := rfl

/-- Empty global tables derive their validity in the literal heap. -/
theorem globals_valid (heap : State Symbol Guard) : EndpointMemoGateTrace.Valid heap globals :=
  ⟨InternedFreshOrdinaryUnfoldMemo.empty_correct heap, SourceEndpointMemo.empty_valid heap⟩

/-- Covered construction derives the complete initial context and exact inherited value. -/
theorem constructed [DecidableEq Symbol] (width : Nat)
    {initial final : Cache.State Key} {originals : List Guard}
    (history : History initial final originals) (valid : Cache.Valid initial)
    (expression : InternedNestedConstruction.Syntax Symbol Guard)
    (covered : ∀ original ∈ SourceEqualityConstraintOrigins.guards expression, original ∈ originals)
    (value : Value Symbol Guard) (heap : State Symbol Guard)
    (built : InternedFreshOrdinaryConstruction.build expression [] empty = .done value heap)
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) :
    Context formulas solver (inventory expression value heap built) (caller width final heap) globals ∧
      ∃ identity, emptyValue final = .live identity [] ∧
        EqReady (caller width final heap).checked.operations.constraints (.live identity []) ∧
        Available heap value ∧ value.free = [] ∧ SourceRecursiveIntersectionInputView.Original value := by
  obtain ⟨ready, available, closed, original⟩ :=
    SourceCurrentConjunctionClassHistoryEntry.constructed width history valid expression covered value heap built
  have allocation := SourceEqualityMkEdgeAllocation.emptyField_correct _ ready.good.operations
  have initialized : SourceCurrentConjunctionClassScan.Ready (checked width final heap) :=
    ⟨⟨ready.good.native, ready.good.heap, allocation.1, ready.good.fields.grows allocation.2.1⟩,
      ready.semantic, ready.costs, ready.scopedCache, ready.idle⟩
  have admitted := SourceCurrentAllocatedNativeInventoryState.initial
    (inventory expression value heap built) formulas solver width ⟨heap, Cache.emptyState⟩
    (operations final) (grows_refl heap) (Cache.extends_refl heap.nodes.issued)
  have context : Context formulas solver (inventory expression value heap built)
      (caller width final heap) globals :=
    ⟨initialized, admitted,
      SourceCurrentAllocatedPartialMemoSound.initial_sound formulas solver (checked width final heap)
        SourceCurrentMemoMergeGraph.empty SourceCurrentEmptinessMemo.empty,
      SourceCurrentMemoMergeEffects.stored_empty heap,
      fun ambient => SourceCurrentMemoMergeLanguage.cache_covers_empty
        (SourceEqualityPCSGuard.holds formulas solver) ambient,
      SourceCurrentEmptinessMemo.empty_correct formulas solver heap, globals_valid heap,
      SourceCurrentAllocatedMuRebuild.constructed expression value heap built⟩
  obtain ⟨identity, same⟩ := emptyValue_live final
  refine ⟨context, identity, same, ?_, available, closed, original⟩
  change EqReady (operations final).constraints (.live identity [])
  rw [← same]
  exact allocation.2.2

end MicroCFTA.SourceCurrentAllocatedPartialInitialization
