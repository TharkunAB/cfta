import MicroCFTA.SourceCurrentAllocatedNativeOriginalHistory

open MicroCFTA Cache InternedConstructorTemplates InternedProbeProvenance
open SourceEqualityOriginalAllocationHistory

#print axioms MicroCFTA.SourceEqualityOriginalAllocationHistory.History.cached
#print axioms MicroCFTA.SourceEqualityOriginalAllocationHistory.History.cached_inventory
#print axioms MicroCFTA.SourceEqualityOriginalAllocationHistory.History.syntax_valid
#print axioms MicroCFTA.SourceEqualityOriginalAllocationHistory.History.fields
#print axioms MicroCFTA.SourceCurrentAllocatedNativeOriginalHistory.constructed
#check @MicroCFTA.SourceEqualityOriginalAllocationHistory.History.cached
#check @MicroCFTA.SourceEqualityOriginalAllocationHistory.History.cached_inventory
#check @MicroCFTA.SourceEqualityOriginalAllocationHistory.History.syntax_valid
#check @MicroCFTA.SourceEqualityOriginalAllocationHistory.History.fields
#check @MicroCFTA.SourceCurrentAllocatedNativeOriginalHistory.constructed

namespace OriginalHistoryChecks
noncomputable section
local notation "Key" => SourceEqualityPartialConstraintKey.Key
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local instance : DecidableEq (EdgeKey Symbol Guard) := Classical.typeDecidableEq _

-- 1. Empty history derives syntax validity without an allowed premise.
example (cache : Cache.State Key) :
    InternedFreshOrdinaryConstraintHeap.SyntaxValid
      (fun guard : Guard => SourceEqualityGuardReadback.Cached guard.equalities)
      (InternedNestedConstruction.Syntax.empty : InternedNestedConstruction.Syntax Symbol Guard) :=
  (History.start cache).syntax_valid .empty (by intro original member; cases member)

-- 2. Actual construction records its normalization event even without an initial validity premise.
example (initial after : Cache.State Key) (original : Guard)
    (cached : SourceEqualityGuardReadback.Cached original.equalities)
    (value : SourceEqualityConstraintAllocation.Value)
    (done : SourceEqualityConstraintAllocation.construct original.equalities initial = (.ok value, after)) :
    ∀ guard ∈ [original], SourceEqualityGuardReadback.Cached guard.equalities :=
  (History.construct (History.start initial) cached done).cached

-- 3. Permitted interleaving retains literal normalization from the causal history.
example {initial before after : Cache.State Key} {originals : List Guard}
    (history : History initial before originals) (steps : Cache.Steps before after) :
    ∀ guard ∈ originals, SourceEqualityGuardReadback.Cached guard.equalities :=
  (History.interleave history steps).cached

-- 4. Original syntax normalization requires only actual historical coverage.
example {initial final : Cache.State Key} {originals : List Guard}
    (history : History initial final originals)
    (expression : InternedNestedConstruction.Syntax Symbol Guard)
    (covered : ∀ guard ∈ SourceEqualityConstraintOrigins.guards expression, guard ∈ originals) :
    InternedFreshOrdinaryConstraintHeap.SyntaxValid
      (fun guard : Guard => SourceEqualityGuardReadback.Cached guard.equalities) expression :=
  history.syntax_valid expression covered

-- 5. Actual resident fields derive ready readback in the same final equality interner.
example {initial final : Cache.State Key} {originals : List Guard}
    (history : History initial final originals) (valid : Cache.Valid initial)
    (expression : InternedNestedConstruction.Syntax Symbol Guard)
    (covered : ∀ guard ∈ SourceEqualityConstraintOrigins.guards expression, guard ∈ originals)
    (value : Value Symbol Guard) (heap : State Symbol Guard)
    (built : InternedFreshOrdinaryConstruction.build expression [] empty = .done value heap)
    (edge : EdgeValue Symbol Guard) (resident : InternedEdgeResidency.EdgeResident heap edge) :
    ∃ loaded : SourceEqualityConjoinAllocation.Constraint FullSyntax.Formula,
      SourceEqualityConstraintFieldLookup.load edge.entry.key.constraint final = .ok (some loaded) ∧
      SourceEqualityConstraintAllocation.Ready final loaded.stored ∧
      SourceEqualityConjoinAllocation.readback loaded = edge.entry.key.constraint ∧
      SourceEqualityPhysicalPayload.read edge.entry.key.constraint.equalities = .ok loaded.stored.payload := by
  have fields := history.fields valid expression covered value heap built
  exact (fields edge.entry.key edge resident).receipts (history.operations_valid valid)

-- 6. An actual empty source build derives all five checked-entry properties.
example (width : Nat) :
    SourceCurrentAllocatedNativePhysicalCompletion.Good
      (⟨SourceRecursiveIntersectionThunks.initial width ⟨empty, Cache.emptyState⟩,
        SourceEqualityConstraintMemoAllocation.initial Cache.emptyState⟩ : Checked width) ∧
      SourceEqualityRequiredSemanticCache.SemanticReady (empty : State Symbol Guard) ∧
      Available empty (.empty : Value Symbol Guard) ∧ (.empty : Value Symbol Guard).free = [] ∧
      SourceRecursiveIntersectionInputView.Original (.empty : Value Symbol Guard) :=
  SourceCurrentAllocatedNativeOriginalHistory.constructed width
    (History.start Cache.emptyState) Cache.empty_valid .empty (by intro original member; cases member)
    .empty empty (by simp [InternedFreshOrdinaryConstruction.build])

-- 7. The actual missing lexical variable branch also returns a derived closed Original value.
example (width : Nat) :
    SourceCurrentAllocatedNativePhysicalCompletion.Good
      (⟨SourceRecursiveIntersectionThunks.initial width ⟨empty, Cache.emptyState⟩,
        SourceEqualityConstraintMemoAllocation.initial Cache.emptyState⟩ : Checked width) ∧
      SourceEqualityRequiredSemanticCache.SemanticReady (empty : State Symbol Guard) ∧
      Available empty (.empty : Value Symbol Guard) ∧ (.empty : Value Symbol Guard).free = [] ∧
      SourceRecursiveIntersectionInputView.Original (.empty : Value Symbol Guard) :=
  SourceCurrentAllocatedNativeOriginalHistory.constructed width
    (History.start Cache.emptyState) Cache.empty_valid (.var 0) (by intro original member; cases member)
    .empty empty (by simp [InternedFreshOrdinaryConstruction.build])

-- 8. Actual field allocation and finite recursive construction derive entry, without supplying a completed build.
example (width : Nat) (symbol : Symbol) (smart : Bool) :
    ∃ (final : Cache.State Key) (value : Value Symbol Guard) (heap : State Symbol Guard),
      History Cache.emptyState final [SourceEqualityConstraintConstructors.top (Formula := FullSyntax.Formula)] ∧
      InternedFreshOrdinaryConstruction.build
        (.binder smart (.node [.mk symbol SourceEqualityConstraintConstructors.top [.var 0]])) [] empty = .done value heap ∧
      SourceCurrentAllocatedNativePhysicalCompletion.Good
        (⟨SourceRecursiveIntersectionThunks.initial width ⟨heap, Cache.emptyState⟩,
          SourceEqualityConstraintMemoAllocation.initial final⟩ : Checked width) ∧
      SourceEqualityRequiredSemanticCache.SemanticReady heap ∧ Available heap value ∧ value.free = [] ∧
      SourceRecursiveIntersectionInputView.Original value := by
  obtain ⟨allocated, final, done, _, _, _, _, _⟩ := SourceEqualityConstraintAllocation.construct_complete
    (SourceEqualityConstraintConstructors.top (Formula := FullSyntax.Formula)).equalities
    SourceEqualityConstraintConstructors.top_cached Cache.emptyState Cache.empty_valid
  let history : History Cache.emptyState final [SourceEqualityConstraintConstructors.top] :=
    .construct (.start _) SourceEqualityConstraintConstructors.top_cached done
  let expression : InternedNestedConstruction.Syntax Symbol Guard :=
    .binder smart (.node [.mk symbol SourceEqualityConstraintConstructors.top [.var 0]])
  have covered : ∀ guard ∈ SourceEqualityConstraintOrigins.guards expression,
      guard ∈ [SourceEqualityConstraintConstructors.top] := by
    intro guard member
    simpa [expression, SourceEqualityConstraintOrigins.guards, SourceEqualityConstraintOrigins.edgeGuards,
      SourceEqualityConstraintOrigins.childGuards] using member
  obtain ⟨value, heap, built⟩ := InternedFreshOrdinaryClosedCompletion.closed_complete expression
  exact ⟨final, value, heap, history, built,
    SourceCurrentAllocatedNativeOriginalHistory.constructed width history Cache.empty_valid expression covered value heap built⟩

-- 9. Any closed selected resident operand derives Original from the constructed coherent heap.
example (width : Nat) {initial final : Cache.State Key} {originals : List Guard}
    (history : History initial final originals) (valid : Cache.Valid initial)
    (expression : InternedNestedConstruction.Syntax Symbol Guard)
    (covered : ∀ guard ∈ SourceEqualityConstraintOrigins.guards expression, guard ∈ originals)
    (value selected : Value Symbol Guard) (heap : State Symbol Guard)
    (built : InternedFreshOrdinaryConstruction.build expression [] empty = .done value heap)
    (available : Available heap selected) (closed : selected.free = []) :
    SourceRecursiveIntersectionInputView.Original selected := by
  have entry := SourceCurrentAllocatedNativeOriginalHistory.constructed width history valid expression covered value heap built
  exact SourceRecursiveIntersectionOriginalOutput.closed_original selected heap entry.1.native.machine.1.coherent available closed

end
end OriginalHistoryChecks
