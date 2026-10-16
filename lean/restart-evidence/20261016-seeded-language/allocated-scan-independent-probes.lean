import MicroCFTA.SourceCurrentConjunctionAllocatedScanSoundness

#print axioms MicroCFTA.SourceCurrentConjunctionAllocatedScanSoundness.prefix_admitted
#print axioms MicroCFTA.SourceCurrentConjunctionAllocatedScanSoundness.finite
#check @MicroCFTA.SourceCurrentConjunctionAllocatedScanSoundness.emptyInventory
#check @MicroCFTA.SourceCurrentConjunctionAllocatedScanSoundness.prefix_admitted
#check @MicroCFTA.SourceCurrentConjunctionAllocatedScanSoundness.finite

namespace MicroCFTA.SourceCurrentConjunctionAllocatedScanIndependentProbes
open Cache Language EqualityNormalize SourceEqualityClassOrder
open InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
open SourceEqualityOriginalAllocationHistory
open SourceCurrentAllocatedNativeEffects (physical)
open SourceCurrentConjunctionClassScan (Ready Scan)
open SourceCurrentAllocatedNativeInventoryState (Inventory At)
open SourceCurrentConjunctionAllocatedClassEntry (prefixState)
open SourceCurrentConjunctionAllocatedScanSoundness (emptyInventory prefix_admitted)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Key" => SourceEqualityPartialConstraintKey.Key
local notation "Allocated" => SourceEqualityConjoinAllocation.Constraint FullSyntax.Formula
local notation "Stored" => SourceEqualityConstraintAllocation.Value
local notation "precheck" => SourceEqualityPartialPrecheckAllocation.run
local notation "initialOperations" => SourceEqualityConstraintMemoAllocation.initial

-- The actual precheck result retains both empty native tables and its exact operation state.
theorem prefix_exact (width : Nat) (heap : State Symbol Guard) (facts : InternedNestedFacts.Facts heap)
    (loaded : Allocated) (inherited : Stored) (cache : Cache.State Key)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula) :
    At formulas solver (emptyInventory heap facts) (prefixState width heap loaded inherited cache) ∧
    (prefixState width heap loaded inherited cache).native.nodes = FlatMemoThunk.empty ∧
    (prefixState width heap loaded inherited cache).native.edges = FlatMemoThunk.empty ∧
    (prefixState width heap loaded inherited cache).native.machine = ⟨heap, Cache.emptyState⟩ ∧
    (prefixState width heap loaded inherited cache).operations =
      (precheck loaded.stored loaded.guard inherited (initialOperations cache)).2 :=
  ⟨prefix_admitted width heap facts loaded inherited cache formulas solver, rfl, rfl, rfl, rfl⟩

section Constructed
variable {initialCache finalCache : Cache.State Key} {originals : List Guard}
  [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq (Value Symbol Guard)]
  (width : Nat) (history : History initialCache finalCache originals) (valid : Cache.Valid initialCache)
  (expression : InternedNestedConstruction.Syntax Symbol Guard)
  (covered : ∀ original ∈ SourceEqualityConstraintOrigins.guards expression, original ∈ originals)
  (value : Value Symbol Guard) (heap : State Symbol Guard)
  (built : InternedFreshOrdinaryConstruction.build expression [] empty = .done value heap)
  (edge : EdgeValue Symbol Guard) (resident : EdgeResident heap edge)
  (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
  (budget : Nat)
include history valid expression covered value built resident

-- Empty fourth-memo correctness is derived inside the actual constructed finite entry.
theorem finite_empty_fourth : ∃ loaded : Allocated,
    SourceEqualityConstraintFieldLookup.load edge.entry.key.constraint finalCache = .ok (some loaded) ∧
    SourceEqualityConjoinAllocation.readback loaded = edge.entry.key.constraint ∧
    SourceEqualityConstraintAllocation.Ready finalCache loaded.stored ∧
    ∀ inherited : Stored, SourceEqualityConstraintAllocation.Ready finalCache inherited →
      ∀ output : List Record,
        (precheck loaded.stored loaded.guard inherited (initialOperations finalCache)).1 = .ok (.classes output) →
        SourceCurrentConjunctionClassScanCompletion.Ranges budget SourceMemoGate.unconstrained
          (SourceEndpointReachability.reaches SourceMemoGate.unconstrained) edge.children
          (output.map Record.paths) (prefixState width heap loaded inherited finalCache) SourceCurrentEmptinessMemo.empty →
        ∃ outcome selected after saved next,
          Scan budget SourceMemoGate.unconstrained (SourceEndpointReachability.reaches SourceMemoGate.unconstrained)
            edge.children (output.map Record.paths) (prefixState width heap loaded inherited finalCache)
            SourceCurrentEmptinessMemo.empty outcome selected after saved ∧
          Ready after ∧ At formulas solver next after ∧
          SourceCurrentEmptinessMemo.Correct formulas solver after.native.machine.heap saved ∧
          (∀ rejected, outcome = some rejected → rejected ∈ output.map Record.paths ∧
            ∀ ambient symbol terms,
              All₂ (InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver) ambient)
                edge.children terms → ¬ClassSat (.node symbol terms) rejected) := by
  obtain ⟨loaded, found, readback, storedReady, entry⟩ :=
    SourceCurrentConjunctionAllocatedScanSoundness.finite width history valid expression covered value heap built
      edge resident formulas solver budget SourceCurrentEmptinessMemo.empty
      (SourceCurrentEmptinessMemo.empty_correct formulas solver heap)
  refine ⟨loaded, found, readback, storedReady, ?_⟩
  intro inherited inheritedReady output checked ranges
  obtain ⟨outcome, selected, after, saved, next, actual, ready, admitted, _, _, correct, _, sound⟩ :=
    entry inherited inheritedReady output checked ranges
  exact ⟨outcome, selected, after, saved, next, actual, ready, admitted, correct, sound⟩

-- A stopped scan rules out an accepted original forest satisfying all actual precheck classes.
theorem stopped_constraints_impossible : ∃ loaded : Allocated,
    SourceEqualityConstraintFieldLookup.load edge.entry.key.constraint finalCache = .ok (some loaded) ∧
    ∀ inherited : Stored, SourceEqualityConstraintAllocation.Ready finalCache inherited →
      ∀ output : List Record,
        (precheck loaded.stored loaded.guard inherited (initialOperations finalCache)).1 = .ok (.classes output) →
        SourceCurrentConjunctionClassScanCompletion.Ranges budget SourceMemoGate.unconstrained
          (SourceEndpointReachability.reaches SourceMemoGate.unconstrained) edge.children
          (output.map Record.paths) (prefixState width heap loaded inherited finalCache) SourceCurrentEmptinessMemo.empty →
        ∃ outcome selected after saved next,
          Scan budget SourceMemoGate.unconstrained (SourceEndpointReachability.reaches SourceMemoGate.unconstrained)
            edge.children (output.map Record.paths) (prefixState width heap loaded inherited finalCache)
            SourceCurrentEmptinessMemo.empty outcome selected after saved ∧
          At formulas solver next after ∧
          ∀ rejected, outcome = some rejected →
            ¬∃ ambient symbol terms,
              All₂ (InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver) ambient)
                edge.children terms ∧ Satisfies (.node symbol terms) (output.map Record.paths) := by
  obtain ⟨loaded, found, _, _, entry⟩ := finite_empty_fourth width history valid expression covered value heap built
    edge resident formulas solver budget
  refine ⟨loaded, found, ?_⟩
  intro inherited inheritedReady output checked ranges
  obtain ⟨outcome, selected, after, saved, next, actual, _, admitted, _, sound⟩ :=
    entry inherited inheritedReady output checked ranges
  refine ⟨outcome, selected, after, saved, next, actual, admitted, ?_⟩
  intro rejected stopped witness
  obtain ⟨ambient, symbol, terms, accepted, satisfies⟩ := witness
  have rejectedLaw := sound rejected stopped
  exact rejectedLaw.2 ambient symbol terms accepted (satisfies rejected rejectedLaw.1)
end Constructed
end MicroCFTA.SourceCurrentConjunctionAllocatedScanIndependentProbes

#print axioms MicroCFTA.SourceCurrentConjunctionAllocatedScanIndependentProbes.prefix_exact
#print axioms MicroCFTA.SourceCurrentConjunctionAllocatedScanIndependentProbes.finite_empty_fourth
#print axioms MicroCFTA.SourceCurrentConjunctionAllocatedScanIndependentProbes.stopped_constraints_impossible
#check @MicroCFTA.SourceCurrentConjunctionAllocatedScanIndependentProbes.prefix_exact
#check @MicroCFTA.SourceCurrentConjunctionAllocatedScanIndependentProbes.finite_empty_fourth
#check @MicroCFTA.SourceCurrentConjunctionAllocatedScanIndependentProbes.stopped_constraints_impossible
