import MicroCFTA.SourceCurrentConjunctionClassHistoryEntry

/-!
# Current class Scan after the actual allocated precheck

The own accessor and precheck retain their returned equality operations.
Their growth retains existing field loads in the unchanged native heap.
A live output derives the original record order and proper paths.
The current Scan starts at that actual returned operation state.

Original construction and allocation history remain explicit. Native word
bounds concern actual reached prefixes. Exact seeded-query language and
source runtime correspondence remain separate obligations.
-/
namespace MicroCFTA.SourceCurrentConjunctionAllocatedClassEntry
open Cache Language EqualityNormalize SourceEqualityClassOrder
open InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
open InternedNestedProvenance (Values)
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks
open SourceEqualityOriginalAllocationHistory
open SourceCurrentAllocatedNativeEffects (physical)
open SourceCurrentConjunctionClassScan (Ready Scan)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Key" => SourceEqualityPartialConstraintKey.Key
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Allocated" => SourceEqualityConjoinAllocation.Constraint FullSyntax.Formula
local notation "Stored" => SourceEqualityConstraintAllocation.Value
local notation "Operations" => SourceEqualityConstraintMemoAllocation.State
local notation "Memo" => SourceCurrentEmptinessMemo.Memo
local notation "initialOperations" => SourceEqualityConstraintMemoAllocation.initial
local notation "prefix" => SourceEqualityPartialPrecheckAllocation.run
local notation "source" => SourceMemoGate.unconstrained
local notation "reaches" => SourceEndpointReachability.reaches source
local notation "Effects" => SourceCurrentConjunctionRowsAllocation.Effects
variable {initialCache finalCache : Cache.State Key} {originals : List Guard}

/-- The precheck result retains its literal operation cache at the unchanged native state. -/
noncomputable def prefixState (width : Nat) (heap : State Symbol Guard) (loaded : Allocated)
    (inherited : Stored) (cache : Cache.State Key) : Checked width :=
  ⟨initial width ⟨heap, Cache.emptyState⟩,
    (prefix loaded.stored loaded.guard inherited (initialOperations cache)).2⟩

/-- Actual operation growth retains all loaded fields and native Scan invariants. -/
theorem operations_ready (before : Checked width) (after : Operations) (ready : Ready before)
    (valid : SourceEqualityConstraintMemoAllocation.Valid after)
    (growth : SourceEqualityConstraintMemoAllocation.Grows before.operations after) :
    Ready (⟨before.native, after⟩ : Checked width) :=
  ⟨⟨ready.good.native, ready.good.heap, valid, ready.good.fields.grows growth⟩,
    ready.semantic, ready.costs, ready.scopedCache, ready.idle⟩

/-- Covered resident fields derive the actual live precheck state and original class records. -/
theorem entry [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (width : Nat) (history : History initialCache finalCache originals) (valid : Cache.Valid initialCache)
    (expression : InternedNestedConstruction.Syntax Symbol Guard)
    (covered : ∀ original ∈ SourceEqualityConstraintOrigins.guards expression, original ∈ originals)
    (value : Value Symbol Guard) (heap : State Symbol Guard)
    (built : InternedFreshOrdinaryConstruction.build expression [] empty = .done value heap)
    (edge : EdgeValue Symbol Guard) (resident : EdgeResident heap edge) :
    ∃ loaded : Allocated,
      SourceEqualityConstraintFieldLookup.load edge.entry.key.constraint finalCache = .ok (some loaded) ∧
      SourceEqualityConjoinAllocation.readback loaded = edge.entry.key.constraint ∧
      SourceEqualityConstraintAllocation.Ready finalCache loaded.stored ∧
      ∀ inherited : Stored, SourceEqualityConstraintAllocation.Ready finalCache inherited →
        ∀ output : List Record,
          (prefix loaded.stored loaded.guard inherited (initialOperations finalCache)).1 = .ok (.classes output) →
          Ready (prefixState width heap loaded inherited finalCache) ∧
          SourceEqualityConstraintMemoAllocation.Grows (initialOperations finalCache)
            (prefixState width heap loaded inherited finalCache).operations ∧
          SourceEqualityPhysicalClassEntry.entry edge.entry.key.constraint inherited.payload = .ok (.classes output) ∧
          (∀ paths ∈ output.map Record.paths, ∀ path ∈ paths, path ≠ []) ∧
          ∃ records,
            SourceEqualityPhysicalPayload.own edge.entry.key.constraint = .ok (some records) ∧
            SourceCompactGuards.sourceEqualities edge.entry.key.constraint = some (records.map Record.paths) ∧
            output = ordered records ∧
            ∀ record ∈ output, Coherent record ∧ EqualityTrie.Ascending record.trie ∧ Nontrivial record.paths := by
  have initialReady := (SourceCurrentConjunctionClassHistoryEntry.constructed width history valid
    expression covered value heap built).1
  have fields := SourceCurrentClassHistoryEntry.constructed width history valid expression covered value heap built
  have cached := SourceEqualityNativeDemandFieldHeap.resident_cached heap fields.2.2.2.1 edge resident
  obtain ⟨loaded, found, readback, storedReady, prechecked⟩ :=
    SourceCurrentClassHistoryEntry.entry width history valid expression covered value heap built edge resident
  refine ⟨loaded, found, readback, storedReady, ?_⟩
  intro inherited inheritedReady output done
  obtain ⟨branch, completed, exactBranch, afterValid, growth⟩ := prechecked inherited inheritedReady
  have same : branch = .classes output := Except.ok.inj (completed.symm.trans done)
  subst branch
  obtain ⟨records, own, originalClasses, _, order, checked⟩ :=
    SourceEqualityPhysicalClassEntry.live_records edge.entry.key.constraint cached inherited.payload output exactBranch
  exact ⟨operations_ready _ _ initialReady afterValid growth, growth, exactBranch,
    SourceEqualityPhysicalClassEntry.live_proper edge.entry.key.constraint cached inherited.payload output exactBranch,
    records, own, originalClasses, order, checked⟩

/-- The live allocated prefix derives finite current Scan with its actual returned operations. -/
theorem finite [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    [DecidableEq (Value Symbol Guard)]
    (width : Nat) (history : History initialCache finalCache originals) (valid : Cache.Valid initialCache)
    (expression : InternedNestedConstruction.Syntax Symbol Guard)
    (covered : ∀ original ∈ SourceEqualityConstraintOrigins.guards expression, original ∈ originals)
    (value : Value Symbol Guard) (heap : State Symbol Guard)
    (built : InternedFreshOrdinaryConstruction.build expression [] empty = .done value heap)
    (edge : EdgeValue Symbol Guard) (resident : EdgeResident heap edge)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (budget : Nat) (memo : Memo) (correct : SourceCurrentEmptinessMemo.Correct formulas solver heap memo) :
    ∃ loaded : Allocated,
      SourceEqualityConstraintFieldLookup.load edge.entry.key.constraint finalCache = .ok (some loaded) ∧
      SourceEqualityConjoinAllocation.readback loaded = edge.entry.key.constraint ∧
      SourceEqualityConstraintAllocation.Ready finalCache loaded.stored ∧
      ∀ inherited : Stored, SourceEqualityConstraintAllocation.Ready finalCache inherited →
        ∀ output : List Record,
          (prefix loaded.stored loaded.guard inherited (initialOperations finalCache)).1 = .ok (.classes output) →
          SourceCurrentConjunctionClassScanCompletion.Ranges budget source reaches edge.children
            (output.map Record.paths) (prefixState width heap loaded inherited finalCache) memo →
          ∃ outcome selected after saved,
            Scan budget source reaches edge.children (output.map Record.paths)
              (prefixState width heap loaded inherited finalCache) memo outcome selected after saved ∧
            Ready after ∧ Effects (physical (prefixState width heap loaded inherited finalCache)) (physical after) ∧
            Values after.native.machine.heap edge.children ∧
            SourceCurrentEmptinessMemo.Correct formulas solver after.native.machine.heap saved ∧
            SourceCurrentEmptinessMemo.Extends memo saved := by
  obtain ⟨loaded, found, readback, storedReady, live⟩ :=
    entry width history valid expression covered value heap built edge resident
  have initialFields := SourceCurrentClassHistoryEntry.constructed width history valid expression covered value heap built
  have available := (initialFields.2.2.2.2.2.2 edge resident).1
  refine ⟨loaded, found, readback, storedReady, ?_⟩
  intro inherited inheritedReady output done ranges
  have checked := live inherited inheritedReady output done
  exact SourceCurrentConjunctionClassScanCompletion.finite formulas solver budget source reaches edge.children
    (output.map Record.paths) (prefixState width heap loaded inherited finalCache) memo checked.1 available
    checked.2.2.2.1 correct ranges

end MicroCFTA.SourceCurrentConjunctionAllocatedClassEntry
