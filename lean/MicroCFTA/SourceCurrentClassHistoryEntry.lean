import MicroCFTA.SourceCurrentAllocatedNativeOriginalHistory

/-!
# Original class entry from one covered allocation history

The history derives normalized syntax and all earlier field origins.
Original construction then derives read-only resident field lookup.
The accessor and precheck retain their actual returned operation state.
The completed operation tables start empty over the retained interner.
This is a cold model projection. It does not reset source global tables.

The scan endpoints retain the existing completed Scan as a premise.
That graph uses the historical native-intersection emptiness decision.
This module does not transfer the later conjunction algorithm or prove
completion of the constrained outer caller or its lazy runtime.
-/
namespace MicroCFTA.SourceCurrentClassHistoryEntry
open Cache Language EqualityNormalize SourceEqualityClassOrder
open InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
open InternedNestedProvenance (Values)
open SourceEqualityNativeScoped SourceEqualityNativeInitial SourceEqualityRequiredCache
open SourceEqualityOriginalAllocationHistory
open SourceCurrentEqualityClassScan SourceCurrentClassScanGlobalMemos
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Key" => SourceEqualityPartialConstraintKey.Key
local notation "Allocated" => SourceEqualityConjoinAllocation.Constraint FullSyntax.Formula
local notation "Stored" => SourceEqualityConstraintAllocation.Value
local notation "Native" => SourceRecursiveIntersectionThunks.State
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Memo" => SourceCurrentEmptinessMemo.Memo
local notation "top" => SourceEqualityConstraintConstructors.top (Formula := FullSyntax.Formula)
local notation "conjoin" => SourceEqualityPCSNativeEdge.conjoin
local notation "CostHeap" => InternedFreshOrdinaryCostHeap.Heap
local notation "FieldHeap" => SourceEqualityNativeDemandFieldHeap.Heap
local notation "source" => SourceMemoGate.unconstrained
local notation "reaches" => SourceEndpointReachability.reaches source
local notation "operations" => SourceEqualityConstraintMemoAllocation.initial
local notation "prefix" => SourceEqualityPartialPrecheckAllocation.run
variable {initialCache finalCache : Cache.State Key} {originals : List Guard}

/-- One covered history derives the cold entry and every resident original field load. -/
theorem constructed [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (width : Nat) (history : History initialCache finalCache originals) (valid : Cache.Valid initialCache)
    (expression : InternedNestedConstruction.Syntax Symbol Guard)
    (covered : ∀ original ∈ SourceEqualityConstraintOrigins.guards expression, original ∈ originals)
    (value : Value Symbol Guard) (heap : State Symbol Guard)
    (built : InternedFreshOrdinaryConstruction.build expression [] empty = .done value heap) :
    SourceEqualityConstraintMemoAllocation.Valid (operations finalCache) ∧
      IdleReady top conjoin (cold width heap) ∧ CostHeap heap ∧ FieldHeap heap ∧
      Available heap value ∧ value.free = [] ∧
      ∀ edge, EdgeResident heap edge → Values heap edge.children ∧
        ∃ loaded : Allocated,
          SourceEqualityConstraintFieldLookup.load edge.entry.key.constraint finalCache = .ok (some loaded) ∧
          SourceEqualityConjoinAllocation.readback loaded = edge.entry.key.constraint ∧
          SourceEqualityConstraintAllocation.Ready finalCache loaded.stored ∧
          SourceEqualityPhysicalPayload.read edge.entry.key.constraint.equalities = .ok loaded.stored.payload :=
  ⟨history.operations_valid valid, SourceCurrentClassOriginalFields.constructed width expression
    (history.syntax_valid expression covered) finalCache (history.inventory valid expression covered)
    value heap built⟩

/-- Every ready inherited value has a finite exact allocated accessor and precheck after the derived load. -/
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
        ∃ branch,
          (prefix loaded.stored loaded.guard inherited (operations finalCache)).1 = .ok branch ∧
          SourceEqualityPhysicalClassEntry.entry edge.entry.key.constraint inherited.payload = .ok branch ∧
          SourceEqualityConstraintMemoAllocation.Valid
            (prefix loaded.stored loaded.guard inherited (operations finalCache)).2 ∧
          SourceEqualityConstraintMemoAllocation.Grows (operations finalCache)
            (prefix loaded.stored loaded.guard inherited (operations finalCache)).2 := by
  have initial := constructed width history valid expression covered value heap built
  obtain ⟨loaded, found, readback, ready, originalRead⟩ := (initial.2.2.2.2.2.2 edge resident).2
  have cached := SourceEqualityNativeDemandFieldHeap.resident_cached heap initial.2.2.2.1 edge resident
  refine ⟨loaded, found, readback, ready, ?_⟩
  intro inherited inheritedReady
  obtain ⟨own, branch, ownRead, done, checked, afterValid, growth⟩ :=
    SourceEqualityPartialPrecheckAllocation.run_correct loaded.stored loaded.guard inherited (operations finalCache)
      initial.1 ready inheritedReady edge.entry.key.constraint.equalities cached originalRead
  have guardEq : loaded.guard = edge.entry.key.constraint.guard :=
    congrArg (fun constraint : Guard => constraint.guard) readback
  have computed : SourceEqualityPhysicalPayload.own edge.entry.key.constraint = .ok own.payload := by
    simpa only [guardEq] using ownRead
  exact ⟨branch, done,
    (SourceEqualityPhysicalClassEntry.entry_of_own edge.entry.key.constraint inherited.payload own.payload computed).trans checked,
    afterValid, growth⟩

/-- A completed cold scan derives its memo invariants without supplied origins, loads, or operation validity. -/
theorem cold_scan_memos [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (width : Nat) (history : History initialCache finalCache originals) (valid : Cache.Valid initialCache)
    (expression : InternedNestedConstruction.Syntax Symbol Guard)
    (covered : ∀ original ∈ SourceEqualityConstraintOrigins.guards expression, original ∈ originals)
    (value : Value Symbol Guard) (heap : State Symbol Guard)
    (built : InternedFreshOrdinaryConstruction.build expression [] empty = .done value heap)
    (edge : EdgeValue Symbol Guard) (resident : EdgeResident heap edge)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula) :
    ∃ loaded : Allocated,
      SourceEqualityConstraintFieldLookup.load edge.entry.key.constraint finalCache = .ok (some loaded) ∧
      SourceEqualityConjoinAllocation.readback loaded = edge.entry.key.constraint ∧
      SourceEqualityConstraintAllocation.Ready finalCache loaded.stored ∧
      ∀ inherited : Stored, SourceEqualityConstraintAllocation.Ready finalCache inherited →
        ∀ output : List Record,
          (prefix loaded.stored loaded.guard inherited (operations finalCache)).1 = .ok (.classes output) →
          ∀ {selected : Constraints} {outcome : Option Class} {after : Native width Symbol Guard} {saved : Memo},
            (trace : Scan source reaches edge.children (output.map Record.paths) (cold width heap)
              SourceCurrentEmptinessMemo.empty outcome selected after saved) →
            SourceEqualityConstraintMemoAllocation.Valid
              (prefix loaded.stored loaded.guard inherited (operations finalCache)).2 ∧
            SourceEqualityConstraintMemoAllocation.Grows (operations finalCache)
              (prefix loaded.stored loaded.guard inherited (operations finalCache)).2 ∧
            ∃ final : Memos, ScanReads trace EndpointMemoGateTrace.empty final ∧
              EndpointMemoGateTrace.Valid after.machine.heap final ∧
              IdleReady top conjoin after ∧ CostHeap after.machine.heap ∧ FieldHeap after.machine.heap ∧
              Keeps heap after.machine.heap ∧ Values after.machine.heap edge.children ∧
              SourceCurrentEmptinessMemo.Correct formulas solver after.machine.heap saved ∧
              SourceCurrentEmptinessMemo.Extends SourceCurrentEmptinessMemo.empty saved := by
  have initial := constructed width history valid expression covered value heap built
  obtain ⟨loaded, found, readback, ready, _⟩ := (initial.2.2.2.2.2.2 edge resident).2
  refine ⟨loaded, found, readback, ready, ?_⟩
  intro inherited inheritedReady output done selected outcome after saved trace
  exact SourceCurrentClassConstructionEntry.cold_scan_memos width expression (history.syntax_valid expression covered)
    value heap built edge resident (operations finalCache) initial.1 loaded found inherited inheritedReady output done
    trace formulas solver

/-- An accepted original edge cannot be rejected by an actual completed scan after the derived allocated prefix. -/
theorem cold_scan_sound [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (width : Nat) (history : History initialCache finalCache originals) (valid : Cache.Valid initialCache)
    (expression : InternedNestedConstruction.Syntax Symbol Guard)
    (covered : ∀ original ∈ SourceEqualityConstraintOrigins.guards expression, original ∈ originals)
    (value : Value Symbol Guard) (heap : State Symbol Guard)
    (built : InternedFreshOrdinaryConstruction.build expression [] empty = .done value heap)
    (edge : EdgeValue Symbol Guard) (resident : EdgeResident heap edge)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (ambient : InternedGuardedLanguage.Env Symbol) (term : Term Symbol)
    (accepted : InternedGuardedLanguage.edgeMeaning (SourceSymbolicIndex.acceptsConstraint formulas solver) ambient edge term) :
    ∃ loaded : Allocated,
      SourceEqualityConstraintFieldLookup.load edge.entry.key.constraint finalCache = .ok (some loaded) ∧
      SourceEqualityConjoinAllocation.readback loaded = edge.entry.key.constraint ∧
      SourceEqualityConstraintAllocation.Ready finalCache loaded.stored ∧
      ∀ inherited : Stored, SourceEqualityConstraintAllocation.Ready finalCache inherited →
        ∀ output : List Record,
          (prefix loaded.stored loaded.guard inherited (operations finalCache)).1 = .ok (.classes output) →
          ∀ {selected : Constraints} {outcome : Option Class} {after : Native width Symbol Guard} {saved : Memo},
            Scan source reaches edge.children (output.map Record.paths) (cold width heap)
              SourceCurrentEmptinessMemo.empty outcome selected after saved → outcome = none :=
  SourceCurrentClassOriginalFields.cold_scan_sound width expression (history.syntax_valid expression covered)
    (operations finalCache) (history.operations_valid valid) (history.inventory valid expression covered)
    value heap built edge resident formulas solver ambient term accepted

end MicroCFTA.SourceCurrentClassHistoryEntry
