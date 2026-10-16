import MicroCFTA.SourceCurrentAllocatedSharedTargetWorkerActual

namespace MicroCFTA.CurrentSharedTargetIndependentReview
open Cache (put)
open Language InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedSharedTargetState (State advance store)
open SourceCurrentAllocatedSharedTargetWorker
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Record" => SourceEqualityClassOrder.Record
local notation "Path" => EqualityNormalize.Path
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Ready" => SourceCurrentAllocatedSharedTargetState.Ready
local notation "Domain" => SourceEqualityProjectionPathDomain.ForestClosed
local notation "ProbeHeap" => InternedFreshOrdinaryProbeHeap.Heap
local notation "ForceRanges" => SourceCurrentAllocatedSharedTargetForce.ForceRanges
local notation "LeafRanges" => SourceCurrentAllocatedSharedTargetLeaf.Ranges
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]

theorem slot_hit_at_zero_bounds_retains_whole_state
    (record : Record) (values : List (Value Symbol Guard)) (path : Path)
    (before : State width) (value : Value Symbol Guard) (present : before.targets path = some value) :
    force 0 0 0 0 0 record values path before = .done value before ∧
      SourceCurrentAllocatedSharedTargetWorkerCompletion.StableRun
        (fun p h m s n => force p h m s n record values path before) value before :=
  ⟨force_hit 0 0 0 0 0 record values path before value present,
    SourceCurrentAllocatedSharedTargetWorkerCompletion.force_complete (.hit present)⟩

theorem target_failure_retains_old_slots_and_reached_checked_state
    (p h m s n : Nat) (record : Record) (values : List (Value Symbol Guard)) (path : Path)
    (before : State width) (checked : SourceEqualityNativeDemand.State width)
    (saved : SourceCurrentAllocatedTargetWorker.Memo)
    (fault : SourceCurrentAllocatedTargetWorker.Fault width)
    (absent : before.targets path = none)
    (failed : SourceCurrentAllocatedTargetWorker.target p h m s n values
      (SourceEqualityClassTarget.operandPaths record.paths path) before.checked before.memo = .failed fault checked saved) :
    force p h m s n record values path before =
      .failed (.target fault) {before with checked := checked, memo := saved} ∧
      (force p h m s n record values path before).state.targets = before.targets ∧
      (force p h m s n record values path before).state.checked.operations = checked.operations ∧
      (force p h m s n record values path before).state.memo = saved := by
  have actual := force_failed p h m s n record values path before absent fault checked saved failed
  exact ⟨actual, by rw [actual]; rfl, by rw [actual]; rfl, by rw [actual]; rfl⟩

theorem hit_then_zero_native_fuel_keeps_exact_continuation
    (record : Record) (values : List (Value Symbol Guard)) (path : Path)
    (target input : Value Symbol Guard) (before : State width)
    (present : before.targets path = some target) :
    leaf 0 0 0 0 0 record values path input before =
      .failed (.native (.yielded (.code (SourceRecursiveIntersectionCode.requestNode
        IntersectionEmptyDomain.emptyDomain target input)) before.checked)) before := by
  simp only [leaf, force, present, Outcome.bind, step, SourceEqualityNativeDemand.execute,
    SourceEqualityNativeDemand.Outcome.state, advance]

theorem miss_stores_only_the_completed_target_and_preserves_other_slots
    (p h m s n : Nat) (record : Record) (values : List (Value Symbol Guard)) (path other : Path)
    (before : State width) (checked : SourceEqualityNativeDemand.State width)
    (saved : SourceCurrentAllocatedTargetWorker.Memo) (value earlier : Value Symbol Guard)
    (absent : before.targets path = none) (different : other ≠ path)
    (old : before.targets other = some earlier)
    (done : SourceCurrentAllocatedTargetWorker.target p h m s n values
      (SourceEqualityClassTarget.operandPaths record.paths path) before.checked before.memo = .done value checked saved) :
    force p h m s n record values path before = .done value (store before path value checked saved) ∧
      (store before path value checked saved).targets other = some earlier := by
  constructor
  · simp only [force, absent, done]
  · simpa only [store, put, different, ite_false] using old

theorem finite_leaf_derives_same_literal_state_and_independent_narrowing
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (record : Record) (values : List (Value Symbol Guard))
    (base : InternedConstructorTemplates.State Symbol Guard) (before : State width)
    (ready : Ready formulas solver inventory record values base before) (known : Values base values)
    (domains : ∀ own ∈ record.paths, Domain (own.map Int.ofNat) values)
    (coherent : SourceEqualityClassOrder.Coherent record) (active : EqualityNormalize.Nontrivial record.paths)
    (path : Path) (member : path ∈ record.paths) (input : Value Symbol Guard)
    (available : Available before.checked.native.machine.heap input) (closed : input.free = [])
    (ranges : LeafRanges record values path input before) (memos : Memos)
    (valid : EndpointMemoGateTrace.Valid before.checked.native.machine.heap memos)
    (probes : ProbeHeap before.checked.native.machine.heap) :
    ∃ result after next final,
      SourceCurrentAllocatedSharedTargetWorkerCompletion.StableRun
        (fun p h m s n => leaf p h m s n record values path input before) result after ∧
      Ready formulas solver next record values base after ∧
      EndpointMemoGateTrace.Valid after.checked.native.machine.heap final ∧
      ProbeHeap after.checked.native.machine.heap ∧ result.free = [] ∧
      SourceCurrentAllocatedSharedTargetForce.Retains before after ∧
      (∀ ambient term, InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver) ambient result term →
        InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver) ambient input term) ∧
      (∀ ambient symbol terms part,
        All₂ (InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver) ambient) values terms →
        EqualityNormalize.ClassSat (.node symbol terms) record.paths →
        (Term.node symbol terms).atPath path = some part →
        InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver) ambient input part →
        InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver) ambient result part) := by
  obtain ⟨result, after, next, final, stable, receipt, probe⟩ :=
    SourceCurrentAllocatedSharedTargetWorkerActual.leaf_finite formulas solver inventory record values base before
      ready known domains coherent active path member input available closed ranges memos valid probes
  exact ⟨result, after, next, final, stable, receipt.ready, receipt.globals.valid, probe,
    receipt.closed, receipt.slots, receipt.narrows, receipt.preserves⟩

end MicroCFTA.CurrentSharedTargetIndependentReview
