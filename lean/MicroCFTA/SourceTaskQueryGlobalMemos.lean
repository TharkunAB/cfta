import MicroCFTA.SourceClassQueryGlobalMemos
import MicroCFTA.SourceEmptinessTaskTrace
import MicroCFTA.SourceEmptinessDecisionCosts

/-!
# Three global tables through actual delayed emptiness work

A first captured-task force executes its stored fold. A shared-result hit
makes no native request. Exposure records actual row-read calls before
pure task capture. Reached worklist branches pass the exact returned tables.
The proofs derive coherence from initial invariants and actual operations.
Completed task receipts do not establish GHC demand or publication.
-/
namespace MicroCFTA.SourceTaskQueryGlobalMemos
open Cache InternedConstructorTemplates InternedProbeProvenance
open SourceEqualityRequiredCache SourceEqualityRequiredSemanticCache SourceEqualityNativeScoped
open SourceEmptinessTasks (Force Ready)
open SourceEmptinessTaskRows (Expose)
open SourceEmptinessTaskTrace (Run)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "TaskState" => SourceEmptinessTasks.State
local notation "Task" => SourceEmptinessTasks.Task Symbol Guard
local notation "Value" => InternedConstructorTemplates.Value Symbol Guard
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Valid" => EndpointMemoGateTrace.Valid
local notation "CostHeap" => InternedFreshOrdinaryCostHeap.Heap

/-- A force records its actual shared read or first captured fold. -/
inductive ForceReads [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {emptyGuard : Guard} {conjoin : Guard → Guard → Guard} :
    {task : Task} → {before : TaskState width Symbol Guard} → {value : Value} →
    {after : TaskState width Symbol Guard} → Force emptyGuard conjoin task before value after → Memos → Memos → Prop where
  | value {before : TaskState width Symbol Guard} {value : Value} {memos : Memos}
      (available : Available before.native.machine.heap value) (closed : value.free = []) :
      ForceReads (.value available closed) memos memos
  | hit {before : TaskState width Symbol Guard} {handle : Nat} {cell : SourceEmptinessTasks.Cell Symbol Guard}
      {value : Value} {memos : Memos} (found : before.cells handle = some cell) (completed : cell.result = some value) :
      ForceReads (.hit found completed) memos memos
  | miss {before : TaskState width Symbol Guard} {handle : Nat} {cell : SourceEmptinessTasks.Cell Symbol Guard}
      {value : Value} {native : SourceRecursiveIntersectionThunks.State width Symbol Guard} {memos saved : Memos}
      {fold : SourceEmptinessClassFold.Fold emptyGuard conjoin cell.body.children cell.body.paths before.native value native}
      (found : before.cells handle = some cell) (suspended : cell.result = none)
      (calls : SourceClassQueryGlobalMemos.FoldReads fold memos saved) :
      ForceReads (.miss found suspended fold) memos saved

/-- Exposure records the row read and retains both query tables during task capture. -/
inductive ExposeReads [DecidableEq (EdgeKey Symbol Guard)] :
    {value : Value} → {before : TaskState width Symbol Guard} → {rows : List (List Task)} →
    {after : TaskState width Symbol Guard} → Expose value before rows after → Memos → Memos → Prop where
  | read {before : TaskState width Symbol Guard} {value : Value}
      {edges : List (EdgeValue Symbol Guard)} {heap : State Symbol Guard} {memos saved : Memos}
      (available : Available before.native.machine.heap value) (closed : value.free = [])
      (actual : SourceEqualityProjectionRead.Read value before.native.machine.heap edges heap)
      (calls : SourceEqualityProjectionMemos.ReadReads actual memos.unfolding saved.unfolding)
      (query : saved.query = memos.query) : ExposeReads (.read available closed actual) memos saved

/-- Reached worklist receipts retain source force, exposure, and suffix order. -/
inductive RunReads [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {emptyGuard : Guard} {conjoin : Guard → Guard → Guard} :
    {budget : Nat} → {seen : DelayedEmptinessExplore.Table Task Value} → {pending : List Task} →
    {before : TaskState width Symbol Guard} → {final : DelayedEmptinessExplore.Table Task Value} →
    {after : TaskState width Symbol Guard} →
    Run emptyGuard conjoin budget seen pending before final after → Memos → Memos → Prop where
  | done : RunReads .done memos memos
  | empty (forced : ForceReads forceTrace memos middle) (rest : RunReads restTrace middle saved) :
      RunReads (.empty forceTrace encoded restTrace) memos saved
  | skipped (forced : ForceReads forceTrace memos middle) (rest : RunReads restTrace middle saved) :
      RunReads (.skipped forceTrace encoded skipped restTrace) memos saved
  | admit (forced : ForceReads forceTrace memos first) (exposed : ExposeReads exposeTrace first middle)
      (rest : RunReads restTrace middle saved) :
      RunReads (.admit forceTrace encoded fresh exposeTrace restTrace) memos saved

/-- Actual force operations derive coherent tables without changing either query table. -/
theorem force_memos [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {emptyGuard : Guard} {conjoin : Guard → Guard → Guard}
    {task : Task} {before after : TaskState width Symbol Guard} {value : Value}
    (trace : Force emptyGuard conjoin task before value after) (ready : Ready emptyGuard conjoin before)
    (costs : CostHeap before.native.machine.heap) (memos : Memos) (valid : Valid before.native.machine.heap memos) :
    ∃ saved, ForceReads trace memos saved ∧ Valid after.native.machine.heap saved ∧
      Extends memos.unfolding saved.unfolding ∧ saved.query = memos.query := by
  cases trace with
  | value available closed => exact ⟨memos, .value available closed, valid, extends_refl _, rfl⟩
  | hit found completed => exact ⟨memos, .hit found completed, valid, extends_refl _, rfl⟩
  | miss found suspended fold =>
      have original := ready.cells _ _ found
      obtain ⟨saved, reads, coherent, retained, query⟩ :=
        SourceClassQueryGlobalMemos.fold_closed_memos fold ready.native original.1 original.2.1 costs memos valid
      exact ⟨saved, .miss found suspended reads, coherent, retained, query⟩

/-- Actual row exposure derives all three coherent tables through effect-free capture. -/
theorem expose_memos [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {emptyGuard : Guard} {conjoin : Guard → Guard → Guard}
    {value : Value} {before after : TaskState width Symbol Guard} {rows : List (List Task)}
    (trace : Expose value before rows after) (ready : Ready emptyGuard conjoin before)
    (costs : CostHeap before.native.machine.heap) (memos : Memos) (valid : Valid before.native.machine.heap memos) :
    ∃ saved, ExposeReads trace memos saved ∧ Valid after.native.machine.heap saved ∧
      Extends memos.unfolding saved.unfolding ∧ saved.query = memos.query := by
  cases trace with
  | read available closed actual =>
      obtain ⟨unfolding, calls, coherent, retained⟩ := SourceEqualityProjectionMemos.read_reads actual
        ready.native.semantic costs available memos.unfolding valid.unfolding
      have effects := actual.verified ready.native.semantic available closed
      have query := SourceEndpointMemo.grows _ _ effects.1.growth effects.1.history memos.query valid.query
      refine ⟨{memos with unfolding := unfolding}, .read available closed actual calls rfl, ?_, retained, rfl⟩
      simpa only [SourceEmptinessTaskRows.captureRows_native, SourceEmptinessTasks.advanceNative,
        advanceHeap, SourceRecursiveIntersectionThunks.advance] using (show Valid _ {memos with unfolding := unfolding} from ⟨coherent, query⟩)

/-- The actual reached exploration derives coherent tables at every force and exposure. -/
theorem run_memos [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {emptyGuard : Guard} {conjoin : Guard → Guard → Guard}
    (trace : Run (width := width) emptyGuard conjoin budget seen pending before final after)
    (ready : Ready emptyGuard conjoin before) (costs : CostHeap before.native.machine.heap)
    (memos : Memos) (valid : Valid before.native.machine.heap memos) :
    ∃ saved, RunReads trace memos saved ∧ Valid after.native.machine.heap saved ∧
      Extends memos.unfolding saved.unfolding ∧ saved.query = memos.query := by
  revert valid memos costs ready
  induction trace with
  | done => intro _ _ memos valid; exact ⟨memos, .done, valid, extends_refl _, rfl⟩
  | empty forced encoded rest ih =>
      intro ready costs memos valid
      have first := forced.effects ready
      obtain ⟨middle, reads, coherent, retained, query⟩ := force_memos forced ready costs memos valid
      obtain ⟨saved, suffix, finalValid, finalRetained, finalQuery⟩ :=
        ih first.1 (SourceEmptinessDecisionCosts.force_costs forced ready costs) middle coherent
      exact ⟨saved, .empty (encoded := encoded) reads suffix, finalValid, extends_trans retained finalRetained, finalQuery.trans query⟩
  | skipped forced encoded skipped rest ih =>
      intro ready costs memos valid
      have first := forced.effects ready
      obtain ⟨middle, reads, coherent, retained, query⟩ := force_memos forced ready costs memos valid
      obtain ⟨saved, suffix, finalValid, finalRetained, finalQuery⟩ :=
        ih first.1 (SourceEmptinessDecisionCosts.force_costs forced ready costs) middle coherent
      exact ⟨saved, .skipped (encoded := encoded) (skipped := skipped) reads suffix, finalValid, extends_trans retained finalRetained, finalQuery.trans query⟩
  | admit forced encoded fresh exposed rest ih =>
      intro ready costs memos valid
      have first := forced.effects ready
      have firstCosts := SourceEmptinessDecisionCosts.force_costs forced ready costs
      obtain ⟨firstMemos, forceReads, firstValid, firstRetained, firstQuery⟩ := force_memos forced ready costs memos valid
      have captured := exposed.effects first.1
      obtain ⟨middle, exposeReads, coherent, retained, query⟩ := expose_memos exposed first.1 firstCosts firstMemos firstValid
      obtain ⟨saved, suffix, finalValid, finalRetained, finalQuery⟩ :=
        ih captured.1 (SourceEmptinessDecisionCosts.expose_costs exposed first.1 firstCosts) middle coherent
      exact ⟨saved, .admit (encoded := encoded) (fresh := fresh) forceReads exposeReads suffix, finalValid,
        extends_trans firstRetained (extends_trans retained finalRetained), finalQuery.trans (query.trans firstQuery)⟩

end MicroCFTA.SourceTaskQueryGlobalMemos
