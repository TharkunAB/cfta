import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryStageResources
import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryLocal

/-!
# Initial resources for local equality reduction

The budget reads the deterministic initial precheck result.
Early branches make no constructor request and retain all warm tables.
A live branch constructs its stage at the same returned operation state.
The original field and inherited payload retain the full existing receipt.
-/
namespace MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryLocalResources
open Cache Language EqualityNormalize InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open SourceCurrentAllocatedNativeInventoryState (Inventory At)
open SourceCurrentConjunctionClassScan (Ready)
open SourceCurrentAllocatedLocalReduction (Reduction Receipt)
open SourceCurrentAllocatedLocalReductionActual (Reads)
open SourceCurrentAllocatedFiniteOrdinaryNativeProfile (ChildrenShape)
open SourceCurrentAllocatedFiniteOrdinaryRequired (NodeNarrow)
open SourceCurrentAllocatedFiniteOrdinaryConstructorWorkTrace (Trace)
open SourceCurrentAllocatedFiniteOrdinaryReservations (nodeRequests edgeRequests)
open MergedOrdinaryHeight (childrenHeight)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Allocated" => SourceEqualityConjoinAllocation.Constraint FullSyntax.Formula
local notation "EqValue" => SourceEqualityConstraintAllocation.Value
local notation "Operations" => SourceEqualityConstraintMemoAllocation.State
local notation "Memo" => SourceCurrentMemoMergeGraph.Memo Symbol Guard
local notation "Fourth" => SourceCurrentEmptinessMemo.Memo
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Valid" => EndpointMemoGateTrace.Valid
local notation "PhysicalStored" => SourceCurrentMemoMergeEffects.Stored
local notation "Profiles" => SourceCurrentAllocatedFiniteOrdinaryMergeProfileCache.Stored
local notation "NativeStored" => SourceCurrentAllocatedFiniteOrdinaryStored.Stored
local notation "OutputStored" => SourceCurrentAllocatedFiniteOrdinaryOutputStored.Stored
local notation "Capacity" => SourceCurrentAllocatedFiniteOrdinaryCapacity.Capacity
local notation "prefixState" => SourceCurrentAllocatedPrecheck.state
local notation "runPrefix" => SourceEqualityPartialPrecheckAllocation.run

/-- Only a live initial precheck selects the stage node budget. -/
noncomputable def nodeBudget (loaded : Allocated) (inherited : EqValue) (operations : Operations)
    (rows arity count depth bound : Nat) : Nat :=
  match (runPrefix loaded.stored loaded.guard inherited operations).1 with
  | .ok (.classes records) => SourceCurrentAllocatedFiniteOrdinaryStageResources.nodeBudget records rows arity count depth bound
  | _ => 0

/-- Only a live initial precheck selects the stage edge budget. -/
noncomputable def edgeBudget (loaded : Allocated) (inherited : EqValue) (operations : Operations)
    (rows arity count depth bound : Nat) : Nat :=
  match (runPrefix loaded.stored loaded.guard inherited operations).1 with
  | .ok (.classes records) => SourceCurrentAllocatedFiniteOrdinaryStageResources.edgeBudget records rows arity count depth bound
  | _ => 0

/-- Early branches retain the original row bound; live classes compute their own bound. -/
noncomputable def outputRows (loaded : Allocated) (inherited : EqValue) (operations : Operations)
    (rows count depth bound : Nat) : Nat :=
  match (runPrefix loaded.stored loaded.guard inherited operations).1 with
  | .ok (.classes records) => SourceCurrentAllocatedFiniteOrdinaryStageResources.outputRows records rows count depth bound
  | _ => rows

/-- The initial precheck selects the literal class-pass arity recurrence. -/
noncomputable def outputArity (loaded : Allocated) (inherited : EqValue) (operations : Operations)
    (arity : Nat) : Nat :=
  match (runPrefix loaded.stored loaded.guard inherited operations).1 with
  | .ok (.classes records) => SourceCurrentAllocatedFiniteOrdinaryStageResources.outputArity records arity
  | _ => arity

private theorem erased_profile (values : List (Value Symbol Guard)) (rows arity : Nat) :
    ChildrenShape rows arity (EqualityLeafProjectionRuntimeEmpty.erase values) := by
  induction values with
  | nil => trivial
  | cons value values ih => exact ⟨trivial, ih⟩

variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq (Value Symbol Guard)]

/-- Initial field facts, profiles, and total headroom construct the full local reduction. -/
theorem complete (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (inventory : Inventory)
    (bits budget : Nat) (original : Guard) (loaded : Allocated) (inherited : EqValue)
    (values : List (Value Symbol Guard)) (before : Checked (bits + 2)) (fourth : Fourth) (memo : Memo)
    (ready : Ready before) (admitted : At formulas solver inventory before)
    (cached : SourceEqualityGuardReadback.Cached original.equalities)
    (found : SourceEqualityConstraintFieldLookup.load original before.operations.constraints = .ok (some loaded))
    (inheritedReady : SourceEqualityConstraintAllocation.Ready before.operations.constraints inherited)
    (available : Values before.native.machine.heap values)
    (correct : SourceCurrentEmptinessMemo.Correct formulas solver before.native.machine.heap fourth)
    (physical : PhysicalStored before.native.machine.heap memo) (profiles : Profiles memo)
    (native : NativeStored before.native) (output : OutputStored before.native)
    (covered : ∀ ambient, SourceCurrentMemoMergeLanguage.CacheCovers (SourceEqualityPCSGuard.holds formulas solver) ambient memo)
    (memos : Memos) (valid : Valid before.native.machine.heap memos)
    (rows arity count depth bound : Nat) (profile : ChildrenShape rows arity values)
    (lengthBound : values.length ≤ count)
    (pathsBound : ∀ records, (runPrefix loaded.stored loaded.guard inherited before.operations).1 = .ok (.classes records) →
      ∀ record ∈ records, ∀ path ∈ record.paths, path.length ≤ depth)
    (heightBound : childrenHeight values ≤ bound)
    (nodes : before.native.machine.heap.nodes.next + nodeBudget loaded inherited before.operations rows arity count depth bound ≤ 2 ^ bits)
    (edges : before.native.machine.heap.edges.next + edgeBudget loaded inherited before.operations rows arity count depth bound ≤ 2 ^ (bits + 2)) :
    ∃ results after saved next final requests,
    ∃ actual : Reduction budget loaded inherited values before fourth memo results after fourth saved,
      Reads formulas solver actual memos final ∧
      Receipt formulas solver next original loaded inherited values results before after fourth fourth memo saved final ∧
      SourceCurrentAllocatedLocalWorkerCompletion.StableRun
        (fun g s r e p h m c n => SourceCurrentAllocatedLocalWorker.reduce g s r e p h m c n
          budget loaded inherited values before fourth memo) results after fourth saved ∧
      NativeStored after.native ∧ OutputStored after.native ∧ Profiles saved ∧
      ChildrenShape (outputRows loaded inherited before.operations rows count depth bound)
        (outputArity loaded inherited before.operations arity) results ∧
      All₂ NodeNarrow values results ∧ results.length = values.length ∧ childrenHeight results ≤ bound ∧
      Trace before.native.machine.heap after.native.machine.heap requests ∧
      nodeRequests requests ≤ nodeBudget loaded inherited before.operations rows arity count depth bound ∧
      edgeRequests requests ≤ edgeBudget loaded inherited before.operations rows arity count depth bound ∧ Capacity bits after ∧
      after.native.machine.heap.nodes.next ≤ before.native.machine.heap.nodes.next + nodeBudget loaded inherited before.operations rows arity count depth bound ∧
      after.native.machine.heap.edges.next ≤ before.native.machine.heap.edges.next + edgeBudget loaded inherited before.operations rows arity count depth bound := by
  have domain := ChildrenShape.domain values profile
  have ranges : SourceCurrentAllocatedLocalReductionActual.Ranges budget loaded inherited values before fourth := by
    intro records _
    exact SourceCurrentAllocatedFiniteOrdinaryScanRanges.scan_ranges budget SourceMemoGate.unconstrained
      (SourceEndpointReachability.reaches SourceMemoGate.unconstrained) values
      (records.map SourceEqualityClassOrder.Record.paths) (prefixState before loaded inherited) fourth
      ready.good.native.machine.1.coherent available domain
  obtain ⟨own, branch, checked⟩ := SourceCurrentAllocatedPrecheck.loaded_complete formulas solver inventory before
    ready admitted original cached loaded found inherited inheritedReady
  cases branch with
  | unchanged =>
      have actual : Reduction budget loaded inherited values before fourth memo values
          (prefixState before loaded inherited) fourth memo := .unchanged checked.actual
      have reads : Reads formulas solver actual memos memos := .unchanged (actual := checked.actual)
      obtain ⟨next, receipt⟩ := SourceCurrentAllocatedLocalReductionActual.verified formulas solver inventory original
        reads ready admitted cached found inheritedReady available correct physical covered ranges valid
      have budgetN : nodeBudget loaded inherited before.operations rows arity count depth bound = 0 := by rw [nodeBudget, checked.actual]
      have budgetE : edgeBudget loaded inherited before.operations rows arity count depth bound = 0 := by rw [edgeBudget, checked.actual]
      refine ⟨values, prefixState before loaded inherited, memo, next, memos, [], actual, reads, receipt,
        SourceCurrentAllocatedLocalWorkerCompletion.reduce_complete actual, native, output, profiles, ?_,
        SourceCurrentAllocatedFiniteOrdinaryNarrow.forest_refl domain, rfl, heightBound, .refl _, ?_, ?_, ?_, ?_, ?_⟩
      · simpa only [outputRows, outputArity, checked.actual] using profile
      · simp only [nodeRequests]; omega
      · simp only [edgeRequests]; omega
      · constructor <;> change before.native.machine.heap.nodes.next ≤ _ <;> first | omega | assumption
      · change before.native.machine.heap.nodes.next ≤ _; omega
      · change before.native.machine.heap.edges.next ≤ _; omega
  | emptyChildren =>
      let results := EqualityLeafProjectionRuntimeEmpty.erase values
      have actual : Reduction budget loaded inherited values before fourth memo results
          (prefixState before loaded inherited) fourth memo := .emptyChildren checked.actual
      have reads : Reads formulas solver actual memos memos := .emptyChildren (actual := checked.actual)
      obtain ⟨next, receipt⟩ := SourceCurrentAllocatedLocalReductionActual.verified formulas solver inventory original
        reads ready admitted cached found inheritedReady available correct physical covered ranges valid
      have budgetN : nodeBudget loaded inherited before.operations rows arity count depth bound = 0 := by rw [nodeBudget, checked.actual]
      have budgetE : edgeBudget loaded inherited before.operations rows arity count depth bound = 0 := by rw [edgeBudget, checked.actual]
      have related := SourceCurrentAllocatedFiniteOrdinaryNarrow.forest_erase (Symbol := Symbol) (Guard := Guard) values
      refine ⟨results, prefixState before loaded inherited, memo, next, memos, [], actual, reads, receipt,
        SourceCurrentAllocatedLocalWorkerCompletion.reduce_complete actual, native, output, profiles, ?_, related,
        List.length_map _, Nat.le_trans (SourceCurrentAllocatedFiniteOrdinaryNarrow.forest_height related) heightBound,
        .refl _, ?_, ?_, ?_, ?_, ?_⟩
      · simpa only [outputRows, outputArity, checked.actual] using erased_profile values rows arity
      · simp only [nodeRequests]; omega
      · simp only [edgeRequests]; omega
      · constructor <;> change before.native.machine.heap.nodes.next ≤ _ <;> first | omega | assumption
      · change before.native.machine.heap.nodes.next ≤ _; omega
      · change before.native.machine.heap.edges.next ≤ _; omega
  | classes records =>
      obtain ⟨proper, _records, _read, _classes, _order, fields⟩ := checked.classes records rfl
      have recordsProper : ∀ record ∈ records, ∀ path ∈ record.paths, path ≠ [] := by
        intro record member
        exact proper record.paths (List.mem_map.mpr ⟨record, member, rfl⟩)
      obtain ⟨results, after, saved, _stageInventory, final, requests, stage, stageReads, _stageReceipt, _stageStable,
        nativeAfter, outputAfter, profilesAfter, produced, related, sameLength, finalHeight, trace, nodeCount, edgeCount,
        capacity, nodeSupply, edgeSupply⟩ := SourceCurrentAllocatedFiniteOrdinaryStageResources.complete
          formulas solver inventory bits budget records values (prefixState before loaded inherited) fourth memo
          checked.ready checked.admitted available recordsProper fields correct physical profiles native output covered memos valid
          rows arity count depth bound profile lengthBound (pathsBound records checked.actual) heightBound
          (by simpa only [nodeBudget, checked.actual] using nodes) (by simpa only [edgeBudget, checked.actual] using edges)
      have actual : Reduction budget loaded inherited values before fourth memo results after fourth saved :=
        .classes checked.actual stage
      have reads : Reads formulas solver actual memos final := .classes (actual := checked.actual) stageReads
      obtain ⟨next, receipt⟩ := SourceCurrentAllocatedLocalReductionActual.verified formulas solver inventory original
        reads ready admitted cached found inheritedReady available correct physical covered ranges valid
      refine ⟨results, after, saved, next, final, requests, actual, reads, receipt,
        SourceCurrentAllocatedLocalWorkerCompletion.reduce_complete actual, nativeAfter, outputAfter, profilesAfter,
        ?_, related, sameLength, finalHeight, trace, ?_, ?_, capacity, ?_, ?_⟩
      · simpa only [outputRows, outputArity, checked.actual] using produced
      · simpa only [nodeBudget, checked.actual] using nodeCount
      · simpa only [edgeBudget, checked.actual] using edgeCount
      · simpa only [nodeBudget, checked.actual] using nodeSupply
      · simpa only [edgeBudget, checked.actual] using edgeSupply

end MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryLocalResources
