import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryStageResources

namespace StageResourceIntegration
open MicroCFTA Cache Language EqualityNormalize InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open SourceCurrentAllocatedNativeInventoryState (Inventory At)
open SourceCurrentConjunctionClassScan (Scan Ready)
open SourceCurrentConjunctionScanClassPass (Reduction Receipt)
open SourceCurrentConjunctionScanClassPassActual (Reads)
open SourceCurrentAllocatedFiniteOrdinaryNativeProfile (ChildrenShape)
open SourceCurrentAllocatedFiniteOrdinaryStageResources
open SourceCurrentAllocatedFiniteOrdinaryConstructorWorkTrace (Trace)
open SourceCurrentAllocatedFiniteOrdinaryReservations (nodeRequests edgeRequests)
open MergedOrdinaryHeight (childrenHeight)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Record" => SourceEqualityClassOrder.Record
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Memo" => SourceCurrentMemoMergeGraph.Memo Symbol Guard
local notation "Fourth" => SourceCurrentEmptinessMemo.Memo
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "NativeStored" => SourceCurrentAllocatedFiniteOrdinaryStored.Stored
local notation "OutputStored" => SourceCurrentAllocatedFiniteOrdinaryOutputStored.Stored
local notation "Profiles" => SourceCurrentAllocatedFiniteOrdinaryMergeProfileCache.Stored
local notation "sourceGate" => SourceMemoGate.unconstrained
local notation "sourceReaches" => SourceEndpointReachability.reaches sourceGate
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq (Value Symbol Guard)]

/-- A constructed complete stage supplies the next allocation-free Scan at its actual return. -/
theorem stage_then_scan (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (inventory : Inventory)
    (bits budget : Nat) (records : List Record) (values : List (Value Symbol Guard))
    (before : Checked (bits + 2)) (fourth : Fourth) (memo : Memo)
    (ready : Ready before) (admitted : At formulas solver inventory before)
    (available : Values before.native.machine.heap values)
    (proper : ∀ record ∈ records, ∀ path ∈ record.paths, path ≠ [])
    (fields : ∀ record ∈ records, SourceEqualityClassOrder.Coherent record ∧
      EqualityTrie.Ascending record.trie ∧ Nontrivial record.paths)
    (correct : SourceCurrentEmptinessMemo.Correct formulas solver before.native.machine.heap fourth)
    (physical : SourceCurrentMemoMergeEffects.Stored before.native.machine.heap memo) (profiles : Profiles memo)
    (native : NativeStored before.native) (output : OutputStored before.native)
    (covered : ∀ ambient, SourceCurrentMemoMergeLanguage.CacheCovers (SourceEqualityPCSGuard.holds formulas solver) ambient memo)
    (memos : Memos) (valid : EndpointMemoGateTrace.Valid before.native.machine.heap memos)
    (rows arity count depth bound : Nat) (profile : ChildrenShape rows arity values)
    (lengthBound : values.length ≤ count)
    (pathsBound : ∀ record ∈ records, ∀ path ∈ record.paths, path.length ≤ depth)
    (heightBound : childrenHeight values ≤ bound)
    (nodes : before.native.machine.heap.nodes.next + nodeBudget records rows arity count depth bound ≤ 2 ^ bits)
    (edges : before.native.machine.heap.edges.next + edgeBudget records rows arity count depth bound ≤ 2 ^ (bits + 2)) :
    ∃ results after saved next final requests,
    ∃ actual : Reduction budget records values before fourth memo none results after fourth saved,
      Reads formulas solver actual memos final ∧
      Receipt formulas solver next records values results before after fourth fourth memo saved none final ∧
      NativeStored after.native ∧ OutputStored after.native ∧ Profiles saved ∧
      SourceCurrentAllocatedFiniteOrdinaryCapacity.Capacity bits after ∧
      Trace before.native.machine.heap after.native.machine.heap requests ∧
      nodeRequests requests ≤ nodeBudget records rows arity count depth bound ∧
      edgeRequests requests ≤ edgeBudget records rows arity count depth bound ∧
      ∃ scan : Scan budget sourceGate sourceReaches results (records.map SourceEqualityClassOrder.Record.paths)
        after fourth none (records.map SourceEqualityClassOrder.Record.paths) after fourth,
        SourceCurrentAllocatedScanSourceReads.ScanReads scan final final := by
  obtain ⟨results, after, saved, next, final, requests, actual, reads, receipt, _stable,
    nativeAfter, outputAfter, profilesAfter, produced, _related, _sameLength, _finalHeight,
    trace, nodeCount, edgeCount, capacity, _nodeSupply, _edgeSupply⟩ :=
    complete formulas solver inventory bits budget records values before fourth memo ready admitted available proper fields correct
      physical profiles native output covered memos valid rows arity count depth bound profile lengthBound pathsBound heightBound nodes edges
  obtain ⟨scan, nextReads⟩ := SourceCurrentAllocatedFiniteOrdinaryScan.construct budget results
    (records.map SourceEqualityClassOrder.Record.paths) after fourth receipt.ready receipt.available
      (ChildrenShape.domain results produced) final
  exact ⟨results, after, saved, next, final, requests, actual, reads, receipt, nativeAfter, outputAfter,
    profilesAfter, capacity, trace, nodeCount, edgeCount, scan, nextReads⟩

private theorem pass_zero (records : List Record) (rows arity depth bound : Nat) :
    SourceCurrentAllocatedFiniteOrdinaryPassResources.nodeBudget records rows arity 0 depth bound = 0 ∧
    SourceCurrentAllocatedFiniteOrdinaryPassResources.edgeBudget records rows arity 0 depth bound = 0 := by
  induction records with
  | nil => exact ⟨rfl, rfl⟩
  | cons record records ih =>
      simp only [SourceCurrentAllocatedFiniteOrdinaryPassResources.nodeBudget,
        SourceCurrentAllocatedFiniteOrdinaryPassResources.edgeBudget,
        SourceCurrentAllocatedFiniteOrdinaryClassResources.nodeBudget,
        SourceCurrentAllocatedFiniteOrdinaryClassResources.edgeBudget, Nat.zero_mul, Nat.add_zero, ih.1, ih.2]
      exact ⟨trivial, trivial⟩

/-- An empty forest needs no constructor headroom even with nonempty class records. -/
theorem empty_forest (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (inventory : Inventory)
    (bits budget : Nat) (records : List Record) (before : Checked (bits + 2)) (fourth : Fourth) (memo : Memo)
    (ready : Ready before) (admitted : At formulas solver inventory before)
    (proper : ∀ record ∈ records, ∀ path ∈ record.paths, path ≠ [])
    (fields : ∀ record ∈ records, SourceEqualityClassOrder.Coherent record ∧
      EqualityTrie.Ascending record.trie ∧ Nontrivial record.paths)
    (correct : SourceCurrentEmptinessMemo.Correct formulas solver before.native.machine.heap fourth)
    (physical : SourceCurrentMemoMergeEffects.Stored before.native.machine.heap memo) (profiles : Profiles memo)
    (native : NativeStored before.native) (output : OutputStored before.native)
    (covered : ∀ ambient, SourceCurrentMemoMergeLanguage.CacheCovers (SourceEqualityPCSGuard.holds formulas solver) ambient memo)
    (memos : Memos) (valid : EndpointMemoGateTrace.Valid before.native.machine.heap memos)
    (rows arity depth bound : Nat)
    (pathsBound : ∀ record ∈ records, ∀ path ∈ record.paths, path.length ≤ depth)
    (nodes : before.native.machine.heap.nodes.next ≤ 2 ^ bits)
    (edges : before.native.machine.heap.edges.next ≤ 2 ^ (bits + 2)) :
    ∃ after saved next final requests,
    ∃ actual : Reduction budget records [] before fourth memo none [] after fourth saved,
      Reads formulas solver actual memos final ∧
      Receipt formulas solver next records [] [] before after fourth fourth memo saved none final ∧
      SourceCurrentAllocatedLocalWorkerCompletion.StableRun
        (fun g s r e p h m c n => SourceCurrentAllocatedLocalWorker.classes g s r e p h m c n
          budget records [] before fourth memo) [] after fourth saved ∧
      NativeStored after.native ∧ OutputStored after.native ∧ Profiles saved ∧
      Trace before.native.machine.heap after.native.machine.heap requests ∧
      nodeRequests requests = 0 ∧ edgeRequests requests = 0 ∧
      SourceCurrentAllocatedFiniteOrdinaryCapacity.Capacity bits after ∧
      after.native.machine.heap.nodes.next ≤ before.native.machine.heap.nodes.next ∧
      after.native.machine.heap.edges.next ≤ before.native.machine.heap.edges.next := by
  have zero := pass_zero records rows arity depth bound
  have nodeZero : nodeBudget records rows arity 0 depth bound = 0 := by simp only [nodeBudget, Nat.zero_mul, Nat.zero_add, zero.1]
  have edgeZero : edgeBudget records rows arity 0 depth bound = 0 := by simp only [edgeBudget, Nat.zero_mul, Nat.zero_add, zero.2]
  obtain ⟨results, after, saved, next, final, requests, actual, reads, receipt, stable,
    nativeAfter, outputAfter, profilesAfter, _produced, _related, sameLength, _finalHeight,
    trace, nodeCount, edgeCount, capacity, nodeSupply, edgeSupply⟩ :=
    complete formulas solver inventory bits budget records [] before fourth memo ready admitted (by simp [Values]) proper fields correct
      physical profiles native output covered memos valid rows arity 0 depth bound (by trivial) (by simp) pathsBound
      (by change 0 ≤ bound; omega) (by simpa only [nodeZero, Nat.add_zero] using nodes) (by simpa only [edgeZero, Nat.add_zero] using edges)
  have resultsEmpty : results = [] := List.length_eq_zero_iff.mp sameLength
  subst results
  rw [nodeZero] at nodeCount nodeSupply
  rw [edgeZero] at edgeCount edgeSupply
  exact ⟨after, saved, next, final, requests, actual, reads, receipt, stable, nativeAfter, outputAfter,
    profilesAfter, trace, Nat.eq_zero_of_le_zero nodeCount, Nat.eq_zero_of_le_zero edgeCount, capacity,
    by simpa only [Nat.add_zero] using nodeSupply, by simpa only [Nat.add_zero] using edgeSupply⟩

set_option pp.explicit true
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 100000
set_option format.width 200
#print axioms stage_then_scan
#check @stage_then_scan
#print axioms empty_forest
#check @empty_forest
end StageResourceIntegration
