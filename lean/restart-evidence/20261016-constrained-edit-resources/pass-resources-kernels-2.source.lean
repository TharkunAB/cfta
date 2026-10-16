import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryPassResources

namespace PassResourceIntegration
open MicroCFTA Cache Language InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open SourceCurrentAllocatedNativeInventoryState (Inventory At)
open SourceCurrentAllocatedClassPass (Fold FoldReads Pass PassReads Receipt)
open SourceCurrentAllocatedFiniteOrdinaryNativeProfile (ChildrenShape)
open SourceCurrentAllocatedFiniteOrdinaryRequired (NodeNarrow)
open SourceCurrentAllocatedFiniteOrdinaryConstructorWorkTrace (Trace)
open SourceCurrentAllocatedFiniteOrdinaryReservations (nodeRequests edgeRequests)
open SourceCurrentAllocatedFiniteOrdinaryPassResources
open MergedOrdinaryHeight (childrenHeight)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Record" => SourceEqualityClassOrder.Record
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Memo" => SourceCurrentMemoMergeGraph.Memo Symbol Guard
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Ready" => SourceCurrentConjunctionClassScan.Ready
local notation "NativeStored" => SourceCurrentAllocatedFiniteOrdinaryStored.Stored
local notation "OutputStored" => SourceCurrentAllocatedFiniteOrdinaryOutputStored.Stored
local notation "Profiles" => SourceCurrentAllocatedFiniteOrdinaryMergeProfileCache.Stored
local notation "Class" => SourceCurrentAllocatedClassEdits.Class
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]

private theorem two_order {bits : Nat} {first second : Record} {values results : List (Value Symbol Guard)}
    {before after : Checked (bits + 2)} {memo saved : Memo}
    (actual : Fold [first, second] values before memo results after saved) :
    ∃ middle step current, Class second values before memo middle step current ∧
      Class first middle step current results after saved := by
  cases actual with
  | cons tail head =>
      cases tail with
      | cons initial secondActual =>
          cases initial
          exact ⟨_, _, _, secondActual, head⟩

private theorem empty_memos {bits : Nat} {formulas : SourceGuards.Formulas FullSyntax.Formula}
    {solver : SourceGuards.Entailment FullSyntax.Formula} {values results : List (Value Symbol Guard)}
    {before after : Checked (bits + 2)} {memo saved : Memo} {memos final : Memos}
    {actual : Pass [] values before memo results after saved}
    (reads : PassReads formulas solver actual memos final) : final = memos := by
  cases reads with
  | done remaining =>
      cases remaining
      rfl

/-- Both classes are constructed from one initial budget and share the actual tail state. -/
theorem two_classes (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (inventory : Inventory)
    (bits : Nat) (first second : Record)
    (coherent : ∀ record ∈ [first, second], SourceEqualityClassOrder.Coherent record)
    (active : ∀ record ∈ [first, second], EqualityNormalize.Nontrivial record.paths)
    (values : List (Value Symbol Guard)) (before : Checked (bits + 2)) (memo : Memo)
    (ready : Ready before) (admitted : At formulas solver inventory before)
    (available : Values before.native.machine.heap values)
    (physical : SourceCurrentMemoMergeEffects.Stored before.native.machine.heap memo) (profiles : Profiles memo)
    (native : NativeStored before.native) (output : OutputStored before.native)
    (covered : ∀ ambient, SourceCurrentMemoMergeLanguage.CacheCovers (SourceEqualityPCSGuard.holds formulas solver) ambient memo)
    (memos : Memos) (valid : EndpointMemoGateTrace.Valid before.native.machine.heap memos)
    (rows arity count depth bound : Nat) (profile : ChildrenShape rows arity values)
    (lengthBound : values.length ≤ count)
    (pathsBound : ∀ record ∈ [first, second], ∀ path ∈ record.paths, path.length ≤ depth)
    (heightBound : childrenHeight values ≤ bound)
    (nodes : before.native.machine.heap.nodes.next + nodeBudget [first, second] rows arity count depth bound ≤ 2 ^ bits)
    (edges : before.native.machine.heap.edges.next + edgeBudget [first, second] rows arity count depth bound ≤ 2 ^ (bits + 2)) :
    ∃ middle step current results after saved next final requests,
    ∃ actual : Fold [first, second] values before memo results after saved,
      FoldReads formulas solver actual memos final ∧
      Class second values before memo middle step current ∧ Class first middle step current results after saved ∧
      Receipt formulas solver next [first, second] values before memo results after saved memos final ∧
      SourceCurrentAllocatedClassWorkerCompletion.StableRun
        (fun e p h m s n => SourceCurrentAllocatedClassWorker.fold e p h m s n [first, second] values before memo) results after saved ∧
      NativeStored after.native ∧ OutputStored after.native ∧ Profiles saved ∧
      ChildrenShape (outputRows [first, second] rows count depth bound) (outputArity [first, second] arity) results ∧
      All₂ NodeNarrow values results ∧ results.length = values.length ∧ childrenHeight results ≤ bound ∧
      Trace before.native.machine.heap after.native.machine.heap requests ∧
      nodeRequests requests ≤ nodeBudget [first, second] rows arity count depth bound ∧
      edgeRequests requests ≤ edgeBudget [first, second] rows arity count depth bound ∧
      SourceCurrentAllocatedFiniteOrdinaryCapacity.Capacity bits after := by
  obtain ⟨results, after, saved, next, final, requests, actual, reads, receipt, stable,
    nativeAfter, outputAfter, profilesAfter, produced, related, sameLength, finalHeight,
    trace, nodeCount, edgeCount, capacity, _nodeSupply, _edgeSupply⟩ :=
    fold_complete formulas solver inventory bits [first, second] coherent active values before memo ready admitted available
      physical profiles native output covered memos valid rows arity count depth bound profile lengthBound pathsBound heightBound nodes edges
  obtain ⟨middle, step, current, secondActual, firstActual⟩ := two_order actual
  exact ⟨middle, step, current, results, after, saved, next, final, requests, actual, reads,
    secondActual, firstActual, receipt, stable, nativeAfter, outputAfter, profilesAfter, produced,
    related, sameLength, finalHeight, trace, nodeCount, edgeCount, capacity⟩

/-- An empty class list can erase an Empty-containing forest with no Work or table change. -/
theorem empty_pass (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (inventory : Inventory)
    (bits : Nat) (values : List (Value Symbol Guard)) (before : Checked (bits + 2)) (memo : Memo)
    (ready : Ready before) (admitted : At formulas solver inventory before)
    (available : Values before.native.machine.heap values)
    (physical : SourceCurrentMemoMergeEffects.Stored before.native.machine.heap memo) (profiles : Profiles memo)
    (native : NativeStored before.native) (output : OutputStored before.native)
    (covered : ∀ ambient, SourceCurrentMemoMergeLanguage.CacheCovers (SourceEqualityPCSGuard.holds formulas solver) ambient memo)
    (memos : Memos) (valid : EndpointMemoGateTrace.Valid before.native.machine.heap memos)
    (rows arity count depth bound : Nat) (profile : ChildrenShape rows arity values)
    (lengthBound : values.length ≤ count) (heightBound : childrenHeight values ≤ bound)
    (nodes : before.native.machine.heap.nodes.next ≤ 2 ^ bits)
    (edges : before.native.machine.heap.edges.next ≤ 2 ^ (bits + 2)) :
    ∃ next, Receipt formulas solver next [] values before memo (EqualityLeafProjectionRuntimeEmpty.propagate values)
      before memo memos memos ∧
      ChildrenShape rows arity (EqualityLeafProjectionRuntimeEmpty.propagate values) ∧
      All₂ NodeNarrow values (EqualityLeafProjectionRuntimeEmpty.propagate values) ∧
      SourceCurrentAllocatedClassWorker.pass 0 0 0 0 0 0 [] values before memo =
        .done (EqualityLeafProjectionRuntimeEmpty.propagate values) before memo ∧
      Trace before.native.machine.heap before.native.machine.heap [] ∧ nodeRequests ([] : List (SourceCurrentAllocatedFiniteOrdinaryReservations.Request Symbol Guard)) = 0 ∧
      edgeRequests ([] : List (SourceCurrentAllocatedFiniteOrdinaryReservations.Request Symbol Guard)) = 0 ∧
      (∀ ambient (symbol : Symbol) terms,
        All₂ (InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver) ambient)
          (EqualityLeafProjectionRuntimeEmpty.propagate values) terms ↔
        All₂ (InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver) ambient) values terms) := by
  obtain ⟨results, after, saved, next, final, _requests, actual, reads, receipt, _stable,
    _nativeAfter, _outputAfter, _profilesAfter, produced, related, _sameLength, _finalHeight,
    _trace, _nodeCount, _edgeCount, _capacity, _nodeSupply, _edgeSupply⟩ :=
    complete formulas solver inventory bits [] (by simp) (by simp) values before memo ready admitted available
      physical profiles native output covered memos valid rows arity count depth bound profile lengthBound (by simp) heightBound
      (by simpa only [nodeBudget, Nat.add_zero] using nodes) (by simpa only [edgeBudget, Nat.add_zero] using edges)
  have sameMemos := empty_memos reads
  subst final
  cases actual with
  | done fold =>
      cases fold
      refine ⟨next, receipt, produced, related, rfl, .refl _, rfl, rfl, ?_⟩
      intro ambient symbol terms
      exact (receipt.language ambient symbol terms).2 (by simp)

set_option pp.explicit true
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 100000
set_option format.width 200
#print axioms two_classes
#check @two_classes
#print axioms empty_pass
#check @empty_pass
end PassResourceIntegration
