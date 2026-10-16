import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryPassInitialCapacity

namespace MicroCFTA.PassInitialChecks
open Cache Language InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open SourceCurrentAllocatedNativeInventoryState (Inventory At)
open SourceCurrentAllocatedClassPass (Fold Pass PassReads Receipt)
open SourceCurrentAllocatedFiniteOrdinaryNativeProfile (ChildrenShape)
open SourceCurrentAllocatedFiniteOrdinaryPassResources (nodeBudget edgeBudget outputRows outputArity)
open MergedOrdinaryHeight (childrenHeight)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Record" => SourceEqualityClassOrder.Record
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Memo" => SourceCurrentMemoMergeGraph.Memo Symbol Guard
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Valid" => EndpointMemoGateTrace.Valid
local notation "Ready" => SourceCurrentConjunctionClassScan.Ready
local notation "PhysicalStored" => SourceCurrentMemoMergeEffects.Stored
local notation "Profiles" => SourceCurrentAllocatedFiniteOrdinaryMergeProfileCache.Stored
local notation "NativeStored" => SourceCurrentAllocatedFiniteOrdinaryStored.Stored
local notation "OutputStored" => SourceCurrentAllocatedFiniteOrdinaryOutputStored.Stored
local notation "MergeStored" => SourceCurrentAllocatedFiniteOrdinaryMergeCache.Stored
local notation "PassCapacity" => SourceCurrentAllocatedFiniteOrdinaryPassCapacity.PassCapacity
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]


/-- Raw empty tails keep the complete checked state and Merge memo. -/
theorem raw_empty_tail {width : Nat} (values results : List (Value Symbol Guard))
    (before after : Checked width) (memo saved : Memo)
    (actual : Fold [] values before memo results after saved) :
    results = values ∧ after = before ∧ saved = memo := by
  exact SourceCurrentAllocatedFiniteOrdinaryPassInitialCapacity.fold_unique actual .nil

/-- Every raw earlier tail receives the head plan at its exact full return. -/
theorem reached_head (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (inventory : Inventory)
    (bits : Nat) (records : List Record)
    (coherent : ∀ record ∈ records, SourceEqualityClassOrder.Coherent record)
    (active : ∀ record ∈ records, EqualityNormalize.Nontrivial record.paths)
    (values : List (Value Symbol Guard)) (before : Checked (bits + 2)) (memo : Memo)
    (ready : Ready before) (admitted : At formulas solver inventory before)
    (available : Values before.native.machine.heap values)
    (physical : PhysicalStored before.native.machine.heap memo) (profiles : Profiles memo)
    (native : NativeStored before.native) (output : OutputStored before.native)
    (covered : ∀ ambient, SourceCurrentMemoMergeLanguage.CacheCovers (SourceEqualityPCSGuard.holds formulas solver) ambient memo)
    (memos : Memos) (valid : Valid before.native.machine.heap memos)
    (rows arity count depth bound : Nat) (profile : ChildrenShape rows arity values)
    (lengthBound : values.length ≤ count)
    (pathsBound : ∀ record ∈ records, ∀ path ∈ record.paths, path.length ≤ depth)
    (heightBound : childrenHeight values ≤ bound)
    (nodes : before.native.machine.heap.nodes.next + nodeBudget records rows arity count depth bound ≤ 2 ^ bits)
    (edges : before.native.machine.heap.edges.next + edgeBudget records rows arity count depth bound ≤ 2 ^ (bits + 2))
    (record : Record) (present : records = record :: records.tail)
    (middle : List (Value Symbol Guard)) (after : Checked (bits + 2)) (saved : Memo)
    (actualTail : Fold records.tail values before memo middle after saved) :
    SourceCurrentAllocatedFiniteOrdinaryClassCapacity.ClassCapacity bits record middle after saved := by
  have capacity := SourceCurrentAllocatedFiniteOrdinaryPassInitialCapacity.complete formulas solver inventory bits records coherent active values before memo
    ready admitted available physical profiles native output covered memos valid rows arity count depth bound
    profile lengthBound pathsBound heightBound nodes edges
  rw [present] at capacity
  exact capacity.head (by simpa only [List.tail_cons] using actualTail)

/-- Initial-only headroom constructs both old ranges and the full current pass receipt. -/
theorem ranges_and_return (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (inventory : Inventory)
    (bits : Nat) (records : List Record)
    (coherent : ∀ record ∈ records, SourceEqualityClassOrder.Coherent record)
    (active : ∀ record ∈ records, EqualityNormalize.Nontrivial record.paths)
    (values : List (Value Symbol Guard)) (before : Checked (bits + 2)) (memo : Memo)
    (ready : Ready before) (admitted : At formulas solver inventory before)
    (available : Values before.native.machine.heap values)
    (physical : PhysicalStored before.native.machine.heap memo) (profiles : Profiles memo)
    (native : NativeStored before.native) (output : OutputStored before.native)
    (covered : ∀ ambient, SourceCurrentMemoMergeLanguage.CacheCovers (SourceEqualityPCSGuard.holds formulas solver) ambient memo)
    (memos : Memos) (valid : Valid before.native.machine.heap memos)
    (rows arity count depth bound : Nat) (profile : ChildrenShape rows arity values)
    (lengthBound : values.length ≤ count)
    (pathsBound : ∀ record ∈ records, ∀ path ∈ record.paths, path.length ≤ depth)
    (heightBound : childrenHeight values ≤ bound)
    (nodes : before.native.machine.heap.nodes.next + nodeBudget records rows arity count depth bound ≤ 2 ^ bits)
    (edges : before.native.machine.heap.edges.next + edgeBudget records rows arity count depth bound ≤ 2 ^ (bits + 2)) :
    SourceCurrentAllocatedClassPass.Ranges records values before memo ∧
    ∃ results after saved next final, ∃ actual : Pass records values before memo results after saved,
      PassReads formulas solver actual memos final ∧
      Receipt formulas solver next records values before memo results after saved memos final ∧
      At formulas solver next after ∧ Valid after.native.machine.heap final ∧
      NativeStored after.native ∧ MergeStored saved ∧
      All₂ SourceCurrentAllocatedFiniteOrdinaryRequired.NodeNarrow values results := by
  have checks := SourceCurrentAllocatedFiniteOrdinaryPassInitialCapacity.ranges formulas solver inventory bits records coherent active
    values before memo ready admitted available physical profiles native output covered memos valid rows arity count depth bound
    profile lengthBound pathsBound heightBound nodes edges
  obtain ⟨results, after, saved, next, final, actual, reads, receipt, nativeAfter, merged, related⟩ :=
    SourceCurrentAllocatedFiniteOrdinaryPassInitialCapacity.finite formulas solver inventory bits records coherent active
      values before memo ready admitted available physical profiles native output covered memos valid rows arity count depth bound
      profile lengthBound pathsBound heightBound nodes edges
  exact ⟨checks, results, after, saved, next, final, actual, reads, receipt, receipt.admitted,
    receipt.globals.valid, nativeAfter, merged, related⟩

end MicroCFTA.PassInitialChecks

#print axioms MicroCFTA.PassInitialChecks.raw_empty_tail
#check @MicroCFTA.PassInitialChecks.raw_empty_tail

#print axioms MicroCFTA.PassInitialChecks.reached_head
#check @MicroCFTA.PassInitialChecks.reached_head

#print axioms MicroCFTA.PassInitialChecks.ranges_and_return
#check @MicroCFTA.PassInitialChecks.ranges_and_return
