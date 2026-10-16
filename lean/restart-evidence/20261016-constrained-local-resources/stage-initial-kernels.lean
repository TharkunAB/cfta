import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryStageInitialCapacity

namespace StageInitialIntegration
open MicroCFTA Cache Language EqualityNormalize InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open SourceCurrentAllocatedNativeInventoryState (Inventory At)
open SourceCurrentConjunctionClassScan (Scan Ready advanceHeap)
open SourceCurrentConjunctionSelectedRecords (Retained)
open SourceCurrentAllocatedFiniteOrdinaryNativeProfile (ChildrenShape)
open SourceCurrentAllocatedFiniteOrdinaryStageResources (nodeBudget edgeBudget)
open MergedOrdinaryHeight (childrenHeight)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Record" => SourceEqualityClassOrder.Record
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Memo" => SourceCurrentMemoMergeGraph.Memo Symbol Guard
local notation "Fourth" => SourceCurrentEmptinessMemo.Memo
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Profiles" => SourceCurrentAllocatedFiniteOrdinaryMergeProfileCache.Stored
local notation "sourceGate" => SourceMemoGate.unconstrained
local notation "sourceReaches" => SourceEndpointReachability.reaches sourceGate
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq (Value Symbol Guard)]

/-- Initial budgets cover every actual earlier Required return and derive the old stage checks. -/
theorem arbitrary_earlier_required (formulas : SourceGuards.Formulas FullSyntax.Formula)
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
    (native : SourceCurrentAllocatedFiniteOrdinaryStored.Stored before.native)
    (output : SourceCurrentAllocatedFiniteOrdinaryOutputStored.Stored before.native)
    (covered : ∀ ambient, SourceCurrentMemoMergeLanguage.CacheCovers (SourceEqualityPCSGuard.holds formulas solver) ambient memo)
    (memos : Memos) (valid : EndpointMemoGateTrace.Valid before.native.machine.heap memos)
    (rows arity count depth bound : Nat) (profile : ChildrenShape rows arity values)
    (lengthBound : values.length ≤ count)
    (pathsBound : ∀ record ∈ records, ∀ path ∈ record.paths, path.length ≤ depth)
    (heightBound : childrenHeight values ≤ bound)
    (nodes : before.native.machine.heap.nodes.next + nodeBudget records rows arity count depth bound ≤ 2 ^ bits)
    (edges : before.native.machine.heap.edges.next + edgeBudget records rows arity count depth bound ≤ 2 ^ (bits + 2))
    {selected : Constraints} {middle : Checked (bits + 2)} {savedFourth : Fourth}
    (scan : Scan budget sourceGate sourceReaches values (records.map SourceEqualityClassOrder.Record.paths)
      before fourth none selected middle savedFourth)
    (kept : List Record) (retained : Retained scan records kept) (fuel readFuel : Nat)
    (requiredValues : List (Value Symbol Guard)) (heap : State Symbol Guard)
    (required : SourceEqualityRequiredExecution.requireAll fuel readFuel (SourceEqualitySelectedRequired.paths selected)
      values middle.native.machine.heap = .done requiredValues heap) :
    SourceCurrentAllocatedFiniteOrdinaryPassCapacity.PassCapacity bits kept requiredValues (advanceHeap middle heap) memo ∧
      SourceCurrentConjunctionScanClassPass.Ranges budget records values before fourth memo := by
  have capacity := SourceCurrentAllocatedFiniteOrdinaryStageInitialCapacity.complete formulas solver inventory bits budget
    records values before fourth memo ready admitted available proper fields correct physical profiles native output covered
    memos valid rows arity count depth bound profile lengthBound pathsBound heightBound nodes edges
  refine ⟨capacity.pass scan kept retained fuel readFuel requiredValues heap required, ?_⟩
  exact SourceCurrentAllocatedFiniteOrdinaryStageCapacity.ranges bits formulas solver inventory budget records values
    before fourth memo ready admitted available (ChildrenShape.domain values profile) proper fields correct physical
    covered native profiles.domain capacity memos valid

set_option pp.explicit true
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 100000
set_option format.width 200
#print axioms arbitrary_earlier_required
#check @arbitrary_earlier_required
end StageInitialIntegration
