import MicroCFTA.SourceCurrentConstrainedCapMixedShared
import MicroCFTA.SourceCurrentAllocatedRecursiveWarmInitialRanges

set_option linter.all true
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.proofs true
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000

namespace MicroCFTA.MixedSharedIntegration
open Cache InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open SourceCurrentConstrainedCap (Cap)
open SourceCurrentConstrainedCapCheckedJointClosed (Plain)
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedSharedTargetState (State Ready)
open SourceCurrentConstrainedCapMixedShared (Stored force_receipt leaf_receipt leafDepth)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Domain" => SourceEqualityProjectionPathDomain.ForestClosed
local notation "operands" => SourceEqualityClassTarget.operandPaths
local notation "targetDepth" => SourceCurrentConstrainedCapMixedTarget.targetDepth
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]

/-- One actual force certificate supports a second depth at a literal full-state warm hit. -/
theorem force_then_another_depth {width : Nat}
    {formulas : SourceGuards.Formulas FullSyntax.Formula} {solver : SourceGuards.Entailment FullSyntax.Formula}
    {inventory next : Inventory} {record : SourceEqualityClassOrder.Record} {values : List (Value Symbol Guard)}
    {base receiptBase : InternedConstructorTemplates.State Symbol Guard} {path : EqualityNormalize.Path}
    {before after : State width} {value : Value Symbol Guard} {memos final : Memos}
    (receipt : SourceCurrentAllocatedSharedTargetForce.Receipt formulas solver next record values receiptBase path
      before value after memos final)
    (ready : Ready formulas solver inventory record values base before) (known : Values base values)
    (stored : Stored record values before) (depth otherDepth : Nat)
    (bounded : ∀ original ∈ values, Cap Plain depth original)
    (otherBounded : ∀ original ∈ values, Cap Plain otherDepth original)
    (domains : ∀ operand ∈ operands record.paths path, Domain operand values) :
    Stored record values after ∧
      Cap Plain (targetDepth depth (operands record.paths path)) value ∧
      Cap Plain (targetDepth otherDepth (operands record.paths path)) value ∧
      SourceCurrentAllocatedSharedTargetForce.Force record values path after value after := by
  have produced := force_receipt receipt ready known stored depth bounded domains
  exact ⟨produced.1, produced.2, produced.1.slots path value receipt.present otherDepth otherBounded domains,
    .hit receipt.present⟩

/-- Entry counters construct a full warm-slot leaf without a future query range or completed query premise. -/
theorem warm_leaf_from_entry (bits : Nat)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (record : SourceEqualityClassOrder.Record) (values : List (Value Symbol Guard))
    (base : InternedConstructorTemplates.State Symbol Guard) (before : State (bits + 2))
    (ready : Ready formulas solver inventory record values base before) (known : Values base values)
    (stored : Stored record values before)
    (domains : ∀ own ∈ record.paths, Domain (own.map Int.ofNat) values)
    (coherent : SourceEqualityClassOrder.Coherent record) (active : EqualityNormalize.Nontrivial record.paths)
    (path : EqualityNormalize.Path) (member : path ∈ record.paths) (target : Value Symbol Guard)
    (present : before.targets path = some target)
    (capturedDepth : Nat) (bounded : ∀ original ∈ values, Cap Plain capturedDepth original)
    (selectedDomains : ∀ operand ∈ operands record.paths path, Domain operand values)
    (input : Value Symbol Guard) (available : Available before.checked.native.machine.heap input) (closed : input.free = [])
    (inputDepth : Nat) (inputCap : Cap Plain inputDepth input)
    (nodes : before.checked.native.machine.heap.nodes.next < 2 ^ bits)
    (edges : before.checked.native.machine.heap.edges.next ≤ 2 ^ (bits + 2))
    (room : before.checked.native.machine.domains.next +
      2 ^ (before.checked.native.machine.heap.nodes.next +
        before.checked.native.machine.heap.nodes.next * before.checked.native.machine.heap.nodes.next) < 2 ^ (bits + 1))
    (memos : Memos) (valid : EndpointMemoGateTrace.Valid before.checked.native.machine.heap memos) :
    ∃ result after next final,
      SourceCurrentAllocatedSharedTargetLeaf.Receipt formulas solver next record values base path input
        before result after memos final ∧
      Stored record values after ∧ Cap Plain (leafDepth record path capturedDepth inputDepth) result ∧
      after.targets = before.targets ∧ after.memo = before.memo := by
  have targetFacts := (ready.receipts path target present).available
  have facts := ready.checked.good.native.machine.1
  have targetOriginal := SourceRecursiveIntersectionOriginalOutput.closed_original target _ facts.coherent targetFacts.1 targetFacts.2
  have inputOriginal := SourceRecursiveIntersectionOriginalOutput.closed_original input _ facts.coherent available closed
  have queryRanges := (SourceCurrentAllocatedRecursiveWarmInitialRanges.warm_initial_ranges bits before.checked
    ready.checked.good ready.checked.semantic target input targetOriginal inputOriginal targetFacts.1 available nodes edges room).1
  have ranges : SourceCurrentAllocatedSharedTargetLeaf.Ranges record values path input before := by
    constructor
    · intro absent
      rw [present] at absent
      cases absent
    · intro value middle forced
      cases forced with
      | hit found =>
          have same : target = value := Option.some.inj (present.symm.trans found)
          subst value
          exact queryRanges
      | miss absent _ => rw [present] at absent; cases absent
  obtain ⟨result, after, next, final, receipt⟩ := SourceCurrentAllocatedSharedTargetLeaf.complete formulas solver
    inventory record values base before ready known domains coherent active path member input available closed ranges memos valid
  have produced := leaf_receipt receipt ready known stored capturedDepth bounded selectedDomains available closed inputDepth inputCap
  refine ⟨result, after, next, final, receipt, produced.1, produced.2, ?_, ?_⟩
  · cases receipt.reads with
    | apply first query =>
        cases first.reads with
        | hit => rfl
        | miss absent _ => rw [present] at absent; cases absent
  · cases receipt.reads with
    | apply first query =>
        cases first.reads with
        | hit => rfl
        | miss absent _ => rw [present] at absent; cases absent

end MicroCFTA.MixedSharedIntegration

#print axioms MicroCFTA.MixedSharedIntegration.force_then_another_depth
#check @MicroCFTA.MixedSharedIntegration.force_then_another_depth
#print axioms MicroCFTA.MixedSharedIntegration.warm_leaf_from_entry
#check @MicroCFTA.MixedSharedIntegration.warm_leaf_from_entry
