import MicroCFTA.SourceCurrentAllocatedSharedEditGraph
import MicroCFTA.SourceCurrentAllocatedSharedEditRanges

open MicroCFTA MicroCFTA.InternedConstructorTemplates
open MicroCFTA.SourceCurrentAllocatedSharedEditGraph
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat}

#print axioms children_length
#check children_length
#check NodeReads
#check ChildrenReads
#check RowsReads
#check ListReads
#check SourceCurrentAllocatedSharedEditRanges.NodeRanges
#check SourceCurrentAllocatedSharedEditRanges.ChildrenRanges
#check SourceCurrentAllocatedSharedEditRanges.RowsRanges
#check SourceCurrentAllocatedSharedEditRanges.ListRanges

omit [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] in
/-- Constructor-only advances retain all nonheap native state and class slots. -/
theorem constructor_tables (before : SharedState width) (heap : State Symbol Guard) :
    (advanceHeap before heap).checked.native.nodes = before.checked.native.nodes ∧
    (advanceHeap before heap).checked.native.edges = before.checked.native.edges ∧
    (advanceHeap before heap).checked.native.machine.domains = before.checked.native.machine.domains ∧
    (advanceHeap before heap).checked.operations = before.checked.operations ∧
    (advanceHeap before heap).targets = before.targets ∧
    (advanceHeap before heap).memo = before.memo := ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Actual child traversal justifies the same-arity source setChildren branch. -/
theorem same_arity_rebuild {record originals entries before values middle index inputs}
    (children : EditChildren (width := width) record originals entries index inputs before values middle)
    (symbol : Symbol) (guard : Guard)
    (ready : SourceEqualityRequiredCache.Ready middle.checked.native.machine.heap)
    (available : InternedNestedProvenance.Values middle.checked.native.machine.heap values) :
    let built := run (makeEdge symbol guard values) middle.checked.native.machine.heap
    built.1.children.length = inputs.length := by
  have built := SourceEqualityRequiredCache.edge symbol guard values middle.checked.native.machine.heap ready available
  exact (congrArg List.length built.2.2).trans (children_length children)

/-- Root list callbacks are ignored even when their target has no range plan. -/
theorem root_leaf_is_silent (record : SourceEqualityClassOrder.Record) (originals values : List (Value Symbol Guard))
    (target : EqualityNormalize.Path) (before : SharedState width)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (base : State Symbol Guard) (memos : EndpointMemoGateTrace.Memos) :
    ∃ actual : EditList record originals (.editAt target) values before values before,
      ListReads formulas solver base actual memos memos ∧
      SourceCurrentAllocatedSharedEditRanges.ListRanges record originals (.editAt target) values before :=
  ⟨.leaf, .leaf, trivial⟩

#print axioms constructor_tables
#print axioms same_arity_rebuild
#print axioms root_leaf_is_silent
