import MicroCFTA.SourceCurrentAllocatedSharedEditEffects

open MicroCFTA
open Cache Language InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values Edges)
open SourceEqualityRequiredCache
open SourceEqualityEdits SourceCurrentEditDomains
open SourceEqualitySharedEditEffects (Allowed)
open SourceCurrentAllocatedNativeEffects (physical)
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedSharedEditGraph SourceCurrentAllocatedSharedEditEffects

#print axioms SourceCurrentAllocatedSharedEditEffects.node_physical
#print axioms SourceCurrentAllocatedSharedEditEffects.edge_physical
#print axioms SourceCurrentAllocatedSharedEditEffects.head_physical
#print axioms SourceCurrentAllocatedSharedEditEffects.node_effects
#print axioms SourceCurrentAllocatedSharedEditEffects.children_effects
#print axioms SourceCurrentAllocatedSharedEditEffects.rows_effects
#print axioms SourceCurrentAllocatedSharedEditEffects.list_effects
#check @SourceCurrentAllocatedSharedEditEffects.node_physical
#check @SourceCurrentAllocatedSharedEditEffects.edge_physical
#check @SourceCurrentAllocatedSharedEditEffects.head_physical
#check @SourceCurrentAllocatedSharedEditEffects.node_effects
#check @SourceCurrentAllocatedSharedEditEffects.children_effects
#check @SourceCurrentAllocatedSharedEditEffects.rows_effects
#check @SourceCurrentAllocatedSharedEditEffects.list_effects
#check @SourceCurrentAllocatedSharedEditEffects.ListSafe

local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Heap" => InternedConstructorTemplates.State Symbol Guard
local notation "Ready" => SourceCurrentAllocatedSharedTargetState.Ready
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Valid" => EndpointMemoGateTrace.Valid
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat}
variable {formulas : SourceGuards.Formulas FullSyntax.Formula}
variable {solver : SourceGuards.Entailment FullSyntax.Formula}
variable {inventory : Inventory} {record : SourceEqualityClassOrder.Record}
variable {originals : List (Value Symbol Guard)} {base : Heap} {state : SharedState width}
variable {memos : Memos}

-- Ignored list-root callbacks admit unrelated open child values.
example (path : EqualityNormalize.Path) (values : List (Value Symbol Guard)) :
    ListSafe (.editAt path) values := trivial

-- A nil traversal retains the actual whole checked state and all memo tables.
example (entries : List (Int × Edits EqualityNormalize.Path)) (index : Nat)
    (populated : Populated (.editBelow entries)) (allowed : Allowed record (.editBelow entries))
    (ready : Ready formulas solver inventory record originals base state)
    (valid : Valid state.checked.native.machine.heap memos) :
    ∃ next, ChildrenReceipt formulas solver next record originals base [] state [] state memos memos :=
  children_effects (offset := index) ChildrenReads.nil populated allowed ready
    (by simp [Values]) (by intro query child found value selected; cases selected) valid

-- Empty rows retain their current inventory without new field allocations.
example (entries : List (Int × Edits EqualityNormalize.Path))
    (populated : Populated (.editBelow entries)) (allowed : Allowed record (.editBelow entries))
    (ready : Ready formulas solver inventory record originals base state)
    (valid : Valid state.checked.native.machine.heap memos) :
    ∃ next, RowsReceipt formulas solver next record originals base [] state [] state memos memos :=
  rows_effects (entries := entries) RowsReads.nil populated allowed ready
    (by simp [Edges]) (by intro edge member; cases member) valid

-- A child-list root leaf performs no native query and preserves all positions.
example (path : EqualityNormalize.Path) (values : List (Value Symbol Guard))
    (member : path ∈ record.paths)
    (ready : Ready formulas solver inventory record originals base state)
    (available : Values state.checked.native.machine.heap values)
    (valid : Valid state.checked.native.machine.heap memos) :
    ∃ next, ChildrenReceipt formulas solver next record originals base values state values state memos memos :=
  list_effects (edits := .editAt path) ListReads.leaf (by simp only [Populated]) (by simpa only [Allowed, SourceEqualityEdits.All] using member) ready available (by simp only [ListSafe]) valid

-- Actual row reconstruction requires field residency, not closed children.
example (ready : Ready formulas solver inventory record originals base state)
    (symbol : Symbol) (guard : Guard) (values : List (Value Symbol Guard))
    (field : SourceCurrentConjunctionEquality.FieldAvailable state.checked.operations guard)
    (available : Values state.checked.native.machine.heap values) :
    (run (makeEdge symbol guard values) state.checked.native.machine.heap).1.children = values :=
  (edge_physical ready symbol guard values field available).2.2.2

-- Head reads retain the same equality-operation state.
example (ready : Ready formulas solver inventory record originals base state)
    {input result : Value Symbol Guard} {heap : Heap}
    (actual : SourceEqualityRequiredHead.Head input state.checked.native.machine.heap result heap)
    (available : Available state.checked.native.machine.heap input) :
    SourceCurrentConjunctionRowsAllocation.Effects (physical state.checked)
      (physical (advanceHeap state heap).checked) ∧
      (advanceHeap state heap).checked.operations = state.checked.operations :=
  ⟨(head_physical ready actual available).2.1, rfl⟩

-- Every actual positional edit supplies the same-arity source fast path.
example {entries index values results before after}
    (actual : EditChildren (width := width) record originals entries index values before results after) :
    results.length = values.length := children_length actual

-- Closedness of any transported source path is retained at the exact result.
example {input result : Value Symbol Guard} {before after : SharedState width} {next : Inventory}
    {final : Memos}
    (receipt : NodeReceipt formulas solver next record originals base input before result after memos final)
    (closed : input.free = []) : result.free = [] :=
  by simpa only [SourceEqualityProjectionPathDomain.NodeClosed] using
    receipt.transport [] (by simpa only [SourceEqualityProjectionPathDomain.NodeClosed] using closed)
