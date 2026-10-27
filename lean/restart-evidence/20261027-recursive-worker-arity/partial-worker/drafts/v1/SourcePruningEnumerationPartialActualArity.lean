import MicroCFTA.SourceCurrentAllocatedPartialActual
import MicroCFTA.SourcePruningEnumerationPartialStepArity
import MicroCFTA.SourcePruningEnumerationParentArity
import MicroCFTA.SourcePruningEnumerationRawRebuildArity
import MicroCFTA.SourcePruningEnumerationCallerArity

/-!
# Arity through the eight actual recursive worker families

The induction follows the existing source-aligned read graph.
Existing physical receipts admit each actual next caller and full memos.
The arity proof covers the literal binder and descendant endpoints.
No smaller-call result invariant is supplied as an admission.
-/
namespace MicroCFTA.SourcePruningEnumerationPartialActualArity
open Cache Language InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values Edges)
open SourceCurrentAllocatedPartialState SourceCurrentAllocatedPartialGraph
open SourceCurrentAllocatedPartialInvariant (Context Post)
open SourceCurrentAllocatedPartialChecks
open SourceCurrentAllocatedPartialSourceReads
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedNativeEffects (physical)
open SourcePruningEnumerationArityOrigins (Heap)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Node" => Value Symbol Guard
local notation "Edge" => EdgeValue Symbol Guard
local notation "EqValue" => SourceEqualityConstraintAllocation.Value
local notation "EqReady" => SourceEqualityConstraintAllocation.Ready
local notation "Resident" => InternedEdgeResidency.EdgeResident
local notation "Memos" => EndpointMemoGateTrace.Memos
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Node] {width budget : Nat}
variable (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)

private def NodeClaim (top : Trace width budget) (request : NodeRequest) (before : Caller width)
    (_result : Node) (after : Caller width) (memos : Memos) (_final : Memos) : Prop :=
  ∀ inventory, Checks top → Context formulas solver inventory before memos →
    EqReady before.checked.operations.constraints request.inherited → Available before.checked.native.machine.heap request.value →
    Heap before.checked.native.machine.heap → Heap after.checked.native.machine.heap

private def EdgeClaim (top : Trace width budget) (request : EdgeRequest) (before : Caller width)
    (_result : Edge) (after : Caller width) (memos : Memos) (_final : Memos) : Prop :=
  ∀ inventory, Checks top → Context formulas solver inventory before memos →
    EqReady before.checked.operations.constraints request.inherited → Resident before.checked.native.machine.heap request.value →
    Heap before.checked.native.machine.heap → Heap after.checked.native.machine.heap

private def RowsClaim {inherited : EqValue} {values results : List Edge} {before after : Caller width}
    (actual : Rows budget inherited values before results after) (memos : Memos) (_final : Memos) : Prop :=
  ∀ inventory, Checks (rowsTrace actual) → Context formulas solver inventory before memos →
    EqReady before.checked.operations.constraints inherited → Edges before.checked.native.machine.heap values →
    Heap before.checked.native.machine.heap → Heap after.checked.native.machine.heap

private def DescendantsClaim {inherited : EqValue} {value result : Edge} {before after : Caller width}
    (actual : Descendants budget inherited value before result after) (memos final : Memos) : Prop :=
  EdgeClaim formulas solver (descendantsTrace actual) ⟨inherited, value⟩ before result after memos final

private def ChildrenClaim {combined : EqValue} {values results : List Node} {before after : Caller width}
    (actual : Children budget combined values before results after) (memos : Memos) (_final : Memos) : Prop :=
  ∀ inventory, Checks (childrenTrace actual) → Context formulas solver inventory before memos →
    EqReady before.checked.operations.constraints combined → Values before.checked.native.machine.heap values →
    Heap before.checked.native.machine.heap → Heap after.checked.native.machine.heap

private def WalkClaim {combined : EqValue} {index : Nat} {values results : List Node} {before after : Caller width}
    (actual : Walk budget combined index values before results after) (memos : Memos) (_final : Memos) : Prop :=
  ∀ inventory, Checks (walkTrace actual) → Context formulas solver inventory before memos →
    EqReady before.checked.operations.constraints combined → Values before.checked.native.machine.heap values →
    Heap before.checked.native.machine.heap → Heap after.checked.native.machine.heap

omit [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Node] in
private theorem values_grow {before after : Caller width} {values : List Node}
    (effects : SourceCurrentConjunctionRowsAllocation.Effects (physical before.checked) (physical after.checked))
    (available : Values before.checked.native.machine.heap values) : Values after.checked.native.machine.heap values :=
  fun value member => effects.keeps.available value (available value member)

omit [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Node] in
private theorem edges_grow {before after : Caller width} {values : List Edge}
    (effects : SourceCurrentConjunctionRowsAllocation.Effects (physical before.checked) (physical after.checked))
    (resident : Edges before.checked.native.machine.heap values) : Edges after.checked.native.machine.heap values :=
  fun edge member => InternedEdgeResidency.edge_grows _ _ effects.keeps.growth edge (resident edge member)

-- Each family uses the same eight actual source-read induction motives.
local macro "arity_induction" recursor:ident reads:ident formulas:ident solver:ident : tactic => `(tactic|
  (apply $recursor
    (motive_1 := fun {budget request before result after} actual memos final _ =>
      NodeClaim $formulas $solver (nodeCallTrace actual) request before result after memos final)
    (motive_2 := fun {budget request before result after} actual memos final _ =>
      NodeClaim $formulas $solver (nodeBodyTrace actual) request before result after memos final)
    (motive_3 := fun {budget request before result after} actual memos final _ =>
      EdgeClaim $formulas $solver (edgeCallTrace actual) request before result after memos final)
    (motive_4 := fun {budget request before result after} actual memos final _ =>
      EdgeClaim $formulas $solver (edgeBodyTrace actual) request before result after memos final)
    (motive_5 := fun {_budget _inherited _values _before _results _after} actual memos final _ =>
      RowsClaim $formulas $solver actual memos final)
    (motive_6 := fun {_budget _inherited _value _before _result _after} actual memos final _ =>
      DescendantsClaim $formulas $solver actual memos final)
    (motive_7 := fun {_budget _combined _values _before _results _after} actual memos final _ =>
      ChildrenClaim $formulas $solver actual memos final)
    (motive_8 := fun {_budget _combined _index _values _before _results _after} actual memos final _ =>
      WalkClaim $formulas $solver actual memos final)
    (t := $reads)
   · intro budget request before handle result after started memos inventory _checks _initial _inherited _available heap
     simpa only [started] using SourcePruningEnumerationCallerArity.beginNode_heap request before heap
   · intro budget original running result middle body memos final request before handle started bodyReads ih
     intro inventory checks initial inherited available heap
     obtain ⟨runningContext, owner, _, _⟩ := SourceCurrentAllocatedPartialCallSteps.node_start $formulas $solver
       initial inherited available started
     have runningHeap : Heap running.checked.native.machine.heap := by
       simpa only [started] using SourcePruningEnumerationCallerArity.beginNode_heap request before heap
     have middleHeap := ih inventory (checks.restrict (.node_evaluate started body))
       runningContext owner.inherited owner.input runningHeap
     exact SourcePruningEnumerationCallerArity.finishNode_heap handle result middle middleHeap
   · intro budget inherited before memos inventory _checks _initial _inherited _available heap
     exact heap
   · intro budget inherited entry members depth free before memos inventory _checks _initial _inherited _available heap
     exact heap
   · intro budget inherited entry body depth ordinary before result heap actual memos inventory _checks initial _inherited available arity
     have returnedHeap := SourcePruningEnumerationPartialStepArity.binder_heap initial.ready initial.probes available actual arity
     exact returnedHeap
   · intro entry depth free budget inherited edges before results middle rows memos final rowsReads ih
     intro inventory checks initial inheritedReady available heap
     have resident := InternedEdgeResidency.resident_edges _ initial.ready.semantic.ready.semantic.1.normal.facts.linked _ available.resident
     have middleHeap := ih inventory (checks.restrict (.node_ordinary rows)) initial inheritedReady resident heap
     exact SourcePruningEnumerationRawRebuildArity.modify_heap (.node entry edges depth free) edges results middle.checked middleHeap
   · intro budget request before handle result after started memos inventory _checks _initial _inherited _resident heap
     simpa only [started] using SourcePruningEnumerationCallerArity.beginEdge_heap request before heap
   · intro budget original running result middle body memos final request before handle started bodyReads ih
     intro inventory checks initial inherited resident heap
     obtain ⟨runningContext, owner, _, _⟩ := SourceCurrentAllocatedPartialCallSteps.edge_start $formulas $solver
       initial inherited resident started
     have runningHeap : Heap running.checked.native.machine.heap := by
       simpa only [started] using SourcePruningEnumerationCallerArity.beginEdge_heap request before heap
     have middleHeap := ih inventory (checks.restrict (.edge_evaluate started body))
       runningContext owner.inherited owner.input runningHeap
     exact SourcePruningEnumerationCallerArity.finishEdge_heap handle result middle middleHeap
   · intro budget edge loaded inherited before result checked fourth merge actual memos final field parentReads
     intro inventory checks initial inheritedReady resident heap
     have live : SourceEqualityMkEdgeAllocation.contradictory edge.entry.key.constraint = false →
         SourceEqualityGuardReadback.Cached edge.entry.key.constraint.equalities ∧
         SourceEqualityConstraintFieldLookup.load edge.entry.key.constraint before.checked.operations.constraints = .ok (some loaded) ∧
         EqReady before.checked.operations.constraints inherited ∧
         Values before.checked.native.machine.heap edge.children ∧
         SourceCurrentAllocatedLocalReductionActual.Ranges budget loaded inherited edge.children before.checked before.fourth := by
       intro test
       exact ⟨(initial.ready.good.fields edge.entry.key edge resident).1, field test, inheritedReady,
         initial.ready.semantic.ready.semantic.1.normal.facts.cached.edges _ edge resident,
         checks.edge_body test loaded (field test)⟩
     exact SourcePruningEnumerationParentArity.parent_heap $formulas $solver inventory parentReads
       initial.ready initial.admitted live initial.correct initial.stored initial.covered initial.globals heap
   · intro budget inherited before memos inventory _checks _initial _inherited _resident heap
     exact heap
   · intro budget inherited original before narrowed middle first memos edgeMemos result afterChildren child childMemos
     intro originals results after tail final edgeReads childrenReads tailReads ihEdge ihChildren ihTail
     intro inventory checks initial inheritedReady resident heap
     have edgeChecks := checks.restrict (.rows_edge first child tail)
     obtain ⟨edgeInventory, edgePost, narrowedResident, _⟩ := SourceCurrentAllocatedPartialActual.edge_call
       $formulas $solver edgeReads inventory edgeChecks initial inheritedReady (resident original List.mem_cons_self)
     have middleHeap := ihEdge inventory edgeChecks initial inheritedReady (resident original List.mem_cons_self) heap
     have childChecks := checks.restrict (.rows_descendants first child tail)
     have inheritedMiddle := inheritedReady.grows edgePost.effects.grows.constraint_growth
     obtain ⟨childInventory, childPost, _resultResident, _⟩ := SourceCurrentAllocatedPartialActual.descendants
       $formulas $solver childrenReads edgeInventory childChecks edgePost.context inheritedMiddle narrowedResident
     have childHeap := ihChildren edgeInventory childChecks edgePost.context inheritedMiddle narrowedResident middleHeap
     have firstPost := edgePost.trans childPost
     exact ihTail childInventory (checks.restrict (.rows_tail first child tail)) childPost.context
       (inheritedReady.grows firstPost.effects.grows.constraint_growth)
       (edges_grow firstPost.effects (fun edge member => resident edge (List.mem_cons_of_mem _ member))) childHeap
   · intro budget payload edge before inherited results middle children memos final combined childReads ih
     intro inventory checks initial inheritedReady resident heap
     obtain ⟨prefixReceipt, prefixPost⟩ := SourceCurrentAllocatedPartialStepEffects.inherited_prefix $formulas $solver
       inventory before memos initial edge inherited payload resident inheritedReady combined
     have inputs := initial.ready.semantic.ready.semantic.1.normal.facts.cached.edges edge.entry.key edge resident
     have childChecks := checks.restrict (.descendants_children combined children)
     have childInputs := values_grow prefixPost.effects inputs
     obtain ⟨next, childPost, _available, _⟩ := SourceCurrentAllocatedPartialActual.children $formulas $solver childReads
       inventory childChecks prefixPost.context prefixReceipt.combinedReady childInputs
     have prefixHeap := SourcePruningEnumerationPartialStepArity.prefix_heap before edge inherited heap
     have middleHeap := ih inventory childChecks prefixPost.context prefixReceipt.combinedReady childInputs prefixHeap
     have firstPost := prefixPost.trans childPost
     exact SourcePruningEnumerationRawRebuildArity.edge_heap edge results middle.checked middleHeap
       childPost.context.ready.semantic.ready.semantic.1.normal.facts.coherent
       (InternedEdgeResidency.edge_grows _ _ firstPost.effects.keeps.growth _ resident) children.length
   · intro budget values before memos inventory _checks _initial _inherited _available heap
     exact heap
   · intro budget identity records values before results after actual memos final walkReads ih
     intro inventory checks initial inherited available heap
     exact ih inventory (checks.restrict (.children_walk actual)) initial inherited available heap
   · intro budget combined index before memos inventory _checks _initial _inherited _available heap
     exact heap
   · intro budget before combined index value result middle first memos headMemos values results after tail final headReads tailReads ihHead ihTail
     intro inventory checks initial inherited available heap
     obtain ⟨descentReceipt, descentPost⟩ := SourceCurrentAllocatedPartialStepEffects.descent $formulas $solver
       inventory before memos initial combined index inherited
     have headChecks := checks.restrict (.walk_head first tail)
     have headInput := descentPost.effects.keeps.available _ (available value List.mem_cons_self)
     obtain ⟨headInventory, headPost, _resultAvailable, _⟩ := SourceCurrentAllocatedPartialActual.node_call $formulas $solver headReads
       inventory headChecks descentPost.context descentReceipt.inherited headInput
     have descentHeap := SourcePruningEnumerationPartialStepArity.descent_heap before combined index heap
     have middleHeap := ihHead inventory headChecks descentPost.context descentReceipt.inherited headInput descentHeap
     have firstPost := descentPost.trans headPost
     exact ihTail headInventory (checks.restrict (.walk_tail first tail)) headPost.context
       (inherited.grows firstPost.effects.grows.constraint_growth)
       (values_grow firstPost.effects (fun child member => available child (List.mem_cons_of_mem _ member))) middleHeap))

/-- An actual completed node call retains arity at its literal full caller. -/
theorem node_call {request : NodeRequest} {before after : Caller width} {result : Node}
    {actual : NodeCall budget request before result after} {memos final : Memos}
    (reads : NodeCallReads formulas solver actual memos final) :
    ∀ inventory, Checks (nodeCallTrace actual) → Context formulas solver inventory before memos →
      EqReady before.checked.operations.constraints request.inherited → Available before.checked.native.machine.heap request.value →
      Heap before.checked.native.machine.heap → Heap after.checked.native.machine.heap := by
  change NodeClaim formulas solver (nodeCallTrace actual) request before result after memos final
  arity_induction NodeCallReads.rec reads formulas solver

/-- Actual node bodies retain arity through their own ordered smaller calls. -/
theorem node_body {request : NodeRequest} {before after : Caller width} {result : Node}
    {actual : NodeBody budget request before result after} {memos final : Memos}
    (reads : NodeBodyReads formulas solver actual memos final) :
    ∀ inventory, Checks (nodeBodyTrace actual) → Context formulas solver inventory before memos →
      EqReady before.checked.operations.constraints request.inherited → Available before.checked.native.machine.heap request.value →
      Heap before.checked.native.machine.heap → Heap after.checked.native.machine.heap := by
  change NodeClaim formulas solver (nodeBodyTrace actual) request before result after memos final
  arity_induction NodeBodyReads.rec reads formulas solver

/-- Edge calls retain arity across their actual owner publication and completion. -/
theorem edge_call {request : EdgeRequest} {before after : Caller width} {result : Edge}
    {actual : EdgeCall budget request before result after} {memos final : Memos}
    (reads : EdgeCallReads formulas solver actual memos final) :
    ∀ inventory, Checks (edgeCallTrace actual) → Context formulas solver inventory before memos →
      EqReady before.checked.operations.constraints request.inherited → Resident before.checked.native.machine.heap request.value →
      Heap before.checked.native.machine.heap → Heap after.checked.native.machine.heap := by
  change EdgeClaim formulas solver (edgeCallTrace actual) request before result after memos final
  arity_induction EdgeCallReads.rec reads formulas solver

/-- An actual parent body derives arity from its reached checked-constructor reads. -/
theorem edge_body {request : EdgeRequest} {before after : Caller width} {result : Edge}
    {actual : EdgeBody budget request before result after} {memos final : Memos}
    (reads : EdgeBodyReads formulas solver actual memos final) :
    ∀ inventory, Checks (edgeBodyTrace actual) → Context formulas solver inventory before memos →
      EqReady before.checked.operations.constraints request.inherited → Resident before.checked.native.machine.heap request.value →
      Heap before.checked.native.machine.heap → Heap after.checked.native.machine.heap := by
  change EdgeClaim formulas solver (edgeBodyTrace actual) request before result after memos final
  arity_induction EdgeBodyReads.rec reads formulas solver

/-- Rows pass the actual parent and descendant caller to their remaining suffix. -/
theorem rows {inherited : EqValue} {values results : List Edge} {before after : Caller width}
    {actual : Rows budget inherited values before results after} {memos final : Memos}
    (reads : RowsReads formulas solver actual memos final) :
    ∀ inventory, Checks (rowsTrace actual) → Context formulas solver inventory before memos →
      EqReady before.checked.operations.constraints inherited → Edges before.checked.native.machine.heap values →
      Heap before.checked.native.machine.heap → Heap after.checked.native.machine.heap := by
  change RowsClaim formulas solver actual memos final
  arity_induction RowsReads.rec reads formulas solver

/-- Descendants use their actual inherited prefix, child count and raw reconstruction. -/
theorem descendants {inherited : EqValue} {value result : Edge} {before after : Caller width}
    {actual : Descendants budget inherited value before result after} {memos final : Memos}
    (reads : DescendantsReads formulas solver actual memos final) :
    ∀ inventory, Checks (descendantsTrace actual) → Context formulas solver inventory before memos →
      EqReady before.checked.operations.constraints inherited → Resident before.checked.native.machine.heap value →
      Heap before.checked.native.machine.heap → Heap after.checked.native.machine.heap := by
  change DescendantsClaim formulas solver actual memos final
  arity_induction DescendantsReads.rec reads formulas solver

/-- Contradiction and live child branches retain the entire actual native arity heap. -/
theorem children {combined : EqValue} {values results : List Node} {before after : Caller width}
    {actual : Children budget combined values before results after} {memos final : Memos}
    (reads : ChildrenReads formulas solver actual memos final) :
    ∀ inventory, Checks (childrenTrace actual) → Context formulas solver inventory before memos →
      EqReady before.checked.operations.constraints combined → Values before.checked.native.machine.heap values →
      Heap before.checked.native.machine.heap → Heap after.checked.native.machine.heap := by
  change ChildrenClaim formulas solver actual memos final
  arity_induction ChildrenReads.rec reads formulas solver

/-- An indexed walk retains arity through the actual descended head and tail. -/
theorem walk {combined : EqValue} {index : Nat} {values results : List Node} {before after : Caller width}
    {actual : Walk budget combined index values before results after} {memos final : Memos}
    (reads : WalkReads formulas solver actual memos final) :
    ∀ inventory, Checks (walkTrace actual) → Context formulas solver inventory before memos →
      EqReady before.checked.operations.constraints combined → Values before.checked.native.machine.heap values →
      Heap before.checked.native.machine.heap → Heap after.checked.native.machine.heap := by
  change WalkClaim formulas solver actual memos final
  arity_induction WalkReads.rec reads formulas solver

end MicroCFTA.SourcePruningEnumerationPartialActualArity
