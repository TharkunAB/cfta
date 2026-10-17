import MicroCFTA.SourceCurrentAllocatedPartialConditionalParentShape
import MicroCFTA.SourceCurrentAllocatedPartialActual

/-!
# Conditional edge certificates through completed mixed outer calls

The induction follows the actual source-read graph and its exact states.
Only empty-own parent results need a shape certificate. Other constrained
results remain unrestricted. No Region condition is required. These
preservation laws do not assert general outer termination.
-/
namespace MicroCFTA.SourceCurrentAllocatedPartialConditionalStoreTrace
open Cache InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values Edges)
open SourceCurrentAllocatedPartialState SourceCurrentAllocatedPartialGraph
open SourceCurrentAllocatedPartialSourceReads SourceCurrentAllocatedPartialChecks
open SourceCurrentAllocatedPartialInvariant (Context)
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedPartialConditionalDomain (Stored)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "Edge" => EdgeValue Symbol Guard
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "EqValue" => SourceEqualityConstraintAllocation.Value
local notation "EqReady" => SourceEqualityConstraintAllocation.Ready
local notation "Memos" => EndpointMemoGateTrace.Memos
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Node] {width budget : Nat}

private def NodeStore (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (top : Trace width budget)
    (request : NodeRequest) (before after : Caller width) (memos : Memos) : Prop :=
  ∀ inventory, Checks top → Context formulas solver inventory before memos →
    EqReady before.checked.operations.constraints request.inherited →
    Available before.checked.native.machine.heap request.value → Stored before → Stored after

private def EdgeStore (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (top : Trace width budget)
    (request : EdgeRequest) (before after : Caller width) (memos : Memos) : Prop :=
  ∀ inventory, Checks top → Context formulas solver inventory before memos →
    EqReady before.checked.operations.constraints request.inherited →
    InternedEdgeResidency.EdgeResident before.checked.native.machine.heap request.value → Stored before → Stored after

private def RowsStore (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (top : Trace width budget)
    (inherited : EqValue) (values : List Edge) (before after : Caller width) (memos : Memos) : Prop :=
  ∀ inventory, Checks top → Context formulas solver inventory before memos →
    EqReady before.checked.operations.constraints inherited →
    Edges before.checked.native.machine.heap values → Stored before → Stored after

private def ChildrenStore (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (top : Trace width budget)
    (combined : EqValue) (values : List Node) (before after : Caller width) (memos : Memos) : Prop :=
  ∀ inventory, Checks top → Context formulas solver inventory before memos →
    EqReady before.checked.operations.constraints combined →
    Values before.checked.native.machine.heap values → Stored before → Stored after

local macro "store_induction" recursor:ident reads:ident formulas:ident solver:ident : tactic => `(tactic|
  (apply $recursor
    (motive_1 := fun {budget request before _result after} actual memos _final _ =>
      NodeStore $formulas $solver (nodeCallTrace actual) request before after memos)
    (motive_2 := fun {budget request before _result after} actual memos _final _ =>
      NodeStore $formulas $solver (nodeBodyTrace actual) request before after memos)
    (motive_3 := fun {budget request before _result after} actual memos _final _ =>
      EdgeStore $formulas $solver (edgeCallTrace actual) request before after memos)
    (motive_4 := fun {budget request before _result after} actual memos _final _ =>
      EdgeStore $formulas $solver (edgeBodyTrace actual) request before after memos)
    (motive_5 := fun {_budget inherited values before _results after} actual memos _final _ =>
      RowsStore $formulas $solver (rowsTrace actual) inherited values before after memos)
    (motive_6 := fun {_budget inherited value before _result after} actual memos _final _ =>
      EdgeStore $formulas $solver (descendantsTrace actual) ⟨inherited, value⟩ before after memos)
    (motive_7 := fun {_budget combined values before _results after} actual memos _final _ =>
      ChildrenStore $formulas $solver (childrenTrace actual) combined values before after memos)
    (motive_8 := fun {_budget combined _index values before _results after} actual memos _final _ =>
      ChildrenStore $formulas $solver (walkTrace actual) combined values before after memos)
    (t := $reads)
   · intro _budget request before _handle _result _after started _memos _inventory _checks _initial _inherited _available stored
     simpa only [started] using stored.beginNode request
   · intro _budget original running _result _middle _body _memos _final request before _handle started _bodyReads ih
     intro inventory checks initial inherited available stored
     obtain ⟨current, owner, _, _⟩ := SourceCurrentAllocatedPartialCallSteps.node_start $formulas $solver
       initial inherited available started
     have runningStored : Stored running := by simpa only [started] using stored.beginNode request
     exact (ih inventory (checks.restrict (.node_evaluate started _)) current owner.inherited owner.input runningStored).finishNode _ _
   · intro _budget _inherited _before _memos _inventory _checks _initial _ready _available stored
     exact stored
   · intro _budget _inherited _entry _members _depth _free _before _memos _inventory _checks _initial _ready _available stored
     exact stored
   · intro _budget _inherited _entry _body _depth _ordinary _before _result _heap _actual _memos _inventory _checks _initial _ready _available stored
     exact stored.advance _ _ _
   · intro _entry _depth _free _budget _inherited _edges _before _results _middle rows _memos _final _rowsReads ih
     intro inventory checks initial inherited available stored
     have resident := InternedEdgeResidency.resident_edges _ initial.ready.semantic.ready.semantic.1.normal.facts.linked _ available.resident
     exact (ih inventory (checks.restrict (.node_ordinary rows)) initial inherited resident stored).advance _ _ _
   · intro _budget request _before _handle _result _after started _memos _inventory _checks _initial _inherited _resident stored
     simpa only [started] using stored.beginEdge request
   · intro _budget original running result middle body _memos _final request _before handle started _bodyReads _ih
     intro _inventory _checks initial inherited resident stored
     obtain ⟨current, owner, _, cell⟩ := SourceCurrentAllocatedPartialCallSteps.edge_start $formulas $solver
       initial inherited resident started
     have runningStored : Stored running := by simpa only [started] using stored.beginEdge request
     have middleStored := SourceCurrentAllocatedPartialConditionalParentShape.stored body runningStored
     have frame := SourceCurrentAllocatedPartialFrames.edge_body body
       (SourceCurrentAllocatedPartialFrames.Protocol.of_valid current.sound.valid)
     exact middleStored.finishEdge result (frame.edge_running handle original cell)
       (fun own => SourceCurrentAllocatedPartialConditionalParentShape.shape $formulas $solver body current owner.inherited owner.input own)
   · intro _budget _edge _loaded _inherited _before _result _checked _fourth _merge _actual _memos _final _field _parentReads
     intro _inventory _checks _initial _ready _resident stored
     exact stored.advance _ _ _
   · intro _budget _inherited _before _memos _inventory _checks _initial _ready _resident stored
     exact stored
   · intro _budget inherited original before _narrowed _middle first memos _edgeMemos _result _afterChildren child _childMemos
     intro _originals _results _after tail _final edgeReads childrenReads _tailReads ihEdge ihChildren ihTail
     intro inventory checks initial inheritedReady resident stored
     have edgeChecks := checks.restrict (.rows_edge first child tail)
     have edgeStored := ihEdge inventory edgeChecks initial inheritedReady (resident original List.mem_cons_self) stored
     obtain ⟨edgeInventory, edgePost, narrowedResident, _edgeLaw⟩ := SourceCurrentAllocatedPartialActual.edge_call $formulas $solver
       edgeReads inventory edgeChecks initial inheritedReady (resident original List.mem_cons_self)
     have childChecks := checks.restrict (.rows_descendants first child tail)
     have childReady := inheritedReady.grows edgePost.effects.grows.constraint_growth
     have childStored := ihChildren edgeInventory childChecks edgePost.context childReady narrowedResident edgeStored
     obtain ⟨childInventory, childPost, _resultResident, _childLaw⟩ := SourceCurrentAllocatedPartialActual.descendants $formulas $solver
       childrenReads edgeInventory childChecks edgePost.context childReady narrowedResident
     have firstPost := edgePost.trans childPost
     exact ihTail childInventory (checks.restrict (.rows_tail first child tail)) childPost.context
       (inheritedReady.grows firstPost.effects.grows.constraint_growth)
       (fun edge member => InternedEdgeResidency.edge_grows _ _ firstPost.effects.keeps.growth edge
         (resident edge (List.mem_cons_of_mem _ member))) childStored
   · intro _budget payload edge before inherited _results _middle children memos _final combined _childReads ih
     intro inventory checks initial inheritedReady resident stored
     obtain ⟨prefixReceipt, prefixPost⟩ := SourceCurrentAllocatedPartialStepEffects.inherited_prefix $formulas $solver
       inventory before memos initial edge inherited payload resident inheritedReady combined
     have inputs := initial.ready.semantic.ready.semantic.1.normal.facts.cached.edges edge.entry.key edge resident
     have current := ih inventory (checks.restrict (.descendants_children combined children)) prefixPost.context prefixReceipt.combinedReady
       (fun value member => prefixPost.effects.keeps.available value (inputs value member)) stored
     exact current.advance _ _ _
   · intro _budget _values _before _memos _inventory _checks _initial _inherited _available stored
     exact stored
   · intro _budget _identity _records _values _before _results _after actual _memos _final _walkReads ih
     intro inventory checks initial inherited available stored
     exact ih inventory (checks.restrict (.children_walk actual)) initial inherited available stored
   · intro _budget _combined _index _before _memos _inventory _checks _initial _inherited _available stored
     exact stored
   · intro _budget before combined index value _result _middle first memos _headMemos _values _results _after tail _final headReads _tailReads ihHead ihTail
     intro inventory checks initial inherited available stored
     obtain ⟨descentReceipt, descentPost⟩ := SourceCurrentAllocatedPartialStepEffects.descent $formulas $solver
       inventory before memos initial combined index inherited
     have headChecks := checks.restrict (.walk_head first tail)
     have headInput := descentPost.effects.keeps.available _ (available value List.mem_cons_self)
     have headStored := ihHead inventory headChecks descentPost.context descentReceipt.inherited headInput stored
     obtain ⟨headInventory, headPost, _resultAvailable, _headLaw⟩ := SourceCurrentAllocatedPartialActual.node_call $formulas $solver
       headReads inventory headChecks descentPost.context descentReceipt.inherited headInput
     have firstPost := descentPost.trans headPost
     exact ihTail headInventory (checks.restrict (.walk_tail first tail)) headPost.context
       (inherited.grows firstPost.effects.grows.constraint_growth)
       (fun child member => firstPost.effects.keeps.available child (available child (List.mem_cons_of_mem _ member))) headStored))

/-- The actual completed node call retains conditional certificates in mixed tables. -/
theorem node_call (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    {inventory : Inventory} {request : NodeRequest} {before after : Caller width} {result : Node}
    {actual : NodeCall budget request before result after} {memos final : Memos}
    (reads : NodeCallReads formulas solver actual memos final) (checks : Checks (nodeCallTrace actual))
    (initial : Context formulas solver inventory before memos)
    (inherited : EqReady before.checked.operations.constraints request.inherited)
    (input : Available before.checked.native.machine.heap request.value) (stored : Stored before) : Stored after := by
  have claim : NodeStore formulas solver (nodeCallTrace actual) request before after memos := by
    store_induction NodeCallReads.rec reads formulas solver
  exact claim inventory checks initial inherited input stored

/-- The actual completed node body retains conditional certificates in mixed tables. -/
theorem node_body (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    {inventory : Inventory} {request : NodeRequest} {before after : Caller width} {result : Node}
    {actual : NodeBody budget request before result after} {memos final : Memos}
    (reads : NodeBodyReads formulas solver actual memos final) (checks : Checks (nodeBodyTrace actual))
    (initial : Context formulas solver inventory before memos)
    (inherited : EqReady before.checked.operations.constraints request.inherited)
    (input : Available before.checked.native.machine.heap request.value) (stored : Stored before) : Stored after := by
  have claim : NodeStore formulas solver (nodeBodyTrace actual) request before after memos := by
    store_induction NodeBodyReads.rec reads formulas solver
  exact claim inventory checks initial inherited input stored

/-- The actual completed edge call retains conditional certificates in mixed tables. -/
theorem edge_call (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    {inventory : Inventory} {request : EdgeRequest} {before after : Caller width} {result : Edge}
    {actual : EdgeCall budget request before result after} {memos final : Memos}
    (reads : EdgeCallReads formulas solver actual memos final) (checks : Checks (edgeCallTrace actual))
    (initial : Context formulas solver inventory before memos)
    (inherited : EqReady before.checked.operations.constraints request.inherited)
    (input : InternedEdgeResidency.EdgeResident before.checked.native.machine.heap request.value) (stored : Stored before) : Stored after := by
  have claim : EdgeStore formulas solver (edgeCallTrace actual) request before after memos := by
    store_induction EdgeCallReads.rec reads formulas solver
  exact claim inventory checks initial inherited input stored

/-- The actual completed edge body retains conditional certificates in mixed tables. -/
theorem edge_body (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    {inventory : Inventory} {request : EdgeRequest} {before after : Caller width} {result : Edge}
    {actual : EdgeBody budget request before result after} {memos final : Memos}
    (reads : EdgeBodyReads formulas solver actual memos final) (checks : Checks (edgeBodyTrace actual))
    (initial : Context formulas solver inventory before memos)
    (inherited : EqReady before.checked.operations.constraints request.inherited)
    (input : InternedEdgeResidency.EdgeResident before.checked.native.machine.heap request.value) (stored : Stored before) : Stored after := by
  have claim : EdgeStore formulas solver (edgeBodyTrace actual) request before after memos := by
    store_induction EdgeBodyReads.rec reads formulas solver
  exact claim inventory checks initial inherited input stored

/-- The actual completed rows retain every conditional returned-owner certificate. -/
theorem rows (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    {inventory : Inventory} {inherited : EqValue} {values results : List Edge} {before after : Caller width}
    {actual : Rows budget inherited values before results after} {memos final : Memos}
    (reads : RowsReads formulas solver actual memos final) (checks : Checks (rowsTrace actual))
    (initial : Context formulas solver inventory before memos)
    (ready : EqReady before.checked.operations.constraints inherited)
    (input : Edges before.checked.native.machine.heap values) (stored : Stored before) : Stored after := by
  have claim : RowsStore formulas solver (rowsTrace actual) inherited values before after memos := by
    store_induction RowsReads.rec reads formulas solver
  exact claim inventory checks initial ready input stored

/-- The actual completed children retain every conditional returned-owner certificate. -/
theorem children (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    {inventory : Inventory} {inherited : EqValue} {values results : List Node} {before after : Caller width}
    {actual : Children budget inherited values before results after} {memos final : Memos}
    (reads : ChildrenReads formulas solver actual memos final) (checks : Checks (childrenTrace actual))
    (initial : Context formulas solver inventory before memos)
    (ready : EqReady before.checked.operations.constraints inherited)
    (input : Values before.checked.native.machine.heap values) (stored : Stored before) : Stored after := by
  have claim : ChildrenStore formulas solver (childrenTrace actual) inherited values before after memos := by
    store_induction ChildrenReads.rec reads formulas solver
  exact claim inventory checks initial ready input stored

/-- The actual completed walk retain every conditional returned-owner certificate. -/
theorem walk (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    {inventory : Inventory} {inherited : EqValue} {index : Nat} {values results : List Node} {before after : Caller width}
    {actual : Walk budget inherited index values before results after} {memos final : Memos}
    (reads : WalkReads formulas solver actual memos final) (checks : Checks (walkTrace actual))
    (initial : Context formulas solver inventory before memos)
    (ready : EqReady before.checked.operations.constraints inherited)
    (input : Values before.checked.native.machine.heap values) (stored : Stored before) : Stored after := by
  have claim : ChildrenStore formulas solver (walkTrace actual) inherited values before after memos := by
    store_induction WalkReads.rec reads formulas solver
  exact claim inventory checks initial ready input stored

/-- Actual returned-edge descendants retain conditional certificates through their inherited prefix. -/
theorem descendants (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    {inventory : Inventory} {inherited : EqValue} {value result : Edge} {before after : Caller width}
    {actual : Descendants budget inherited value before result after} {memos final : Memos}
    (reads : DescendantsReads formulas solver actual memos final) (checks : Checks (descendantsTrace actual))
    (initial : Context formulas solver inventory before memos)
    (ready : EqReady before.checked.operations.constraints inherited)
    (input : InternedEdgeResidency.EdgeResident before.checked.native.machine.heap value) (stored : Stored before) : Stored after := by
  have claim : EdgeStore formulas solver (descendantsTrace actual) ⟨inherited, value⟩ before after memos := by
    store_induction DescendantsReads.rec reads formulas solver
  exact claim inventory checks initial ready input stored

end MicroCFTA.SourceCurrentAllocatedPartialConditionalStoreTrace
