import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryOuterProfiles
import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryGuardParent
import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryParentProfiles
import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryOuterVerification
import MicroCFTA.SourceCurrentAllocatedPartialInitialization
import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryOutputStored
import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryMergeProfileCache
import MicroCFTA.SourceCurrentAllocatedPartialActual

/-!
# Universal lower guard stores through all actual outer families

The induction follows the same strict actual read graphs in source order.
Each reached parent derives its own guard vector from the resident domain.
Its actual producer retains both universal lower guard tables.
The complete earlier strong profile store and narrowing law remain present.
Public endpoints derive their own reached checks. They assert no graph
existence or quantitative hereditary law for outer returned cells.
-/
namespace MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryOuterGuardStores
open Cache Language InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values Edges)
open SourceCurrentAllocatedPartialState SourceCurrentAllocatedPartialGraph
open SourceCurrentAllocatedPartialInvariant (Context)
open SourceCurrentAllocatedPartialChecks SourceCurrentAllocatedPartialSourceReads
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedNativeEffects (physical)
open SourceCurrentAllocatedFiniteOrdinaryRequired (NodeNarrow EdgeNarrow)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Node" => Value Symbol Guard
local notation "Edge" => EdgeValue Symbol Guard
local notation "EqValue" => SourceEqualityConstraintAllocation.Value
local notation "EqReady" => SourceEqualityConstraintAllocation.Ready
local notation "Resident" => InternedEdgeResidency.EdgeResident
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "DNode" => SourceCurrentAllocatedFiniteOrdinaryDomain.Node
local notation "DEdge" => SourceCurrentAllocatedFiniteOrdinaryDomain.Edge
local notation "DRows" => SourceCurrentAllocatedFiniteOrdinaryDomain.Rows
local notation "DChildren" => SourceCurrentAllocatedFiniteOrdinaryDomain.Children
variable {width budget : Nat}
local notation "NativeStored" => SourceCurrentAllocatedFiniteOrdinaryStored.Stored
local notation "OutputStored" => SourceCurrentAllocatedFiniteOrdinaryOutputStored.Stored
local notation "Profiles" => SourceCurrentAllocatedFiniteOrdinaryMergeProfileCache.Stored
local notation "ReturnedStored" => SourceCurrentAllocatedFiniteOrdinaryReturned.Stored

local notation "NativeGuards" => SourceCurrentAllocatedFiniteOrdinaryGuardStored.Stored
local notation "MergeGuards" => SourceCurrentAllocatedFiniteOrdinaryMergeGuardCache.Stored

/-- The whole existing strong store also retains both universal lower guard tables. -/
structure Stored (state : Caller width) extends SourceCurrentAllocatedFiniteOrdinaryOuterProfiles.Stored state : Prop where
  /-- Native cells retain guard laws for their exact stored operands. -/
  nativeGuard : NativeGuards state.checked.native
  /-- Merge entries retain guard laws for their exact captured owners. -/
  mergeGuard : MergeGuards state.merge

/-- The stronger guard store retains the entire earlier structural invariant. -/
theorem Stored.structural {state : Caller width} (stored : Stored state) :
    SourceCurrentAllocatedFiniteOrdinaryOuterState.Stored state := stored.toStored.structural

/-- Fresh outer tables retain all supplied lower certificates. -/
theorem initial (checked : SourceEqualityNativeDemand.State width)
    (memo : SourceCurrentMemoMergeGraph.Memo Symbol Guard) (fourth : SourceCurrentEmptinessMemo.Memo)
    (native : NativeStored checked.native) (output : OutputStored checked.native) (profiles : Profiles memo)
    (guards : NativeGuards checked.native) (mergeGuards : MergeGuards memo) :
    Stored (SourceCurrentAllocatedPartialState.initial checked memo fourth) :=
  ⟨SourceCurrentAllocatedFiniteOrdinaryOuterProfiles.initial checked memo fourth native output profiles, guards, mergeGuards⟩

/-- Literal logical initialization derives both guard stores from empty lower tables. -/
theorem caller_stored (width : Nat) (cache : Cache.State SourceEqualityPartialConstraintKey.Key)
    (heap : InternedConstructorTemplates.State Symbol Guard) :
    Stored (SourceCurrentAllocatedPartialInitialization.caller width cache heap) :=
  ⟨SourceCurrentAllocatedFiniteOrdinaryOuterProfiles.caller_stored width cache heap,
    SourceCurrentAllocatedFiniteOrdinaryGuardStored.initial_stored width ⟨heap, Cache.emptyState⟩,
    SourceCurrentAllocatedFiniteOrdinaryMergeGuardCache.empty_stored⟩

private theorem Stored.advance {before : Caller width} (stored : Stored before)
    (checked : SourceEqualityNativeDemand.State width) (fourth : SourceCurrentEmptinessMemo.Memo)
    (memo : SourceCurrentMemoMergeGraph.Memo Symbol Guard) (native : NativeStored checked.native)
    (output : OutputStored checked.native) (profiles : Profiles memo)
    (guards : NativeGuards checked.native) (mergeGuards : MergeGuards memo) :
    Stored (SourceCurrentAllocatedPartialState.advance before checked fourth memo) :=
  ⟨stored.toStored.advance checked fourth memo native output profiles, guards, mergeGuards⟩

private theorem Stored.advancePhysical {before : Caller width} (stored : Stored before)
    (physical : SourceCurrentConjunctionRowsAllocation.State Symbol FullSyntax.Formula) :
    Stored (SourceCurrentAllocatedPartialState.advance before (SourceCurrentAllocatedQueryMemo.advancePhysical before.checked physical)
      before.fourth before.merge) :=
  ⟨stored.toStored.advancePhysical physical,
    SourceCurrentAllocatedFiniteOrdinaryGuardStored.advance_stored _ _ stored.nativeGuard, stored.mergeGuard⟩

private theorem Stored.beginNode {before : Caller width} (stored : Stored before) (request : NodeRequest) :
    Stored (beginNode request before).2.2 :=
  ⟨stored.toStored.beginNode request, stored.nativeGuard, stored.mergeGuard⟩

private theorem Stored.beginEdge {before : Caller width} (stored : Stored before) (request : EdgeRequest) :
    Stored (beginEdge request before).2.2 :=
  ⟨stored.toStored.beginEdge request, stored.nativeGuard, stored.mergeGuard⟩

private theorem Stored.finishNode {before : Caller width} (stored : Stored before)
    {handle : Nat} {owner : NodeRequest} (result : Node)
    (running : before.nodeResults.cells handle = some ⟨owner, .evaluating⟩)
    (law : DNode owner.value → NodeNarrow owner.value result) : Stored (finishNode handle result before) :=
  ⟨stored.toStored.finishNode result running law, stored.nativeGuard, stored.mergeGuard⟩

private theorem Stored.finishEdge {before : Caller width} (stored : Stored before)
    {handle : Nat} {owner : EdgeRequest} (result : Edge)
    (running : before.edgeResults.cells handle = some ⟨owner, .evaluating⟩)
    (law : DEdge owner.value → EdgeNarrow owner.value result) : Stored (finishEdge handle result before) :=
  ⟨stored.toStored.finishEdge result running law, stored.nativeGuard, stored.mergeGuard⟩

variable (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)

private theorem values_grow {before after : Caller width} {values : List Node}
    (effects : SourceCurrentConjunctionRowsAllocation.Effects (physical before.checked) (physical after.checked))
    (available : Values before.checked.native.machine.heap values) : Values after.checked.native.machine.heap values :=
  fun value member => effects.keeps.available value (available value member)

private theorem edges_grow {before after : Caller width} {values : List Edge}
    (effects : SourceCurrentConjunctionRowsAllocation.Effects (physical before.checked) (physical after.checked))
    (resident : Edges before.checked.native.machine.heap values) : Edges after.checked.native.machine.heap values :=
  fun edge member => InternedEdgeResidency.edge_grows _ _ effects.keeps.growth edge (resident edge member)

variable [DecidableEq (EdgeKey Symbol Guard)]

private theorem raw_modify {inventory : Inventory} {before : Caller width} {memos : Memos}
    (initial : Context formulas solver inventory before memos) (stored : Stored before)
    (entry : Interned InternedBinderProtocol.NodeKey) (oldRows newRows : List Edge)
    (depth : Nat) (free : List InternedBinderProtocol.Reference)
    (available : Available before.checked.native.machine.heap (.node entry oldRows depth free))
    (resident : Edges before.checked.native.machine.heap newRows)
    (domain : DNode (.node entry oldRows depth free)) (related : All₂ EdgeNarrow oldRows newRows) :
    Stored (SourceCurrentAllocatedPartialState.advance before (SourceCurrentAllocatedRawRebuild.modify (.node entry oldRows depth free) oldRows newRows before.checked).2
      before.fourth before.merge) ∧
      NodeNarrow (.node entry oldRows depth free)
        (SourceCurrentAllocatedRawRebuild.modify (.node entry oldRows depth free) oldRows newRows before.checked).1 := by
  have receipt := SourceCurrentAllocatedRawRebuild.modify_verified formulas solver inventory entry oldRows newRows depth free
    before.checked initial.ready initial.admitted available resident
  have native : SourceCurrentAllocatedFiniteOrdinaryStored.Stored
      (SourceCurrentAllocatedRawRebuild.modify (.node entry oldRows depth free) oldRows newRows before.checked).2.native := by
    constructor
    · simpa only [receipt.nodes] using stored.native.nodes
    · simpa only [receipt.edges] using stored.native.edges
  have output : OutputStored
      (SourceCurrentAllocatedRawRebuild.modify (.node entry oldRows depth free) oldRows newRows before.checked).2.native :=
    ⟨by simpa only [receipt.nodes] using stored.output.nodes,
      by simpa only [receipt.edges] using stored.output.edges⟩
  have guards : NativeGuards
      (SourceCurrentAllocatedRawRebuild.modify (.node entry oldRows depth free) oldRows newRows before.checked).2.native :=
    ⟨by simpa only [receipt.nodes] using stored.nativeGuard.nodes,
      by simpa only [receipt.edges] using stored.nativeGuard.edges⟩
  refine ⟨stored.advance _ _ _ native output stored.profiles guards stored.mergeGuard, ?_⟩
  by_cases same : newRows.map (fun row => row.entry.identity) = oldRows.map (fun row => row.entry.identity)
  · rw [SourceCurrentAllocatedRawRebuild.modify_unchanged _ _ _ _ same]
    exact SourceCurrentAllocatedFiniteOrdinaryNarrow.node_refl domain
  · simp only [SourceCurrentAllocatedRawRebuild.modify, SourceEqualityPartialNodeRebuild.modify, same, ↓reduceIte]
    have facts := initial.ready.semantic.ready.semantic.1.normal.facts
    exact SourceCurrentAllocatedFiniteOrdinaryNarrow.makeNode entry oldRows newRows depth free
      before.checked.native.machine.heap facts.coherent facts.linked resident related

private theorem raw_edge {inventory : Inventory} {before : Caller width} {memos : Memos}
    (initial : Context formulas solver inventory before memos) (stored : Stored before)
    (original : Edge) (children : List Node)
    (available : Values before.checked.native.machine.heap children)
    (related : All₂ NodeNarrow original.children children) :
    Stored (SourceCurrentAllocatedPartialState.advance before (SourceCurrentAllocatedRawRebuild.edge original children before.checked).2 before.fourth before.merge) ∧
      EdgeNarrow original (SourceCurrentAllocatedRawRebuild.edge original children before.checked).1 := by
  refine ⟨?_, ?_⟩
  · exact stored.advancePhysical _
  · have facts := initial.ready.semantic.ready.semantic.1.normal.facts
    exact SourceCurrentAllocatedFiniteOrdinaryNarrow.makeEdge original children before.checked.native.machine.heap
      facts.coherent facts.cached available related

variable [DecidableEq Symbol] [DecidableEq Node]

/-- A completed node returns its same-state structural certificate and input-relative bound. -/
private def NodeBound (top : Trace width budget) (request : NodeRequest) (before : Caller width)
    (result : Node) (after : Caller width) (memos _final : Memos) : Prop :=
  ∀ inventory, Checks top → Context formulas solver inventory before memos →
    EqReady before.checked.operations.constraints request.inherited → Available before.checked.native.machine.heap request.value →
    DNode request.value → Stored before → Stored after ∧ NodeNarrow request.value result

/-- A completed edge returns its same-state structural certificate and input-relative bound. -/
private def EdgeBound (top : Trace width budget) (request : EdgeRequest) (before : Caller width)
    (result : Edge) (after : Caller width) (memos _final : Memos) : Prop :=
  ∀ inventory, Checks top → Context formulas solver inventory before memos →
    EqReady before.checked.operations.constraints request.inherited → Resident before.checked.native.machine.heap request.value →
    DEdge request.value → Stored before → Stored after ∧ EdgeNarrow request.value result

/-- Ordered source rows return positional row domain and height bounds. -/
private def RowsBound {inherited : EqValue} {values results : List Edge} {before after : Caller width}
    (actual : Rows budget inherited values before results after) (memos _final : Memos) : Prop :=
  ∀ inventory, Checks (rowsTrace actual) → Context formulas solver inventory before memos →
    EqReady before.checked.operations.constraints inherited → Edges before.checked.native.machine.heap values →
    DRows values → Stored before → Stored after ∧ All₂ EdgeNarrow values results

/-- Actual descendants retain the returned edge's domain and original height bound. -/
private def DescendantsBound {inherited : EqValue} {value result : Edge} {before after : Caller width}
    (actual : Descendants budget inherited value before result after) (memos _final : Memos) : Prop :=
  EdgeBound formulas solver (descendantsTrace actual) ⟨inherited, value⟩ before result after memos _final

/-- Actual child branches derive positional structural bounds for every returned slot. -/
private def ChildrenBound {combined : EqValue} {values results : List Node} {before after : Caller width}
    (actual : Children budget combined values before results after) (memos _final : Memos) : Prop :=
  ∀ inventory, Checks (childrenTrace actual) → Context formulas solver inventory before memos →
    EqReady before.checked.operations.constraints combined → Values before.checked.native.machine.heap values →
    DChildren values → Stored before → Stored after ∧ All₂ NodeNarrow values results

/-- Each indexed walk derives positional node bounds at the literal source offsets. -/
private def WalkBound {combined : EqValue} {index : Nat} {values results : List Node} {before after : Caller width}
    (actual : Walk budget combined index values before results after) (memos _final : Memos) : Prop :=
  ∀ inventory, Checks (walkTrace actual) → Context formulas solver inventory before memos →
    EqReady before.checked.operations.constraints combined → Values before.checked.native.machine.heap values →
    DChildren values → Stored before → Stored after ∧ All₂ NodeNarrow values results

-- The eight motives use the same source-aligned read induction.
local macro "structural_induction" recursor:ident reads:ident formulas:ident solver:ident : tactic => `(tactic|
  (apply $recursor
    (motive_1 := fun {budget request before result after} actual memos final _ =>
      NodeBound $formulas $solver (nodeCallTrace actual) request before result after memos final)
    (motive_2 := fun {budget request before result after} actual memos final _ =>
      NodeBound $formulas $solver (nodeBodyTrace actual) request before result after memos final)
    (motive_3 := fun {budget request before result after} actual memos final _ =>
      EdgeBound $formulas $solver (edgeCallTrace actual) request before result after memos final)
    (motive_4 := fun {budget request before result after} actual memos final _ =>
      EdgeBound $formulas $solver (edgeBodyTrace actual) request before result after memos final)
    (motive_5 := fun {_budget _inherited _values _before _results _after} actual memos final _ =>
      RowsBound $formulas $solver actual memos final)
    (motive_6 := fun {_budget _inherited _value _before _result _after} actual memos final _ =>
      DescendantsBound $formulas $solver actual memos final)
    (motive_7 := fun {_budget _combined _values _before _results _after} actual memos final _ =>
      ChildrenBound $formulas $solver actual memos final)
    (motive_8 := fun {_budget _combined _index _values _before _results _after} actual memos final _ =>
      WalkBound $formulas $solver actual memos final)
    (t := $reads)
   · intro budget request before handle result after started memos inventory checks initial inherited available domain stored
     obtain ⟨same, bound⟩ := stored.structural.node_ready $formulas $solver request after handle result initial.sound
       initial.ready.semantic.ready.semantic.1.normal.facts.coherent available domain started
     exact ⟨same.symm ▸ stored, bound⟩
   · intro budget original running result middle body memos final request before handle started bodyReads ih
     intro inventory checks initial inherited available domain stored
     obtain ⟨runningContext, owner, key, cell⟩ := SourceCurrentAllocatedPartialCallSteps.node_start $formulas $solver
       initial inherited available started
     obtain ⟨same, ownerDomain, _⟩ := SourceCurrentAllocatedFiniteOrdinaryOuterState.node_evaluate $formulas $solver request original before running handle
       initial.sound initial.ready.semantic.ready.semantic.1.normal.facts.coherent inherited available domain started
     have runningStored : Stored running := by simpa only [started] using stored.beginNode request
     have smallerChecks := checks.restrict (.node_evaluate started body)
     have resultBound := ih inventory smallerChecks runningContext owner.inherited owner.input ownerDomain runningStored
     have frame := SourceCurrentAllocatedPartialFrames.node_body body
       (SourceCurrentAllocatedPartialFrames.Protocol.of_valid runningContext.sound.valid)
     refine ⟨resultBound.1.finishNode result (frame.node_running handle original cell) (fun _ => resultBound.2), ?_⟩
     simpa only [same] using resultBound.2
   · intro budget inherited before memos inventory checks initial inheritedReady available domain stored
     exact ⟨stored, SourceCurrentAllocatedFiniteOrdinaryNarrow.node_refl domain⟩
   · intro budget inherited entry members depth free before memos inventory checks initial inheritedReady available domain stored
     cases domain
   · intro budget inherited entry body depth ordinary before result heap actual memos inventory checks initial inheritedReady available domain stored
     cases domain
   · intro entry depth free budget inherited edges before results middle rows memos final rowsReads ih
     intro inventory checks initial inheritedReady available domain stored
     have resident := InternedEdgeResidency.resident_edges _ initial.ready.semantic.ready.semantic.1.normal.facts.linked _ available.resident
     have smallerChecks := checks.restrict (.node_ordinary rows)
     have resultBound := ih inventory smallerChecks initial inheritedReady resident domain.rows stored
     obtain ⟨next, post, rowsResident, _⟩ := SourceCurrentAllocatedPartialActual.rows $formulas $solver rowsReads
       inventory smallerChecks initial inheritedReady resident
     exact raw_modify $formulas $solver post.context resultBound.1 entry edges results depth free
       (post.effects.keeps.available _ available) rowsResident domain resultBound.2
   · intro budget request before handle result after started memos inventory checks initial inherited resident domain stored
     obtain ⟨same, bound⟩ := stored.structural.edge_ready $formulas $solver request after handle result initial.sound
       initial.ready.semantic.ready.semantic.1.normal.facts.coherent resident domain started
     exact ⟨same.symm ▸ stored, bound⟩
   · intro budget original running result middle body memos final request before handle started bodyReads ih
     intro inventory checks initial inherited resident domain stored
     obtain ⟨runningContext, owner, key, cell⟩ := SourceCurrentAllocatedPartialCallSteps.edge_start $formulas $solver
       initial inherited resident started
     obtain ⟨same, ownerDomain, _⟩ := SourceCurrentAllocatedFiniteOrdinaryOuterState.edge_evaluate $formulas $solver request original before running handle
       initial.sound initial.ready.semantic.ready.semantic.1.normal.facts.coherent inherited resident domain started
     have runningStored : Stored running := by simpa only [started] using stored.beginEdge request
     have smallerChecks := checks.restrict (.edge_evaluate started body)
     have resultBound := ih inventory smallerChecks runningContext owner.inherited owner.input ownerDomain runningStored
     have frame := SourceCurrentAllocatedPartialFrames.edge_body body
       (SourceCurrentAllocatedPartialFrames.Protocol.of_valid runningContext.sound.valid)
     refine ⟨resultBound.1.finishEdge result (frame.edge_running handle original cell) (fun _ => resultBound.2), ?_⟩
     simpa only [same] using resultBound.2
   · intro budget edge loaded inherited before result checked fourth merge actual memos final field parentReads
     intro inventory checks initial inheritedReady resident domain stored
     have live : SourceEqualityMkEdgeAllocation.contradictory edge.entry.key.constraint = false →
         SourceEqualityGuardReadback.Cached edge.entry.key.constraint.equalities ∧
         SourceEqualityConstraintFieldLookup.load edge.entry.key.constraint before.checked.operations.constraints = .ok (some loaded) ∧
         EqReady before.checked.operations.constraints inherited ∧ Values before.checked.native.machine.heap edge.children := by
       intro test
       exact ⟨(initial.ready.good.fields _ _ resident).1, field test, inheritedReady,
         initial.ready.semantic.ready.semantic.1.normal.facts.cached.edges _ edge resident⟩
     obtain ⟨native, output, profiles, bound⟩ := SourceCurrentAllocatedFiniteOrdinaryParentProfiles.structure_from_reads $formulas $solver
       inventory edge parentReads initial.ready initial.admitted live domain initial.correct initial.stored initial.covered
       stored.native stored.profiles stored.output initial.globals
     have guardProfile := SourceCurrentAllocatedFiniteOrdinaryGuardProfiles.edge_self edge domain
     have guardBound := SourceCurrentAllocatedFiniteOrdinaryGuardParent.structure_from_reads $formulas $solver
       inventory edge parentReads initial.ready initial.admitted live _ guardProfile initial.correct initial.stored initial.covered
       stored.native stored.profiles.domain initial.globals stored.nativeGuard stored.mergeGuard
     exact ⟨stored.advance checked fourth merge native output profiles guardBound.2.1 guardBound.2.2.1, bound⟩
   · intro budget inherited before memos inventory checks initial inheritedReady resident domain stored
     exact ⟨stored, .nil⟩
   · intro budget inherited original before narrowed middle first memos edgeMemos result afterChildren child childMemos
     intro originals results after tail final edgeReads childrenReads tailReads ihEdge ihChildren ihTail
     intro inventory checks initial inheritedReady resident domain stored
     cases domain with
     | cons firstDomain restDomain =>
         have edgeChecks := checks.restrict (.rows_edge first child tail)
         have firstBound := ihEdge inventory edgeChecks initial inheritedReady (resident original List.mem_cons_self) firstDomain stored
         obtain ⟨edgeInventory, edgePost, narrowedResident, _⟩ := SourceCurrentAllocatedPartialActual.edge_call $formulas $solver edgeReads
           inventory edgeChecks initial inheritedReady (resident original List.mem_cons_self)
         have childChecks := checks.restrict (.rows_descendants first child tail)
         have childBound := ihChildren edgeInventory childChecks edgePost.context
           (inheritedReady.grows edgePost.effects.grows.constraint_growth) narrowedResident firstBound.2.1 firstBound.1
         obtain ⟨childInventory, childPost, resultResident, _⟩ := SourceCurrentAllocatedPartialActual.descendants $formulas $solver childrenReads
           edgeInventory childChecks edgePost.context (inheritedReady.grows edgePost.effects.grows.constraint_growth) narrowedResident
         have firstPost := edgePost.trans childPost
         have tailBound := ihTail childInventory (checks.restrict (.rows_tail first child tail)) childPost.context
           (inheritedReady.grows firstPost.effects.grows.constraint_growth)
           (edges_grow firstPost.effects (fun edge member => resident edge (List.mem_cons_of_mem _ member))) restDomain childBound.1
         exact ⟨tailBound.1, .cons (SourceCurrentAllocatedFiniteOrdinaryNarrow.edge_trans firstBound.2 childBound.2) tailBound.2⟩
   · intro budget payload edge before inherited results middle children memos final combined childReads ih
     intro inventory checks initial inheritedReady resident domain stored
     obtain ⟨prefixReceipt, prefixPost⟩ := SourceCurrentAllocatedPartialStepEffects.inherited_prefix $formulas $solver
       inventory before memos initial edge inherited payload resident inheritedReady combined
     have prefixStored : Stored (prefixState before edge inherited) := stored.advancePhysical _
     have inputs := initial.ready.semantic.ready.semantic.1.normal.facts.cached.edges edge.entry.key edge resident
     have childChecks := checks.restrict (.descendants_children combined children)
     have childBound := ih inventory childChecks prefixPost.context prefixReceipt.combinedReady
       (values_grow prefixPost.effects inputs) domain prefixStored
     obtain ⟨next, childPost, available, _⟩ := SourceCurrentAllocatedPartialActual.children $formulas $solver childReads
       inventory childChecks prefixPost.context prefixReceipt.combinedReady (values_grow prefixPost.effects inputs)
     exact raw_edge $formulas $solver childPost.context childBound.1 edge results
       available childBound.2
   · intro budget values before memos inventory checks initial inherited available domain stored
     exact ⟨stored, SourceCurrentAllocatedFiniteOrdinaryNarrow.forest_erase values⟩
   · intro budget identity records values before results after actual memos final walkReads ih
     intro inventory checks initial inherited available domain stored
     exact ih inventory (checks.restrict (.children_walk actual)) initial inherited available domain stored
   · intro budget combined index before memos inventory checks initial inherited available domain stored
     exact ⟨stored, .nil⟩
   · intro budget before combined index value result middle first memos headMemos values results after tail final headReads tailReads ihHead ihTail
     intro inventory checks initial inherited available domain stored
     cases domain with
     | cons firstDomain restDomain =>
         obtain ⟨descentReceipt, descentPost⟩ := SourceCurrentAllocatedPartialStepEffects.descent $formulas $solver
           inventory before memos initial combined index inherited
         have descentStored : Stored (descend before combined index).2 := stored.advancePhysical _
         have headChecks := checks.restrict (.walk_head first tail)
         have headBound := ihHead inventory headChecks descentPost.context descentReceipt.inherited
           (descentPost.effects.keeps.available _ (available value List.mem_cons_self)) firstDomain descentStored
         obtain ⟨headInventory, headPost, resultAvailable, _⟩ := SourceCurrentAllocatedPartialActual.node_call $formulas $solver headReads
           inventory headChecks descentPost.context descentReceipt.inherited
           (descentPost.effects.keeps.available _ (available value List.mem_cons_self))
         have firstPost := descentPost.trans headPost
         have tailBound := ihTail headInventory (checks.restrict (.walk_tail first tail)) headPost.context
           (inherited.grows firstPost.effects.grows.constraint_growth)
           (values_grow firstPost.effects (fun child member => available child (List.mem_cons_of_mem _ member))) restDomain headBound.1
         exact ⟨tailBound.1, .cons headBound.2 tailBound.2⟩))

/-- Supplied actual node call reads retain the whole strong store and both lower guard tables at the same return. -/
theorem node_call {request : NodeRequest} {before after : Caller width} {result : Node}
    {actual : NodeCall budget request before result after} {memos final : Memos}
    (reads : NodeCallReads formulas solver actual memos final) (inventory : Inventory)
    (initial : Context formulas solver inventory before memos)
    (inherited : EqReady before.checked.operations.constraints request.inherited)
    (available : Available before.checked.native.machine.heap request.value) (domain : DNode request.value) (stored : Stored before) :
    Stored after ∧ NodeNarrow request.value result := by
  have checks := (SourceCurrentAllocatedFiniteOrdinaryOuterVerification.node_call formulas solver
    reads inventory initial inherited available domain stored.structural).1
  have bounded : NodeBound formulas solver (nodeCallTrace actual) request before result after memos final := by
    structural_induction NodeCallReads.rec reads formulas solver
  exact bounded inventory checks initial inherited available domain stored

/-- Supplied actual node body reads retain the whole strong store and both lower guard tables at the same return. -/
theorem node_body {request : NodeRequest} {before after : Caller width} {result : Node}
    {actual : NodeBody budget request before result after} {memos final : Memos}
    (reads : NodeBodyReads formulas solver actual memos final) (inventory : Inventory)
    (initial : Context formulas solver inventory before memos)
    (inherited : EqReady before.checked.operations.constraints request.inherited)
    (available : Available before.checked.native.machine.heap request.value) (domain : DNode request.value) (stored : Stored before) :
    Stored after ∧ NodeNarrow request.value result := by
  have checks := (SourceCurrentAllocatedFiniteOrdinaryOuterVerification.node_body formulas solver
    reads inventory initial inherited available domain stored.structural).1
  have bounded : NodeBound formulas solver (nodeBodyTrace actual) request before result after memos final := by
    structural_induction NodeBodyReads.rec reads formulas solver
  exact bounded inventory checks initial inherited available domain stored

/-- Supplied actual edge call reads retain the whole strong store and both lower guard tables at the same return. -/
theorem edge_call {request : EdgeRequest} {before after : Caller width} {result : Edge}
    {actual : EdgeCall budget request before result after} {memos final : Memos}
    (reads : EdgeCallReads formulas solver actual memos final) (inventory : Inventory)
    (initial : Context formulas solver inventory before memos)
    (inherited : EqReady before.checked.operations.constraints request.inherited)
    (available : Resident before.checked.native.machine.heap request.value) (domain : DEdge request.value) (stored : Stored before) :
    Stored after ∧ EdgeNarrow request.value result := by
  have checks := (SourceCurrentAllocatedFiniteOrdinaryOuterVerification.edge_call formulas solver
    reads inventory initial inherited available domain stored.structural).1
  have bounded : EdgeBound formulas solver (edgeCallTrace actual) request before result after memos final := by
    structural_induction EdgeCallReads.rec reads formulas solver
  exact bounded inventory checks initial inherited available domain stored

/-- Supplied actual edge body reads retain the whole strong store and both lower guard tables at the same return. -/
theorem edge_body {request : EdgeRequest} {before after : Caller width} {result : Edge}
    {actual : EdgeBody budget request before result after} {memos final : Memos}
    (reads : EdgeBodyReads formulas solver actual memos final) (inventory : Inventory)
    (initial : Context formulas solver inventory before memos)
    (inherited : EqReady before.checked.operations.constraints request.inherited)
    (available : Resident before.checked.native.machine.heap request.value) (domain : DEdge request.value) (stored : Stored before) :
    Stored after ∧ EdgeNarrow request.value result := by
  have checks := (SourceCurrentAllocatedFiniteOrdinaryOuterVerification.edge_body formulas solver
    reads inventory initial inherited available domain stored.structural).1
  have bounded : EdgeBound formulas solver (edgeBodyTrace actual) request before result after memos final := by
    structural_induction EdgeBodyReads.rec reads formulas solver
  exact bounded inventory checks initial inherited available domain stored

/-- Supplied actual rows reads retain the whole strong store and both lower guard tables at the same return. -/
theorem rows {inherited : EqValue} {values results : List Edge} {before after : Caller width}
    {actual : Rows budget inherited values before results after} {memos final : Memos}
    (reads : RowsReads formulas solver actual memos final) (inventory : Inventory)
    (initial : Context formulas solver inventory before memos)
    (inheritedReady : EqReady before.checked.operations.constraints inherited)
    (available : Edges before.checked.native.machine.heap values) (domain : DRows values) (stored : Stored before) :
    Stored after ∧ All₂ EdgeNarrow values results := by
  have checks := (SourceCurrentAllocatedFiniteOrdinaryOuterVerification.rows formulas solver
    reads inventory initial inheritedReady available domain stored.structural).1
  have bounded : RowsBound formulas solver actual memos final := by
    structural_induction RowsReads.rec reads formulas solver
  exact bounded inventory checks initial inheritedReady available domain stored

/-- Supplied actual descendants reads retain the whole strong store and both lower guard tables at the same return. -/
theorem descendants {inherited : EqValue} {value result : Edge} {before after : Caller width}
    {actual : Descendants budget inherited value before result after} {memos final : Memos}
    (reads : DescendantsReads formulas solver actual memos final) (inventory : Inventory)
    (initial : Context formulas solver inventory before memos)
    (inheritedReady : EqReady before.checked.operations.constraints inherited)
    (available : Resident before.checked.native.machine.heap value) (domain : DEdge value) (stored : Stored before) :
    Stored after ∧ EdgeNarrow value result := by
  have checks := (SourceCurrentAllocatedFiniteOrdinaryOuterVerification.descendants formulas solver
    reads inventory initial inheritedReady available domain stored.structural).1
  have bounded : DescendantsBound formulas solver actual memos final := by
    structural_induction DescendantsReads.rec reads formulas solver
  exact bounded inventory checks initial inheritedReady available domain stored

/-- Supplied actual children reads retain the whole strong store and both lower guard tables at the same return. -/
theorem children {combined : EqValue} {values results : List Node} {before after : Caller width}
    {actual : Children budget combined values before results after} {memos final : Memos}
    (reads : ChildrenReads formulas solver actual memos final) (inventory : Inventory)
    (initial : Context formulas solver inventory before memos)
    (inheritedReady : EqReady before.checked.operations.constraints combined)
    (available : Values before.checked.native.machine.heap values) (domain : DChildren values) (stored : Stored before) :
    Stored after ∧ All₂ NodeNarrow values results := by
  have checks := (SourceCurrentAllocatedFiniteOrdinaryOuterVerification.children formulas solver
    reads inventory initial inheritedReady available domain stored.structural).1
  have bounded : ChildrenBound formulas solver actual memos final := by
    structural_induction ChildrenReads.rec reads formulas solver
  exact bounded inventory checks initial inheritedReady available domain stored

/-- Supplied actual walk reads retain the whole strong store and both lower guard tables at the same return. -/
theorem walk {combined : EqValue} {index : Nat} {values results : List Node} {before after : Caller width}
    {actual : Walk budget combined index values before results after} {memos final : Memos}
    (reads : WalkReads formulas solver actual memos final) (inventory : Inventory)
    (initial : Context formulas solver inventory before memos)
    (inheritedReady : EqReady before.checked.operations.constraints combined)
    (available : Values before.checked.native.machine.heap values) (domain : DChildren values) (stored : Stored before) :
    Stored after ∧ All₂ NodeNarrow values results := by
  have checks := (SourceCurrentAllocatedFiniteOrdinaryOuterVerification.walk formulas solver
    reads inventory initial inheritedReady available domain stored.structural).1
  have bounded : WalkBound formulas solver actual memos final := by
    structural_induction WalkReads.rec reads formulas solver
  exact bounded inventory checks initial inheritedReady available domain stored

end MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryOuterGuardStores
