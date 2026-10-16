import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryActualParentWork
import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryOuterQuantitativeProducer
import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryOuterBudgetNumbers
import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryRawRebuildResources

/-!
# Constructor Work through the same actual outer reads

The proof records requests at their actual intermediate heaps.
It follows parent reduction, returned descendants, and the original suffix.
Earlier reads derive the current Context, profile, and causal stores.
No capacity, reserved headroom, or future result law is an input.
-/
namespace MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryActualOuterWork
open Cache Language InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values Edges)
open SourceCurrentAllocatedPartialState SourceCurrentAllocatedPartialGraph
open SourceCurrentAllocatedPartialSourceReads SourceCurrentAllocatedPartialChecks
open SourceCurrentAllocatedPartialInvariant (Context)
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedNativeEffects (physical)
open SourceCurrentAllocatedFiniteOrdinaryNativeProfile (NodeShape RowsShape EdgeShape ChildrenShape)
open SourceCurrentAllocatedFiniteOrdinaryOuterQuantitativeState (Stored)
open SourceCurrentAllocatedFiniteOrdinaryOuterBudgetNumbers
open SourceCurrentAllocatedFiniteOrdinaryParentUniformBudgets (nodeBudget edgeBudget)
open SourceCurrentAllocatedFiniteOrdinaryParentUniformNumbers (parentRows)
open SourceCurrentAllocatedFiniteOrdinaryGuardEnvelope (Limits)
open SourceCurrentAllocatedFiniteOrdinaryConstructorWorkTrace (Trace nodeRequests_append edgeRequests_append)
open SourceCurrentAllocatedFiniteOrdinaryReservations (nodeRequests edgeRequests)
open MergedOrdinaryHeight (height edgeHeight edgesHeight childrenHeight)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Heap" => InternedConstructorTemplates.State Symbol Guard
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
local notation "GPNode" => SourceCurrentAllocatedFiniteOrdinaryGuardProfiles.Node
local notation "GPRows" => SourceCurrentAllocatedFiniteOrdinaryGuardProfiles.Rows
local notation "GPEdge" => SourceCurrentAllocatedFiniteOrdinaryGuardProfiles.Edge
local notation "GPChildren" => SourceCurrentAllocatedFiniteOrdinaryGuardProfiles.Children
local notation "parentGuards" => SourceCurrentAllocatedFiniteOrdinaryGuardParent.outputLimit
section WorkAlgebra
variable [DecidableEq (EdgeKey Symbol Guard)]

/-- The trace retains its exact actual heaps and bounds both constructor request counts. -/
def WorkBounds (before after : Heap) (nodes edges : Nat) : Prop :=
  ∃ requests, Trace before after requests ∧ nodeRequests requests ≤ nodes ∧ edgeRequests requests ≤ edges

/-- An unchanged heap emits no constructor request. -/
theorem WorkBounds.refl (before : Heap) : WorkBounds before before 0 0 :=
  ⟨[], .refl _, Nat.le_refl _, Nat.le_refl _⟩

/-- Larger numeric envelopes retain the same trace and request list. -/
theorem WorkBounds.mono {before after : Heap} {nodes edges largerNodes largerEdges : Nat}
    (actual : WorkBounds before after nodes edges) (nodeBound : nodes ≤ largerNodes) (edgeBound : edges ≤ largerEdges) :
    WorkBounds before after largerNodes largerEdges := by
  obtain ⟨requests, trace, nodes, edges⟩ := actual
  exact ⟨requests, trace, Nat.le_trans nodes nodeBound, Nat.le_trans edges edgeBound⟩

/-- Sequential composition retains the actual request order and exact middle heap. -/
theorem WorkBounds.trans {before middle after : Heap} {firstNodes firstEdges lastNodes lastEdges : Nat}
    (first : WorkBounds before middle firstNodes firstEdges) (last : WorkBounds middle after lastNodes lastEdges) :
    WorkBounds before after (firstNodes + lastNodes) (firstEdges + lastEdges) := by
  obtain ⟨earlier, first, firstN, firstE⟩ := first
  obtain ⟨later, last, lastN, lastE⟩ := last
  refine ⟨earlier ++ later, first.trans last, ?_, ?_⟩
  · rw [nodeRequests_append]; exact Nat.add_le_add firstN lastN
  · rw [edgeRequests_append]; exact Nat.add_le_add firstE lastE

end WorkAlgebra

variable {width budget : Nat}
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

private theorem modify_work (original : Node) (oldRows newRows : List Edge) (before : SourceEqualityNativeDemand.State width) :
    WorkBounds before.native.machine.heap (SourceCurrentAllocatedRawRebuild.modify original oldRows newRows before).2.native.machine.heap 1 0 := by
  obtain ⟨trace, nodes, edges⟩ := SourceCurrentAllocatedFiniteOrdinaryRawRebuildResources.modify_work original oldRows newRows before
  exact ⟨_, trace, nodes, Nat.le_of_eq edges⟩

private theorem edge_work (original : Edge) (values : List Node) (before : SourceEqualityNativeDemand.State width) :
    WorkBounds before.native.machine.heap (SourceCurrentAllocatedRawRebuild.edge original values before).2.native.machine.heap 0 1 := by
  refine ⟨_, .work _ (makeEdge original.entry.key.symbol original.entry.key.constraint values), ?_, ?_⟩
  · simp only [SourceCurrentAllocatedFiniteOrdinaryReservations.makeEdge_observe, nodeRequests, Nat.le_refl]
  · simp only [SourceCurrentAllocatedFiniteOrdinaryReservations.makeEdge_observe, edgeRequests, Nat.le_refl]

variable [DecidableEq Symbol] [DecidableEq Node]

private def NodeBound (top : SourceCurrentAllocatedPartialChecks.Trace width budget) (request : NodeRequest) (before : Caller width)
    (_result : Node) (after : Caller width) (memos _final : Memos) : Prop :=
  ∀ inventory, Checks top → Context formulas solver inventory before memos →
    EqReady before.checked.operations.constraints request.inherited → Available before.checked.native.machine.heap request.value →
    DNode request.value → Stored before → ∀ rows arity bound (limits : Limits),
    NodeShape rows arity request.value → GPNode limits request.value → height request.value ≤ bound →
    WorkBounds before.checked.native.machine.heap after.checked.native.machine.heap
      (nodeNodes rows arity limits bound) (nodeEdges rows arity limits bound)

private def EdgeBound (top : SourceCurrentAllocatedPartialChecks.Trace width budget) (request : EdgeRequest) (before : Caller width)
    (_result : Edge) (after : Caller width) (memos _final : Memos) : Prop :=
  ∀ inventory, Checks top → Context formulas solver inventory before memos →
    EqReady before.checked.operations.constraints request.inherited → Resident before.checked.native.machine.heap request.value →
    DEdge request.value → Stored before → ∀ rows arity bound (limits : Limits),
    EdgeShape rows arity request.value → GPEdge limits request.value → edgeHeight request.value ≤ bound →
    WorkBounds before.checked.native.machine.heap after.checked.native.machine.heap
      (nodeBudget limits rows arity bound) (edgeBudget limits rows arity bound)

private def RowsBound {inherited : EqValue} {values results : List Edge} {before after : Caller width}
    (actual : Rows budget inherited values before results after) (memos _final : Memos) : Prop :=
  ∀ inventory, Checks (rowsTrace actual) → Context formulas solver inventory before memos →
    EqReady before.checked.operations.constraints inherited → Edges before.checked.native.machine.heap values →
    DRows values → Stored before → ∀ rows arity bound (limits : Limits),
    RowsShape rows arity values → GPRows limits values → edgesHeight values ≤ bound →
    WorkBounds before.checked.native.machine.heap after.checked.native.machine.heap
      (values.length * rowNodes rows arity limits bound) (values.length * rowEdges rows arity limits bound)

private def DescendantsBound {inherited : EqValue} {value result : Edge} {before after : Caller width}
    (actual : Descendants budget inherited value before result after) (memos _final : Memos) : Prop :=
  ∀ inventory, Checks (descendantsTrace actual) → Context formulas solver inventory before memos →
    EqReady before.checked.operations.constraints inherited → Resident before.checked.native.machine.heap value →
    DEdge value → Stored before → ∀ rows arity bound (limits : Limits),
    EdgeShape rows arity value → GPEdge limits value → edgeHeight value ≤ bound →
    WorkBounds before.checked.native.machine.heap after.checked.native.machine.heap
      (descendantsNodes rows arity limits bound) (descendantsEdges rows arity limits bound)

private def ChildrenBound {combined : EqValue} {values results : List Node} {before after : Caller width}
    (actual : Children budget combined values before results after) (memos _final : Memos) : Prop :=
  ∀ inventory, Checks (childrenTrace actual) → Context formulas solver inventory before memos →
    EqReady before.checked.operations.constraints combined → Values before.checked.native.machine.heap values →
    DChildren values → Stored before → ∀ rows arity bound (limits : Limits),
    ChildrenShape rows arity values → GPChildren limits values → childrenHeight values ≤ bound →
    WorkBounds before.checked.native.machine.heap after.checked.native.machine.heap
      (values.length * nodeNodes rows arity limits bound) (values.length * nodeEdges rows arity limits bound)

private def WalkBound {combined : EqValue} {index : Nat} {values results : List Node} {before after : Caller width}
    (actual : Walk budget combined index values before results after) (memos _final : Memos) : Prop :=
  ∀ inventory, Checks (walkTrace actual) → Context formulas solver inventory before memos →
    EqReady before.checked.operations.constraints combined → Values before.checked.native.machine.heap values →
    DChildren values → Stored before → ∀ rows arity bound (limits : Limits),
    ChildrenShape rows arity values → GPChildren limits values → childrenHeight values ≤ bound →
    WorkBounds before.checked.native.machine.heap after.checked.native.machine.heap
      (values.length * nodeNodes rows arity limits bound) (values.length * nodeEdges rows arity limits bound)

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
     intro rows arity bound limits profile guards bounded
     have components := beginNode_components request before
     rw [started] at components
     dsimp only at components
     simpa only [components.1] using (WorkBounds.refl before.checked.native.machine.heap).mono
       (Nat.zero_le (nodeNodes rows arity limits bound)) (Nat.zero_le (nodeEdges rows arity limits bound))
   · intro budget original running result middle body memos final request before handle started bodyReads ih
     intro inventory checks initial inherited available domain stored rows arity bound limits profile guards bounded
     obtain ⟨runningContext, owner, key, cell⟩ := SourceCurrentAllocatedPartialCallSteps.node_start $formulas $solver
       initial inherited available started
     obtain ⟨same, ownerDomain, _⟩ := SourceCurrentAllocatedFiniteOrdinaryOuterState.node_evaluate $formulas $solver request original before running handle
       initial.sound initial.ready.semantic.ready.semantic.1.normal.facts.coherent inherited available domain started
     have runningStored : Stored running := by simpa only [started] using stored.beginNode request
     have actualWork := ih inventory (checks.restrict (.node_evaluate started body)) runningContext
       owner.inherited owner.input ownerDomain runningStored rows arity bound limits
       (by simpa only [same] using profile) (by simpa only [same] using guards) (by simpa only [same] using bounded)
     have components := beginNode_components request before
     rw [started] at components
     dsimp only at components
     simpa only [finishNode, components.1] using actualWork
   · intro budget inherited before memos inventory checks initial inheritedReady available domain stored
     intro rows arity bound limits profile guards bounded
     exact (WorkBounds.refl _).mono (Nat.zero_le _) (Nat.zero_le _)
   · intro budget inherited entry members depth free before memos inventory checks initial inheritedReady available domain stored
     cases domain
   · intro budget inherited entry body depth ordinary before result heap actual memos inventory checks initial inheritedReady available domain stored
     cases domain
   · intro entry depth free budget inherited edges before results middle rows memos final rowsReads ih
     intro inventory checks initial inheritedReady available domain stored rowLimit arity bound limits profile guards bounded
     have resident := InternedEdgeResidency.resident_edges _ initial.ready.semantic.ready.semantic.1.normal.facts.linked _ available.resident
     cases bound with
     | zero => simp only [height] at bounded; omega
     | succ bound =>
         have actualWork := ih inventory (checks.restrict (.node_ordinary rows)) initial inheritedReady resident domain.rows stored
           rowLimit arity bound limits profile.2 guards (Nat.le_of_add_le_add_right bounded)
         have returned := actualWork.trans (modify_work (.node entry edges depth free) edges results middle.checked)
         apply returned.mono
         · have enough := Nat.mul_le_mul_right (rowNodes rowLimit arity limits bound) profile.1
           change edges.length * rowNodes rowLimit arity limits bound + 1 ≤ 1 + rowLimit * rowNodes rowLimit arity limits bound
           omega
         · exact Nat.le_trans (by omega : edges.length * rowEdges rowLimit arity limits bound + 0 ≤
             edges.length * rowEdges rowLimit arity limits bound)
             (Nat.mul_le_mul_right (rowEdges rowLimit arity limits bound) profile.1)
   · intro budget request before handle result after started memos inventory checks initial inherited resident domain stored
     intro rows arity bound limits profile guards bounded
     have components := beginEdge_components request before
     rw [started] at components
     dsimp only at components
     simpa only [components.1] using (WorkBounds.refl before.checked.native.machine.heap).mono
       (Nat.zero_le (nodeBudget limits rows arity bound)) (Nat.zero_le (edgeBudget limits rows arity bound))
   · intro budget original running result middle body memos final request before handle started bodyReads ih
     intro inventory checks initial inherited resident domain stored rows arity bound limits profile guards bounded
     obtain ⟨runningContext, owner, key, cell⟩ := SourceCurrentAllocatedPartialCallSteps.edge_start $formulas $solver
       initial inherited resident started
     obtain ⟨same, ownerDomain, _⟩ := SourceCurrentAllocatedFiniteOrdinaryOuterState.edge_evaluate $formulas $solver request original before running handle
       initial.sound initial.ready.semantic.ready.semantic.1.normal.facts.coherent inherited resident domain started
     have runningStored : Stored running := by simpa only [started] using stored.beginEdge request
     have actualWork := ih inventory (checks.restrict (.edge_evaluate started body)) runningContext
       owner.inherited owner.input ownerDomain runningStored rows arity bound limits
       (by simpa only [same] using profile) (by simpa only [same] using guards) (by simpa only [same] using bounded)
     have components := beginEdge_components request before
     rw [started] at components
     dsimp only at components
     simpa only [finishEdge, components.1] using actualWork
   · intro budget edge loaded inherited before result checked fourth merge actual memos final field parentReads
     intro inventory checks initial inheritedReady resident domain stored rows arity bound limits profile guards bounded
     exact SourceCurrentAllocatedFiniteOrdinaryActualParentWork.edge_body $formulas $solver
       (EdgeBodyReads.parent (field := field) parentReads) inventory initial inheritedReady resident stored
       limits rows arity bound guards profile bounded
   · intro budget inherited before memos inventory checks initial inheritedReady resident domain stored
     intro rows arity bound limits profile guards bounded
     simpa only [List.length_nil, Nat.zero_mul] using WorkBounds.refl before.checked.native.machine.heap
   · intro budget inherited original before narrowed middle first memos edgeMemos result afterChildren child childMemos
     intro originals results after tail final edgeReads childrenReads tailReads ihEdge ihChildren ihTail
     intro inventory checks initial inheritedReady resident domain stored rowLimit arity bound limits profile guards bounded
     cases domain with
     | cons firstDomain restDomain =>
         have edgeChecks := checks.restrict (.rows_edge first child tail)
         have firstWork := ihEdge inventory edgeChecks initial inheritedReady (resident original List.mem_cons_self) firstDomain stored
           rowLimit arity bound limits profile.1 guards.1 (Nat.le_trans (Nat.le_max_left _ _) bounded)
         have produced := SourceCurrentAllocatedFiniteOrdinaryOuterEdgeShapes.edge_call $formulas $solver edgeReads inventory
           initial inheritedReady (resident original List.mem_cons_self) firstDomain stored
         obtain ⟨edgeInventory, edgePost, narrowedResident, _⟩ := SourceCurrentAllocatedPartialActual.edge_call $formulas $solver edgeReads
           inventory edgeChecks initial inheritedReady (resident original List.mem_cons_self)
         have narrowedProfile := produced.2.2 rowLimit arity bound limits profile.1 guards.1 (Nat.le_trans (Nat.le_max_left _ _) bounded)
         have childChecks := checks.restrict (.rows_descendants first child tail)
         have childWork := ihChildren edgeInventory childChecks edgePost.context
           (inheritedReady.grows edgePost.effects.grows.constraint_growth) narrowedResident produced.2.1.1 produced.1
           (parentRows limits rowLimit arity bound) (max arity 1) bound (parentGuards limits)
           narrowedProfile.1 narrowedProfile.2 (Nat.le_trans produced.2.1.2 (Nat.le_trans (Nat.le_max_left _ _) bounded))
         have childProduced := SourceCurrentAllocatedFiniteOrdinaryOuterQuantitativeProducer.descendants $formulas $solver childrenReads edgeInventory
           edgePost.context (inheritedReady.grows edgePost.effects.grows.constraint_growth) narrowedResident produced.2.1.1 produced.1
         obtain ⟨childInventory, childPost, resultResident, _⟩ := SourceCurrentAllocatedPartialActual.descendants $formulas $solver childrenReads
           edgeInventory childChecks edgePost.context (inheritedReady.grows edgePost.effects.grows.constraint_growth) narrowedResident
         have firstPost := edgePost.trans childPost
         have tailWork := ihTail childInventory (checks.restrict (.rows_tail first child tail)) childPost.context
           (inheritedReady.grows firstPost.effects.grows.constraint_growth)
           (edges_grow firstPost.effects (fun edge member => resident edge (List.mem_cons_of_mem _ member))) restDomain childProduced.1
           rowLimit arity bound limits profile.2 guards.2 (Nat.le_trans (Nat.le_max_right _ _) bounded)
         simpa only [descendantsNodes, descendantsEdges, rowNodes, rowEdges, List.length_cons,
           Nat.add_mul, Nat.one_mul, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using firstWork.trans (childWork.trans tailWork)
   · intro budget payload edge before inherited results middle children memos final combined childReads ih
     intro inventory checks initial inheritedReady resident domain stored rows arity bound limits profile guards bounded
     obtain ⟨prefixReceipt, prefixPost⟩ := SourceCurrentAllocatedPartialStepEffects.inherited_prefix $formulas $solver
       inventory before memos initial edge inherited payload resident inheritedReady combined
     have prefixStored : Stored (prefixState before edge inherited) := stored.advancePhysical _
     have inputs := initial.ready.semantic.ready.semantic.1.normal.facts.cached.edges edge.entry.key edge resident
     have actualWork := ih inventory (checks.restrict (.descendants_children combined children)) prefixPost.context prefixReceipt.combinedReady
       (values_grow prefixPost.effects inputs) domain prefixStored rows arity bound limits
       (EdgeShape.children edge profile) (SourceCurrentAllocatedFiniteOrdinaryGuardProfiles.Edge.children edge guards)
       (by simpa only [SourceCurrentAllocatedFiniteOrdinaryDomain.edgeHeight_children] using bounded)
     have returned := actualWork.trans (edge_work edge results middle.checked)
     apply returned.mono
     · simpa only [descendantsNodes, Nat.add_zero] using Nat.mul_le_mul_right (nodeNodes rows arity limits bound) (EdgeShape.arity edge profile)
     · have enough := Nat.mul_le_mul_right (nodeEdges rows arity limits bound) (EdgeShape.arity edge profile)
       change edge.children.length * nodeEdges rows arity limits bound + 1 ≤ 1 + arity * nodeEdges rows arity limits bound
       omega
   · intro budget values before memos inventory checks initial inherited available domain stored
     intro rows arity bound limits profile guards bounded
     exact (WorkBounds.refl _).mono (Nat.zero_le _) (Nat.zero_le _)
   · intro budget identity records values before results after actual memos final walkReads ih
     intro inventory checks initial inherited available domain stored
     exact ih inventory (checks.restrict (.children_walk actual)) initial inherited available domain stored
   · intro budget combined index before memos inventory checks initial inherited available domain stored
     intro rows arity bound limits profile guards bounded
     simpa only [List.length_nil, Nat.zero_mul] using WorkBounds.refl before.checked.native.machine.heap
   · intro budget before combined index value result middle first memos headMemos values results after tail final headReads tailReads ihHead ihTail
     intro inventory checks initial inherited available domain stored rowLimit arity bound limits profile guards bounded
     cases domain with
     | cons firstDomain restDomain =>
         obtain ⟨descentReceipt, descentPost⟩ := SourceCurrentAllocatedPartialStepEffects.descent $formulas $solver
           inventory before memos initial combined index inherited
         have descentStored : Stored (descend before combined index).2 := stored.advancePhysical _
         have headChecks := checks.restrict (.walk_head first tail)
         have firstWork := ihHead inventory headChecks descentPost.context descentReceipt.inherited
           (descentPost.effects.keeps.available _ (available value List.mem_cons_self)) firstDomain descentStored
           rowLimit arity bound limits profile.1 guards.1 (Nat.le_trans (Nat.le_max_left _ _) bounded)
         have produced := SourceCurrentAllocatedFiniteOrdinaryOuterQuantitativeProducer.node_call $formulas $solver headReads inventory
           descentPost.context descentReceipt.inherited (descentPost.effects.keeps.available _ (available value List.mem_cons_self)) firstDomain descentStored
         obtain ⟨headInventory, headPost, resultAvailable, _⟩ := SourceCurrentAllocatedPartialActual.node_call $formulas $solver headReads
           inventory headChecks descentPost.context descentReceipt.inherited
           (descentPost.effects.keeps.available _ (available value List.mem_cons_self))
         have firstPost := descentPost.trans headPost
         have tailWork := ihTail headInventory (checks.restrict (.walk_tail first tail)) headPost.context
           (inherited.grows firstPost.effects.grows.constraint_growth)
           (values_grow firstPost.effects (fun child member => available child (List.mem_cons_of_mem _ member))) restDomain produced.1
           rowLimit arity bound limits profile.2 guards.2 (Nat.le_trans (Nat.le_max_right _ _) bounded)
         have nativeSame := (SourceCurrentAllocatedPartialDescent.components before combined index).2.1
         simpa only [nativeSame, List.length_cons, Nat.add_mul, Nat.one_mul, Nat.add_comm] using firstWork.trans tailWork))

/-- The same actual node call reads produce the ordered constructor trace within the initial envelope. -/
theorem node_call {request : NodeRequest} {before after : Caller width} {result : Node}
    {actual : NodeCall budget request before result after} {memos final : Memos}
    (reads : NodeCallReads formulas solver actual memos final) (inventory : Inventory)
    (initial : Context formulas solver inventory before memos)
    (inherited : EqReady before.checked.operations.constraints request.inherited)
    (available : Available before.checked.native.machine.heap request.value) (domain : DNode request.value) (stored : Stored before)
    (rows arity bound : Nat) (limits : Limits) (profile : NodeShape rows arity request.value)
    (guards : GPNode limits request.value) (heightBound : height request.value ≤ bound) :
    WorkBounds before.checked.native.machine.heap after.checked.native.machine.heap
      (nodeNodes rows arity limits bound) (nodeEdges rows arity limits bound) := by
  have checks := (SourceCurrentAllocatedFiniteOrdinaryOuterVerification.node_call formulas solver
    reads inventory initial inherited available domain stored.structural).1
  have bounded : NodeBound formulas solver (nodeCallTrace actual) request before result after memos final := by
    structural_induction NodeCallReads.rec reads formulas solver
  exact bounded inventory checks initial inherited available domain stored rows arity bound limits profile guards heightBound

/-- The same actual node body reads produce the ordered constructor trace within the initial envelope. -/
theorem node_body {request : NodeRequest} {before after : Caller width} {result : Node}
    {actual : NodeBody budget request before result after} {memos final : Memos}
    (reads : NodeBodyReads formulas solver actual memos final) (inventory : Inventory)
    (initial : Context formulas solver inventory before memos)
    (inherited : EqReady before.checked.operations.constraints request.inherited)
    (available : Available before.checked.native.machine.heap request.value) (domain : DNode request.value) (stored : Stored before)
    (rows arity bound : Nat) (limits : Limits) (profile : NodeShape rows arity request.value)
    (guards : GPNode limits request.value) (heightBound : height request.value ≤ bound) :
    WorkBounds before.checked.native.machine.heap after.checked.native.machine.heap
      (nodeNodes rows arity limits bound) (nodeEdges rows arity limits bound) := by
  have checks := (SourceCurrentAllocatedFiniteOrdinaryOuterVerification.node_body formulas solver
    reads inventory initial inherited available domain stored.structural).1
  have bounded : NodeBound formulas solver (nodeBodyTrace actual) request before result after memos final := by
    structural_induction NodeBodyReads.rec reads formulas solver
  exact bounded inventory checks initial inherited available domain stored rows arity bound limits profile guards heightBound

/-- The same actual edge call reads produce the ordered constructor trace within the initial envelope. -/
theorem edge_call {request : EdgeRequest} {before after : Caller width} {result : Edge}
    {actual : EdgeCall budget request before result after} {memos final : Memos}
    (reads : EdgeCallReads formulas solver actual memos final) (inventory : Inventory)
    (initial : Context formulas solver inventory before memos)
    (inherited : EqReady before.checked.operations.constraints request.inherited)
    (available : Resident before.checked.native.machine.heap request.value) (domain : DEdge request.value) (stored : Stored before)
    (rows arity bound : Nat) (limits : Limits) (profile : EdgeShape rows arity request.value)
    (guards : GPEdge limits request.value) (heightBound : edgeHeight request.value ≤ bound) :
    WorkBounds before.checked.native.machine.heap after.checked.native.machine.heap
      (nodeBudget limits rows arity bound) (edgeBudget limits rows arity bound) := by
  have checks := (SourceCurrentAllocatedFiniteOrdinaryOuterVerification.edge_call formulas solver
    reads inventory initial inherited available domain stored.structural).1
  have bounded : EdgeBound formulas solver (edgeCallTrace actual) request before result after memos final := by
    structural_induction EdgeCallReads.rec reads formulas solver
  exact bounded inventory checks initial inherited available domain stored rows arity bound limits profile guards heightBound

/-- The same actual edge body reads produce the ordered constructor trace within the initial envelope. -/
theorem edge_body {request : EdgeRequest} {before after : Caller width} {result : Edge}
    {actual : EdgeBody budget request before result after} {memos final : Memos}
    (reads : EdgeBodyReads formulas solver actual memos final) (inventory : Inventory)
    (initial : Context formulas solver inventory before memos)
    (inherited : EqReady before.checked.operations.constraints request.inherited)
    (available : Resident before.checked.native.machine.heap request.value) (domain : DEdge request.value) (stored : Stored before)
    (rows arity bound : Nat) (limits : Limits) (profile : EdgeShape rows arity request.value)
    (guards : GPEdge limits request.value) (heightBound : edgeHeight request.value ≤ bound) :
    WorkBounds before.checked.native.machine.heap after.checked.native.machine.heap
      (nodeBudget limits rows arity bound) (edgeBudget limits rows arity bound) := by
  have checks := (SourceCurrentAllocatedFiniteOrdinaryOuterVerification.edge_body formulas solver
    reads inventory initial inherited available domain stored.structural).1
  have bounded : EdgeBound formulas solver (edgeBodyTrace actual) request before result after memos final := by
    structural_induction EdgeBodyReads.rec reads formulas solver
  exact bounded inventory checks initial inherited available domain stored rows arity bound limits profile guards heightBound

/-- The same actual rows reads produce the ordered constructor trace within the initial envelope. -/
theorem rows {inherited : EqValue} {values results : List Edge} {before after : Caller width}
    {actual : Rows budget inherited values before results after} {memos final : Memos}
    (reads : RowsReads formulas solver actual memos final) (inventory : Inventory)
    (initial : Context formulas solver inventory before memos)
    (inheritedReady : EqReady before.checked.operations.constraints inherited)
    (available : Edges before.checked.native.machine.heap values) (domain : DRows values) (stored : Stored before)
    (rowLimit arity bound : Nat) (limits : Limits) (profile : RowsShape rowLimit arity values)
    (guards : GPRows limits values) (heightBound : edgesHeight values ≤ bound) :
    WorkBounds before.checked.native.machine.heap after.checked.native.machine.heap
      (values.length * rowNodes rowLimit arity limits bound) (values.length * rowEdges rowLimit arity limits bound) := by
  have checks := (SourceCurrentAllocatedFiniteOrdinaryOuterVerification.rows formulas solver
    reads inventory initial inheritedReady available domain stored.structural).1
  have bounded : RowsBound formulas solver actual memos final := by
    structural_induction RowsReads.rec reads formulas solver
  exact bounded inventory checks initial inheritedReady available domain stored rowLimit arity bound limits profile guards heightBound

/-- The same actual descendants reads produce the ordered constructor trace within the initial envelope. -/
theorem descendants {inherited : EqValue} {value result : Edge} {before after : Caller width}
    {actual : Descendants budget inherited value before result after} {memos final : Memos}
    (reads : DescendantsReads formulas solver actual memos final) (inventory : Inventory)
    (initial : Context formulas solver inventory before memos)
    (inheritedReady : EqReady before.checked.operations.constraints inherited)
    (available : Resident before.checked.native.machine.heap value) (domain : DEdge value) (stored : Stored before)
    (rows arity bound : Nat) (limits : Limits) (profile : EdgeShape rows arity value)
    (guards : GPEdge limits value) (heightBound : edgeHeight value ≤ bound) :
    WorkBounds before.checked.native.machine.heap after.checked.native.machine.heap
      (descendantsNodes rows arity limits bound) (descendantsEdges rows arity limits bound) := by
  have checks := (SourceCurrentAllocatedFiniteOrdinaryOuterVerification.descendants formulas solver
    reads inventory initial inheritedReady available domain stored.structural).1
  have bounded : DescendantsBound formulas solver actual memos final := by
    structural_induction DescendantsReads.rec reads formulas solver
  exact bounded inventory checks initial inheritedReady available domain stored rows arity bound limits profile guards heightBound

/-- The same actual children reads produce the ordered constructor trace within the initial envelope. -/
theorem children {combined : EqValue} {values results : List Node} {before after : Caller width}
    {actual : Children budget combined values before results after} {memos final : Memos}
    (reads : ChildrenReads formulas solver actual memos final) (inventory : Inventory)
    (initial : Context formulas solver inventory before memos)
    (inheritedReady : EqReady before.checked.operations.constraints combined)
    (available : Values before.checked.native.machine.heap values) (domain : DChildren values) (stored : Stored before)
    (rows arity bound : Nat) (limits : Limits) (profile : ChildrenShape rows arity values)
    (guards : GPChildren limits values) (heightBound : childrenHeight values ≤ bound) :
    WorkBounds before.checked.native.machine.heap after.checked.native.machine.heap
      (values.length * nodeNodes rows arity limits bound) (values.length * nodeEdges rows arity limits bound) := by
  have checks := (SourceCurrentAllocatedFiniteOrdinaryOuterVerification.children formulas solver
    reads inventory initial inheritedReady available domain stored.structural).1
  have bounded : ChildrenBound formulas solver actual memos final := by
    structural_induction ChildrenReads.rec reads formulas solver
  exact bounded inventory checks initial inheritedReady available domain stored rows arity bound limits profile guards heightBound

/-- The same actual walk reads produce the ordered constructor trace within the initial envelope. -/
theorem walk {combined : EqValue} {index : Nat} {values results : List Node} {before after : Caller width}
    {actual : Walk budget combined index values before results after} {memos final : Memos}
    (reads : WalkReads formulas solver actual memos final) (inventory : Inventory)
    (initial : Context formulas solver inventory before memos)
    (inheritedReady : EqReady before.checked.operations.constraints combined)
    (available : Values before.checked.native.machine.heap values) (domain : DChildren values) (stored : Stored before)
    (rows arity bound : Nat) (limits : Limits) (profile : ChildrenShape rows arity values)
    (guards : GPChildren limits values) (heightBound : childrenHeight values ≤ bound) :
    WorkBounds before.checked.native.machine.heap after.checked.native.machine.heap
      (values.length * nodeNodes rows arity limits bound) (values.length * nodeEdges rows arity limits bound) := by
  have checks := (SourceCurrentAllocatedFiniteOrdinaryOuterVerification.walk formulas solver
    reads inventory initial inheritedReady available domain stored.structural).1
  have bounded : WalkBound formulas solver actual memos final := by
    structural_induction WalkReads.rec reads formulas solver
  exact bounded inventory checks initial inheritedReady available domain stored rows arity bound limits profile guards heightBound

end MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryActualOuterWork
