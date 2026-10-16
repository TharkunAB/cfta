import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryOuterEdgeShapes
import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryGuardConstructors

/-!
# Quantitative certificates from actual outer reads

The induction follows the same stored owner and each earlier returned prefix.
A parent returns before its children are traversed.
Each finish installs the law derived from that owner's smaller body reads.
The proof needs no future profile, resource headroom, or completed enclosing call.
-/
namespace MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryOuterQuantitativeProducer
open Cache Language InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values Edges)
open SourceCurrentAllocatedPartialState SourceCurrentAllocatedPartialGraph
open SourceCurrentAllocatedPartialSourceReads SourceCurrentAllocatedPartialChecks
open SourceCurrentAllocatedPartialInvariant (Context)
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedNativeEffects (physical)
open SourceCurrentAllocatedFiniteOrdinaryRequired (NodeNarrow EdgeNarrow)
open SourceCurrentAllocatedFiniteOrdinaryNativeProfile (NodeShape RowsShape EdgeShape ChildrenShape)
open SourceCurrentAllocatedFiniteOrdinaryOuterQuantitativeState (Stored)
open SourceCurrentAllocatedFiniteOrdinaryOuterQuantitativeReturned (NodeCertificate EdgeCertificate)
open SourceCurrentAllocatedFiniteOrdinaryOuterProfileNumbers (nodeRows nodeGuards)
open SourceCurrentAllocatedFiniteOrdinaryParentUniformNumbers (parentRows)
open SourceCurrentAllocatedFiniteOrdinaryGuardEnvelope (Limits)
open MergedOrdinaryHeight (height edgeHeight edgesHeight childrenHeight)
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
local notation "GPNode" => SourceCurrentAllocatedFiniteOrdinaryGuardProfiles.Node
local notation "GPRows" => SourceCurrentAllocatedFiniteOrdinaryGuardProfiles.Rows
local notation "GPEdge" => SourceCurrentAllocatedFiniteOrdinaryGuardProfiles.Edge
local notation "GPChildren" => SourceCurrentAllocatedFiniteOrdinaryGuardProfiles.Children
local notation "parentGuards" => SourceCurrentAllocatedFiniteOrdinaryGuardParent.outputLimit
variable {width budget : Nat}

/-- Original child positions share one input envelope through their ordered calls. -/
def ChildrenCertificate (values results : List Node) : Prop :=
  ∀ rows arity bound (limits : Limits), ChildrenShape rows arity values → GPChildren limits values →
    childrenHeight values ≤ bound → ChildrenShape (nodeRows rows arity limits bound) (max arity 1) results ∧
      GPChildren (nodeGuards rows arity limits bound) results

/-- Descendant rebuilding retains the returned raw field and traverses its returned children. -/
def DescendantsCertificate (value result : Edge) : Prop :=
  ∀ rows arity bound (limits : Limits), EdgeShape rows arity value → GPEdge limits value →
    edgeHeight value ≤ bound → EdgeShape (nodeRows rows arity limits bound) (max arity 1) result ∧
      GPEdge (nodeGuards rows arity limits bound) result

/-- Each original row runs its parent before traversal of the returned children. -/
def RowsCertificate (values results : List Edge) : Prop :=
  ∀ rows arity bound (limits : Limits), RowsShape rows arity values → GPRows limits values →
    edgesHeight values ≤ bound →
    RowsShape (nodeRows (parentRows limits rows arity bound) (max arity 1) (parentGuards limits) bound)
      (max arity 1) results ∧
    GPRows (nodeGuards (parentRows limits rows arity bound) (max arity 1) (parentGuards limits) bound) results

private theorem erased_profiles (values : List Node) (rows arity : Nat) (limits : Limits) :
    ChildrenShape rows arity (EqualityLeafProjectionRuntimeEmpty.erase values) ∧
      GPChildren limits (EqualityLeafProjectionRuntimeEmpty.erase values) := by
  induction values with
  | nil => exact ⟨True.intro, True.intro⟩
  | cons value rest ih => exact ⟨⟨True.intro, ih.1⟩, True.intro, ih.2⟩

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

private theorem modify_profile
    (entry : Interned InternedBinderProtocol.NodeKey) (oldRows newRows : List Edge)
    (depth : Nat) (free : List InternedBinderProtocol.Reference) (before : SourceEqualityNativeDemand.State width)
    (coherent : InternedRecordCoherence.Coherent before.native.machine.heap)
    (linked : InternedEdgeResidency.Linked before.native.machine.heap)
    (available : Available before.native.machine.heap (.node entry oldRows depth free))
    (resident : Edges before.native.machine.heap newRows)
    (rows arity : Nat) (limits : Limits) (profile : RowsShape rows arity newRows)
    (lengthBound : newRows.length ≤ rows) (guards : GPRows limits newRows) :
    NodeShape rows arity (SourceCurrentAllocatedRawRebuild.modify (.node entry oldRows depth free) oldRows newRows before).1 ∧
      GPNode limits (SourceCurrentAllocatedRawRebuild.modify (.node entry oldRows depth free) oldRows newRows before).1 := by
  by_cases same : newRows.map (fun edge => edge.entry.identity) = oldRows.map (fun edge => edge.entry.identity)
  · have oldResident := InternedEdgeResidency.resident_edges _ linked _ available.resident
    have equal := InternedEdgeResidency.edge_lists_equal _ coherent newRows oldRows resident oldResident same
    rw [SourceCurrentAllocatedRawRebuild.modify_unchanged _ _ _ _ same]
    rw [← equal]
    exact ⟨⟨lengthBound, profile⟩, guards⟩
  · simp only [SourceCurrentAllocatedRawRebuild.modify, SourceEqualityPartialNodeRebuild.modify, same, ↓reduceIte]
    exact ⟨SourceCurrentAllocatedFiniteOrdinaryOutputConstructors.makeNode newRows _ coherent linked resident profile lengthBound,
      SourceCurrentAllocatedFiniteOrdinaryGuardConstructors.makeNode newRows _ coherent linked resident guards⟩

variable [DecidableEq Symbol] [DecidableEq Node]

private def NodeBound (top : Trace width budget) (request : NodeRequest) (before : Caller width)
    (result : Node) (after : Caller width) (memos _final : Memos) : Prop :=
  ∀ inventory, Checks top → Context formulas solver inventory before memos →
    EqReady before.checked.operations.constraints request.inherited → Available before.checked.native.machine.heap request.value →
    DNode request.value → Stored before → Stored after ∧ NodeNarrow request.value result ∧ NodeCertificate request result

private def EdgeBound (top : Trace width budget) (request : EdgeRequest) (before : Caller width)
    (result : Edge) (after : Caller width) (memos _final : Memos) : Prop :=
  ∀ inventory, Checks top → Context formulas solver inventory before memos →
    EqReady before.checked.operations.constraints request.inherited → Resident before.checked.native.machine.heap request.value →
    DEdge request.value → Stored before → Stored after ∧ EdgeNarrow request.value result ∧ EdgeCertificate request result

private def RowsBound {inherited : EqValue} {values results : List Edge} {before after : Caller width}
    (actual : Rows budget inherited values before results after) (memos _final : Memos) : Prop :=
  ∀ inventory, Checks (rowsTrace actual) → Context formulas solver inventory before memos →
    EqReady before.checked.operations.constraints inherited → Edges before.checked.native.machine.heap values →
    DRows values → Stored before → Stored after ∧ All₂ EdgeNarrow values results ∧ RowsCertificate values results

private def DescendantsBound {inherited : EqValue} {value result : Edge} {before after : Caller width}
    (actual : Descendants budget inherited value before result after) (memos _final : Memos) : Prop :=
  ∀ inventory, Checks (descendantsTrace actual) → Context formulas solver inventory before memos →
    EqReady before.checked.operations.constraints inherited → Resident before.checked.native.machine.heap value →
    DEdge value → Stored before → Stored after ∧ EdgeNarrow value result ∧ DescendantsCertificate value result

private def ChildrenBound {combined : EqValue} {values results : List Node} {before after : Caller width}
    (actual : Children budget combined values before results after) (memos _final : Memos) : Prop :=
  ∀ inventory, Checks (childrenTrace actual) → Context formulas solver inventory before memos →
    EqReady before.checked.operations.constraints combined → Values before.checked.native.machine.heap values →
    DChildren values → Stored before → Stored after ∧ All₂ NodeNarrow values results ∧ ChildrenCertificate values results

private def WalkBound {combined : EqValue} {index : Nat} {values results : List Node} {before after : Caller width}
    (actual : Walk budget combined index values before results after) (memos _final : Memos) : Prop :=
  ∀ inventory, Checks (walkTrace actual) → Context formulas solver inventory before memos →
    EqReady before.checked.operations.constraints combined → Values before.checked.native.machine.heap values →
    DChildren values → Stored before → Stored after ∧ All₂ NodeNarrow values results ∧ ChildrenCertificate values results

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
     have quantitative := stored.node_ready $formulas $solver request after handle result initial.sound
       initial.ready.semantic.ready.semantic.1.normal.facts.coherent available started
     have narrowed := stored.structural.node_ready $formulas $solver request after handle result initial.sound
       initial.ready.semantic.ready.semantic.1.normal.facts.coherent available domain started
     exact ⟨quantitative.1.symm ▸ stored, narrowed.2, quantitative.2⟩
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
     refine ⟨resultBound.1.finishNode result (frame.node_running handle original cell) (fun _ => resultBound.2.1) resultBound.2.2, ?_, ?_⟩
     · simpa only [same] using resultBound.2.1
     · simpa only [NodeCertificate, same] using resultBound.2.2
   · intro budget inherited before memos inventory checks initial inheritedReady available domain stored
     exact ⟨stored, SourceCurrentAllocatedFiniteOrdinaryNarrow.node_refl domain, by intro rows arity bound limits profile guards bounded; exact ⟨True.intro, True.intro⟩⟩
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
     have base := SourceCurrentAllocatedFiniteOrdinaryOuterGuardStores.node_body $formulas $solver
       (NodeBodyReads.ordinary rowsReads) inventory initial inheritedReady available domain stored.base
     refine ⟨⟨base.1, resultBound.1.returned.advance _ _ _⟩, base.2, ?_⟩
     intro rowLimit arity bound limits profile guards bounded
     cases bound with
     | zero => simp only [height] at bounded; omega
     | succ bound =>
         have edgeBound : edgesHeight edges ≤ bound := Nat.le_of_add_le_add_right bounded
         have produced := resultBound.2.2 rowLimit arity bound limits profile.2 guards edgeBound
         have facts := post.context.ready.semantic.ready.semantic.1.normal.facts
         have shaped := modify_profile entry edges results depth free middle.checked facts.coherent facts.linked
           (post.effects.keeps.available _ available) rowsResident
           (nodeRows rowLimit arity limits (bound + 1)) (max arity 1)
           (nodeGuards rowLimit arity limits (bound + 1))
           (RowsShape.mono results produced.1 (Nat.le_max_right _ _) (Nat.le_refl _))
           (by rw [rows.length]; exact Nat.le_trans profile.1 (Nat.le_max_left _ _)) produced.2
         exact shaped
   · intro budget request before handle result after started memos inventory checks initial inherited resident domain stored
     exact SourceCurrentAllocatedFiniteOrdinaryOuterEdgeShapes.edge_call $formulas $solver
       (EdgeCallReads.hit (budget := budget) (started := started)) inventory initial inherited resident domain stored
   · intro budget original running result middle body memos final request before handle started bodyReads _ih
     intro inventory checks initial inherited resident domain stored
     exact SourceCurrentAllocatedFiniteOrdinaryOuterEdgeShapes.edge_call $formulas $solver
       (EdgeCallReads.evaluate (started := started) bodyReads) inventory initial inherited resident domain stored
   · intro budget edge loaded inherited before result checked fourth merge actual memos final field parentReads
     intro inventory checks initial inheritedReady resident domain stored
     exact SourceCurrentAllocatedFiniteOrdinaryOuterEdgeShapes.edge_body $formulas $solver
       (EdgeBodyReads.parent (field := field) parentReads) inventory initial inheritedReady resident domain stored
   · intro budget inherited before memos inventory checks initial inheritedReady resident domain stored
     exact ⟨stored, .nil, by intro rows arity bound limits profile guards bounded; exact ⟨True.intro, True.intro⟩⟩
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
           (inheritedReady.grows edgePost.effects.grows.constraint_growth) narrowedResident firstBound.2.1.1 firstBound.1
         obtain ⟨childInventory, childPost, resultResident, _⟩ := SourceCurrentAllocatedPartialActual.descendants $formulas $solver childrenReads
           edgeInventory childChecks edgePost.context (inheritedReady.grows edgePost.effects.grows.constraint_growth) narrowedResident
         have firstPost := edgePost.trans childPost
         have tailBound := ihTail childInventory (checks.restrict (.rows_tail first child tail)) childPost.context
           (inheritedReady.grows firstPost.effects.grows.constraint_growth)
           (edges_grow firstPost.effects (fun edge member => resident edge (List.mem_cons_of_mem _ member))) restDomain childBound.1
         refine ⟨tailBound.1, .cons (SourceCurrentAllocatedFiniteOrdinaryNarrow.edge_trans firstBound.2.1 childBound.2.1) tailBound.2.1, ?_⟩
         intro rowLimit arity bound limits profile guards bounded
         have firstShape := firstBound.2.2 rowLimit arity bound limits profile.1 guards.1 (Nat.le_trans (Nat.le_max_left _ _) bounded)
         have childrenShape := childBound.2.2 _ _ bound _ firstShape.1 firstShape.2
           (Nat.le_trans firstBound.2.1.2 (Nat.le_trans (Nat.le_max_left _ _) bounded))
         have tailShape := tailBound.2.2 rowLimit arity bound limits profile.2 guards.2 (Nat.le_trans (Nat.le_max_right _ _) bounded)
         exact ⟨⟨by simpa only [Nat.max_assoc, Nat.max_self] using childrenShape.1, tailShape.1⟩,
           childrenShape.2, tailShape.2⟩
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
     have base := SourceCurrentAllocatedFiniteOrdinaryOuterGuardStores.descendants $formulas $solver
       (DescendantsReads.run (combined := combined) childReads) inventory initial inheritedReady resident domain stored.base
     refine ⟨⟨base.1, childBound.1.returned.advance _ _ _⟩, base.2, ?_⟩
     intro rowLimit arity bound limits profile guards bounded
     have produced := childBound.2.2 rowLimit arity bound limits (EdgeShape.children edge profile)
       (SourceCurrentAllocatedFiniteOrdinaryGuardProfiles.Edge.children edge guards)
       (by simpa only [SourceCurrentAllocatedFiniteOrdinaryDomain.edgeHeight_children] using bounded)
     have facts := childPost.context.ready.semantic.ready.semantic.1.normal.facts
     have numeric := SourceCurrentAllocatedFiniteOrdinaryOutputConstructors.makeEdge edge.entry.key.symbol edge.entry.key.constraint
       results middle.checked.native.machine.heap facts.coherent facts.cached available produced.1
       (by rw [children.length]; exact Nat.le_trans (EdgeShape.arity edge profile) (Nat.le_max_left _ _))
     have guarded := SourceCurrentAllocatedFiniteOrdinaryGuardConstructors.makeEdge edge.entry.key.symbol edge.entry.key.constraint
       results middle.checked.native.machine.heap facts.coherent facts.cached available
       (SourceCurrentAllocatedFiniteOrdinaryGuardLimits.bounds_mono edge.entry.key.constraint
         (SourceCurrentAllocatedFiniteOrdinaryGuardProfiles.Edge.guard edge guards)
         (SourceCurrentAllocatedFiniteOrdinaryOuterProfileNumbers.nodeGuards_ge rowLimit arity limits bound)) produced.2
     exact ⟨numeric, guarded⟩
   · intro budget values before memos inventory checks initial inherited available domain stored
     refine ⟨stored, SourceCurrentAllocatedFiniteOrdinaryNarrow.forest_erase values, ?_⟩
     intro rows arity bound limits profile guards bounded
     exact erased_profiles values _ _ _
   · intro budget identity records values before results after actual memos final walkReads ih
     intro inventory checks initial inherited available domain stored
     exact ih inventory (checks.restrict (.children_walk actual)) initial inherited available domain stored
   · intro budget combined index before memos inventory checks initial inherited available domain stored
     exact ⟨stored, .nil, by intro rows arity bound limits profile guards bounded; exact ⟨True.intro, True.intro⟩⟩
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
         refine ⟨tailBound.1, .cons headBound.2.1 tailBound.2.1, ?_⟩
         intro rowLimit arity bound limits profile guards bounded
         have firstShape := headBound.2.2 rowLimit arity bound limits profile.1 guards.1 (Nat.le_trans (Nat.le_max_left _ _) bounded)
         have tailShape := tailBound.2.2 rowLimit arity bound limits profile.2 guards.2 (Nat.le_trans (Nat.le_max_right _ _) bounded)
         exact ⟨⟨firstShape.1, tailShape.1⟩, firstShape.2, tailShape.2⟩))

/-- Supplied actual node call reads derive universal quantitative profiles and retain the same complete state stores. -/
theorem node_call {request : NodeRequest} {before after : Caller width} {result : Node}
    {actual : NodeCall budget request before result after} {memos final : Memos}
    (reads : NodeCallReads formulas solver actual memos final) (inventory : Inventory)
    (initial : Context formulas solver inventory before memos)
    (inherited : EqReady before.checked.operations.constraints request.inherited)
    (available : Available before.checked.native.machine.heap request.value) (domain : DNode request.value) (stored : Stored before) :
    Stored after ∧ NodeNarrow request.value result ∧ NodeCertificate request result := by
  have checks := (SourceCurrentAllocatedFiniteOrdinaryOuterVerification.node_call formulas solver
    reads inventory initial inherited available domain stored.structural).1
  have bounded : NodeBound formulas solver (nodeCallTrace actual) request before result after memos final := by
    structural_induction NodeCallReads.rec reads formulas solver
  exact bounded inventory checks initial inherited available domain stored

/-- Supplied actual node body reads derive universal quantitative profiles and retain the same complete state stores. -/
theorem node_body {request : NodeRequest} {before after : Caller width} {result : Node}
    {actual : NodeBody budget request before result after} {memos final : Memos}
    (reads : NodeBodyReads formulas solver actual memos final) (inventory : Inventory)
    (initial : Context formulas solver inventory before memos)
    (inherited : EqReady before.checked.operations.constraints request.inherited)
    (available : Available before.checked.native.machine.heap request.value) (domain : DNode request.value) (stored : Stored before) :
    Stored after ∧ NodeNarrow request.value result ∧ NodeCertificate request result := by
  have checks := (SourceCurrentAllocatedFiniteOrdinaryOuterVerification.node_body formulas solver
    reads inventory initial inherited available domain stored.structural).1
  have bounded : NodeBound formulas solver (nodeBodyTrace actual) request before result after memos final := by
    structural_induction NodeBodyReads.rec reads formulas solver
  exact bounded inventory checks initial inherited available domain stored

/-- Supplied actual rows reads derive universal quantitative profiles and retain the same complete state stores. -/
theorem rows {inherited : EqValue} {values results : List Edge} {before after : Caller width}
    {actual : Rows budget inherited values before results after} {memos final : Memos}
    (reads : RowsReads formulas solver actual memos final) (inventory : Inventory)
    (initial : Context formulas solver inventory before memos)
    (inheritedReady : EqReady before.checked.operations.constraints inherited)
    (available : Edges before.checked.native.machine.heap values) (domain : DRows values) (stored : Stored before) :
    Stored after ∧ All₂ EdgeNarrow values results ∧ RowsCertificate values results := by
  have checks := (SourceCurrentAllocatedFiniteOrdinaryOuterVerification.rows formulas solver
    reads inventory initial inheritedReady available domain stored.structural).1
  have bounded : RowsBound formulas solver actual memos final := by
    structural_induction RowsReads.rec reads formulas solver
  exact bounded inventory checks initial inheritedReady available domain stored

/-- Supplied actual descendants reads derive universal quantitative profiles and retain the same complete state stores. -/
theorem descendants {inherited : EqValue} {value result : Edge} {before after : Caller width}
    {actual : Descendants budget inherited value before result after} {memos final : Memos}
    (reads : DescendantsReads formulas solver actual memos final) (inventory : Inventory)
    (initial : Context formulas solver inventory before memos)
    (inheritedReady : EqReady before.checked.operations.constraints inherited)
    (available : Resident before.checked.native.machine.heap value) (domain : DEdge value) (stored : Stored before) :
    Stored after ∧ EdgeNarrow value result ∧ DescendantsCertificate value result := by
  have checks := (SourceCurrentAllocatedFiniteOrdinaryOuterVerification.descendants formulas solver
    reads inventory initial inheritedReady available domain stored.structural).1
  have bounded : DescendantsBound formulas solver actual memos final := by
    structural_induction DescendantsReads.rec reads formulas solver
  exact bounded inventory checks initial inheritedReady available domain stored

/-- Supplied actual children reads derive universal quantitative profiles and retain the same complete state stores. -/
theorem children {combined : EqValue} {values results : List Node} {before after : Caller width}
    {actual : Children budget combined values before results after} {memos final : Memos}
    (reads : ChildrenReads formulas solver actual memos final) (inventory : Inventory)
    (initial : Context formulas solver inventory before memos)
    (inheritedReady : EqReady before.checked.operations.constraints combined)
    (available : Values before.checked.native.machine.heap values) (domain : DChildren values) (stored : Stored before) :
    Stored after ∧ All₂ NodeNarrow values results ∧ ChildrenCertificate values results := by
  have checks := (SourceCurrentAllocatedFiniteOrdinaryOuterVerification.children formulas solver
    reads inventory initial inheritedReady available domain stored.structural).1
  have bounded : ChildrenBound formulas solver actual memos final := by
    structural_induction ChildrenReads.rec reads formulas solver
  exact bounded inventory checks initial inheritedReady available domain stored

/-- Supplied actual walk reads derive universal quantitative profiles and retain the same complete state stores. -/
theorem walk {combined : EqValue} {index : Nat} {values results : List Node} {before after : Caller width}
    {actual : Walk budget combined index values before results after} {memos final : Memos}
    (reads : WalkReads formulas solver actual memos final) (inventory : Inventory)
    (initial : Context formulas solver inventory before memos)
    (inheritedReady : EqReady before.checked.operations.constraints combined)
    (available : Values before.checked.native.machine.heap values) (domain : DChildren values) (stored : Stored before) :
    Stored after ∧ All₂ NodeNarrow values results ∧ ChildrenCertificate values results := by
  have checks := (SourceCurrentAllocatedFiniteOrdinaryOuterVerification.walk formulas solver
    reads inventory initial inheritedReady available domain stored.structural).1
  have bounded : WalkBound formulas solver actual memos final := by
    structural_induction WalkReads.rec reads formulas solver
  exact bounded inventory checks initial inheritedReady available domain stored

end MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryOuterQuantitativeProducer
