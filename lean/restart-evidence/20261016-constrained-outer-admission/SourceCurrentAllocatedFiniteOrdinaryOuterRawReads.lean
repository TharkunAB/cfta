import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryOuterNumericEntries
import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryOuterParentReads
import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryOuterVerification

/-!
# Strict reads from actual completed finite ordinary outer graphs

The mutual induction follows the supplied raw graph in source order.
Each earlier prefix constructs its own reads and derives the next context.
Numeric entry plans restrict to the exact reached request and state.
No enclosing completion or future physical or result law is supplied.
-/
namespace MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryOuterRawReads
open Cache Language InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
open InternedNestedProvenance (Values Edges)
open SourceCurrentAllocatedPartialState SourceCurrentAllocatedPartialGraph
open SourceCurrentAllocatedPartialSourceReads
open SourceCurrentAllocatedPartialInvariant (Context)
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedFiniteOrdinaryOuterState (Stored)
open SourceCurrentAllocatedFiniteOrdinaryOuterEntries (Entry)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "Edge" => EdgeValue Symbol Guard
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "EqValue" => SourceEqualityConstraintAllocation.Value
local notation "EqReady" => SourceEqualityConstraintAllocation.Ready
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "DNode" => SourceCurrentAllocatedFiniteOrdinaryDomain.Node
local notation "DEdge" => SourceCurrentAllocatedFiniteOrdinaryDomain.Edge
local notation "DChildren" => SourceCurrentAllocatedFiniteOrdinaryDomain.Children
local notation "DRows" => SourceCurrentAllocatedFiniteOrdinaryDomain.Rows
local notation "Plan" => SourceCurrentAllocatedFiniteOrdinaryOuterNumericEntries.Plan
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Node]
variable {bits budget : Nat}
variable (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)

private def NodeGoal (bits budget : Nat) (entry : Entry (bits + 2)) (request : NodeRequest) (before : Caller (bits + 2))
    (reads : Memos → Memos → Prop) : Prop :=
  ∀ inventory memos, Context formulas solver inventory before memos → EqReady before.checked.operations.constraints request.inherited →
    Available before.checked.native.machine.heap request.value → DNode request.value → Stored before →
    Plan bits budget entry → ∃ final, reads memos final

private def EdgeGoal (bits budget : Nat) (entry : Entry (bits + 2)) (request : EdgeRequest) (before : Caller (bits + 2))
    (reads : Memos → Memos → Prop) : Prop :=
  ∀ inventory memos, Context formulas solver inventory before memos → EqReady before.checked.operations.constraints request.inherited →
    EdgeResident before.checked.native.machine.heap request.value → DEdge request.value → Stored before →
    Plan bits budget entry → ∃ final, reads memos final

private def RowsGoal (bits budget : Nat) (inherited : EqValue) (values : List Edge) (before : Caller (bits + 2))
    (reads : Memos → Memos → Prop) : Prop :=
  ∀ inventory memos, Context formulas solver inventory before memos → EqReady before.checked.operations.constraints inherited →
    Edges before.checked.native.machine.heap values → DRows values → Stored before →
    Plan bits budget (.rows inherited values before) → ∃ final, reads memos final

private def ChildrenGoal (bits budget : Nat) (combined : EqValue) (values : List Node) (before : Caller (bits + 2))
    (entry : Entry (bits + 2)) (reads : Memos → Memos → Prop) : Prop :=
  ∀ inventory memos, Context formulas solver inventory before memos → EqReady before.checked.operations.constraints combined →
    Values before.checked.native.machine.heap values → DChildren values → Stored before →
    Plan bits budget entry → ∃ final, reads memos final

-- Each induction hypothesis constructs reads only for its actual smaller raw graph.
local macro "raw_reads_induction" recursor:ident actual:ident bits:ident formulas:ident solver:ident : tactic => `(tactic|
  (apply $recursor
    (motive_1 := fun request before _result _after own =>
      NodeGoal $formulas $solver $bits _ (.nodeCall request before) request before
        (fun memos final => NodeCallReads $formulas $solver own memos final))
    (motive_2 := fun request before _result _after own =>
      NodeGoal $formulas $solver $bits _ (.nodeBody request before) request before
        (fun memos final => NodeBodyReads $formulas $solver own memos final))
    (motive_3 := fun request before _result _after own =>
      EdgeGoal $formulas $solver $bits _ (.edgeCall request before) request before
        (fun memos final => EdgeCallReads $formulas $solver own memos final))
    (motive_4 := fun request before _result _after own =>
      EdgeGoal $formulas $solver $bits _ (.edgeBody request before) request before
        (fun memos final => EdgeBodyReads $formulas $solver own memos final))
    (motive_5 := fun inherited values before _results _after own =>
      RowsGoal $formulas $solver $bits _ inherited values before
        (fun memos final => RowsReads $formulas $solver own memos final))
    (motive_6 := fun inherited value before _result _after own =>
      EdgeGoal $formulas $solver $bits _ (.descendants inherited value before) ⟨inherited, value⟩ before
        (fun memos final => DescendantsReads $formulas $solver own memos final))
    (motive_7 := fun combined values before _results _after own =>
      ChildrenGoal $formulas $solver $bits _ combined values before (.children combined values before)
        (fun memos final => ChildrenReads $formulas $solver own memos final))
    (motive_8 := fun combined index values before _results _after own =>
      ChildrenGoal $formulas $solver $bits _ combined values before (.walk combined index values before)
        (fun memos final => WalkReads $formulas $solver own memos final))
    (t := $actual)
   · intro request before handle running result started inventory memos initial inherited available domain stored plan
     exact ⟨memos, .hit (started := started)⟩
   · intro request before handle running owner result middle started body ih
     intro inventory memos initial inherited available domain stored plan
     obtain ⟨current, good, _key, _cell⟩ := SourceCurrentAllocatedPartialCallSteps.node_start $formulas $solver
       initial inherited available started
     have ownerDomain := (SourceCurrentAllocatedFiniteOrdinaryOuterState.node_evaluate $formulas $solver request owner before running handle
       initial.sound initial.ready.semantic.ready.semantic.1.normal.facts.coherent inherited available domain started).2.1
     have runningStored : Stored running := by simpa only [started] using stored.beginNode request
     obtain ⟨final, reads⟩ := ih inventory memos current good.inherited good.input ownerDomain runningStored
       (plan.restrict (.direct (.node_evaluate started)))
     exact ⟨final, .evaluate (started := started) reads⟩
   · intro inherited before inventory memos initial inheritedReady available domain stored plan
     exact ⟨memos, .empty⟩
   · intro inherited entry members depth free before inventory memos initial inheritedReady available domain stored plan
     cases domain
   · intro entry body depth ordinary result heap inherited before actual inventory memos initial inheritedReady available domain stored plan
     cases domain
   · intro inherited edges before results middle entry depth free actual ih
     intro inventory memos initial inheritedReady available domain stored plan
     have resident := InternedEdgeResidency.resident_edges _ initial.ready.semantic.ready.semantic.1.normal.facts.linked _ available.resident
     obtain ⟨final, reads⟩ := ih inventory memos initial inheritedReady resident domain.rows stored
       (plan.restrict (.direct .node_ordinary))
     exact ⟨final, .ordinary reads⟩
   · intro request before handle running result started inventory memos initial inherited resident domain stored plan
     exact ⟨memos, .hit (started := started)⟩
   · intro request before handle running owner result middle started body ih
     intro inventory memos initial inherited resident domain stored plan
     obtain ⟨current, good, _key, _cell⟩ := SourceCurrentAllocatedPartialCallSteps.edge_start $formulas $solver
       initial inherited resident started
     have ownerDomain := (SourceCurrentAllocatedFiniteOrdinaryOuterState.edge_evaluate $formulas $solver request owner before running handle
       initial.sound initial.ready.semantic.ready.semantic.1.normal.facts.coherent inherited resident domain started).2.1
     have runningStored : Stored running := by simpa only [started] using stored.beginEdge request
     obtain ⟨final, reads⟩ := ih inventory memos current good.inherited good.input ownerDomain runningStored
       (plan.restrict (.direct (.edge_evaluate started)))
     exact ⟨final, .evaluate (started := started) reads⟩
   · intro loaded inherited result checked fourth merge edge before field actual
     intro inventory memos initial inheritedReady resident domain stored plan
     exact SourceCurrentAllocatedFiniteOrdinaryOuterParentReads.edge_body $bits $formulas $solver (.parent field actual)
       inventory initial inheritedReady resident domain stored plan.edge_body_capacity
   · intro inherited before inventory memos initial inheritedReady resident domain stored plan
     exact ⟨memos, .nil⟩
   · intro inherited original before narrowed middle result afterChildren originals results after first child tail ihEdge ihChildren ihTail
     intro inventory memos initial inheritedReady resident domain stored plan
     cases domain with
     | cons firstDomain restDomain =>
         have edgeResident := resident original List.mem_cons_self
         obtain ⟨edgeMemos, edgeReads⟩ := ihEdge inventory memos initial inheritedReady edgeResident firstDomain stored
           (plan.restrict (.direct .rows_edge))
         obtain ⟨_checks, edgeInventory, edgePost, narrowedResident, edgeStored, firstBound, _law⟩ :=
           SourceCurrentAllocatedFiniteOrdinaryOuterVerification.edge_call $formulas $solver edgeReads inventory initial
             inheritedReady edgeResident firstDomain stored
         have nextInherited := inheritedReady.grows edgePost.effects.grows.constraint_growth
         obtain ⟨childMemos, childReads⟩ := ihChildren edgeInventory edgeMemos edgePost.context nextInherited narrowedResident firstBound.1 edgeStored
           (plan.restrict (.direct (.rows_descendants first)))
         obtain ⟨_childChecks, childInventory, childPost, _resident, childStored, _childBound, _childLaw⟩ :=
           SourceCurrentAllocatedFiniteOrdinaryOuterVerification.descendants $formulas $solver childReads edgeInventory
             edgePost.context nextInherited narrowedResident firstBound.1 edgeStored
         have firstPost := edgePost.trans childPost
         have tailResident : Edges afterChildren.checked.native.machine.heap originals := fun edge member =>
           edge_grows _ _ firstPost.effects.keeps.growth edge (resident edge (List.mem_cons_of_mem _ member))
         obtain ⟨final, tailReads⟩ := ihTail childInventory childMemos childPost.context
           (inheritedReady.grows firstPost.effects.grows.constraint_growth) tailResident restDomain childStored
           (plan.restrict (.direct (.rows_tail first child)))
         exact ⟨final, .cons edgeReads childReads tailReads⟩
   · intro inherited payload before edge results middle combined actual ih
     intro inventory memos initial inheritedReady resident domain stored plan
     obtain ⟨prefixReceipt, prefixPost⟩ := SourceCurrentAllocatedPartialStepEffects.inherited_prefix $formulas $solver
       inventory before memos initial edge inherited payload resident inheritedReady combined
     have inputs := initial.ready.semantic.ready.semantic.1.normal.facts.cached.edges edge.entry.key edge resident
     have available : Values (prefixState before edge inherited).checked.native.machine.heap edge.children :=
       fun value member => prefixPost.effects.keeps.available value (inputs value member)
     obtain ⟨final, reads⟩ := ih inventory memos prefixPost.context prefixReceipt.combinedReady available domain
       (stored.prefixState edge inherited) (plan.restrict (.direct (.descendants_children combined)))
     exact ⟨final, .run (combined := combined) reads⟩
   · intro values before inventory memos initial inherited available domain stored plan
     exact ⟨memos, .contradiction⟩
   · intro identity records values before results after actual ih inventory memos initial inherited available domain stored plan
     obtain ⟨final, reads⟩ := ih inventory memos initial inherited available domain stored (plan.restrict (.direct .children_live))
     exact ⟨final, .live reads⟩
   · intro combined index before inventory memos initial inherited available domain stored plan
     exact ⟨memos, .nil⟩
   · intro before combined index value result middle values results after first tail ihHead ihTail
     intro inventory memos initial inherited available domain stored plan
     cases domain with
     | cons firstDomain restDomain =>
         obtain ⟨descentReceipt, descentPost⟩ := SourceCurrentAllocatedPartialStepEffects.descent $formulas $solver
           inventory before memos initial combined index inherited
         have firstAvailable := descentPost.effects.keeps.available _ (available value List.mem_cons_self)
         obtain ⟨headMemos, headReads⟩ := ihHead inventory memos descentPost.context descentReceipt.inherited firstAvailable firstDomain
           (stored.descend combined index) (plan.restrict (.direct .walk_node))
         obtain ⟨_headChecks, headInventory, headPost, _output, headStored, _headBound, _headLaw⟩ :=
           SourceCurrentAllocatedFiniteOrdinaryOuterVerification.node_call $formulas $solver headReads inventory descentPost.context
             descentReceipt.inherited firstAvailable firstDomain (stored.descend combined index)
         have firstPost := descentPost.trans headPost
         have tailAvailable : Values middle.checked.native.machine.heap values := fun child member =>
           firstPost.effects.keeps.available child (available child (List.mem_cons_of_mem _ member))
         obtain ⟨final, tailReads⟩ := ihTail headInventory headMemos headPost.context
           (inherited.grows firstPost.effects.grows.constraint_growth) tailAvailable restDomain headStored
           (plan.restrict (.direct (.walk_tail first)))
         exact ⟨final, .cons headReads tailReads⟩))

/-- The actual node call constructs strict reads at the same exact returned state. -/
theorem node_call (bits : Nat)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula) {request : NodeRequest} {before after : Caller (bits + 2)} {result : Node}
    (actual : NodeCall budget request before result after) (inventory : Inventory) {memos : Memos}
    (initial : Context formulas solver inventory before memos) (inherited : EqReady before.checked.operations.constraints request.inherited)
    (resident : Available before.checked.native.machine.heap request.value) (domain : DNode request.value) (stored : Stored before)
    (plan : Plan bits budget (.nodeCall request before)) : ∃ final, NodeCallReads formulas solver actual memos final := by
  have construction : NodeGoal formulas solver bits budget (.nodeCall request before) request before
      (fun memos final => NodeCallReads formulas solver actual memos final) := by
    raw_reads_induction NodeCall.rec actual bits formulas solver
  exact construction inventory memos initial inherited resident domain stored plan

/-- The actual node body constructs strict reads at the same exact returned state. -/
theorem node_body (bits : Nat)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula) {request : NodeRequest} {before after : Caller (bits + 2)} {result : Node}
    (actual : NodeBody budget request before result after) (inventory : Inventory) {memos : Memos}
    (initial : Context formulas solver inventory before memos) (inherited : EqReady before.checked.operations.constraints request.inherited)
    (resident : Available before.checked.native.machine.heap request.value) (domain : DNode request.value) (stored : Stored before)
    (plan : Plan bits budget (.nodeBody request before)) : ∃ final, NodeBodyReads formulas solver actual memos final := by
  have construction : NodeGoal formulas solver bits budget (.nodeBody request before) request before
      (fun memos final => NodeBodyReads formulas solver actual memos final) := by
    raw_reads_induction NodeBody.rec actual bits formulas solver
  exact construction inventory memos initial inherited resident domain stored plan

/-- The actual edge call constructs strict reads at the same exact returned state. -/
theorem edge_call (bits : Nat)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula) {request : EdgeRequest} {before after : Caller (bits + 2)} {result : Edge}
    (actual : EdgeCall budget request before result after) (inventory : Inventory) {memos : Memos}
    (initial : Context formulas solver inventory before memos) (inherited : EqReady before.checked.operations.constraints request.inherited)
    (resident : EdgeResident before.checked.native.machine.heap request.value) (domain : DEdge request.value) (stored : Stored before)
    (plan : Plan bits budget (.edgeCall request before)) : ∃ final, EdgeCallReads formulas solver actual memos final := by
  have construction : EdgeGoal formulas solver bits budget (.edgeCall request before) request before
      (fun memos final => EdgeCallReads formulas solver actual memos final) := by
    raw_reads_induction EdgeCall.rec actual bits formulas solver
  exact construction inventory memos initial inherited resident domain stored plan

/-- The actual edge body constructs strict reads at the same exact returned state. -/
theorem edge_body (bits : Nat)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula) {request : EdgeRequest} {before after : Caller (bits + 2)} {result : Edge}
    (actual : EdgeBody budget request before result after) (inventory : Inventory) {memos : Memos}
    (initial : Context formulas solver inventory before memos) (inherited : EqReady before.checked.operations.constraints request.inherited)
    (resident : EdgeResident before.checked.native.machine.heap request.value) (domain : DEdge request.value) (stored : Stored before)
    (plan : Plan bits budget (.edgeBody request before)) : ∃ final, EdgeBodyReads formulas solver actual memos final := by
  have construction : EdgeGoal formulas solver bits budget (.edgeBody request before) request before
      (fun memos final => EdgeBodyReads formulas solver actual memos final) := by
    raw_reads_induction EdgeBody.rec actual bits formulas solver
  exact construction inventory memos initial inherited resident domain stored plan

/-- The actual rows constructs ordered strict reads from only initial facts and numeric entry plans. -/
theorem rows (bits : Nat)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula) {inherited : EqValue} {values result : List Edge}
    {before after : Caller (bits + 2)}
    (actual : Rows budget inherited values before result after) (inventory : Inventory) {memos : Memos}
    (initial : Context formulas solver inventory before memos) (inheritedReady : EqReady before.checked.operations.constraints inherited)
    (resident : Edges before.checked.native.machine.heap values) (domain : DRows values) (stored : Stored before)
    (plan : Plan bits budget (.rows inherited values before)) : ∃ final, RowsReads formulas solver actual memos final := by
  have construction : RowsGoal formulas solver bits budget inherited values before
      (fun memos final => RowsReads formulas solver actual memos final) := by
    raw_reads_induction Rows.rec actual bits formulas solver
  exact construction inventory memos initial inheritedReady resident domain stored plan

/-- The actual descendants constructs ordered strict reads from only initial facts and numeric entry plans. -/
theorem descendants (bits : Nat)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula) {inherited : EqValue} {value result : Edge}
    {before after : Caller (bits + 2)}
    (actual : Descendants budget inherited value before result after) (inventory : Inventory) {memos : Memos}
    (initial : Context formulas solver inventory before memos) (inheritedReady : EqReady before.checked.operations.constraints inherited)
    (resident : EdgeResident before.checked.native.machine.heap value) (domain : DEdge value) (stored : Stored before)
    (plan : Plan bits budget (.descendants inherited value before)) : ∃ final, DescendantsReads formulas solver actual memos final := by
  have construction : EdgeGoal formulas solver bits budget (.descendants inherited value before) ⟨inherited, value⟩ before
      (fun memos final => DescendantsReads formulas solver actual memos final) := by
    raw_reads_induction Descendants.rec actual bits formulas solver
  exact construction inventory memos initial inheritedReady resident domain stored plan

/-- The actual children constructs ordered strict reads from only initial facts and numeric entry plans. -/
theorem children (bits : Nat)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula) {inherited : EqValue} {values result : List Node}
    {before after : Caller (bits + 2)}
    (actual : Children budget inherited values before result after) (inventory : Inventory) {memos : Memos}
    (initial : Context formulas solver inventory before memos) (inheritedReady : EqReady before.checked.operations.constraints inherited)
    (resident : Values before.checked.native.machine.heap values) (domain : DChildren values) (stored : Stored before)
    (plan : Plan bits budget (.children inherited values before)) : ∃ final, ChildrenReads formulas solver actual memos final := by
  have construction : ChildrenGoal formulas solver bits budget inherited values before (.children inherited values before)
      (fun memos final => ChildrenReads formulas solver actual memos final) := by
    raw_reads_induction Children.rec actual bits formulas solver
  exact construction inventory memos initial inheritedReady resident domain stored plan

/-- The actual walk constructs ordered strict reads from only initial facts and numeric entry plans. -/
theorem walk (bits : Nat)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula) {inherited : EqValue} {index : Nat} {values result : List Node}
    {before after : Caller (bits + 2)}
    (actual : Walk budget inherited index values before result after) (inventory : Inventory) {memos : Memos}
    (initial : Context formulas solver inventory before memos) (inheritedReady : EqReady before.checked.operations.constraints inherited)
    (resident : Values before.checked.native.machine.heap values) (domain : DChildren values) (stored : Stored before)
    (plan : Plan bits budget (.walk inherited index values before)) : ∃ final, WalkReads formulas solver actual memos final := by
  have construction : ChildrenGoal formulas solver bits budget inherited values before (.walk inherited index values before)
      (fun memos final => WalkReads formulas solver actual memos final) := by
    raw_reads_induction Walk.rec actual bits formulas solver
  exact construction inventory memos initial inheritedReady resident domain stored plan

end MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryOuterRawReads
