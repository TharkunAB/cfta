import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryScanRanges
import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryOuterActual

/-!
# Derived checks for actual constrained finite ordinary caller reads

The mutual induction follows the supplied strict read graph in source order.
Every reached parent derives its own Scan checks from resident domain input.
Earlier returned prefixes derive the next Context and causal certificates.
The same actual return then has its full semantic and structural receipts.
No Checks, future range plan, result law, or final invariant is an input.
These results verify completed graphs. They do not construct finite graphs
or remove the separate class-target and leaf capacity obligations.
-/
namespace MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryOuterVerification
open Cache Language InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
open InternedNestedProvenance (Values Edges)
open SourceCurrentAllocatedPartialState SourceCurrentAllocatedPartialGraph
open SourceCurrentAllocatedPartialSourceReads SourceCurrentAllocatedPartialChecks
open SourceCurrentAllocatedPartialInvariant (Context Post)
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedFiniteOrdinaryOuterState (Stored)
open SourceCurrentAllocatedFiniteOrdinaryRequired (NodeNarrow EdgeNarrow)
open SourceCurrentAllocatedPartialMemoSound (NodeLaw EdgeLaw)
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
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Node] {width budget : Nat}
variable (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)

private def NodeChecks (top : Trace width budget) (request : NodeRequest) (before : Caller width) (memos : Memos) : Prop :=
  ∀ inventory, Context formulas solver inventory before memos → EqReady before.checked.operations.constraints request.inherited →
    Available before.checked.native.machine.heap request.value → DNode request.value → Stored before → Checks top

private def EdgeChecks (top : Trace width budget) (request : EdgeRequest) (before : Caller width) (memos : Memos) : Prop :=
  ∀ inventory, Context formulas solver inventory before memos → EqReady before.checked.operations.constraints request.inherited →
    EdgeResident before.checked.native.machine.heap request.value → DEdge request.value → Stored before → Checks top

private def RowsChecks {inherited : EqValue} {values results : List Edge} {before after : Caller width}
    (actual : Rows budget inherited values before results after) (memos : Memos) : Prop :=
  ∀ inventory, Context formulas solver inventory before memos → EqReady before.checked.operations.constraints inherited →
    Edges before.checked.native.machine.heap values → DRows values → Stored before → Checks (rowsTrace actual)

private def ChildrenChecks {combined : EqValue} {values results : List Node} {before after : Caller width}
    (actual : Children budget combined values before results after) (memos : Memos) : Prop :=
  ∀ inventory, Context formulas solver inventory before memos → EqReady before.checked.operations.constraints combined →
    Values before.checked.native.machine.heap values → DChildren values → Stored before → Checks (childrenTrace actual)

private def WalkChecks {combined : EqValue} {index : Nat} {values results : List Node} {before after : Caller width}
    (actual : Walk budget combined index values before results after) (memos : Memos) : Prop :=
  ∀ inventory, Context formulas solver inventory before memos → EqReady before.checked.operations.constraints combined →
    Values before.checked.native.machine.heap values → DChildren values → Stored before → Checks (walkTrace actual)

-- Each induction hypothesis verifies only the literal smaller read graph.
local macro "checks_induction" recursor:ident reads:ident formulas:ident solver:ident : tactic => `(tactic|
  (apply $recursor
    (motive_1 := fun {budget request before result after} actual memos final _ =>
      NodeChecks $formulas $solver (nodeCallTrace actual) request before memos)
    (motive_2 := fun {budget request before result after} actual memos final _ =>
      NodeChecks $formulas $solver (nodeBodyTrace actual) request before memos)
    (motive_3 := fun {budget request before result after} actual memos final _ =>
      EdgeChecks $formulas $solver (edgeCallTrace actual) request before memos)
    (motive_4 := fun {budget request before result after} actual memos final _ =>
      EdgeChecks $formulas $solver (edgeBodyTrace actual) request before memos)
    (motive_5 := fun {_budget _inherited _values _before _results _after} actual memos final _ =>
      RowsChecks $formulas $solver actual memos)
    (motive_6 := fun {budget inherited value before result after} actual memos final _ =>
      EdgeChecks $formulas $solver (descendantsTrace actual) ⟨inherited, value⟩ before memos)
    (motive_7 := fun {_budget _combined _values _before _results _after} actual memos final _ =>
      ChildrenChecks $formulas $solver actual memos)
    (motive_8 := fun {_budget _combined _index _values _before _results _after} actual memos final _ =>
      WalkChecks $formulas $solver actual memos)
    (t := $reads)
   · intro budget request before handle result after started memos inventory initial inherited available domain stored
     exact SourceCurrentAllocatedPartialChecksComposition.node_hit started
   · intro budget owner running result middle body memos final request before handle started bodyReads ih
     intro inventory initial inherited available domain stored
     obtain ⟨current, good, _key, _cell⟩ := SourceCurrentAllocatedPartialCallSteps.node_start $formulas $solver
       initial inherited available started
     have ownerDomain := (SourceCurrentAllocatedFiniteOrdinaryOuterState.node_evaluate $formulas $solver request owner before running handle
       initial.sound initial.ready.semantic.ready.semantic.1.normal.facts.coherent inherited available domain started).2.1
     have runningStored : Stored running := by simpa only [started] using stored.beginNode request
     exact SourceCurrentAllocatedPartialChecksComposition.node_evaluate started body
       (ih inventory current good.inherited good.input ownerDomain runningStored)
   · intro budget inherited before memos inventory initial inheritedReady available domain stored
     exact SourceCurrentAllocatedPartialChecksComposition.empty
   · intro budget inherited entry members depth free before memos inventory initial inheritedReady available domain stored
     cases domain
   · intro budget inherited entry body depth ordinary before result heap actual memos inventory initial inheritedReady available domain stored
     cases domain
   · intro entry depth free budget inherited edges before results middle rows memos final rowsReads ih
     intro inventory initial inheritedReady available domain stored
     have resident := InternedEdgeResidency.resident_edges _ initial.ready.semantic.ready.semantic.1.normal.facts.linked _ available.resident
     exact SourceCurrentAllocatedPartialChecksComposition.ordinary rows
       (ih inventory initial inheritedReady resident domain.rows stored)
   · intro budget request before handle result after started memos inventory initial inherited resident domain stored
     exact SourceCurrentAllocatedPartialChecksComposition.edge_hit started
   · intro budget owner running result middle body memos final request before handle started bodyReads ih
     intro inventory initial inherited resident domain stored
     obtain ⟨current, good, _key, _cell⟩ := SourceCurrentAllocatedPartialCallSteps.edge_start $formulas $solver
       initial inherited resident started
     have ownerDomain := (SourceCurrentAllocatedFiniteOrdinaryOuterState.edge_evaluate $formulas $solver request owner before running handle
       initial.sound initial.ready.semantic.ready.semantic.1.normal.facts.coherent inherited resident domain started).2.1
     have runningStored : Stored running := by simpa only [started] using stored.beginEdge request
     exact SourceCurrentAllocatedPartialChecksComposition.edge_evaluate started body
       (ih inventory current good.inherited good.input ownerDomain runningStored)
   · intro budget edge loaded inherited before result checked fourth merge actual memos final field parentReads
     intro inventory initial inheritedReady resident domain stored
     exact SourceCurrentAllocatedFiniteOrdinaryScanRanges.edge_body_checks (.parent field actual)
       initial.ready.semantic resident domain
   · intro budget inherited before memos inventory initial inheritedReady resident domain stored
     exact SourceCurrentAllocatedPartialChecksComposition.rows_nil
   · intro budget inherited original before narrowed middle first memos edgeMemos result afterChildren child childMemos
     intro originals results after tail final edgeReads childrenReads tailReads ihEdge ihChildren ihTail
     intro inventory initial inheritedReady resident domain stored
     cases domain with
     | cons firstDomain restDomain =>
         have edgeResident := resident original List.mem_cons_self
         have firstChecks := ihEdge inventory initial inheritedReady edgeResident firstDomain stored
         obtain ⟨edgeInventory, edgePost, narrowedResident, _⟩ := SourceCurrentAllocatedPartialActual.edge_call $formulas $solver
           edgeReads inventory firstChecks initial inheritedReady edgeResident
         have firstBound := SourceCurrentAllocatedFiniteOrdinaryOuterActual.edge_call $formulas $solver edgeReads
           inventory firstChecks initial inheritedReady edgeResident firstDomain stored
         have nextInherited := inheritedReady.grows edgePost.effects.grows.constraint_growth
         have childChecks := ihChildren edgeInventory edgePost.context nextInherited narrowedResident firstBound.2.1 firstBound.1
         obtain ⟨childInventory, childPost, _resident, _⟩ := SourceCurrentAllocatedPartialActual.descendants $formulas $solver
           childrenReads edgeInventory childChecks edgePost.context nextInherited narrowedResident
         have childBound := SourceCurrentAllocatedFiniteOrdinaryOuterActual.descendants $formulas $solver childrenReads
           edgeInventory childChecks edgePost.context nextInherited narrowedResident firstBound.2.1 firstBound.1
         have firstPost := edgePost.trans childPost
         have tailResident : Edges afterChildren.checked.native.machine.heap originals := fun edge member =>
           edge_grows _ _ firstPost.effects.keeps.growth edge (resident edge (List.mem_cons_of_mem _ member))
         have tailChecks := ihTail childInventory childPost.context
           (inheritedReady.grows firstPost.effects.grows.constraint_growth) tailResident restDomain childBound.1
         exact SourceCurrentAllocatedPartialChecksComposition.rows_cons first child tail firstChecks childChecks tailChecks
   · intro budget payload edge before inherited results middle children memos final combined childReads ih
     intro inventory initial inheritedReady resident domain stored
     obtain ⟨prefixReceipt, prefixPost⟩ := SourceCurrentAllocatedPartialStepEffects.inherited_prefix $formulas $solver
       inventory before memos initial edge inherited payload resident inheritedReady combined
     have inputs := initial.ready.semantic.ready.semantic.1.normal.facts.cached.edges edge.entry.key edge resident
     have available : Values (prefixState before edge inherited).checked.native.machine.heap edge.children :=
       fun value member => prefixPost.effects.keeps.available value (inputs value member)
     exact SourceCurrentAllocatedPartialChecksComposition.descendants_run combined children
       (ih inventory prefixPost.context prefixReceipt.combinedReady available domain (stored.prefixState edge inherited))
   · intro budget values before memos inventory initial inherited available domain stored
     exact SourceCurrentAllocatedPartialChecksComposition.children_contradiction
   · intro budget identity records values before results after actual memos final walkReads ih
     intro inventory initial inherited available domain stored
     exact SourceCurrentAllocatedPartialChecksComposition.children_live actual
       (ih inventory initial inherited available domain stored)
   · intro budget combined index before memos inventory initial inherited available domain stored
     exact SourceCurrentAllocatedPartialChecksComposition.walk_nil
   · intro budget before combined index value result middle first memos headMemos values results after tail final headReads tailReads ihHead ihTail
     intro inventory initial inherited available domain stored
     cases domain with
     | cons firstDomain restDomain =>
         obtain ⟨descentReceipt, descentPost⟩ := SourceCurrentAllocatedPartialStepEffects.descent $formulas $solver
           inventory before memos initial combined index inherited
         have firstAvailable := descentPost.effects.keeps.available _ (available value List.mem_cons_self)
         have firstChecks := ihHead inventory descentPost.context descentReceipt.inherited firstAvailable firstDomain
           (stored.descend combined index)
         obtain ⟨headInventory, headPost, _output, _⟩ := SourceCurrentAllocatedPartialActual.node_call $formulas $solver
           headReads inventory firstChecks descentPost.context descentReceipt.inherited firstAvailable
         have headBound := SourceCurrentAllocatedFiniteOrdinaryOuterActual.node_call $formulas $solver headReads
           inventory firstChecks descentPost.context descentReceipt.inherited firstAvailable firstDomain (stored.descend combined index)
         have firstPost := descentPost.trans headPost
         have tailAvailable : Values middle.checked.native.machine.heap values := fun child member =>
           firstPost.effects.keeps.available child (available child (List.mem_cons_of_mem _ member))
         have tailChecks := ihTail headInventory headPost.context
           (inherited.grows firstPost.effects.grows.constraint_growth) tailAvailable restDomain headBound.1
         exact SourceCurrentAllocatedPartialChecksComposition.walk_cons first tail firstChecks tailChecks))

/-- Supplied node-call reads derive their own checks and the exact complete return. -/
theorem node_call {request : NodeRequest} {before after : Caller width} {result : Node}
    {actual : NodeCall budget request before result after} {memos final : Memos}
    (reads : NodeCallReads formulas solver actual memos final) (inventory : Inventory)
    (initial : Context formulas solver inventory before memos) (inherited : EqReady before.checked.operations.constraints request.inherited)
    (available : Available before.checked.native.machine.heap request.value) (domain : DNode request.value) (stored : Stored before) :
    Checks (nodeCallTrace actual) ∧ ∃ next, Post formulas solver next before after final ∧
      Available after.checked.native.machine.heap result ∧ Stored after ∧ NodeNarrow request.value result ∧ NodeLaw formulas solver request result := by
  have derived : NodeChecks formulas solver (nodeCallTrace actual) request before memos := by
    checks_induction NodeCallReads.rec reads formulas solver
  have checks := derived inventory initial inherited available domain stored
  obtain ⟨next, post, output, law⟩ := SourceCurrentAllocatedPartialActual.node_call formulas solver reads inventory checks initial inherited available
  have bounds := SourceCurrentAllocatedFiniteOrdinaryOuterActual.node_call formulas solver reads inventory checks initial inherited available domain stored
  exact ⟨checks, next, post, output, bounds.1, bounds.2, law⟩

/-- Supplied node-body reads derive checks without an external completed-body law. -/
theorem node_body {request : NodeRequest} {before after : Caller width} {result : Node}
    {actual : NodeBody budget request before result after} {memos final : Memos}
    (reads : NodeBodyReads formulas solver actual memos final) (inventory : Inventory)
    (initial : Context formulas solver inventory before memos) (inherited : EqReady before.checked.operations.constraints request.inherited)
    (available : Available before.checked.native.machine.heap request.value) (domain : DNode request.value) (stored : Stored before) :
    Checks (nodeBodyTrace actual) ∧ ∃ next, Post formulas solver next before after final ∧
      Available after.checked.native.machine.heap result ∧ Stored after ∧ NodeNarrow request.value result ∧ NodeLaw formulas solver request result := by
  have derived : NodeChecks formulas solver (nodeBodyTrace actual) request before memos := by
    checks_induction NodeBodyReads.rec reads formulas solver
  have checks := derived inventory initial inherited available domain stored
  obtain ⟨next, post, output, law⟩ := SourceCurrentAllocatedPartialActual.node_body formulas solver reads inventory checks initial inherited available
  have bounds := SourceCurrentAllocatedFiniteOrdinaryOuterActual.node_body formulas solver reads inventory checks initial inherited available domain stored
  exact ⟨checks, next, post, output, bounds.1, bounds.2, law⟩

/-- Supplied edge-call reads derive owner checks and preserve the same literal result. -/
theorem edge_call {request : EdgeRequest} {before after : Caller width} {result : Edge}
    {actual : EdgeCall budget request before result after} {memos final : Memos}
    (reads : EdgeCallReads formulas solver actual memos final) (inventory : Inventory)
    (initial : Context formulas solver inventory before memos) (inherited : EqReady before.checked.operations.constraints request.inherited)
    (resident : EdgeResident before.checked.native.machine.heap request.value) (domain : DEdge request.value) (stored : Stored before) :
    Checks (edgeCallTrace actual) ∧ ∃ next, Post formulas solver next before after final ∧
      EdgeResident after.checked.native.machine.heap result ∧ Stored after ∧ EdgeNarrow request.value result ∧ EdgeLaw formulas solver request result := by
  have derived : EdgeChecks formulas solver (edgeCallTrace actual) request before memos := by
    checks_induction EdgeCallReads.rec reads formulas solver
  have checks := derived inventory initial inherited resident domain stored
  obtain ⟨next, post, output, law⟩ := SourceCurrentAllocatedPartialActual.edge_call formulas solver reads inventory checks initial inherited resident
  have bounds := SourceCurrentAllocatedFiniteOrdinaryOuterActual.edge_call formulas solver reads inventory checks initial inherited resident domain stored
  exact ⟨checks, next, post, output, bounds.1, bounds.2, law⟩

/-- Supplied current parent reads derive their own Scan-only checks. -/
theorem edge_body {request : EdgeRequest} {before after : Caller width} {result : Edge}
    {actual : EdgeBody budget request before result after} {memos final : Memos}
    (reads : EdgeBodyReads formulas solver actual memos final) (inventory : Inventory)
    (initial : Context formulas solver inventory before memos) (inherited : EqReady before.checked.operations.constraints request.inherited)
    (resident : EdgeResident before.checked.native.machine.heap request.value) (domain : DEdge request.value) (stored : Stored before) :
    Checks (edgeBodyTrace actual) ∧ ∃ next, Post formulas solver next before after final ∧
      EdgeResident after.checked.native.machine.heap result ∧ Stored after ∧ EdgeNarrow request.value result ∧ EdgeLaw formulas solver request result := by
  have checks := SourceCurrentAllocatedFiniteOrdinaryScanRanges.edge_body_checks actual initial.ready.semantic resident domain
  obtain ⟨next, post, output, law⟩ := SourceCurrentAllocatedPartialActual.edge_body formulas solver reads inventory checks initial inherited resident
  have bounds := SourceCurrentAllocatedFiniteOrdinaryOuterActual.edge_body formulas solver reads inventory checks initial inherited resident domain stored
  exact ⟨checks, next, post, output, bounds.1, bounds.2, law⟩

/-- Ordered supplied row reads derive checks at each actual reached prefix. -/
theorem rows {inherited : EqValue} {values results : List Edge} {before after : Caller width}
    {actual : Rows budget inherited values before results after} {memos final : Memos}
    (reads : RowsReads formulas solver actual memos final) (inventory : Inventory)
    (initial : Context formulas solver inventory before memos) (inheritedReady : EqReady before.checked.operations.constraints inherited)
    (resident : Edges before.checked.native.machine.heap values) (domain : DRows values) (stored : Stored before) :
    Checks (rowsTrace actual) ∧ ∃ next, Post formulas solver next before after final ∧
      Edges after.checked.native.machine.heap results ∧ Stored after ∧ All₂ EdgeNarrow values results ∧
      SourceCurrentAllocatedPartialForestLanguage.RowsLaw formulas solver actual := by
  have derived : RowsChecks formulas solver actual memos := by
    checks_induction RowsReads.rec reads formulas solver
  have checks := derived inventory initial inheritedReady resident domain stored
  obtain ⟨next, post, output, law⟩ := SourceCurrentAllocatedPartialActual.rows formulas solver reads inventory checks initial inheritedReady resident
  have bounds := SourceCurrentAllocatedFiniteOrdinaryOuterActual.rows formulas solver reads inventory checks initial inheritedReady resident domain stored
  exact ⟨checks, next, post, output, bounds.1, bounds.2, law⟩

/-- Actual inherited-prefix and child reads derive the same complete descendant return. -/
theorem descendants {inherited : EqValue} {value result : Edge} {before after : Caller width}
    {actual : Descendants budget inherited value before result after} {memos final : Memos}
    (reads : DescendantsReads formulas solver actual memos final) (inventory : Inventory)
    (initial : Context formulas solver inventory before memos) (inheritedReady : EqReady before.checked.operations.constraints inherited)
    (resident : EdgeResident before.checked.native.machine.heap value) (domain : DEdge value) (stored : Stored before) :
    Checks (descendantsTrace actual) ∧ ∃ next, Post formulas solver next before after final ∧
      EdgeResident after.checked.native.machine.heap result ∧ Stored after ∧ EdgeNarrow value result ∧ EdgeLaw formulas solver ⟨inherited, value⟩ result := by
  have derived : EdgeChecks formulas solver (descendantsTrace actual) ⟨inherited, value⟩ before memos := by
    checks_induction DescendantsReads.rec reads formulas solver
  have checks := derived inventory initial inheritedReady resident domain stored
  obtain ⟨next, post, output, law⟩ := SourceCurrentAllocatedPartialActual.descendants formulas solver reads inventory checks initial inheritedReady resident
  have bounds := SourceCurrentAllocatedFiniteOrdinaryOuterActual.descendants formulas solver reads inventory checks initial inheritedReady resident domain stored
  exact ⟨checks, next, post, output, bounds.1, bounds.2, law⟩

/-- Supplied child reads derive their own checks, positional bounds, and inherited-conditioned language. -/
theorem children {combined : EqValue} {values results : List Node} {before after : Caller width}
    {actual : Children budget combined values before results after} {memos final : Memos}
    (reads : ChildrenReads formulas solver actual memos final) (inventory : Inventory)
    (initial : Context formulas solver inventory before memos) (inherited : EqReady before.checked.operations.constraints combined)
    (available : Values before.checked.native.machine.heap values) (domain : DChildren values) (stored : Stored before) :
    Checks (childrenTrace actual) ∧ ∃ next, Post formulas solver next before after final ∧
      Values after.checked.native.machine.heap results ∧ Stored after ∧ All₂ NodeNarrow values results ∧
      SourceCurrentAllocatedPartialWalkLanguage.ChildrenLaw formulas solver actual := by
  have derived : ChildrenChecks formulas solver actual memos := by
    checks_induction ChildrenReads.rec reads formulas solver
  have checks := derived inventory initial inherited available domain stored
  obtain ⟨next, post, output, law⟩ := SourceCurrentAllocatedPartialActual.children formulas solver reads inventory checks initial inherited available
  have bounds := SourceCurrentAllocatedFiniteOrdinaryOuterActual.children formulas solver reads inventory checks initial inherited available domain stored
  exact ⟨checks, next, post, output, bounds.1, bounds.2, law⟩

/-- Indexed walk reads derive checks in literal child order and retain the complete returned caller. -/
theorem walk {combined : EqValue} {index : Nat} {values results : List Node} {before after : Caller width}
    {actual : Walk budget combined index values before results after} {memos final : Memos}
    (reads : WalkReads formulas solver actual memos final) (inventory : Inventory)
    (initial : Context formulas solver inventory before memos) (inherited : EqReady before.checked.operations.constraints combined)
    (available : Values before.checked.native.machine.heap values) (domain : DChildren values) (stored : Stored before) :
    Checks (walkTrace actual) ∧ ∃ next, Post formulas solver next before after final ∧
      Values after.checked.native.machine.heap results ∧ Stored after ∧ All₂ NodeNarrow values results ∧
      SourceCurrentAllocatedPartialWalkLanguage.WalkLaw formulas solver actual := by
  have derived : WalkChecks formulas solver actual memos := by
    checks_induction WalkReads.rec reads formulas solver
  have checks := derived inventory initial inherited available domain stored
  obtain ⟨next, post, output, law⟩ := SourceCurrentAllocatedPartialActual.walk formulas solver reads inventory checks initial inherited available
  have bounds := SourceCurrentAllocatedFiniteOrdinaryOuterActual.walk formulas solver reads inventory checks initial inherited available domain stored
  exact ⟨checks, next, post, output, bounds.1, bounds.2, law⟩

end MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryOuterVerification
