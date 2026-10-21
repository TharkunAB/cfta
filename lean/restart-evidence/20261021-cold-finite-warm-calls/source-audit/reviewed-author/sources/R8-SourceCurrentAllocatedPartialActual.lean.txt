import MicroCFTA.SourceCurrentAllocatedPartialCallSteps
import MicroCFTA.SourceCurrentAllocatedPartialChecks
import MicroCFTA.SourceCurrentAllocatedPartialForestLanguage
import MicroCFTA.SourceCurrentAllocatedPartialStepEffects

/-!
# Mutual correctness of completed current recursive calls

The induction follows the supplied source-aligned read graph. Every smaller
call derives its own language and physical receipt at its actual return.
The range plan contains only reached Scan word checks. This theorem does
not assert that every request has a completed graph.
-/
namespace MicroCFTA.SourceCurrentAllocatedPartialActual
open Cache Language InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values Edges)
open SourceCurrentAllocatedPartialState SourceCurrentAllocatedPartialGraph
open SourceCurrentAllocatedPartialMemoSound (NodeLaw EdgeLaw)
open SourceCurrentAllocatedPartialInvariant (Context Post)
open SourceCurrentAllocatedPartialChecks
open SourceCurrentAllocatedPartialSourceReads
open SourceCurrentAllocatedPartialWalkLanguage (WalkLaw ChildrenLaw)
open SourceCurrentAllocatedPartialForestLanguage (RowsLaw)
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedNativeEffects (physical)
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

/-- A completed node returns its independent law and its literal full context. -/
def NodeClaim (top : Trace width budget) (request : NodeRequest) (before : Caller width)
    (result : Node) (after : Caller width) (memos final : Memos) : Prop :=
  ∀ inventory, Checks top → Context formulas solver inventory before memos →
    EqReady before.checked.operations.constraints request.inherited → Available before.checked.native.machine.heap request.value →
    ∃ next, Post formulas solver next before after final ∧ Available after.checked.native.machine.heap result ∧
      NodeLaw formulas solver request result

/-- A completed edge returns its independent law and its literal full context. -/
def EdgeClaim (top : Trace width budget) (request : EdgeRequest) (before : Caller width)
    (result : Edge) (after : Caller width) (memos final : Memos) : Prop :=
  ∀ inventory, Checks top → Context formulas solver inventory before memos →
    EqReady before.checked.operations.constraints request.inherited → Resident before.checked.native.machine.heap request.value →
    ∃ next, Post formulas solver next before after final ∧ Resident after.checked.native.machine.heap result ∧
      EdgeLaw formulas solver request result

/-- Ordered source rows return resident rows and their derived union law. -/
def RowsClaim {inherited : EqValue} {values results : List Edge} {before after : Caller width}
    (actual : Rows budget inherited values before results after) (memos final : Memos) : Prop :=
  ∀ inventory, Checks (rowsTrace actual) → Context formulas solver inventory before memos →
    EqReady before.checked.operations.constraints inherited → Edges before.checked.native.machine.heap values →
    ∃ next, Post formulas solver next before after final ∧ Edges after.checked.native.machine.heap results ∧
      RowsLaw formulas solver actual

/-- Actual descendants retain the returned edge's complete field and derived law. -/
def DescendantsClaim {inherited : EqValue} {value result : Edge} {before after : Caller width}
    (actual : Descendants budget inherited value before result after) (memos final : Memos) : Prop :=
  EdgeClaim formulas solver (descendantsTrace actual) ⟨inherited, value⟩ before result after memos final

/-- Actual child branches derive every returned slot and their parent-conditioned law. -/
def ChildrenClaim {combined : EqValue} {values results : List Node} {before after : Caller width}
    (actual : Children budget combined values before results after) (memos final : Memos) : Prop :=
  ∀ inventory, Checks (childrenTrace actual) → Context formulas solver inventory before memos →
    EqReady before.checked.operations.constraints combined → Values before.checked.native.machine.heap values →
    ∃ next, Post formulas solver next before after final ∧ Values after.checked.native.machine.heap results ∧
      ChildrenLaw formulas solver actual

/-- Each indexed walk derives its smaller node laws at the literal source offsets. -/
def WalkClaim {combined : EqValue} {index : Nat} {values results : List Node} {before after : Caller width}
    (actual : Walk budget combined index values before results after) (memos final : Memos) : Prop :=
  ∀ inventory, Checks (walkTrace actual) → Context formulas solver inventory before memos →
    EqReady before.checked.operations.constraints combined → Values before.checked.native.machine.heap values →
    ∃ next, Post formulas solver next before after final ∧ Values after.checked.native.machine.heap results ∧
      WalkLaw formulas solver actual

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

-- Each endpoint uses the same eight source-read induction motives.
local macro "actual_induction" recursor:ident reads:ident formulas:ident solver:ident : tactic => `(tactic|
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
   · intro budget request before handle result after started memos inventory checks initial inherited available
     exact ⟨inventory, SourceCurrentAllocatedPartialCallSteps.node_hit $formulas $solver initial inherited available started⟩
   · intro budget original running result middle body memos final request before handle started bodyReads ih
     intro inventory checks initial inherited available
     obtain ⟨runningContext, owner, _, _⟩ := SourceCurrentAllocatedPartialCallSteps.node_start $formulas $solver
       initial inherited available started
     obtain ⟨next, post, resident, law⟩ := ih inventory (checks.restrict (.node_evaluate started body))
       runningContext owner.inherited owner.input
     exact ⟨next, SourceCurrentAllocatedPartialCallSteps.node_finish $formulas $solver initial inherited available
       started body post resident law⟩
   · intro budget inherited before memos inventory _checks initial _inherited _available
     exact ⟨inventory, Post.refl initial, InternedProbeProvenance.empty_available _,
       SourceCurrentAllocatedPartialCallSteps.node_refl $formulas $solver _⟩
   · intro budget inherited entry members depth free before memos inventory _checks initial _inherited available
     exact ⟨inventory, Post.refl initial, available, SourceCurrentAllocatedPartialCallSteps.node_refl $formulas $solver _⟩
   · intro budget inherited entry body depth ordinary before result heap actual memos inventory _checks initial _inherited available
     exact ⟨inventory, SourceCurrentAllocatedPartialCallSteps.node_binder $formulas $solver initial available actual⟩
   · intro entry depth free budget inherited edges before results middle rows memos final rowsReads ih
     intro inventory checks initial inheritedReady available
     have resident := InternedEdgeResidency.resident_edges _ initial.ready.semantic.ready.semantic.1.normal.facts.linked _ available.resident
     obtain ⟨next, post, rowsResident, law⟩ := ih inventory (checks.restrict (.node_ordinary rows)) initial inheritedReady resident
     obtain ⟨rebuilt, last⟩ := SourceCurrentAllocatedPartialStepEffects.modify $formulas $solver next middle final post.context
       entry edges results depth free (post.effects.keeps.available _ available) rowsResident
     exact ⟨next, post.trans last, rebuilt.available, SourceCurrentAllocatedPartialForestLanguage.ordinary $formulas $solver rows law rebuilt⟩
   · intro budget request before handle result after started memos inventory checks initial inherited resident
     exact ⟨inventory, SourceCurrentAllocatedPartialCallSteps.edge_hit $formulas $solver initial inherited resident started⟩
   · intro budget original running result middle body memos final request before handle started bodyReads ih
     intro inventory checks initial inherited resident
     obtain ⟨runningContext, owner, _, _⟩ := SourceCurrentAllocatedPartialCallSteps.edge_start $formulas $solver
       initial inherited resident started
     obtain ⟨next, post, available, law⟩ := ih inventory (checks.restrict (.edge_evaluate started body))
       runningContext owner.inherited owner.input
     exact ⟨next, SourceCurrentAllocatedPartialCallSteps.edge_finish $formulas $solver initial inherited resident
       started body post available law⟩
   · intro budget edge loaded inherited before result checked fourth merge actual memos final field parentReads
     intro inventory checks initial inheritedReady resident
     obtain ⟨next, receipt, _, probes⟩ := SourceCurrentAllocatedPartialEdgeActual.edge_body $formulas $solver inventory
       (SourceCurrentAllocatedPartialSourceReads.EdgeBodyReads.parent (field := field) parentReads)
       initial.ready initial.admitted initial.sound inheritedReady resident initial.correct initial.stored initial.covered
       checks.edge_body initial.globals initial.probes
     exact ⟨next, ⟨⟨receipt.ready, receipt.admitted, receipt.sound, receipt.stored, receipt.covered,
       receipt.correct, receipt.globals, probes⟩, receipt.effects, receipt.retained, receipt.fourthRetained⟩,
       receipt.resident, receipt.language⟩
   · intro budget inherited before memos inventory _checks initial _inherited _resident
     exact ⟨inventory, Post.refl initial, (by intro row member; cases member),
       SourceCurrentAllocatedPartialForestLanguage.rows_nil $formulas $solver budget inherited before⟩
   · intro budget inherited original before narrowed middle first memos edgeMemos result afterChildren child childMemos
     intro originals results after tail final edgeReads childrenReads tailReads ihEdge ihChildren ihTail
     intro inventory checks initial inheritedReady resident
     obtain ⟨edgeInventory, edgePost, narrowedResident, edgeLaw⟩ := ihEdge inventory
       (checks.restrict (.rows_edge first child tail)) initial inheritedReady (resident original List.mem_cons_self)
     obtain ⟨childInventory, childPost, resultResident, childLaw⟩ := ihChildren edgeInventory
       (checks.restrict (.rows_descendants first child tail)) edgePost.context
       (inheritedReady.grows edgePost.effects.grows.constraint_growth) narrowedResident
     have firstPost := edgePost.trans childPost
     obtain ⟨next, tailPost, resultsResident, tailLaw⟩ := ihTail childInventory
       (checks.restrict (.rows_tail first child tail)) childPost.context
       (inheritedReady.grows firstPost.effects.grows.constraint_growth)
       (edges_grow firstPost.effects (fun edge member => resident edge (List.mem_cons_of_mem _ member)))
     refine ⟨next, firstPost.trans tailPost, ?_,
       SourceCurrentAllocatedPartialForestLanguage.rows_cons $formulas $solver first child tail edgeLaw childLaw tailLaw⟩
     intro edge member
     rcases List.mem_cons.mp member with same | member
     · subst edge
       exact InternedEdgeResidency.edge_grows _ _ tailPost.effects.keeps.growth _ resultResident
     · exact resultsResident edge member
   · intro budget payload edge before inherited results middle children memos final combined childReads ih
     intro inventory checks initial inheritedReady resident
     obtain ⟨prefixReceipt, prefixPost⟩ := SourceCurrentAllocatedPartialStepEffects.inherited_prefix $formulas $solver
       inventory before memos initial edge inherited payload resident inheritedReady combined
     have inputs := initial.ready.semantic.ready.semantic.1.normal.facts.cached.edges edge.entry.key edge resident
     obtain ⟨next, childPost, available, law⟩ := ih inventory
       (checks.restrict (.descendants_children combined children)) prefixPost.context prefixReceipt.combinedReady
       (values_grow prefixPost.effects inputs)
     have firstPost := prefixPost.trans childPost
     obtain ⟨rebuilt, last⟩ := SourceCurrentAllocatedPartialStepEffects.raw_edge $formulas $solver next middle final childPost.context
       edge results (InternedEdgeResidency.edge_grows _ _ firstPost.effects.keeps.growth _ resident) available children.length
     exact ⟨next, firstPost.trans last, rebuilt.resident,
       SourceCurrentAllocatedPartialForestLanguage.descendants $formulas $solver prefixReceipt children law rebuilt⟩
   · intro budget values before memos inventory _checks initial _inherited _available
     refine ⟨inventory, Post.refl initial, ?_,
       SourceCurrentAllocatedPartialWalkLanguage.children_contradiction $formulas $solver budget values before⟩
     intro value member
     obtain ⟨original, _, same⟩ := List.mem_map.mp member
     subst value
     exact InternedProbeProvenance.empty_available _
   · intro budget identity records values before results after actual memos final walkReads ih
     intro inventory checks initial inherited available
     obtain ⟨next, post, valuesAvailable, law⟩ := ih inventory (checks.restrict (.children_walk actual)) initial inherited available
     exact ⟨next, post, valuesAvailable, SourceCurrentAllocatedPartialWalkLanguage.children_live $formulas $solver actual inherited.2 law⟩
   · intro budget combined index before memos inventory _checks initial _inherited _available
     exact ⟨inventory, Post.refl initial, (by intro value member; cases member),
       SourceCurrentAllocatedPartialWalkLanguage.walk_nil $formulas $solver budget combined index before⟩
   · intro budget before combined index value result middle first memos headMemos values results after tail final headReads tailReads ihHead ihTail
     intro inventory checks initial inherited available
     obtain ⟨descentReceipt, descentPost⟩ := SourceCurrentAllocatedPartialStepEffects.descent $formulas $solver
       inventory before memos initial combined index inherited
     obtain ⟨headInventory, headPost, resultAvailable, headLaw⟩ := ihHead inventory
       (checks.restrict (.walk_head first tail)) descentPost.context descentReceipt.inherited
       (descentPost.effects.keeps.available _ (available value List.mem_cons_self))
     have firstPost := descentPost.trans headPost
     obtain ⟨next, tailPost, valuesAvailable, tailLaw⟩ := ihTail headInventory (checks.restrict (.walk_tail first tail)) headPost.context
       (inherited.grows firstPost.effects.grows.constraint_growth)
       (values_grow firstPost.effects (fun child member => available child (List.mem_cons_of_mem _ member)))
     refine ⟨next, firstPost.trans tailPost, ?_,
       SourceCurrentAllocatedPartialWalkLanguage.walk_cons_receipt $formulas $solver first tail descentReceipt headLaw tailLaw⟩
     intro child member
     rcases List.mem_cons.mp member with same | member
     · subst child
       exact tailPost.effects.keeps.available _ resultAvailable
     · exact valuesAvailable child member))

/-- Every supplied completed node call derives its current physical and language receipt. -/
theorem node_call {request : NodeRequest} {before after : Caller width} {result : Node}
    {actual : NodeCall budget request before result after} {memos final : Memos}
    (reads : NodeCallReads formulas solver actual memos final) :
    NodeClaim formulas solver (nodeCallTrace actual) request before result after memos final := by
  actual_induction NodeCallReads.rec reads formulas solver

/-- Actual node bodies derive their laws from their own smaller source calls. -/
theorem node_body {request : NodeRequest} {before after : Caller width} {result : Node}
    {actual : NodeBody budget request before result after} {memos final : Memos}
    (reads : NodeBodyReads formulas solver actual memos final) :
    NodeClaim formulas solver (nodeBodyTrace actual) request before result after memos final := by
  actual_induction NodeBodyReads.rec reads formulas solver

/-- Completed edge calls finish their actual stored owners and retain all warm invariants. -/
theorem edge_call {request : EdgeRequest} {before after : Caller width} {result : Edge}
    {actual : EdgeCall budget request before result after} {memos final : Memos}
    (reads : EdgeCallReads formulas solver actual memos final) :
    EdgeClaim formulas solver (edgeCallTrace actual) request before result after memos final := by
  actual_induction EdgeCallReads.rec reads formulas solver

/-- The strict current parent leaf derives the complete edge-body receipt. -/
theorem edge_body {request : EdgeRequest} {before after : Caller width} {result : Edge}
    {actual : EdgeBody budget request before result after} {memos final : Memos}
    (reads : EdgeBodyReads formulas solver actual memos final) :
    EdgeClaim formulas solver (edgeBodyTrace actual) request before result after memos final := by
  actual_induction EdgeBodyReads.rec reads formulas solver

/-- Source row order composes parent reduction, returned-edge descendants, and the suffix. -/
theorem rows {inherited : EqValue} {values results : List Edge} {before after : Caller width}
    {actual : Rows budget inherited values before results after} {memos final : Memos}
    (reads : RowsReads formulas solver actual memos final) : RowsClaim formulas solver actual memos final := by
  actual_induction RowsReads.rec reads formulas solver

/-- Descendants derive their law through the actual inherited prefix and same-arity reconstruction. -/
theorem descendants {inherited : EqValue} {value result : Edge} {before after : Caller width}
    {actual : Descendants budget inherited value before result after} {memos final : Memos}
    (reads : DescendantsReads formulas solver actual memos final) : DescendantsClaim formulas solver actual memos final := by
  actual_induction DescendantsReads.rec reads formulas solver

/-- Both child branches derive availability and their parent-conditioned language law. -/
theorem children {combined : EqValue} {values results : List Node} {before after : Caller width}
    {actual : Children budget combined values before results after} {memos final : Memos}
    (reads : ChildrenReads formulas solver actual memos final) : ChildrenClaim formulas solver actual memos final := by
  actual_induction ChildrenReads.rec reads formulas solver

/-- Indexed child walks derive each head law from the smaller actual node call. -/
theorem walk {combined : EqValue} {index : Nat} {values results : List Node} {before after : Caller width}
    {actual : Walk budget combined index values before results after} {memos final : Memos}
    (reads : WalkReads formulas solver actual memos final) : WalkClaim formulas solver actual memos final := by
  actual_induction WalkReads.rec reads formulas solver

/-- A completed top-level call with an allocated empty inherited payload preserves the full language. -/
theorem root_exact {inventory : Inventory} {identity : Nat} {value result : Node} {before after : Caller width}
    {actual : NodeCall budget ⟨.live identity [], value⟩ before result after} {memos final : Memos}
    (reads : NodeCallReads formulas solver actual memos final) (checks : Checks (nodeCallTrace actual))
    (initial : Context formulas solver inventory before memos)
    (inherited : EqReady before.checked.operations.constraints (.live identity []))
    (available : Available before.checked.native.machine.heap value) :
    ∃ next, Post formulas solver next before after final ∧ Available after.checked.native.machine.heap result ∧
      ∀ ambient term, InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver) ambient result term ↔
        InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver) ambient value term := by
  obtain ⟨next, post, resident, law⟩ := node_call formulas solver reads inventory checks initial inherited available
  refine ⟨next, post, resident, ?_⟩
  intro ambient term
  apply (law ambient term).2
  simp [SourceEqualityConstraintAllocation.Value.payload, SourceEqualityPrecheck.Sat, EqualityNormalize.Satisfies]

end MicroCFTA.SourceCurrentAllocatedPartialActual
