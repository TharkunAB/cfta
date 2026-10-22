import MicroCFTA.MergedFreshOrdinaryColdTermination
import MicroCFTA.InternedNormalizationFree

/-!
# Physical cache effects of required-path reconstruction

The worker calls the actual edge and node constructors. These lemmas derive
the cache and closed-value invariants needed by subsequent cold head reads.
Canonical hits use the existing payload readback theorems.
-/
namespace MicroCFTA.SourceEqualityRequiredCache
open Cache InternedConstructorTemplates InternedProbeProvenance InternedRecordCoherence
open InternedNestedFacts InternedEdgeResidency
open InternedNestedProvenance (Values Edges)
open MergedColdReaderClosedInputs (ClosedValues ClosedEdges)
open SourceRecursiveIntersectionSemanticHeap (SemanticHeap)

/-- A worker cache supports complete closed recursive head exposure. -/
structure Ready (state : State Symbol Guard) : Prop where
  semantic : SemanticHeap state
  covered : Covered [] state
  depth : InternedOpenDepthReadback.Heap state

/-- A completed reconstruction retains the full ready cache and both histories. -/
structure Keeps (before after : State Symbol Guard) : Prop where
  ready : Ready after
  growth : Grows before after
  history : Extends before.nodes.issued after.nodes.issued

/-- Earlier available values remain available after actual worker effects. -/
theorem Keeps.available {before after : State Symbol Guard} (keeps : Keeps before after)
    (value : Value Symbol Guard) (available : Available before value) : Available after value :=
  available.grows before after keeps.growth keeps.history

/-- An operation with no effects retains every ready-cache premise. -/
theorem pure_keeps (state : State Symbol Guard) (ready : Ready state) : Keeps state state :=
  ⟨ready, grows_refl _, extends_refl _⟩

/-- Successive physical operations compose their exact cache histories. -/
theorem Keeps.trans {before middle after : State Symbol Guard}
    (first : Keeps before middle) (second : Keeps middle after) : Keeps before after :=
  ⟨second.ready, grows_trans first.growth second.growth, extends_trans first.history second.history⟩

/-- Original closed construction derives every required initial cache premise. -/
theorem constructed [DecidableEq (EdgeKey Symbol Guard)] (expression : InternedNestedConstruction.Syntax Symbol Guard)
    (value : Value Symbol Guard) (state : State Symbol Guard)
    (built : InternedFreshOrdinaryConstruction.build expression [] empty = .done value state) : Ready state := by
  refine ⟨SourceRecursiveIntersectionSemanticHeap.constructed expression value state built,
    InternedFreshOrdinaryCoverage.closed_covered expression value state built, ?_⟩
  simpa only [built, InternedNestedConstruction.Outcome.state] using InternedOpenDepthExecution.closed_heap expression

/-- Actual edge rebuilding retains all invariants and the exact ordered child payload. -/
theorem edge [DecidableEq (EdgeKey Symbol Guard)] (symbol : Symbol) (guard : Guard)
    (values : List (Value Symbol Guard)) (state : State Symbol Guard) (ready : Ready state)
    (available : Values state values) :
    Keeps state (run (makeEdge symbol guard values) state).2 ∧
      EdgeResident (run (makeEdge symbol guard values) state).2 (run (makeEdge symbol guard values) state).1 ∧
      (run (makeEdge symbol guard values) state).1.children = values := by
  have facts := ready.semantic.1.normal.facts
  have checked := InternedNestedFacts.edge_verified symbol guard values state facts available
  refine ⟨⟨⟨SourceRecursiveIntersectionSemanticHeap.edge symbol guard values state ready.semantic available,
    InternedNestedCoverage.run_covered _ state facts.coherent.valid ready.covered, ready.depth⟩,
    checked.growth, checked.history⟩, ?_, ?_⟩
  · exact checked.result _ _ rfl
  · exact InternedShallowValues.makeEdge_children symbol guard values state facts.coherent facts.cached available

/-- Source ordinary-node requests return only empty or ordinary node records. -/
def Ordinary : Value Symbol Guard → Prop
  | .empty | .node .. => True
  | _ => False

/-- Canonical node hits cannot replace a row request by a recursive or union record. -/
theorem node_ordinary [DecidableEq (EdgeKey Symbol Guard)] (edges : List (EdgeValue Symbol Guard))
    (state : State Symbol Guard) (facts : Facts state) (resident : Edges state edges) :
    Ordinary (run (makeNode edges) state).1 := by
  have selected : Edges state (canonicalEdges (surviving edges)) := by
    intro edge member
    exact resident edge (List.mem_filter.mp (canonicalEdges_member _ edge member)).1
  unfold makeNode
  dsimp only
  split
  · trivial
  · rename_i first rest same
    obtain ⟨entry, readback⟩ := identifyNode_readback (first :: rest) state facts.coherent facts.linked
      (fun edge member => selected edge (by simpa only [same] using member))
    change Ordinary (nodeStep _ _ state).1
    rw [readback]
    trivial

/-- Actual node rebuilding retains readiness, residency, closedness, and its ordinary head. -/
theorem node [DecidableEq (EdgeKey Symbol Guard)] (edges : List (EdgeValue Symbol Guard))
    (state : State Symbol Guard) (ready : Ready state) (resident : Edges state edges) (closed : ClosedEdges edges) :
    Keeps state (run (makeNode edges) state).2 ∧
      Available (run (makeNode edges) state).2 (run (makeNode edges) state).1 ∧
      (run (makeNode edges) state).1.free = [] ∧ Ordinary (run (makeNode edges) state).1 := by
  have facts := ready.semantic.1.normal.facts
  have checked := InternedNestedFacts.node_verified edges state facts resident
  refine ⟨⟨⟨SourceRecursiveIntersectionSemanticHeap.node edges state ready.semantic resident,
    InternedNestedCoverage.run_covered _ state facts.coherent.valid ready.covered,
    InternedOpenDepthReadback.preserve state _ ready.depth (InternedShallowHeap.makeNode_noNewMu edges state)⟩,
    checked.growth, checked.history⟩, checked.result _ _ rfl,
    MergedColdReaderClosedInputs.makeNode_closed edges state facts resident closed,
    node_ordinary edges state facts resident⟩

end MicroCFTA.SourceEqualityRequiredCache
