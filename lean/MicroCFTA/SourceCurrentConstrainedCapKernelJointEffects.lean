import MicroCFTA.SourceCurrentConstrainedCapKernelJoint

/-!
# Actual primitive effects retain the joint recursive context

The three literal source constructors retain semantic and guard heaps.
Their actual physical histories retain each immutable source record.
-/
namespace MicroCFTA.SourceCurrentConstrainedCapKernelJoint
open Cache InternedConstructorTemplates InternedProbeProvenance InternedNestedFacts InternedEdgeResidency
open SourceRecursiveIntersectionKernel
variable {Symbol Guard : Type} [DecidableEq (EdgeKey Symbol Guard)]

/-- Actual edge construction retains the joint context from its available ordered children. -/
theorem Context.edge {annotation : Guard → Prop} {source : State Symbol Guard} {state : Machine Symbol Guard}
    (context : Context annotation source state) (symbol : Symbol) (guard : Guard) (values : List (Value Symbol Guard))
    (available : ∀ value ∈ values, Available state.heap value) :
    Context annotation source {state with heap := (run (makeEdge symbol guard values) state.heap).2} := by
  have physical := InternedNestedFacts.edge_verified symbol guard values state.heap context.valid.1 available
  exact ⟨⟨physical.facts, context.valid.2⟩,
    SourceRecursiveIntersectionSemanticHeap.edge symbol guard values state.heap context.semantic available,
    context.guards, grows_trans context.growth physical.growth, extends_trans context.history physical.history⟩

/-- Actual node construction retains the joint context from its resident literal rows. -/
theorem Context.node {annotation : Guard → Prop} {source : State Symbol Guard} {state : Machine Symbol Guard}
    (context : Context annotation source state) (edges : List (EdgeValue Symbol Guard))
    (resident : ∀ edge ∈ edges, EdgeResident state.heap edge) :
    Context annotation source {state with heap := (run (makeNode edges) state.heap).2} := by
  have physical := InternedNestedFacts.node_verified edges state.heap context.valid.1 resident
  exact ⟨⟨physical.facts, context.valid.2⟩,
    SourceRecursiveIntersectionSemanticHeap.node edges state.heap context.semantic resident,
    SourceCurrentConstrainedCapGuardHeap.preserve annotation state.heap _ context.guards
      (InternedShallowHeap.makeNode_noNewMu edges state.heap),
    grows_trans context.growth physical.growth, extends_trans context.history physical.history⟩

/-- Actual union construction retains the joint context from its available literal operands. -/
theorem Context.union {annotation : Guard → Prop} {source : State Symbol Guard} {state : Machine Symbol Guard}
    (context : Context annotation source state) (values : List (Value Symbol Guard))
    (available : ∀ value ∈ values, Available state.heap value) :
    Context annotation source {state with heap := (run (makeUnion values) state.heap).2} := by
  have physical := InternedNestedFacts.union_verified values state.heap context.valid.1 available
  exact ⟨⟨physical.facts, context.valid.2⟩,
    SourceRecursiveIntersectionSemanticHeap.union values state.heap context.semantic available,
    SourceCurrentConstrainedCapGuardHeap.preserve annotation state.heap _ context.guards
      (InternedShallowHeap.makeUnion_noNewMu values state.heap),
    grows_trans context.growth physical.growth, extends_trans context.history physical.history⟩

end MicroCFTA.SourceCurrentConstrainedCapKernelJoint
