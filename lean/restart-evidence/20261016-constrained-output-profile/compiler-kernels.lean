import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryOutputNode
import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryOutputEdge

namespace OutputCompilerChecks
open MicroCFTA Cache InternedConstructorTemplates InternedProbeProvenance
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceCurrentAllocatedFiniteOrdinaryOutputCode SourceCurrentAllocatedFiniteOrdinaryOutputStored
open SourceEqualityRequiredSemanticCache (SemanticReady)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "Edge" => EdgeValue Symbol Guard
local notation "emptyDomain" => IntersectionEmptyDomain.emptyDomain
local notation "NodeShape" => SourceCurrentAllocatedFiniteOrdinaryNativeProfile.NodeShape
local notation "EdgeShape" => SourceCurrentAllocatedFiniteOrdinaryNativeProfile.EdgeShape
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]

/-- The actual closed-self branch returns the original profiled resident record. -/
theorem self_profile (state : Machine Symbol Guard) (valid : Valid state) (semantic : SemanticReady state.heap)
    (entry : Interned InternedBinderProtocol.NodeKey) (rows : List Edge) (depth : Nat)
    (available : Available state.heap (.node entry rows depth []))
    (domain : SourceCurrentAllocatedFiniteOrdinaryDomain.Rows rows) :
    NodeCertificate ⟨emptyDomain, .node entry rows depth [], .node entry rows depth []⟩ (.node entry rows depth []) := by
  have compiled := SourceCurrentAllocatedFiniteOrdinaryOutputNode.node_certified
    ⟨emptyDomain, .node entry rows depth [], .node entry rows depth []⟩ state valid semantic available available
    ⟨rfl, .ordinary domain, .ordinary domain⟩
  simpa [compileNode, SourceRecursiveIntersectionControl.decision, SourceRecursiveIntersectionControl.hasEmpty,
    SourceRecursiveIntersectionControl.reset, SourceRecursiveIntersectionControl.closedSelf,
    Value.referenceOf, Value.free, IntersectionEmptyDomain.emptyDomain, IntersectionEmptyDomain.emptyKey, Certified] using compiled

/-- An empty ordinary join checks its literal Work return at the unchanged source machine. -/
theorem empty_rows_profile (state : Machine Symbol Guard) (valid : Valid state) (semantic : SemanticReady state.heap)
    (first second : Interned InternedBinderProtocol.NodeKey) :
    NodeCertificate ⟨emptyDomain, .node first [] 0 [], .node second [] 0 []⟩ (.empty : Node) := by
  have compiled := SourceCurrentAllocatedFiniteOrdinaryOutputNode.rows_certified emptyDomain rfl
    first [] 0 [] second [] 0 [] .nil .nil state valid semantic
  have inputs : SourceEqualityNativeDemandHeapPrimitives.WorkInputs state.heap (makeNode []) :=
    .node [] (by intro edge absent; cases absent)
  apply compiled .empty state ?_ inputs valid (.refl _) semantic
  simp [work, makeNode, surviving, canonicalEdges, run, EnumerationBuilderCaches.canonicalIds]

omit [DecidableEq Symbol] in
/-- Nullary accepted code derives the profile of its exact raw constructor result. -/
theorem nullary_profile (left right : Interned (InternedConstructorTemplates.EdgeKey Symbol Guard))
    (combined : SourceEqualityConjoinAllocation.Constraint FullSyntax.Formula)
    (state : Machine Symbol Guard) (valid : Valid state) (semantic : SemanticReady state.heap) :
    EdgeCertificate ⟨emptyDomain, .mk left [], .mk right []⟩
      (run (makeEdge left.key.symbol (SourceEqualityConjoinAllocation.readback combined) []) state.heap).1 := by
  let job := makeEdge left.key.symbol (SourceEqualityConjoinAllocation.readback combined) ([] : List Node)
  have inputs : SourceEqualityNativeDemandHeapPrimitives.WorkInputs state.heap job :=
    .edge _ _ [] (by intro value absent; cases absent)
  have checked := SourceEqualityNativeDemandValidity.work_checked job state valid inputs
  have ready := SourceCurrentAllocatedNativeSemanticHeap.work_semantic job state.heap semantic inputs
  have compiled := SourceCurrentAllocatedFiniteOrdinaryOutputEdge.children_certified
    ⟨emptyDomain, .mk left [], .mk right []⟩ ⟨rfl, .nil, .nil⟩ combined state valid semantic
  exact compiled (run job state.heap).1 {state with heap := (run job state.heap).2} rfl inputs checked.1 checked.2 ready

omit [DecidableEq Symbol] in
/-- A rejected nullary edge can return the source one-child sentinel and needs arity one. -/
theorem nullary_sentinel (left right : Interned (InternedConstructorTemplates.EdgeKey Symbol Guard))
    (state : Machine Symbol Guard) (valid : Valid state) (semantic : SemanticReady state.heap) :
    let result := (run (makeEdge left.key.symbol SourceEqualityConstraintConstructors.top [.empty]) state.heap).1
    EdgeShape 0 1 result ∧ result.children = [.empty] ∧ ¬ EdgeShape 0 0 result := by
  let request : EdgeRequest Symbol Guard := ⟨emptyDomain, .mk left [], .mk right []⟩
  let job : Work Symbol Guard Edge := makeEdge left.key.symbol SourceEqualityConstraintConstructors.top [.empty]
  have values : InternedNestedProvenance.Values state.heap [.empty] := by
    intro value member
    have same := List.mem_singleton.mp member
    subst value
    exact empty_available _
  have inputs : SourceEqualityNativeDemandHeapPrimitives.WorkInputs state.heap job := .edge _ _ _ values
  have checked := SourceEqualityNativeDemandValidity.work_checked job state valid inputs
  have ready := SourceCurrentAllocatedNativeSemanticHeap.work_semantic job state.heap semantic inputs
  have compiled := SourceCurrentAllocatedFiniteOrdinaryOutputEdge.sentinel_certified request state valid semantic
  have law := compiled (run job state.heap).1 {state with heap := (run job state.heap).2} rfl inputs checked.1 checked.2 ready
  have shape : EdgeShape 0 1 (run job state.heap).1 := law rfl 0 0 (by trivial) (by trivial)
  have children := InternedShallowValues.makeEdge_children left.key.symbol SourceEqualityConstraintConstructors.top
    [.empty] state.heap valid.1.coherent valid.1.cached values
  refine ⟨shape, children, ?_⟩
  intro impossible
  have length := SourceCurrentAllocatedFiniteOrdinaryNativeProfile.EdgeShape.arity _ impossible
  rw [children] at length
  simp only [List.length_singleton] at length
  omega

/-- Full equality and Boolean guards remain unrestricted in the concrete compiler certificate. -/
theorem guarded_compile (request : NodeRequest Symbol Guard) (state : Machine Symbol Guard)
    (valid : Valid state) (semantic : SemanticReady state.heap)
    (left : Available state.heap request.left) (right : Available state.heap request.right)
    (inputs : NodeInputs request) :
    Certified (compileNode request) state (fun _ value => ∀ rows arity,
      NodeShape rows arity request.left → NodeShape rows arity request.right →
      NodeShape (rows * rows) (max arity 1) value) := by
  have certificate := SourceCurrentAllocatedFiniteOrdinaryOutputNode.node_certified request state valid semantic left right inputs
  have added := certified_bind _ .pure state valid semantic _
    (fun _ value => ∀ rows arity, NodeShape rows arity request.left → NodeShape rows arity request.right →
      NodeShape (rows * rows) (max arity 1) value) certificate
    (fun _ _ _ _ _ law => law inputs.1)
  simpa only [SourceEqualityNativeDemand.code_bind_pure] using added

omit [DecidableEq Symbol] in
/-- Actual arity mismatch certifies the literal emitted sentinel without any field lookup. -/
theorem mismatch_profile {width : Nat} (request : EdgeRequest Symbol Guard) (inputs : EdgeInputs request)
    (before : SourceEqualityNativeDemand.State width)
    (good : SourceCurrentAllocatedNativePhysicalCompletion.Good before) (semantic : SemanticReady before.native.machine.heap)
    (mismatch : request.left.children.length ≠ request.right.children.length) :
    Certified ((SourceEqualityNativeCheckedCode.sentinel request.left).bind .pure) before.native.machine
      (fun _ value => EdgeCertificate request value) := by
  have yielded := SourceEqualityNativeDemand.body_mismatch request .pure before mismatch
  exact SourceCurrentAllocatedFiniteOrdinaryOutputEdge.body_certified request inputs before
    {before with operations := SourceEqualityMkEdgeAllocation.emptyField before.operations} .pure _ good semantic yielded
    (fun _ value => EdgeCertificate request value) (fun _ _ _ _ _ _ law => law)

#print axioms self_profile
#check @self_profile
#print axioms empty_rows_profile
#check @empty_rows_profile
#print axioms nullary_profile
#check @nullary_profile
#print axioms nullary_sentinel
#check @nullary_sentinel
#print axioms guarded_compile
#check @guarded_compile
#print axioms mismatch_profile
#check @mismatch_profile
end OutputCompilerChecks
