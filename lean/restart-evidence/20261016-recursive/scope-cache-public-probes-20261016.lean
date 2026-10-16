import MicroCFTA.SourceCurrentAllocatedNativeScopeCache

open MicroCFTA Cache InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks
open SourceCurrentAllocatedNativeScopeCache

#print axioms MicroCFTA.SourceCurrentAllocatedNativeScopeCache.initial_scoped
#print axioms MicroCFTA.SourceCurrentAllocatedNativeScopeCache.advance_scoped
#print axioms MicroCFTA.SourceCurrentAllocatedNativeScopeCache.lookupNode_scoped
#print axioms MicroCFTA.SourceCurrentAllocatedNativeScopeCache.lookupEdge_scoped
#print axioms MicroCFTA.SourceCurrentAllocatedNativeScopeCache.demandNode_scoped
#print axioms MicroCFTA.SourceCurrentAllocatedNativeScopeCache.demandEdge_scoped
#print axioms MicroCFTA.SourceCurrentAllocatedNativeScopeCache.finishNode_scoped
#print axioms MicroCFTA.SourceCurrentAllocatedNativeScopeCache.finishEdge_scoped
#print axioms MicroCFTA.SourceCurrentAllocatedNativeScopeCache.node_observed_ready
#print axioms MicroCFTA.SourceCurrentAllocatedNativeScopeCache.edge_observed_ready
#print axioms MicroCFTA.SourceCurrentAllocatedNativeScopeCache.node_started
#print axioms MicroCFTA.SourceCurrentAllocatedNativeScopeCache.edge_started

#check @MicroCFTA.SourceCurrentAllocatedNativeScopeCache.initial_scoped
#check @MicroCFTA.SourceCurrentAllocatedNativeScopeCache.advance_scoped
#check @MicroCFTA.SourceCurrentAllocatedNativeScopeCache.lookupNode_scoped
#check @MicroCFTA.SourceCurrentAllocatedNativeScopeCache.lookupEdge_scoped
#check @MicroCFTA.SourceCurrentAllocatedNativeScopeCache.demandNode_scoped
#check @MicroCFTA.SourceCurrentAllocatedNativeScopeCache.demandEdge_scoped
#check @MicroCFTA.SourceCurrentAllocatedNativeScopeCache.finishNode_scoped
#check @MicroCFTA.SourceCurrentAllocatedNativeScopeCache.finishEdge_scoped
#check @MicroCFTA.SourceCurrentAllocatedNativeScopeCache.node_observed_ready
#check @MicroCFTA.SourceCurrentAllocatedNativeScopeCache.edge_observed_ready
#check @MicroCFTA.SourceCurrentAllocatedNativeScopeCache.node_started
#check @MicroCFTA.SourceCurrentAllocatedNativeScopeCache.edge_started

namespace ScopeCacheChecks
variable {Symbol Guard : Type} {width : Nat}

-- 1. Empty tables need no physical or language invariant.
example (machine : Machine Symbol Guard) : Scoped (initial width machine) := initial_scoped width machine

-- 2. Scope is independent of the replacement machine and its heap.
example (state : SourceRecursiveIntersectionThunks.State width Symbol Guard)
    (after : Machine Symbol Guard) (scopes : Scoped state) : Scoped (advance state after) :=
  advance_scoped state after scopes

-- 3. Node publication adds no returned result obligation.
example (machine : Machine Symbol Guard) (request : NodeRequest Symbol Guard) :
    Scoped (lookupNode width request (initial width machine)).2 :=
  lookupNode_scoped _ request (initial_scoped width machine)

-- 4. Edge publication adds no returned result obligation.
example (machine : Machine Symbol Guard) (request : EdgeRequest Symbol Guard) :
    Scoped (lookupEdge width request (initial width machine)).2 :=
  lookupEdge_scoped _ request (initial_scoped width machine)

-- 5. Demand retains node scope after actual publication.
example (machine : Machine Symbol Guard) (request : NodeRequest Symbol Guard) (handle : Nat) :
    Scoped (demandNode handle (lookupNode width request (initial width machine)).2).2 :=
  demandNode_scoped _ handle (lookupNode_scoped _ request (initial_scoped width machine))

-- 6. Demand retains edge scope after actual publication.
example (machine : Machine Symbol Guard) (request : EdgeRequest Symbol Guard) (handle : Nat) :
    Scoped (demandEdge handle (lookupEdge width request (initial width machine)).2).2 :=
  demandEdge_scoped _ handle (lookupEdge_scoped _ request (initial_scoped width machine))

-- 7. Empty-domain node scope implies cached free-list closedness.
example (left right result : Value Symbol Guard)
    (scope : NodeLaw ⟨IntersectionEmptyDomain.emptyDomain, left, right⟩ result) : result.free = [] :=
  SourceRecursiveIntersectionResultScope.empty_scope result scope

-- 8. Empty-domain edge scope closes every actual ordered child.
example (left right result : EdgeValue Symbol Guard)
    (scope : EdgeLaw ⟨IntersectionEmptyDomain.emptyDomain, left, right⟩ result) :
    ∀ child ∈ result.children, child.free = [] := by
  intro child member
  exact SourceRecursiveIntersectionResultScope.empty_scope child (scope child member)

-- 9. A closed local result suffices for any exact evaluating node request.
example (state : SourceRecursiveIntersectionThunks.State width Symbol Guard) (handle : Nat)
    (request : NodeRequest Symbol Guard) (result : Value Symbol Guard) (scopes : Scoped state)
    (running : state.nodes.cells handle = some ⟨request, .evaluating⟩) (closed : result.free = []) :
    Scoped (finishNode handle result state) :=
  finishNode_scoped state handle request result scopes running
    (SourceRecursiveIntersectionResultScope.closed _ result closed)

-- 10. Repeated references need membership in the actual incoming seen list.
example (request : NodeRequest Symbol Guard) (pair : Nat × Nat) (member : pair ∈ request.domain.key.seen) :
    NodeLaw request (SourceRecursiveIntersectionControl.repeatedValue pair) :=
  SourceRecursiveIntersectionResultScope.repeated _ pair member

-- 11. Ordinary references cannot satisfy this intersection-only result invariant.
example (request : NodeRequest Symbol Guard) (name : Nat) :
    ¬ NodeLaw request (.reference (.interned name)) := by
  intro scope
  obtain ⟨pair, _, impossible⟩ := scope (.interned name) (by simp [Value.free])
  cases impossible

-- 12. A real warm ready hit at the empty domain returns a syntactically closed result.
example (request : NodeRequest Symbol Guard)
    (before chosen after : SourceRecursiveIntersectionThunks.State width Symbol Guard)
    (handle : Nat) (result : Value Symbol Guard)
    (physical : SourceCurrentAllocatedNativePhysicalCache.Valid before) (scopes : Scoped before)
    (ready : NodeReady before.machine request)
    (safe : SourceRecursiveIntersectionMemo.KeySafe width request.domain request.left request.right)
    (selected : lookupNode width request before = (.memoized handle, chosen))
    (demanded : demandNode handle chosen = (.ready result, after))
    (domain : request.domain = IntersectionEmptyDomain.emptyDomain) : result.free = [] := by
  have scope := (node_observed_ready request before chosen after handle result physical scopes ready safe selected demanded).1
  change SourceRecursiveIntersectionResultScope.Scope request.domain.key.seen result at scope
  rw [domain] at scope
  exact SourceRecursiveIntersectionResultScope.empty_scope result scope

end ScopeCacheChecks
