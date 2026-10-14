import MicroCFTA.SourceRecursiveIntersectionScopeRows

/-!
# Actual bounded recursive execution derives result pair scope

Every successful actual source call retains its semantic heap. Its free
names belong to the incoming domain's seen pairs. The proof follows actual
branches, domain entry, ordered calls, and optional-binder construction.
-/
namespace MicroCFTA.SourceRecursiveIntersectionScopeCalls
open Cache InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
open InternedBinderProtocol IntersectionFlatMemoKeyDomain
open SourceRecursiveIntersectionKernel
open SourceRecursiveIntersectionResultScope (Scope)
open SourceRecursiveIntersectionScopeEffects (Observed)
open SourceRecursiveIntersectionSemanticHeap (SemanticHeap)

/-- Full source branch selection composes checked recursive requests with exact physical effects. -/
theorem onNode_scoped [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] (emptyGuard : Guard) (conjoin : Guard → Guard → Guard)
    (call : Interned DomainKey → Value Symbol Guard → Value Symbol Guard → Machine Symbol Guard → Result Symbol Guard (Value Symbol Guard))
    (calls : Calls call) (scopes : ScopedCalls call) (domain : Interned DomainKey) (left right : Value Symbol Guard) (state : Machine Symbol Guard)
    (valid : SourceRecursiveIntersectionKernel.Valid state) (known : Domain state domain) (leftAvailable : Available state.heap left) (rightAvailable : Available state.heap right) (heap : SemanticHeap state.heap) :
    Observed (onNode emptyGuard conjoin call domain left right state) (Scope domain.key.seen) := by
  cases selected : SourceRecursiveIntersectionControl.decision domain.key left right with
  | empty =>
      simp only [onNode, selected]
      exact SourceRecursiveIntersectionScopeEffects.pure state heap .empty _ (SourceRecursiveIntersectionResultScope.closed _ _ rfl)
  | reset =>
      simp only [onNode, selected]
      apply SourceRecursiveIntersectionScopeEffects.map _ _ _
        (scopes _ left right state valid (empty_domain state) leftAvailable rightAvailable heap)
      intro value scope
      exact SourceRecursiveIntersectionResultScope.weaken [] _ (by intro pair member; cases member) value scope
  | self =>
      simp only [onNode, selected]
      exact SourceRecursiveIntersectionScopeEffects.pure state heap left _
        (SourceRecursiveIntersectionResultScope.closed _ _ (SourceRecursiveIntersectionResultScope.self_closed _ _ _ selected))
  | swap =>
      simp only [onNode, selected]
      exact scopes domain right left state valid known rightAvailable leftAvailable heap
  | repeated key =>
      simp only [onNode, selected]
      exact SourceRecursiveIntersectionScopeEffects.pure state heap _ _
        (SourceRecursiveIntersectionResultScope.repeated domain.key.seen key
          (SourceRecursiveIntersectionResultScope.repeated_seen _ _ _ key selected))
  | bothMu | leftMu | rightMu =>
      simp only [onNode, selected]
      exact mu_scoped call calls scopes domain left right state valid known leftAvailable rightAvailable heap
  | leftUnion =>
      simp only [onNode, selected]
      cases left with
      | union entry members depth free =>
          exact union_scoped call calls scopes domain members right true state valid known rightAvailable
            (fun value member => leftAvailable.children value (by simpa only [children] using member)) heap
      | empty | reference | node | mu => exact SourceRecursiveIntersectionScopeEffects.failed _ state _
  | rightUnion =>
      simp only [onNode, selected]
      cases right with
      | union entry members depth free =>
          exact union_scoped call calls scopes domain members left false state valid known leftAvailable
            (fun value member => rightAvailable.children value (by simpa only [children] using member)) heap
      | empty | reference | node | mu => exact SourceRecursiveIntersectionScopeEffects.failed _ state _
  | leftReference =>
      simp only [onNode, selected]
      cases left with
      | reference name =>
          cases name <;> try exact SourceRecursiveIntersectionScopeEffects.failed _ state _
          rename_i identity
          exact reference_scoped call scopes domain identity right true state valid known rightAvailable heap
      | empty | node | union | mu => exact SourceRecursiveIntersectionScopeEffects.failed _ state _
  | rightReference =>
      simp only [onNode, selected]
      cases right with
      | reference name =>
          cases name <;> try exact SourceRecursiveIntersectionScopeEffects.failed _ state _
          rename_i identity
          exact reference_scoped call scopes domain identity left false state valid known leftAvailable heap
      | empty | node | union | mu => exact SourceRecursiveIntersectionScopeEffects.failed _ state _
  | ordinary =>
      simp only [onNode, selected]
      cases left <;> cases right <;> try exact SourceRecursiveIntersectionScopeEffects.failed _ state _
      rename_i first firstEdges firstDepth firstFree second secondEdges secondDepth secondFree
      exact node_scoped emptyGuard conjoin call calls scopes domain firstEdges secondEdges state valid known
        (fun edge member => valid.1.linked first.key _ (leftAvailable.resident first rfl) edge member)
        (fun edge member => valid.1.linked second.key _ (rightAvailable.resident second rfl) edge member) heap
  | unsupported =>
      simp only [onNode, selected]
      exact SourceRecursiveIntersectionScopeEffects.failed _ state _

/-- Every bounded recursive source call derives complete state invariants and available successful results. -/
theorem execute_scoped [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] (emptyGuard : Guard) (conjoin : Guard → Guard → Guard)
    (fuel : Nat) : ScopedCalls (execute (Symbol := Symbol) emptyGuard conjoin fuel) := by
  induction fuel with
  | zero =>
      intro domain left right state valid known leftAvailable rightAvailable heap
      simp only [execute]
      exact SourceRecursiveIntersectionScopeEffects.failed .exhausted state _
  | succ fuel ih =>
      intro domain left right state valid known leftAvailable rightAvailable heap
      simp only [execute]
      exact onNode_scoped emptyGuard conjoin _ (execute_checked emptyGuard conjoin fuel) ih domain left right state valid known leftAvailable rightAvailable heap

/-- An actual successful empty-domain source request derives a closed result. -/
theorem execute_closed [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] (emptyGuard : Guard) (conjoin : Guard → Guard → Guard)
    (fuel : Nat) (left right : Value Symbol Guard) (state : Machine Symbol Guard) (valid : SourceRecursiveIntersectionKernel.Valid state)
    (leftAvailable : Available state.heap left) (rightAvailable : Available state.heap right) (heap : SemanticHeap state.heap)
    (value : Value Symbol Guard) (after : Machine Symbol Guard)
    (done : execute emptyGuard conjoin fuel IntersectionEmptyDomain.emptyDomain left right state = .done value after) : value.free = [] := by
  have observed := execute_scoped emptyGuard conjoin fuel IntersectionEmptyDomain.emptyDomain left right state valid
    (empty_domain state) leftAvailable rightAvailable heap value after done
  exact SourceRecursiveIntersectionResultScope.empty_scope value observed.2

end MicroCFTA.SourceRecursiveIntersectionScopeCalls
