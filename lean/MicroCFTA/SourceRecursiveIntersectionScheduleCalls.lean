import MicroCFTA.SourceRecursiveIntersectionNodeSchedule
import MicroCFTA.SourceRecursiveIntersectionEdgeSchedule
import MicroCFTA.SourceRecursiveIntersectionCompileMuBounds

/-!
# Recursive correspondence in one actual final cache

Completed recursive calls replay without allocation in their final cache.
The original operand scope supplies every body, row child, and binder read.
Semantic fuel can increase without changing any successful result.
-/
namespace MicroCFTA.SourceRecursiveIntersectionKernel
open Cache Language Binding InternedConstructorTemplates InternedProbeProvenance
open InternedBinderProtocol IntersectionFlatMemoKeyDomain
open SourceRecursiveIntersectionCode (NodeScope EdgeScope)
open SourceRecursiveIntersectionInputView (view inputOf row)
open SourceRecursiveIntersectionScheduleConstructors (Corresponds)
open SourceRecursiveIntersectionScheduleEnvironment (Ordered)

/-- Each completed allocation-free original call has its exact bounded semantic schedule result. -/
def ScheduleCalls [DecidableEq Symbol]
    (call : Interned DomainKey → Value Symbol Guard → Value Symbol Guard → Machine Symbol Guard → Result Symbol Guard (Value Symbol Guard))
    (state : Machine Symbol Guard) (holds : Guard → Term Symbol → Bool) (fuel : Nat) : Prop :=
  ∀ domain left right, Domain state domain → NodeScope state.heap ⟨domain, left, right⟩ → Ordered domain.key.seen →
    ∀ value, call domain left right state = .done value state → ∃ shape,
      IntersectSchedule.run (view state.heap holds) fuel (SourceRecursiveIntersectionSchedule.domain domain.key)
        (inputOf left) (inputOf right) = .ok shape ∧ Corresponds holds value shape

/-- Successful local correspondence remains exact at every larger semantic bound. -/
theorem ScheduleCalls.larger [DecidableEq Symbol]
    (call : Interned DomainKey → Value Symbol Guard → Value Symbol Guard → Machine Symbol Guard → Result Symbol Guard (Value Symbol Guard))
    (state : Machine Symbol Guard) (holds : Guard → Term Symbol → Bool) (before after : Nat) (enough : before ≤ after)
    (correct : ScheduleCalls call state holds before) : ScheduleCalls call state holds after := by
  intro domain left right known scope ordered value done
  obtain ⟨shape, completed, meaning⟩ := correct domain left right known scope ordered value done
  exact ⟨shape, IntersectSchedule.run_stable _ before after enough _ _ _ shape completed, meaning⟩

/-- Actual heap and history growth retain original operand and binder scope. -/
theorem schedule_scope_grows (before after : Machine Symbol Guard) (growth : Extension before after)
    (request : SourceRecursiveIntersectionThunks.NodeRequest Symbol Guard) (scope : NodeScope before.heap request) :
    NodeScope after.heap request := by
  refine ⟨scope.left, scope.right, growth.available _ scope.leftAvailable, growth.available _ scope.rightAvailable, ?_⟩
  intro name member
  exact SourceRecursiveIntersectionInputView.OriginalInput.grows before.heap after.heap growth.heap growth.history
    (.mu name) (scope.bindings name member)

/-- Original scoped edge requests derive the complete exact semantic edge step from recursive correspondence. -/
theorem edge_schedule_calls [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (emptyGuard : Guard) (conjoin : Guard → Guard → Guard)
    (call : Interned DomainKey → Value Symbol Guard → Value Symbol Guard → Machine Symbol Guard → Result Symbol Guard (Value Symbol Guard))
    (calls : Calls call) (replay : Replays call) (state : Machine Symbol Guard) (valid : Valid state)
    (holds : Guard → Term Symbol → Bool)
    (conjoined : ∀ first second term, holds (conjoin first second) term = (holds first term && holds second term))
    (fuel : Nat) (correct : ScheduleCalls call state holds fuel)
    (request : SourceRecursiveIntersectionThunks.EdgeRequest Symbol Guard) (known : Domain state request.domain)
    (scope : EdgeScope state.heap request) (ordered : Ordered request.domain.key.seen)
    (value : EdgeValue Symbol Guard)
    (done : edge emptyGuard conjoin (call request.domain) request.left request.right state = .done value state) :
    ∃ shape, IntersectSchedule.edge (view state.heap holds) (fuel + 1) (SourceRecursiveIntersectionSchedule.domain request.domain.key)
      (row holds request.left) (row holds request.right) = .ok shape ∧
      SourceRecursiveIntersectionScheduleConstructors.EdgeCorresponds holds value shape := by
  apply edge_schedule emptyGuard conjoin call calls replay request.domain request.left request.right state valid known
    scope.leftResident scope.rightResident value done holds conjoined (view state.heap holds) fuel
  intro pair member child completed
  exact correct request.domain pair.1 pair.2 known (scope.child state.heap valid.1 request pair member) ordered child completed

/-- Original scoped node requests derive the ordered semantic row computation from recursive correspondence. -/
theorem node_schedule_calls [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (emptyGuard : Guard) (conjoin : Guard → Guard → Guard)
    (call : Interned DomainKey → Value Symbol Guard → Value Symbol Guard → Machine Symbol Guard → Result Symbol Guard (Value Symbol Guard))
    (calls : Calls call) (replay : Replays call) (state : Machine Symbol Guard) (valid : Valid state)
    (holds : Guard → Term Symbol → Bool)
    (conjoined : ∀ first second term, holds (conjoin first second) term = (holds first term && holds second term))
    (fuel : Nat) (correct : ScheduleCalls call state holds fuel) (domain : Interned DomainKey) (known : Domain state domain)
    (first : Interned NodeKey) (left : List (EdgeValue Symbol Guard)) (leftDepth : Nat) (leftFree : List Reference)
    (second : Interned NodeKey) (right : List (EdgeValue Symbol Guard)) (rightDepth : Nat) (rightFree : List Reference)
    (scope : NodeScope state.heap ⟨domain, .node first left leftDepth leftFree, .node second right rightDepth rightFree⟩)
    (ordered : Ordered domain.key.seen) (value : Value Symbol Guard)
    (done : node emptyGuard conjoin (call domain) left right state = .done value state) :
    ∃ shape,
      (IntersectSchedule.walk (fun pair => IntersectSchedule.edge (view state.heap holds) (fuel + 1)
        (SourceRecursiveIntersectionSchedule.domain domain.key) pair.1 pair.2)
        (IntersectSchedule.joined (left.map (row holds)) (right.map (row holds)))).map Shape.alternatives = .ok shape ∧
      Corresponds holds value shape := by
  apply node_schedule emptyGuard conjoin call calls replay domain left right state valid known
    (fun edge member => valid.1.linked first.key _ (scope.leftAvailable.resident first rfl) edge member)
    (fun edge member => valid.1.linked second.key _ (scope.rightAvailable.resident second rfl) edge member)
    value done holds (view state.heap holds) (fuel + 1)
  intro pair member result completed
  have originals := (pairs_member left right pair).mp member
  have rows := scope.rows state.heap valid.1 domain first left leftDepth leftFree second right rightDepth rightFree
    pair.1 pair.2 originals.1 originals.2.1
  exact edge_schedule_calls emptyGuard conjoin call calls replay state valid holds conjoined fuel correct
    ⟨domain, pair.1, pair.2⟩ known rows ordered result completed

end MicroCFTA.SourceRecursiveIntersectionKernel
