import MicroCFTA.SourceRecursiveIntersectionNativeRunningBefore
import MicroCFTA.SourceRecursiveIntersectionRequestProgress

/-!
# Semantic bounds of active native requests

Each running cell retains its exact original request and a least successful
semantic bound. Enclosing bounds dominate the current source body. Empty
memo state, publication, source growth, demand, and completed frames retain
the required bound invariant.
-/
namespace MicroCFTA.SourceRecursiveIntersectionNative
open Cache InternedConstructorTemplates InternedBinderProtocol IntersectionFlatMemoKeyDomain
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceRecursiveIntersectionInputView IntersectSchedule

/-- Read the exact semantic node request from its captured original physical fields. -/
def nodeSemantic (request : NodeRequest Symbol Guard) : Call Symbol :=
  .node (SourceRecursiveIntersectionSchedule.domain request.domain.key) (inputOf request.left) (inputOf request.right)

/-- Read the exact semantic row request from its original fields and complete executable guards. -/
def edgeSemantic (holds : Guard → Language.Term Symbol → Bool) (request : EdgeRequest Symbol Guard) : Call Symbol :=
  .edge (SourceRecursiveIntersectionSchedule.domain request.domain.key) (row holds request.left) (row holds request.right)

/-- Every running request has a finite least semantic bound at or above the current body bound. -/
structure ActiveAbove [DecidableEq Symbol] (view : View Symbol) (holds : Guard → Language.Term Symbol → Bool) (bound : Nat)
    (state : SourceRecursiveIntersectionThunks.State width Symbol Guard) : Prop where
  nodes : ∀ handle request, state.nodes.cells handle = some ⟨request, .evaluating⟩ →
    ∃ complete : Completes view (nodeSemantic request), bound ≤ requiredFuel view (nodeSemantic request) complete
  edges : ∀ handle request, state.edges.cells handle = some ⟨request, .evaluating⟩ →
    ∃ complete : Completes view (edgeSemantic holds request), bound ≤ requiredFuel view (edgeSemantic holds request) complete

/-- Empty native memo state has no active-bound obligations. -/
theorem active_initial [DecidableEq Symbol] (view : View Symbol) (holds : Guard → Language.Term Symbol → Bool) (bound : Nat)
    (machine : Machine Symbol Guard) : ActiveAbove view holds bound (initial width machine) := by
  constructor <;> intro handle request impossible <;> cases impossible

/-- A smaller current body bound retains all enclosing active bounds. -/
theorem ActiveAbove.weaken [DecidableEq Symbol] (view : View Symbol) (holds : Guard → Language.Term Symbol → Bool)
    (before after : Nat) (smaller : after ≤ before) (state : SourceRecursiveIntersectionThunks.State width Symbol Guard)
    (active : ActiveAbove view holds before state) : ActiveAbove view holds after state := by
  constructor
  · intro handle request running
    obtain ⟨complete, bounded⟩ := active.nodes handle request running
    exact ⟨complete, Nat.le_trans smaller bounded⟩
  · intro handle request running
    obtain ⟨complete, bounded⟩ := active.edges handle request running
    exact ⟨complete, Nat.le_trans smaller bounded⟩

/-- A source transition that leaves no new running cells retains every active bound. -/
theorem ActiveAbove.running_before [DecidableEq Symbol] (view : View Symbol) (holds : Guard → Language.Term Symbol → Bool)
    (bound : Nat) (before after : SourceRecursiveIntersectionThunks.State width Symbol Guard)
    (active : ActiveAbove view holds bound before) (retained : Retains after before) : ActiveAbove view holds bound after :=
  ⟨fun handle request running => active.nodes handle request (retained.1 handle request running),
    fun handle request running => active.edges handle request (retained.2 handle request running)⟩

/-- Actual node publication retains all enclosing active bounds. -/
theorem ActiveAbove.lookupNode [DecidableEq Symbol] (view : View Symbol) (holds : Guard → Language.Term Symbol → Bool)
    (bound : Nat) (state : SourceRecursiveIntersectionThunks.State width Symbol Guard) (active : ActiveAbove view holds bound state)
    (request : NodeRequest Symbol Guard) : ActiveAbove view holds bound (SourceRecursiveIntersectionThunks.lookupNode width request state).2 :=
  active.running_before view holds bound state _ (lookupNode_running_before request state)

/-- Actual edge publication retains all enclosing active bounds. -/
theorem ActiveAbove.lookupEdge [DecidableEq Symbol] (view : View Symbol) (holds : Guard → Language.Term Symbol → Bool)
    (bound : Nat) (state : SourceRecursiveIntersectionThunks.State width Symbol Guard) (active : ActiveAbove view holds bound state)
    (request : EdgeRequest Symbol Guard) : ActiveAbove view holds bound (SourceRecursiveIntersectionThunks.lookupEdge width request state).2 :=
  active.running_before view holds bound state _ (lookupEdge_running_before request state)

/-- Actual physical and domain effects retain all enclosing active bounds. -/
theorem ActiveAbove.advance [DecidableEq Symbol] (view : View Symbol) (holds : Guard → Language.Term Symbol → Bool)
    (bound : Nat) (state : SourceRecursiveIntersectionThunks.State width Symbol Guard) (active : ActiveAbove view holds bound state)
    (machine : Machine Symbol Guard) : ActiveAbove view holds bound (SourceRecursiveIntersectionThunks.advance state machine) :=
  ⟨active.nodes, active.edges⟩

/-- Starting an original node adds exactly its own certified semantic bound. -/
theorem ActiveAbove.startNode [DecidableEq Symbol] (view : View Symbol) (holds : Guard → Language.Term Symbol → Bool)
    (bound : Nat) (chosen current : SourceRecursiveIntersectionThunks.State width Symbol Guard)
    (active : ActiveAbove view holds bound chosen) (handle : Nat) (request : NodeRequest Symbol Guard)
    (demand : demandNode handle chosen = (.evaluate request, current)) (complete : Completes view (nodeSemantic request))
    (bounded : bound ≤ requiredFuel view (nodeSemantic request) complete) : ActiveAbove view holds bound current := by
  constructor
  · intro other original running
    by_cases same : other = handle
    · subst other
      have captured := (demandNode_evaluate handle chosen current request demand).2
      have equal := Option.some.inj (running.symm.trans captured)
      have requests : original = request := congrArg FlatMemoThunk.Cell.request equal
      subst original
      exact ⟨complete, bounded⟩
    · exact active.nodes other original (demandNode_running_before_other handle other chosen current _ demand original same running)
  · intro other original running
    have same : chosen.edges = current.edges := congrArg (fun actual => actual.2.edges) demand
    rw [← same] at running
    exact active.edges other original running

/-- Starting an original row adds exactly its own certified semantic bound. -/
theorem ActiveAbove.startEdge [DecidableEq Symbol] (view : View Symbol) (holds : Guard → Language.Term Symbol → Bool)
    (bound : Nat) (chosen current : SourceRecursiveIntersectionThunks.State width Symbol Guard)
    (active : ActiveAbove view holds bound chosen) (handle : Nat) (request : EdgeRequest Symbol Guard)
    (demand : demandEdge handle chosen = (.evaluate request, current)) (complete : Completes view (edgeSemantic holds request))
    (bounded : bound ≤ requiredFuel view (edgeSemantic holds request) complete) : ActiveAbove view holds bound current := by
  constructor
  · intro other original running
    have same : chosen.nodes = current.nodes := congrArg (fun actual => actual.2.nodes) demand
    rw [← same] at running
    exact active.nodes other original running
  · intro other original running
    by_cases same : other = handle
    · subst other
      have captured := (demandEdge_evaluate handle chosen current request demand).2
      have equal := Option.some.inj (running.symm.trans captured)
      have requests : original = request := congrArg FlatMemoThunk.Cell.request equal
      subst original
      exact ⟨complete, bounded⟩
    · exact active.edges other original (demandEdge_running_before_other handle other chosen current _ demand original same running)

/-- An original completed node frame restores the caller's stronger active bound. -/
theorem ActiveAbove.finishNode [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] (view : View Symbol)
    (holds : Guard → Language.Term Symbol → Bool) (bound : Nat) (emptyGuard : Guard) (conjoin : Guard → Guard → Guard)
    (handle : Nat) (request : NodeRequest Symbol Guard) (chosen current middle : SourceRecursiveIntersectionThunks.State width Symbol Guard)
    (value : Value Symbol Guard) (active : ActiveAbove view holds bound chosen)
    (demand : demandNode handle chosen = (.evaluate request, current)) (shape : Shape current)
    (body : Evaluation width Symbol Guard emptyGuard conjoin (compileNode request) current value middle) :
    ActiveAbove view holds bound (SourceRecursiveIntersectionThunks.finishNode handle value middle) :=
  active.running_before view holds bound chosen _ (node_body_finish_before emptyGuard conjoin handle request chosen current middle value demand shape body)

/-- An original completed row frame restores the caller's stronger active bound. -/
theorem ActiveAbove.finishEdge [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] (view : View Symbol)
    (holds : Guard → Language.Term Symbol → Bool) (bound : Nat) (emptyGuard : Guard) (conjoin : Guard → Guard → Guard)
    (handle : Nat) (request : EdgeRequest Symbol Guard) (chosen current middle : SourceRecursiveIntersectionThunks.State width Symbol Guard)
    (value : EdgeValue Symbol Guard) (active : ActiveAbove view holds bound chosen)
    (demand : demandEdge handle chosen = (.evaluate request, current)) (shape : Shape current)
    (body : Evaluation width Symbol Guard emptyGuard conjoin (compileEdge emptyGuard conjoin request) current value middle) :
    ActiveAbove view holds bound (SourceRecursiveIntersectionThunks.finishEdge handle value middle) :=
  active.running_before view holds bound chosen _ (edge_body_finish_before emptyGuard conjoin handle request chosen current middle value demand shape body)

end MicroCFTA.SourceRecursiveIntersectionNative
