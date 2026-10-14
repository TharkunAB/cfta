import MicroCFTA.InternedFreshOrdinaryUnfoldRank
import MicroCFTA.RankedGateCompletion

/-!
# A general gate rank for actual repaired interned records

Each node retains its complete source cache and its derived semantic heaps.
The gate reads original edge children and cached metadata. Its unfolding
operation executes the repaired stored adapter and retains the returned
cache. No shallow-body or root-shape restriction is imposed.
-/
namespace MicroCFTA.InternedFreshOrdinaryGateRank
open Cache InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedNestedConstruction (Syntax Outcome)
open InternedFreshOrdinaryContext
open InternedBinderProtocol (NodeKey)

/-- An available source record retains all invariants needed by later actual unfoldings. -/
structure Node (Symbol Guard : Type) where
  state : State Symbol Guard
  value : Value Symbol Guard
  context : Context state []
  depth : InternedFreshOrdinaryDepthHeap.Heap state
  covered : Covered [] state
  costs : InternedFreshOrdinaryCostHeap.Heap state
  available : Available state value

/-- An original stored child shares its parent's complete cache and semantic heaps. -/
def child (node : Node Symbol Guard) (value : Value Symbol Guard) (available : Available node.state value) : Node Symbol Guard :=
  { node with value := value, available := available }

/-- The gate view retains every original ordered edge and child position. -/
def view (node : Node Symbol Guard) : RecursiveReductionBarrier.View (Node Symbol Guard) :=
  match original : node.value with
  | .empty => .empty
  | .reference _ => .reference
  | .union .. => .union
  | .mu .. => .binder
  | .node _ edges _ _ => .branches (edges.attach.map fun edge =>
      edge.val.children.attach.map fun value => child node value.val (by
        apply node.available.children value.val
        rw [original]
        exact List.mem_flatMap.mpr ⟨edge.val, edge.property, value.property⟩))

/-- The gate identifies a binder exactly when the source record is a Mu. -/
theorem view_binder (node : Node Symbol Guard) : view node = .binder ↔
    ∃ entry body depth ordinary, node.value = .mu entry body depth ordinary := by
  unfold view
  split <;> simp_all

/-- A total actual unfolding retains its complete executable trace equation. -/
structure Step [DecidableEq (EdgeKey Symbol Guard)] (before : Node Symbol Guard) where
  result : Node Symbol Guard
  actual : InternedFreshOrdinaryStoredSubstitution.unfold before.value before.state = .done result.value result.state

/-- Actual repaired unfolding completes and returns the semantic heaps for the next gate call. -/
def step [DecidableEq (EdgeKey Symbol Guard)] (node : Node Symbol Guard) : Step node := by
  have complete := InternedFreshOrdinaryStoredSubstitution.unfold_complete_costs node.value node.state
    node.context node.depth node.costs node.covered node.available
  cases computed : InternedFreshOrdinaryStoredSubstitution.unfold node.value node.state with
  | pending key after =>
      exfalso
      obtain ⟨value, final, done, _⟩ := complete
      simp [computed] at done
  | done value after =>
      have retained : Context after [] ∧ InternedFreshOrdinaryDepthHeap.Heap after ∧ Covered [] after ∧
          InternedFreshOrdinaryCostHeap.Heap after ∧ Available after value := by
        obtain ⟨actualValue, actualState, done, context, depth, covered, costs, available, _, _⟩ := complete
        rw [computed] at done
        cases done
        exact ⟨context, depth, covered, costs, available⟩
      exact ⟨⟨after, value, retained.1, retained.2.1, retained.2.2.1, retained.2.2.2.1, retained.2.2.2.2⟩, computed⟩

/-- The read adapter uses actual cached depth, free-set emptiness, and repaired source unfolding. -/
def read [DecidableEq (EdgeKey Symbol Guard)] (unconstrained : Value Symbol Guard → Bool) :
    ConstrainedRecursionGate.Read (Node Symbol Guard) where
  view := view
  nested := fun node => node.value.depth
  free := fun node => node.value.free.map (fun _ => 0)
  unconstrained := fun node => unconstrained node.value
  unfold := fun node => (step node).result

/-- Erasing free-name payloads preserves the gate's exact emptiness test. -/
theorem read_free_empty [DecidableEq (EdgeKey Symbol Guard)] (unconstrained : Value Symbol Guard → Bool)
    (node : Node Symbol Guard) : ((read unconstrained).free node).isEmpty = node.value.free.isEmpty := by simp [read]

/-- Actual open unfolding supplies the gate rank for every constraint predicate. -/
def ranking [DecidableEq (EdgeKey Symbol Guard)] (unconstrained : Value Symbol Guard → Bool) :
    ConstrainedRecursionGate.UnfoldingRank (read unconstrained) where
  rank := fun node => InternedFreeOccurrenceRank.rank node.value
  decreases := by
    intro node binder _ opened
    rw [read_free_empty] at opened
    obtain ⟨entry, body, depth, ordinary, original⟩ := (view_binder node).mp binder
    have available : Available node.state (.mu entry body depth ordinary) := original ▸ node.available
    have openBody : (Value.mu entry body depth ordinary).free ≠ [] := by
      intro closed
      simp [original, closed] at opened
    have actual := (step node).actual
    rw [original] at actual
    simpa only [read, original] using InternedFreshOrdinaryUnfoldRank.unfold_decreases entry body depth ordinary
      node.state node.context node.depth node.costs available openBody _ _ actual

/-- The actual repaired constrained-recursion gate has a total decision for every finite path. -/
def total [DecidableEq (EdgeKey Symbol Guard)] (unconstrained : Value Symbol Guard → Bool)
    (path : EqualityNormalize.Path) (node : Node Symbol Guard) : Bool :=
  ConstrainedRecursionGate.total (read unconstrained) (ranking unconstrained) path node

/-- Sufficient fuel returns the exact total decision and every larger fuel amount returns the same result. -/
theorem eventually_exact [DecidableEq (EdgeKey Symbol Guard)] (unconstrained : Value Symbol Guard → Bool)
    (path : EqualityNormalize.Path) (node : Node Symbol Guard) :
    ∃ bound, ∀ extra, ConstrainedRecursionGate.nodeMeets (read unconstrained) (bound + extra) path node =
      some (total unconstrained path node) :=
  RankedGateCompletion.eventually_exact (read unconstrained) (ranking unconstrained) path node

/-- Original completed source construction supplies a certified node without extra cache premises. -/
def fromCompleted [DecidableEq (EdgeKey Symbol Guard)] (expression : Syntax Symbol Guard)
    (value : Value Symbol Guard) (state : State Symbol Guard)
    (done : InternedFreshOrdinaryConstruction.build expression [] empty = .done value state) : Node Symbol Guard := by
  have context : Context state [] := by simpa only [done, Outcome.state] using empty_context.build expression
  exact ⟨state, value, context,
    by simpa only [done, Outcome.state] using
      (InternedRecordDepthExecution.build_depth expression [] empty empty_context InternedFreshOrdinaryDepthHeap.empty_heap).heap,
    InternedFreshOrdinaryCoverage.closed_covered expression value state done,
    by simpa only [done, Outcome.state] using InternedFreshOrdinaryCosts.closed_heap expression,
    (InternedFreshOrdinaryFacts.build_verified expression [] empty empty_context.normal.facts empty_context.inputs).result value state done⟩

/-- Original source construction completes and supplies finite gate evaluation at every path. -/
theorem source_eventually_exact [DecidableEq (EdgeKey Symbol Guard)] (expression : Syntax Symbol Guard)
    (unconstrained : Value Symbol Guard → Bool) :
    ∃ value state, ∃ done : InternedFreshOrdinaryConstruction.build expression [] empty = .done value state,
      ∀ path, ∃ bound, ∀ extra,
        ConstrainedRecursionGate.nodeMeets (read unconstrained) (bound + extra) path
          (fromCompleted expression value state done) =
        some (total unconstrained path (fromCompleted expression value state done)) := by
  obtain ⟨value, state, done⟩ := InternedFreshOrdinaryClosedCompletion.closed_complete expression
  exact ⟨value, state, done, fun path => eventually_exact unconstrained path _⟩

end MicroCFTA.InternedFreshOrdinaryGateRank
