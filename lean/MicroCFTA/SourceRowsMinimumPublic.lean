import MicroCFTA.SourceRowsMinimumAdapter
import MicroCFTA.SourceInternedRowsLanguage

/-!
# Current productiveRows through the actual shared adapter

The finite worklist, exact toRows readback, and minimum-size convergence are
composed here. The result is structural productivity, as the source requires
for its overlap test. Constraints are retained by toRows and ignored only by
the minimum-size calculation. Native exposure is the immutable heap boundary.
-/

namespace MicroCFTA.SourceRowsMinimumPublic

open Language SourceInternedRows SourceRowsMinimumAdapter

/-- Ordinary minimum rows are exactly the adapter interpretation that ignores constraint payloads. -/
theorem ordinary_readback (raw : List (State × List (Transition Symbol Constraint))) :
    automaton raw = FTAValidation.rowFor (interpretedRows (fun _ _ => true) raw) := by
  funext state
  rw [interpreted_lookup]
  rfl

/-- The complete root row is unchanged by actual toRows readback, including the empty root. -/
theorem root_readback (heap : Heap Symbol Constraint) (fuel : Nat) (root : Ref)
    (raw : List (State × List (Transition Symbol Constraint))) (done : toRows heap fuel root = some raw) :
    automaton raw (stateOf root) = graph heap (fun _ _ => true) (stateOf root) := by
  cases root with
  | none =>
      cases Option.some.inj done
      simp [automaton, lookup, graph, stateOf]
  | some identity =>
      simp only [automaton, stateOf, toRows_root heap fuel identity raw done, graph, List.map_map]
      rfl

/-- The table's exact structural root language follows from the completed source traversal. -/
theorem root_language (heap : Heap Symbol Constraint) (fuel : Nat) (root : Ref)
    (raw : List (State × List (Transition Symbol Constraint))) (done : toRows heap fuel root = some raw)
    (term : Term Symbol) :
    Accepts (automaton raw) (stateOf root) term ↔ Accepts (graph heap (fun _ _ => true)) (stateOf root) term := by
  rw [ordinary_readback]
  exact toRows_language heap (fun _ _ => true) fuel root raw done term

/-- Actual polymorphic Table.minimumSizes computes the original exposed heap's least structural term size. -/
theorem minimum_root_exact (heap : Heap Symbol Constraint) (fuel : Nat) (root : Ref)
    (raw : List (State × List (Transition Symbol Constraint))) (done : toRows heap fuel root = some raw) (size : Nat) :
    minimumSizes raw (stateOf root) = some size ↔
      (∃ term, Accepts (graph heap (fun _ _ => true)) (stateOf root) term ∧ RecursiveSize.nodeSize term = size) ∧
      (∀ term, Accepts (graph heap (fun _ _ => true)) (stateOf root) term → size ≤ RecursiveSize.nodeSize term) := by
  rw [minimum_exact]
  simp only [root_language heap fuel root raw done]

/-- The source tests nodeEdges first, then the minimum-table key for stateOf the same root. -/
def productiveRows (heap : Heap Symbol Constraint) (root : Ref)
    (raw : List (State × List (Transition Symbol Constraint))) : Bool :=
  if (graph heap (fun _ _ => true) (stateOf root)).isEmpty then false else (minimumSizes raw (stateOf root)).isSome

/-- The actual nodeEdges precheck agrees with the exact raw table root lookup. -/
theorem productive_readback (heap : Heap Symbol Constraint) (fuel : Nat) (root : Ref)
    (raw : List (State × List (Transition Symbol Constraint))) (done : toRows heap fuel root = some raw) :
    productiveRows heap root raw = SourceRowsMinimumAdapter.productiveRows raw (stateOf root) := by
  have empty : (graph heap (fun _ _ => true) (stateOf root)).isEmpty = (lookup raw (stateOf root)).isEmpty := by
    rw [← root_readback heap fuel root raw done]
    simp [automaton]
  unfold productiveRows SourceRowsMinimumAdapter.productiveRows
  rw [empty]
  cases (lookup raw (stateOf root)).isEmpty <;> rfl

/-- No abstract productivity premise remains: the actual adapter and recurrence decide structural nonemptiness. -/
theorem productive_exact (heap : Heap Symbol Constraint) (fuel : Nat) (root : Ref)
    (raw : List (State × List (Transition Symbol Constraint))) (done : toRows heap fuel root = some raw) :
    productiveRows heap root raw = true ↔ ∃ term, Accepts (graph heap (fun _ _ => true)) (stateOf root) term := by
  rw [productive_readback heap fuel root raw done, SourceRowsMinimumAdapter.productive_exact]
  simp only [root_language heap fuel root raw done]

/-- The EmptyState sentinel is rejected before any lookup even in an arbitrary supplied table. -/
theorem productive_empty (heap : Heap Symbol Constraint)
    (raw : List (State × List (Transition Symbol Constraint))) : productiveRows heap none raw = false := rfl

/-- Finite closed native exposure gives both completed row readback and completed minimum-table evaluation. -/
theorem finite (heap : Heap Symbol Constraint) (domain : List Nat) (closed : ClosedDomain heap domain)
    (root : Ref) (supported : ∀ identity, root = some identity → identity ∈ domain) :
    ∃ fuel raw minimumFuel,
      (∀ larger, fuel ≤ larger → toRows heap larger root = some raw) ∧
      MinimumSize.sweeps (automaton raw) (raw.map Prod.fst) minimumFuel (fun _ => none) = minimumSizes raw ∧
      MinimumSize.sweep (automaton raw) (raw.map Prod.fst) (minimumSizes raw) = minimumSizes raw := by
  obtain ⟨fuel, raw, readback⟩ := toRows_finite heap domain closed root supported
  obtain ⟨minimumFuel, reached, stable⟩ := SourceRowsMinimumAdapter.finite raw
  exact ⟨fuel, raw, minimumFuel, readback, reached, stable⟩

/-- Repeated completed adapter traversals have exactly the same minimum root value. -/
theorem readback_invariant (heap : Heap Symbol Constraint) (root : Ref) (firstFuel secondFuel : Nat)
    (first second : List (State × List (Transition Symbol Constraint)))
    (firstDone : toRows heap firstFuel root = some first) (secondDone : toRows heap secondFuel root = some second) :
    minimumSizes first (stateOf root) = minimumSizes second (stateOf root) := by
  apply SourceRowsMinimumShape.minimum_language (automaton first) (automaton second)
    (plain first) (plain second) _ _ (SourceRowsMinimumAdapter.supported first) (SourceRowsMinimumAdapter.supported second)
  intro term
  exact (root_language heap firstFuel root first firstDone term).trans
    (root_language heap secondFuel root second secondDone term).symm

end MicroCFTA.SourceRowsMinimumPublic
