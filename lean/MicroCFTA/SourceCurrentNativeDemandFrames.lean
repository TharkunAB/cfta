import MicroCFTA.SourceRecursiveIntersectionThunks

set_option autoImplicit false

/-!
# Actual request publication and evaluating cells

Demand retains the published table and counter. Its evaluating outcome keeps
the exact stored request. A cold native node lookup supplies that request
from the original call. Warm observations retain their own stored request.

These laws describe the actual lookup and demand results.
-/
namespace MicroCFTA.SourceCurrentNativeDemandFrames

/-- Actual demand derives its evaluating cell and retains every non-starting table. -/
theorem demand_frame {Key Request Answer : Type}
    (handle : Nat) (state : FlatMemoThunk.State Key Request Answer) :
    let actual := FlatMemoThunk.demand handle state
    actual.2.table = state.table ∧ actual.2.next = state.next ∧
      match actual.1 with
      | .evaluate original =>
          state.cells handle = some ⟨original, .suspended⟩ ∧
          actual.2.cells handle = some ⟨original, .evaluating⟩
      | .absent | .busy | .ready _ => actual.2 = state := by
  cases stored : state.cells handle with
  | none =>
      simpa only [FlatMemoThunk.demand, stored] using
        (show state.table = state.table ∧ state.next = state.next ∧ state = state from ⟨rfl, rfl, rfl⟩)
  | some cell =>
      cases cell with
      | mk original status =>
          cases status with
          | suspended =>
              have fields : (FlatMemoThunk.setStatus handle .evaluating state).table = state.table ∧
                  (FlatMemoThunk.setStatus handle .evaluating state).next = state.next := by
                rw [FlatMemoThunk.setStatus, stored]
                exact ⟨rfl, rfl⟩
              have installed := FlatMemoThunk.setStatus_cell handle .evaluating state
                ⟨original, .suspended⟩ stored
              simpa only [FlatMemoThunk.demand, stored] using
                (show (FlatMemoThunk.setStatus handle .evaluating state).table = state.table ∧
                  (FlatMemoThunk.setStatus handle .evaluating state).next = state.next ∧
                  state.cells handle = some ⟨original, .suspended⟩ ∧
                  (FlatMemoThunk.setStatus handle .evaluating state).cells handle =
                    some ⟨original, .evaluating⟩ from ⟨fields.1, fields.2, stored, installed⟩)
          | evaluating =>
              simpa only [FlatMemoThunk.demand, stored] using
                (show state.table = state.table ∧ state.next = state.next ∧ state = state from ⟨rfl, rfl, rfl⟩)
          | returned value =>
              simpa only [FlatMemoThunk.demand, stored] using
                (show state.table = state.table ∧ state.next = state.next ∧ state = state from ⟨rfl, rfl, rfl⟩)

/-- Literal native lookup and demand derive the original cold request without a future frame premise. -/
theorem node_lookup_demand_frame {Symbol Guard : Type} (width : Nat)
    (request : SourceRecursiveIntersectionThunks.NodeRequest Symbol Guard)
    (state : SourceRecursiveIntersectionThunks.State width Symbol Guard) :
    let selected := SourceRecursiveIntersectionThunks.lookupNode width request state
    match selected.1 with
    | .direct original => original = request ∧ selected.2 = state
    | .memoized handle =>
        selected.2.machine = state.machine ∧ selected.2.edges = state.edges ∧
          (∀ key, SourceRecursiveIntersectionMemo.requestKey width request.domain request.left request.right = some key →
            state.nodes.table key = none →
            handle = state.nodes.next ∧ selected.2.nodes.cells handle = some ⟨request, .suspended⟩) ∧
          let actual := FlatMemoThunk.demand handle selected.2.nodes
          actual.2.table = selected.2.nodes.table ∧ actual.2.next = selected.2.nodes.next ∧
            match actual.1 with
            | .evaluate original =>
                selected.2.nodes.cells handle = some ⟨original, .suspended⟩ ∧
                actual.2.cells handle = some ⟨original, .evaluating⟩
            | .absent | .busy | .ready _ => actual.2 = selected.2.nodes := by
  cases keyed : SourceRecursiveIntersectionMemo.requestKey width request.domain request.left request.right with
  | none =>
      simpa only [SourceRecursiveIntersectionThunks.lookupNode, keyed] using
        (show request = request ∧ state = state from ⟨rfl, rfl⟩)
  | some key =>
      cases looked : FlatMemoThunk.lookupOrInsert key request state.nodes with
      | mk handle nodes =>
          simp only [SourceRecursiveIntersectionThunks.lookupNode, keyed, looked]
          refine ⟨True.intro, True.intro, ?_, ?_⟩
          intro other same missing
          have keyEq : key = other := Option.some.inj same
          subst other
          have published := FlatMemoThunk.lookup_miss key request state.nodes missing
          rw [looked] at published
          have handleEq : handle = state.nodes.next := published.1
          exact ⟨handleEq, by rw [handleEq]; exact published.2.2⟩
          have frame := demand_frame handle nodes
          refine ⟨frame.1, frame.2.1, ?_⟩
          cases observed : (FlatMemoThunk.demand handle nodes).1 <;>
            simpa only [observed] using frame.2.2

end MicroCFTA.SourceCurrentNativeDemandFrames
