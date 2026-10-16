import MicroCFTA.InternedConstructorTemplates

/-!
# Constructor reservation counts

The observed Work trace records each actual request and its initial lookup.
Only a miss reserves an identity in sequential Work.
Atomic traces count every reservation, including candidates that lose an insert.
The results do not bound other callers or repeated host evaluations.
-/
namespace MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryReservations
open Cache InternedConstructorTemplates
open InternedBinderProtocol (NodeKey)

section Cache
variable {Key : Type} [DecidableEq Key]

/-- A hit consumes no identity; a miss consumes one identity. -/
theorem intern_next (state : Cache.State Key) (key : Key) :
    (Cache.intern state key).2.next = state.next + (if (state.table key).isNone then 1 else 0) := by
  cases found : state.table key <;> simp [Cache.intern, found, Cache.reserve, Cache.install]

/-- Sequential interning preserves every earlier issued candidate. -/
theorem intern_issued (state : Cache.State Key) (key : Key) (valid : Cache.Valid state) :
    Extends state.issued (Cache.intern state key).2.issued := by
  cases found : state.table key with
  | some entry => simpa [Cache.intern, found] using extends_refl state.issued
  | none => simpa [Cache.intern, found, Cache.install] using reserve_extends state key valid

/-- The count increases only at an actual atomic reservation. -/
inductive AtomicTrace : Cache.State Key → Cache.State Key → Nat → Prop where
  | refl (state : Cache.State Key) : AtomicTrace state state 0
  | reserve (earlier : AtomicTrace before current count) (key : Key) :
      AtomicTrace before (Cache.reserve current key).2 (count + 1)
  | install (earlier : AtomicTrace before current count) (candidate : Interned Key)
      (issued : current.issued candidate.identity = some candidate.key) :
      AtomicTrace before (Cache.install current candidate) count

variable {before after : Cache.State Key} {count : Nat}

/-- The counted trace retains the actual atomic schedule. -/
theorem AtomicTrace.steps (actual : AtomicTrace before after count) : Cache.Steps before after := by
  induction actual with
  | refl => exact .refl _
  | reserve earlier key ih => exact .next ih (.reserve _ key)
  | install earlier candidate issued ih => exact .next ih (.install _ candidate issued)

/-- Every finite atomic schedule has its own reservation count. -/
theorem AtomicTrace.of_steps (actual : Cache.Steps before after) :
    ∃ count, AtomicTrace before after count := by
  induction actual with
  | refl => exact ⟨0, .refl _⟩
  | next earlier one ih =>
      obtain ⟨count, counted⟩ := ih
      cases one with
      | reserve key => exact ⟨count + 1, .reserve counted key⟩
      | install candidate issued => exact ⟨count, .install counted candidate issued⟩

/-- Installation cannot refund a reservation, including a losing reservation. -/
theorem AtomicTrace.next_exact (actual : AtomicTrace before after count) :
    after.next = before.next + count := by
  induction actual with
  | refl => omega
  | reserve earlier key ih => simp only [Cache.reserve] at *; omega
  | install earlier candidate issued ih => simpa only [Cache.install] using ih

/-- A valid initial supply retains its entire issued history. -/
theorem AtomicTrace.issued (actual : AtomicTrace before after count) (valid : Cache.Valid before) :
    Extends before.issued after.issued := Cache.steps_issued_extends valid actual.steps

end Cache

section Work
variable {Symbol Guard Result First : Type}
variable [DecidableEq (EdgeKey Symbol Guard)]

/-- One request records its cache family, actual key, and initial miss. -/
inductive Request (Symbol Guard : Type) where
  | node (key : NodeKey) (miss : Bool)
  | edge (key : EdgeKey Symbol Guard) (miss : Bool)

/-- Count node-cache requests without inspecting counters. -/
def nodeRequests : List (Request Symbol Guard) → Nat
  | [] => 0
  | .node _ _ :: rest => 1 + nodeRequests rest
  | .edge _ _ :: rest => nodeRequests rest

/-- Count edge-cache requests without inspecting counters. -/
def edgeRequests : List (Request Symbol Guard) → Nat
  | [] => 0
  | .node _ _ :: rest => edgeRequests rest
  | .edge _ _ :: rest => 1 + edgeRequests rest

/-- Count node-cache misses in the recorded request list. -/
def nodeReservations : List (Request Symbol Guard) → Nat
  | [] => 0
  | .node _ miss :: rest => (if miss then 1 else 0) + nodeReservations rest
  | .edge _ _ :: rest => nodeReservations rest

/-- Count edge-cache misses in the recorded request list. -/
def edgeReservations : List (Request Symbol Guard) → Nat
  | [] => 0
  | .node _ _ :: rest => edgeReservations rest
  | .edge _ miss :: rest => (if miss then 1 else 0) + edgeReservations rest

/-- Observe the literal request order and the selected actual continuations. -/
def observe (work : Work Symbol Guard Result) (state : State Symbol Guard) : List (Request Symbol Guard) :=
  match work with
  | .pure _ => []
  | .node key identify next =>
      .node key (state.nodes.table key).isNone ::
        observe (next (nodeStep key identify state).1) (nodeStep key identify state).2
  | .edge key identify next =>
      .edge key (state.edges.table key).isNone ::
        observe (next (edgeStep key identify state).1) (edgeStep key identify state).2

omit [DecidableEq (EdgeKey Symbol Guard)] in
/-- A node request changes only its own supply. -/
theorem nodeStep_next (key : NodeKey) (identify : Interned NodeKey → Value Symbol Guard)
    (state : State Symbol Guard) :
    (nodeStep key identify state).2.nodes.next = state.nodes.next + (if (state.nodes.table key).isNone then 1 else 0) ∧
    (nodeStep key identify state).2.edges.next = state.edges.next := by
  exact ⟨intern_next state.nodes key, rfl⟩

/-- An edge request changes only its own supply. -/
theorem edgeStep_next (key : EdgeKey Symbol Guard)
    (identify : Interned (EdgeKey Symbol Guard) → EdgeValue Symbol Guard) (state : State Symbol Guard) :
    (edgeStep key identify state).2.edges.next = state.edges.next + (if (state.edges.table key).isNone then 1 else 0) ∧
    (edgeStep key identify state).2.nodes.next = state.nodes.next := by
  exact ⟨intern_next state.edges key, rfl⟩

/-- Both final counters equal their initial counters plus actual recorded misses. -/
theorem run_next (work : Work Symbol Guard Result) (state : State Symbol Guard) :
    (run work state).2.nodes.next = state.nodes.next + nodeReservations (observe work state) ∧
    (run work state).2.edges.next = state.edges.next + edgeReservations (observe work state) := by
  induction work generalizing state with
  | pure value => simp [run, observe, nodeReservations, edgeReservations]
  | node key identify next ih =>
      have tail := ih (nodeStep key identify state).1 (nodeStep key identify state).2
      have one := nodeStep_next key identify state
      simp only [run, observe, nodeReservations, edgeReservations]
      omega
  | edge key identify next ih =>
      have tail := ih (edgeStep key identify state).1 (edgeStep key identify state).2
      have one := edgeStep_next key identify state
      simp only [run, observe, nodeReservations, edgeReservations]
      omega

omit [DecidableEq (EdgeKey Symbol Guard)] in
/-- Actual misses cannot exceed the number of cache requests. -/
theorem reservations_le_requests (requests : List (Request Symbol Guard)) :
    nodeReservations requests ≤ nodeRequests requests ∧ edgeReservations requests ≤ edgeRequests requests := by
  induction requests with
  | nil => exact ⟨Nat.le_refl _, Nat.le_refl _⟩
  | cons first rest ih =>
      cases first with
      | node key miss => cases miss <;> simp_all [nodeReservations, edgeReservations, nodeRequests, edgeRequests] <;> omega
      | edge key miss => cases miss <;> simp_all [nodeReservations, edgeReservations, nodeRequests, edgeRequests] <;> omega

/-- Actual executed request counts bound both constructor supplies. -/
theorem run_next_le (work : Work Symbol Guard Result) (state : State Symbol Guard) :
    (run work state).2.nodes.next ≤ state.nodes.next + nodeRequests (observe work state) ∧
    (run work state).2.edges.next ≤ state.edges.next + edgeRequests (observe work state) := by
  have exactCounts := run_next work state
  have bounded := reservations_le_requests (observe work state)
  omega

/-- The Work execution retains both earlier issued histories. -/
theorem run_issued (work : Work Symbol Guard Result) (state : State Symbol Guard) (valid : Valid state) :
    Extends state.nodes.issued (run work state).2.nodes.issued ∧
    Extends state.edges.issued (run work state).2.edges.issued := by
  induction work generalizing state with
  | pure value => exact ⟨extends_refl _, extends_refl _⟩
  | node key identify next ih =>
      have one := nodeStep_correct key identify state valid
      have tail := ih (nodeStep key identify state).1 _ one.1
      exact ⟨extends_trans (intern_issued state.nodes key valid.2) tail.1, tail.2⟩
  | edge key identify next ih =>
      have one := edgeStep_correct key identify state valid
      have tail := ih (edgeStep key identify state).1 _ one.1
      exact ⟨tail.1, extends_trans (intern_issued state.edges key valid.1) tail.2⟩

/-- Sequencing concatenates the actual observed request lists. -/
theorem observe_bind (work : Work Symbol Guard First) (next : First → Work Symbol Guard Result)
    (state : State Symbol Guard) :
    observe (work.bind next) state = observe work state ++ observe (next (run work state).1) (run work state).2 := by
  induction work generalizing state with
  | pure value => rfl
  | node key identify resume ih => simp only [Work.bind, observe, run, List.cons_append, ih]
  | edge key identify resume ih => simp only [Work.bind, observe, run, List.cons_append, ih]

/-- One raw edge constructor makes exactly one edge-cache request. -/
theorem makeEdge_observe (symbol : Symbol) (guard : Guard) (children : List (Value Symbol Guard))
    (state : State Symbol Guard) :
    observe (makeEdge symbol guard children) state =
      [.edge ⟨symbol, children.map Value.referenceOf, guard⟩
        (state.edges.table ⟨symbol, children.map Value.referenceOf, guard⟩).isNone] := rfl

/-- A raw edge constructor reserves at most one edge identity and no node identity. -/
theorem makeEdge_next (symbol : Symbol) (guard : Guard) (children : List (Value Symbol Guard))
    (state : State Symbol Guard) :
    (run (makeEdge symbol guard children) state).2.nodes.next = state.nodes.next ∧
    (run (makeEdge symbol guard children) state).2.edges.next ≤ state.edges.next + 1 := by
  have actual := run_next (makeEdge symbol guard children) state
  simp only [makeEdge_observe, nodeReservations, edgeReservations] at actual
  split at actual <;> omega

/-- Filtering all rows emits no node-cache request; otherwise exactly one request occurs. -/
theorem makeNode_requests (edges : List (EdgeValue Symbol Guard)) (state : State Symbol Guard) :
    nodeRequests (observe (makeNode edges) state) =
      (if canonicalEdges (surviving edges) = [] then 0 else 1) ∧
    edgeRequests (observe (makeNode edges) state) = 0 := by
  unfold makeNode
  cases kept : canonicalEdges (surviving edges) <;>
    simp [observe, nodeRequests, edgeRequests]

/-- A raw node constructor reserves at most one node identity and no edge identity. -/
theorem makeNode_next (edges : List (EdgeValue Symbol Guard)) (state : State Symbol Guard) :
    (run (makeNode edges) state).2.nodes.next ≤ state.nodes.next + 1 ∧
    (run (makeNode edges) state).2.edges.next = state.edges.next := by
  have bounds := run_next_le (makeNode edges) state
  have exactCounts := run_next (makeNode edges) state
  have requests := makeNode_requests edges state
  have reserved := reservations_le_requests (observe (makeNode edges) state)
  split at requests <;> omega

end Work
end MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryReservations
