import MicroCFTA.EnumerationSharedRows

/-!
# Interned bounded-row construction

Each constructor step reads its already issued children and interns its row
key. Cache growth preserves those reads and the returned row key. The theorem
is scoped to that constructor step. It does not require a finite cache to
contain the results of every possible depth bound.
-/

namespace MicroCFTA.EnumerationInternedRows
open EnumerationState EnumerationSemantics EnumerationSharedRows

abbrev RowKey (Symbol Guard : Type) := List (Edge Symbol Guard)

/-- Issued identities name immutable constructor row keys. -/
def lookup (state : Cache.State (RowKey Symbol Guard)) (identity : Nat) : RowKey Symbol Guard :=
  (state.issued identity).getD []

/-- Interned row keys contain only checked constructor edges. -/
def StoredValid (state : Cache.State (RowKey Symbol Guard)) : Prop :=
  ∀ identity key, state.issued identity = some key → ∀ edge ∈ key, ValidEdge edge

/-- Read the finite interned row table as an enumeration graph. -/
def graph (state : Cache.State (RowKey Symbol Guard)) (meet : Nat → Nat → Nat) : Graph Symbol Guard where
  node identity := match lookup state identity with | [] => .empty | edge :: rest => .alternatives (edge :: rest)
  intersect := meet

theorem graph_rows (state : Cache.State (RowKey Symbol Guard)) (meet : Nat → Nat → Nat) (identity : Nat) :
    nodeRows (graph state meet) identity = lookup state identity := by
  cases found : lookup state identity <;> simp [nodeRows, graph, found]

/-- A valid stored row table derives the complete enumeration invariant. -/
theorem complete (state : Cache.State (RowKey Symbol Guard)) (meet : Nat → Nat → Nat)
    (valid : StoredValid state) : CompleteGraph (graph state meet) := by
  constructor
  · intro node body
    cases found : lookup state node <;> simp [graph, found]
  · intro node edges view edge member
    have present : edge ∈ lookup state node := by
      cases found : lookup state node with
      | nil => simp [graph, found] at view
      | cons first rest =>
          simp only [graph, found, Node.alternatives.injEq] at view
          simpa only [view] using member
    cases issued : state.issued node with
    | none => simp [lookup, issued] at present
    | some key => exact valid node key issued edge (by simpa [lookup, issued] using present)

/-- Issued row keys do not change when the cache grows. -/
theorem lookup_stable (before after : Cache.State (RowKey Symbol Guard))
    (growth : Cache.Extends before.issued after.issued) (identity : Nat) (key : RowKey Symbol Guard)
    (issued : before.issued identity = some key) : lookup before identity = lookup after identity := by
  simp [lookup, issued, growth identity key issued]

/-- Sequential interning preserves every already issued constructor key. -/
theorem intern_grows [DecidableEq (RowKey Symbol Guard)] (state : Cache.State (RowKey Symbol Guard))
    (valid : Cache.Valid state) (key : RowKey Symbol Guard) :
    Cache.Extends state.issued (Cache.intern state key).2.issued := by
  cases found : state.table key with
  | some entry => simpa [Cache.intern, found] using Cache.extends_refl state.issued
  | none => simpa [Cache.intern, found, Cache.install] using Cache.reserve_extends state key valid

/-- Interning returns the requested row key, including a cache hit on an equal output. -/
theorem intern_readback [DecidableEq (RowKey Symbol Guard)] (state : Cache.State (RowKey Symbol Guard))
    (valid : Cache.Valid state) (key : RowKey Symbol Guard) :
    (Cache.intern state key).2.issued (Cache.intern state key).1.identity = some key := by
  obtain ⟨safe, present, _⟩ := Cache.intern_correct state key valid
  exact (safe.2 key _ present).2

/-- Interning a checked row key preserves validity of every stored edge. -/
theorem intern_storedValid [DecidableEq (RowKey Symbol Guard)] (state : Cache.State (RowKey Symbol Guard))
    (stored : StoredValid state) (key : RowKey Symbol Guard) (checked : ∀ edge ∈ key, ValidEdge edge) :
    StoredValid (Cache.intern state key).2 := by
  cases found : state.table key with
  | some entry => simpa [Cache.intern, found] using stored
  | none =>
      intro identity actual issued edge member
      by_cases fresh : identity = state.next
      · have same : key = actual := by simpa [Cache.intern, found, Cache.install, Cache.reserve, fresh] using issued
        exact checked edge (same ▸ member)
      · have old : state.issued identity = some actual := by
          simpa [Cache.intern, found, Cache.install, Cache.reserve, fresh] using issued
        exact stored identity actual old edge member

/-- A constructor step needs only the child rows it reads at this bound. -/
def ChildrenReady (encode : Nat × Nat → Nat) (source : Nat → RowKey Symbol Guard)
    (state : Cache.State (RowKey Symbol Guard)) : Nat → Nat → Prop
  | 0, _ => True
  | remaining + 1, node => ∀ edge ∈ source node, ∀ child ∈ edge.children,
      ∃ key, state.issued (encode (remaining, child)) = some key

/-- Later cache growth preserves this step's empty-child checks. -/
theorem construct_stable (encode : Nat × Nat → Nat) (source : Nat → RowKey Symbol Guard)
    (before after : Cache.State (RowKey Symbol Guard)) (growth : Cache.Extends before.issued after.issued)
    (height node : Nat) (ready : ChildrenReady encode source before height node) :
    construct encode (lookup before) source height node = construct encode (lookup after) source height node := by
  cases height with
  | zero => rfl
  | succ remaining =>
      unfold construct
      apply congrArg (List.map (EnumerationBoundedRows.copyEdge encode remaining))
      apply List.filter_congr
      intro edge filtered
      apply Bool.eq_iff_iff.mpr
      simp only [List.all_eq_true]
      have reads : ∀ child ∈ edge.children, lookup before (encode (remaining, child)) = lookup after (encode (remaining, child)) := by
        intro child member
        obtain ⟨key, issued⟩ := ready edge (List.mem_filter.mp filtered).1 child member
        exact lookup_stable before after growth _ key issued
      constructor
      · intro kept child member
        rw [← reads child member]
        exact kept child member
      · intro kept child member
        rw [reads child member]
        exact kept child member

/-- Execute one bounded constructor step and return its canonical interned identity. -/
def step [DecidableEq (RowKey Symbol Guard)] (encode : Nat × Nat → Nat) (source : Nat → RowKey Symbol Guard)
    (height node : Nat) (state : Cache.State (RowKey Symbol Guard)) :
    Cache.Interned (RowKey Symbol Guard) × Cache.State (RowKey Symbol Guard) :=
  Cache.intern state (construct encode (lookup state) source height node)

/-- A completed constructor step has exact row readback after any permitted cache growth. -/
theorem step_final_readback [DecidableEq (RowKey Symbol Guard)] (encode : Nat × Nat → Nat)
    (source : Nat → RowKey Symbol Guard) (height node : Nat) (before final : Cache.State (RowKey Symbol Guard))
    (valid : Cache.Valid before) (ready : ChildrenReady encode source before height node)
    (growth : Cache.Extends (step encode source height node before).2.issued final.issued) :
    lookup final (step encode source height node before).1.identity = construct encode (lookup final) source height node := by
  have issued := intern_readback before valid (construct encode (lookup before) source height node)
  have stored := growth _ _ issued
  simp only [lookup, step, stored, Option.getD_some]
  exact construct_stable encode source before final
    (Cache.extends_trans (intern_grows before valid _) growth) height node ready

end MicroCFTA.EnumerationInternedRows
