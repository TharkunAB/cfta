import MicroCFTA.SourceInternedRowsValidated
import MicroCFTA.EnumerationInternedRows

/-!
# Issued-row heap instantiation of the shared adapter

The existing constructor cache supplies immutable node rows and a finite
identity bound. Child availability is a local heap invariant. It derives
finite traversal and excludes the empty-child validation case. Equality
tries and residual guards stay in the same annotation pair.
-/
namespace MicroCFTA.SourceInternedRows

/-- Store both kinds of source edge constraint without evaluating either. -/
abbrev Annotation (Guard : Type) := List EqualityTrie.Trie × Option Guard

/-- The bounded constructor row model uses only issued child identities. -/
def exposure (edge : EnumerationState.Edge Symbol Guard) : Row Symbol (Annotation Guard) :=
  ⟨edge.symbol, edge.children.map some, (edge.equalities, edge.residual)⟩

/-- Read an immutable issued-row snapshot through the existing cache adapter. -/
def issuedHeap (state : Cache.State (EnumerationInternedRows.RowKey Symbol Guard)) : Heap Symbol (Annotation Guard) :=
  fun identity => (EnumerationInternedRows.lookup state identity).map exposure

/-- Every stored edge child has an available row in the same snapshot. -/
def ChildrenIssued (state : Cache.State (EnumerationInternedRows.RowKey Symbol Guard)) : Prop :=
  ∀ identity key, state.issued identity = some key →
    ∀ edge ∈ key, ∀ child ∈ edge.children, ∃ childKey, state.issued child = some childKey

/-- Exposed children are exactly the original issued child IDs. -/
theorem issued_successors (state : Cache.State (EnumerationInternedRows.RowKey Symbol Guard)) (identity : Nat) :
    successors (issuedHeap state) identity =
      (EnumerationInternedRows.lookup state identity).flatMap EnumerationState.Edge.children := by
  simp [successors, children, issuedHeap, exposure, List.flatMap_map, List.filterMap_flatMap,
    List.filterMap_map]

/-- The allocation supply derives a finite closed domain for the source traversal. -/
theorem issued_closed (state : Cache.State (EnumerationInternedRows.RowKey Symbol Guard))
    (valid : Cache.Valid state) (children : ChildrenIssued state) :
    ClosedDomain (issuedHeap state) (List.range state.next) := by
  intro identity _ child member
  rw [issued_successors] at member
  cases issued : state.issued identity with
  | none => simp [EnumerationInternedRows.lookup, issued] at member
  | some key =>
    obtain ⟨edge, edgeIn, childIn⟩ := List.mem_flatMap.mp member
    have actual : edge ∈ key := by simpa [EnumerationInternedRows.lookup, issued] using edgeIn
    obtain ⟨childKey, available⟩ := children identity key issued edge actual child childIn
    exact List.mem_range.mpr (valid.1 child childKey available)

/-- Every exposed child is nonempty by the stored row representation itself. -/
theorem issued_noEmpty (state : Cache.State (EnumerationInternedRows.RowKey Symbol Guard)) (root : Ref) :
    NoEmptyBelow (issuedHeap state) root := by
  intro identity _ row member
  obtain ⟨edge, _, rfl⟩ := List.mem_map.mp member
  simp [exposure]

/-- An available interned root derives a stable finite complete row exposure. -/
theorem issued_toRows (state : Cache.State (EnumerationInternedRows.RowKey Symbol Guard))
    (valid : Cache.Valid state) (children : ChildrenIssued state) (identity : Nat)
    (key : EnumerationInternedRows.RowKey Symbol Guard) (issued : state.issued identity = some key) :
    ∃ fuel result, ∀ larger, fuel ≤ larger → toRows (issuedHeap state) larger (some identity) = some result := by
  apply toRows_finite (issuedHeap state) (List.range state.next) (issued_closed state valid children)
  intro next same
  have equal := Option.some.inj same
  subst next
  exact List.mem_range.mpr (valid.1 identity key issued)

/-- Completed issued-row exposure is a closed explicit table for every guard interpretation. -/
theorem issued_table_closed (state : Cache.State (EnumerationInternedRows.RowKey Symbol Guard))
    (holds : Annotation Guard → Language.Term Symbol → Bool) (fuel : Nat) (root : Ref)
    (result : List (State × List (Transition Symbol (Annotation Guard))))
    (done : toRows (issuedHeap state) fuel root = some result) :
    FTAValidation.Closed (interpretedRows holds result) :=
  toRows_closed (issuedHeap state) holds fuel root result done (issued_noEmpty state root)

/-- Cache growth preserves all rows at an already issued source identity. -/
theorem issued_stable (before after : Cache.State (EnumerationInternedRows.RowKey Symbol Guard))
    (growth : Cache.Extends before.issued after.issued) (identity : Nat)
    (key : EnumerationInternedRows.RowKey Symbol Guard) (issued : before.issued identity = some key) :
    issuedHeap before identity = issuedHeap after identity := by
  simp only [issuedHeap, EnumerationInternedRows.lookup_stable before after growth identity key issued]

/-- A constructor's canonical cache result gives the row adapter its actual requested row key. -/
theorem intern_exposure [DecidableEq (EnumerationInternedRows.RowKey Symbol Guard)]
    (before : Cache.State (EnumerationInternedRows.RowKey Symbol Guard)) (valid : Cache.Valid before)
    (key : EnumerationInternedRows.RowKey Symbol Guard) :
    issuedHeap (Cache.intern before key).2 (Cache.intern before key).1.identity = key.map exposure := by
  have issued := EnumerationInternedRows.intern_readback before valid key
  simp [issuedHeap, EnumerationInternedRows.lookup, issued]

end MicroCFTA.SourceInternedRows
