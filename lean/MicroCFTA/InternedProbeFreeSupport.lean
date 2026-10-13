import MicroCFTA.InternedSourceFreeNames

/-!
# Interned free names in recursive probe dependencies

An interned free name occurs in a complete Mu exactly when it occurs in
one of the two stored probes. A Mu boundary contributes all its free
names to its containing ordinary value. These facts propagate absence
through finite chains of stored probe dependencies. They do not exclude
a fresh Mu whose free-name set is empty.
-/
namespace MicroCFTA.InternedProbeFreeSupport
open Cache InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedFreshProbeKeys InternedNormalizationFree InternedBoundaryAtoms
open InternedFreeNameHeap InternedFreeNameDecoder InternedNestedConstruction InternedNestedProvenance
open InternedStoredMuOrigins
open InternedBinderProtocol (Reference NodeKey)

/-- An interned name survives decoding from either actual stored probe. -/
theorem interned_probe_member (entry : Interned NodeKey) (body depth ordinary : Value Symbol Guard)
    (correct : Correct entry body depth ordinary) (identity : Nat) :
    .interned identity ∈ (Value.mu entry body depth ordinary).free ↔
      .interned identity ∈ depth.free ∨ .interned identity ∈ ordinary.free := by
  simpa [decode] using correct (.interned identity)

/-- Absence of an interned name from a complete Mu implies absence from both probes. -/
theorem interned_probe_absent (entry : Interned NodeKey) (body depth ordinary : Value Symbol Guard)
    (correct : Correct entry body depth ordinary) (identity : Nat) :
    .interned identity ∉ (Value.mu entry body depth ordinary).free ↔
      .interned identity ∉ depth.free ∧ .interned identity ∉ ordinary.free := by
  rw [interned_probe_member entry body depth ordinary correct identity, not_or]

/-- Every free name of an available Mu boundary is free in its containing ordinary value. -/
theorem boundary_free (value : Value Symbol Guard) (state : State Symbol Guard) (coherent : Coherent state)
    (available : Available state value) (entry : Interned NodeKey) (body depth ordinary : Value Symbol Guard)
    (stored : Available state (.mu entry body depth ordinary))
    (boundary : .mu entry.identity ∈ atoms value) (name : Reference)
    (member : name ∈ (Value.mu entry body depth ordinary).free) : name ∈ value.free := by
  cases value with
  | empty | reference => simp [atoms] at boundary
  | node own edges level free =>
      obtain ⟨edge, included, child, selected, boundary⟩ :=
        (edge_member edges (.mu entry.identity)).mp (by simpa only [atoms] using boundary)
      have childMember : child ∈ edges.flatMap EdgeValue.children := List.mem_flatMap.mpr ⟨edge, included, selected⟩
      have childFree := boundary_free child state coherent (available.children child childMember)
        entry body depth ordinary stored boundary name member
      rw [Value.free, node_free state coherent own edges level free available.resident, childFree_member]
      exact ⟨child, childMember, childFree⟩
  | union own members level free =>
      obtain ⟨child, included, boundary⟩ :=
        (many_member members (.mu entry.identity)).mp (by simpa only [atoms] using boundary)
      have childFree := boundary_free child state coherent (available.children child included)
        entry body depth ordinary stored boundary name member
      rw [Value.free, union_free state coherent own members level free available.resident, childFree_member]
      exact ⟨child, included, childFree⟩
  | mu own ownBody ownDepth ownOrdinary =>
      have sameIdentity : entry.identity = own.identity := by simpa [atoms] using boundary
      have same := resident_reference_injective state coherent (.mu entry body depth ordinary)
        (.mu own ownBody ownDepth ownOrdinary) stored.resident available.resident
        (by simp only [Value.referenceOf, sameIdentity])
      exact same ▸ member
termination_by sizeOf value
decreasing_by
  · have edgeSmall := List.sizeOf_lt_of_mem included
    cases edge with
    | mk edgeEntry children =>
        have childSmall := List.sizeOf_lt_of_mem selected
        simp only [EdgeValue.children] at childSmall
        simp_wf
        simp only [EdgeValue.mk.sizeOf_spec] at edgeSmall
        subst value
        simp only [Value.node.sizeOf_spec]
        omega
  · have childSmall := List.sizeOf_lt_of_mem included
    simp_wf
    subst value
    simp only [Value.union.sizeOf_spec]
    omega

/-- A complete stored record supports each interned reference in its free-name set. -/
def Supports (state : State Symbol Guard) (key : NodeKey) (identity : Nat) : Prop :=
  ∃ value, state.nodeRecords key = some value ∧ .interned identity ∈ value.free

/-- A recursive probe dependency selects a complete Mu boundary in either stored probe. -/
def ProbeStep (state : State Symbol Guard) (first second : NodeKey) : Prop :=
  ∃ entry body depth ordinary nextEntry nextBody nextDepth nextOrdinary,
    state.nodeRecords first = some (.mu entry body depth ordinary) ∧
    state.nodeRecords second = some (.mu nextEntry nextBody nextDepth nextOrdinary) ∧
    (.mu nextEntry.identity ∈ atoms depth ∨ .mu nextEntry.identity ∈ atoms ordinary)

/-- Finite probe dependency chains include the original record. -/
inductive ProbeChain (state : State Symbol Guard) : NodeKey → NodeKey → Prop where
  | refl (key : NodeKey) : ProbeChain state key key
  | step {first middle last : NodeKey} (head : ProbeStep state first middle)
      (tail : ProbeChain state middle last) : ProbeChain state first last

/-- Every interned name supported by a Mu dependency is supported by its parent record. -/
theorem step_support (state : State Symbol Guard) (coherent : Coherent state) (cached : Cached state)
    (heap : Heap state) (first second : NodeKey) (step : ProbeStep state first second)
    (identity : Nat) (supported : Supports state second identity) : Supports state first identity := by
  obtain ⟨entry, body, depth, ordinary, nextEntry, nextBody, nextDepth, nextOrdinary,
    firstStored, secondStored, boundary⟩ := step
  obtain ⟨value, found, member⟩ := supported
  have same : value = .mu nextEntry nextBody nextDepth nextOrdinary := Option.some.inj (found.symm.trans secondStored)
  subst value
  have available := cached.nodes first _ firstStored
  have nextAvailable := cached.nodes second _ secondStored
  refine ⟨_, firstStored, (interned_probe_member entry body depth ordinary (heap _ _ _ _ _ firstStored) identity).mpr ?_⟩
  rcases boundary with boundary | boundary
  · exact Or.inl (boundary_free depth state coherent (available.children depth (by simp [children]))
      nextEntry nextBody nextDepth nextOrdinary nextAvailable boundary (.interned identity) member)
  · exact Or.inr (boundary_free ordinary state coherent (available.children ordinary (by simp [children]))
      nextEntry nextBody nextDepth nextOrdinary nextAvailable boundary (.interned identity) member)

/-- Interned free-name support propagates backwards along every finite probe dependency chain. -/
theorem chain_support (state : State Symbol Guard) (coherent : Coherent state) (cached : Cached state)
    (heap : Heap state) (first last : NodeKey) (chain : ProbeChain state first last)
    (identity : Nat) (supported : Supports state last identity) : Supports state first identity := by
  induction chain with
  | refl => exact supported
  | step head tail ih => exact step_support state coherent cached heap _ _ head identity (ih supported)

/-- Interned-name absence propagates forwards along every finite probe dependency chain. -/
theorem chain_absent (state : State Symbol Guard) (coherent : Coherent state) (cached : Cached state)
    (heap : Heap state) (first last : NodeKey) (chain : ProbeChain state first last)
    (identity : Nat) (absent : ¬ Supports state first identity) : ¬ Supports state last identity :=
  fun present => absent (chain_support state coherent cached heap first last chain identity present)

/-- A complete Mu cannot support its own bound reference. -/
theorem own_absent (state : State Symbol Guard) (key : NodeKey) (entry : Interned NodeKey)
    (body depth ordinary : Value Symbol Guard) (stored : state.nodeRecords key = some (.mu entry body depth ordinary)) :
    ¬ Supports state key entry.identity := by
  rintro ⟨value, found, member⟩
  have same : value = .mu entry body depth ordinary := Option.some.inj (found.symm.trans stored)
  subst value
  simp [Value.free] at member

/-- No recursive probe dependency supports the original complete Mu's own bound name. -/
theorem chain_own_absent (state : State Symbol Guard) (coherent : Coherent state) (cached : Cached state)
    (heap : Heap state) (first last : NodeKey) (chain : ProbeChain state first last)
    (entry : Interned NodeKey) (body depth ordinary : Value Symbol Guard)
    (stored : state.nodeRecords first = some (.mu entry body depth ordinary)) :
    ¬ Supports state last entry.identity :=
  chain_absent state coherent cached heap first last chain entry.identity (own_absent state first entry body depth ordinary stored)

/-- Actual closed source execution establishes support absence throughout each stored Mu's probe dependencies. -/
theorem closed_chain_own_absent [DecidableEq (EdgeKey Symbol Guard)] (expression : Syntax Symbol Guard)
    (first last : NodeKey) (chain : ProbeChain (build expression [] empty).state first last)
    (entry : Interned NodeKey) (body depth ordinary : Value Symbol Guard)
    (stored : (build expression [] empty).state.nodeRecords first = some (.mu entry body depth ordinary)) :
    ¬ Supports (build expression [] empty).state last entry.identity := by
  have normal := build_normal expression [] empty empty_normal (by simp [Values])
  exact chain_own_absent _ normal.facts.coherent normal.facts.cached (InternedNestedFreeNames.closed_heap expression)
    first last chain entry body depth ordinary stored

end MicroCFTA.InternedProbeFreeSupport
