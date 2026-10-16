import MicroCFTA.SourceRecursiveIntersectionDomain
import MicroCFTA.SourceLeafRowProgress

/-!
# Finite canonical domains over original source identities

The inventory uses subsets of initial binder names and operand pairs.
Each free entry maps its name to the same Mu reference. Canonicalization
removes repeated names and pairs. The list length is a conservative bound.
-/
namespace MicroCFTA.SourceRecursiveIntersectionDomainInventory
open IntersectionFlatMemoKeyDomain SourceRecursiveIntersectionDomain
open CanonicalClasses InternedBinderProtocol Std
attribute [local instance] lexOrd

/-- A domain uses only the initial names and pairs, with exact source readback. -/
structure Supported (binders : List Nat) (pairs : List (Nat × Nat)) (key : DomainKey) : Prop where
  /-- Both source containers use ascending key order. -/
  canonical : Canonical key
  /-- Each free name maps to its own Mu reference. -/
  typed : Typed key
  /-- Every free name comes from the initial binder carrier. -/
  names : ∀ name ∈ SourceRecursiveIntersectionDomain.names key, name ∈ binders
  /-- Every remembered pair comes from the initial operand carrier. -/
  seen : ∀ pair ∈ key.seen, pair ∈ pairs

/-- Canonicalize a selected set of own-identity Mu bindings and recursive pairs. -/
def canonical (binders : List Nat) (pairs : List (Nat × Nat)) : DomainKey :=
  ⟨(sortedSet binders).map (fun name => (name, NodeRef.mu name)), sortedSet pairs⟩

/-- Every selected key has the source's ascending map and set order. -/
theorem canonical_canonical (binders : List Nat) (pairs : List (Nat × Nat)) : Canonical (canonical binders pairs) :=
  ⟨List.pairwise_map.mpr (nat_ordered binders), pairs_ordered pairs⟩

/-- Every selected free entry points to its own original Mu identity. -/
theorem canonical_typed (binders : List Nat) (pairs : List (Nat × Nat)) : Typed (canonical binders pairs) := by
  intro binding member
  obtain ⟨name, _, rfl⟩ := List.mem_map.mp member
  rfl

/-- Canonicalization keeps exactly the selected binder names. -/
theorem canonical_names (binders : List Nat) (pairs : List (Nat × Nat)) :
    names (canonical binders pairs) = sortedSet binders := by
  simp [names, canonical, List.map_map, Function.comp_def]

/-- Typed entries can be reconstructed from their name list. -/
theorem typed_free (key : DomainKey) (typed : Typed key) :
    key.free = (names key).map (fun name => (name, NodeRef.mu name)) := by
  rw [names, List.map_map]
  symm
  calc
    _ = key.free.map id := by
      apply List.map_congr_left
      intro binding member
      exact Prod.ext rfl (typed binding member).symm
    _ = key.free := List.map_id

/-- Canonical typed domains are determined by their free names and seen pairs. -/
theorem canonical_eq (key : DomainKey) (ordered : Canonical key) (typed : Typed key)
    (binders : List Nat) (pairs : List (Nat × Nat))
    (sameNames : ∀ name, name ∈ binders ↔ name ∈ names key)
    (samePairs : ∀ pair, pair ∈ pairs ↔ pair ∈ key.seen) : canonical binders pairs = key := by
  apply (canonical_eq_iff _ _ (canonical_canonical binders pairs) ordered).mpr
  constructor
  · intro binding
    rw [typed_free key typed]
    simp only [canonical, List.mem_map, mem_sortedSet]
    exact exists_congr (fun name => and_congr_left (fun _ => sameNames name))
  · intro pair
    exact (mem_sortedSet pairs pair).trans (samePairs pair)

/-- Enumerate every canonical source key from initial subset choices. -/
def inventory (binders : List Nat) (pairs : List (Nat × Nat)) : List DomainKey :=
  (SourceLeafRowProgress.subsets binders).flatMap fun selectedNames =>
    (SourceLeafRowProgress.subsets pairs).map (canonical selectedNames)

/-- Every enumerated key uses only the initial carrier. -/
theorem supported_of_mem {binders : List Nat} {pairs : List (Nat × Nat)} {key : DomainKey}
    (member : key ∈ inventory binders pairs) : Supported binders pairs key := by
  obtain ⟨selectedNames, namesMember, rest⟩ := List.mem_flatMap.mp member
  obtain ⟨selectedPairs, pairsMember, rfl⟩ := List.mem_map.mp rest
  refine ⟨canonical_canonical _ _, canonical_typed _ _, ?_, ?_⟩
  · intro name member
    rw [canonical_names] at member
    exact SourceLeafRowProgress.subsets_subset binders selectedNames namesMember name
      ((mem_sortedSet _ _).mp member)
  · intro pair member
    exact SourceLeafRowProgress.subsets_subset pairs selectedPairs pairsMember pair
      ((mem_sortedSet _ _).mp member)

/-- Filtering the initial carriers supplies a witness for every supported domain. -/
theorem mem_of_supported {binders : List Nat} {pairs : List (Nat × Nat)} {key : DomainKey}
    (supported : Supported binders pairs key) : key ∈ inventory binders pairs := by
  let chosenNames := binders.filter fun name => decide (name ∈ names key)
  let chosenPairs := pairs.filter fun pair => decide (pair ∈ key.seen)
  have same : canonical chosenNames chosenPairs = key := by
    apply canonical_eq key supported.canonical supported.typed
    · intro name
      simp only [chosenNames, List.mem_filter, decide_eq_true_eq]
      exact and_iff_right_of_imp (supported.names name)
    · intro pair
      simp only [chosenPairs, List.mem_filter, decide_eq_true_eq]
      exact and_iff_right_of_imp (supported.seen pair)
  apply List.mem_flatMap.mpr
  refine ⟨chosenNames, SourceLeafRowProgress.filter_mem_subsets _ _, ?_⟩
  exact List.mem_map.mpr ⟨chosenPairs, SourceLeafRowProgress.filter_mem_subsets _ _, same⟩

/-- Inventory membership is exactly canonical typed support in the initial carrier. -/
theorem mem_inventory_iff (binders : List Nat) (pairs : List (Nat × Nat)) (key : DomainKey) :
    key ∈ inventory binders pairs ↔ Supported binders pairs key :=
  ⟨supported_of_mem, mem_of_supported⟩

/-- The explicit inventory length counts all subset choices before duplicate removal. -/
theorem inventory_length (binders : List Nat) (pairs : List (Nat × Nat)) :
    (inventory binders pairs).length = 2 ^ (binders.length + pairs.length) := by
  simp [inventory, List.length_flatMap, SourceLeafRowProgress.subsets_length,
    List.map_const', List.sum_replicate_nat, Nat.pow_add]

/-- The source constant empty domain is supported for every initial carrier. -/
theorem supported_empty (binders : List Nat) (pairs : List (Nat × Nat)) :
    Supported binders pairs IntersectionEmptyDomain.emptyKey := by
  constructor
  · constructor <;> simp [IntersectionEmptyDomain.emptyKey]
  · intro binding member; cases member
  · intro name member; cases member
  · intro pair member; cases member

/-- The source constant empty domain belongs to every inventory. -/
theorem empty_mem (binders : List Nat) (pairs : List (Nat × Nat)) :
    IntersectionEmptyDomain.emptyKey ∈ inventory binders pairs := mem_of_supported (supported_empty binders pairs)

/-- Actual source extension stays within the original name and pair carrier. -/
theorem Supported.extend {binders : List Nat} {pairs : List (Nat × Nat)} {key : DomainKey}
    (supported : Supported binders pairs key) (bound : List Nat) (pair : Nat × Nat)
    (boundNames : ∀ name ∈ bound, name ∈ binders) (pairMember : pair ∈ pairs) :
    Supported binders pairs (SourceRecursiveIntersectionDomain.extend key bound pair) := by
  refine ⟨extend_canonical _ _ _, extend_typed _ _ _, ?_, ?_⟩
  · intro name member
    rcases (extend_names key bound pair name).mp member with new | old
    · exact boundNames name new
    · exact supported.names name old
  · intro next member
    rcases (extend_seen key bound pair next).mp member with rfl | old
    · exact pairMember
    · exact supported.seen next old

/-- Actual source extension of an enumerated key produces another enumerated key. -/
theorem extend_mem {binders : List Nat} {pairs : List (Nat × Nat)} {key : DomainKey}
    (member : key ∈ inventory binders pairs) (bound : List Nat) (pair : Nat × Nat)
    (boundNames : ∀ name ∈ bound, name ∈ binders) (pairMember : pair ∈ pairs) :
    SourceRecursiveIntersectionDomain.extend key bound pair ∈ inventory binders pairs :=
  mem_of_supported ((supported_of_mem member).extend bound pair boundNames pairMember)

end MicroCFTA.SourceRecursiveIntersectionDomainInventory
