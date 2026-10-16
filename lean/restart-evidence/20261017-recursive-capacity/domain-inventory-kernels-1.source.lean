import MicroCFTA.SourceRecursiveIntersectionDomainInventory

set_option linter.all true
set_option pp.explicit true
set_option pp.proofs true
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 1000000
set_option pp.fullNames true

namespace MicroCFTA.DomainInventoryChecks
open SourceRecursiveIntersectionDomainInventory SourceRecursiveIntersectionDomain
open IntersectionFlatMemoKeyDomain InternedBinderProtocol

/-- Two actual source extensions retain canonical names and ordered pairs after repeated bindings. -/
theorem repeated_bindings_two_pairs :
    let first := SourceRecursiveIntersectionDomain.extend IntersectionEmptyDomain.emptyKey [1, 0, 1] (1, 0)
    let second := SourceRecursiveIntersectionDomain.extend first [0, 1, 0] (0, 1)
    second ∈ inventory [0, 1] [(0, 1), (1, 0)] ∧
      second.free = [(0, NodeRef.mu 0), (1, NodeRef.mu 1)] ∧ second.seen = [(0, 1), (1, 0)] := by
  dsimp only
  refine ⟨extend_mem (extend_mem (empty_mem _ _) [1, 0, 1] (1, 0) (by simp) (by simp))
    [0, 1, 0] (0, 1) (by simp) (by simp), ?_⟩
  decide

/-- A finite extension sequence uses the original inventory regardless of its length or repetitions. -/
theorem extension_sequence (binders : List Nat) (pairs : List (Nat × Nat))
    (steps : List (List Nat × (Nat × Nat)))
    (inputs : ∀ step ∈ steps, (∀ name ∈ step.1, name ∈ binders) ∧ step.2 ∈ pairs) :
    ∀ key, key ∈ inventory binders pairs →
      steps.foldl (fun current step => SourceRecursiveIntersectionDomain.extend current step.1 step.2) key ∈
        inventory binders pairs := by
  induction steps with
  | nil => intro key member; exact member
  | cons first rest ih =>
      intro key member
      have firstInputs := inputs first List.mem_cons_self
      exact ih (fun step inside => inputs step (List.mem_cons_of_mem first inside)) _
        (extend_mem member first.1 first.2 firstInputs.1 firstInputs.2)

/-- Every distinct supported family has the same initial power-of-two bound. -/
theorem arbitrary_distinct_family (binders : List Nat) (pairs : List (Nat × Nat)) (keys : List DomainKey)
    (distinct : keys.Nodup)
    (canonical : ∀ key ∈ keys, IntersectionFlatMemoKeyDomain.Canonical key)
    (typed : ∀ key ∈ keys, SourceRecursiveIntersectionDomain.Typed key)
    (names : ∀ key ∈ keys, ∀ name ∈ SourceRecursiveIntersectionDomain.names key, name ∈ binders)
    (seen : ∀ key ∈ keys, ∀ pair ∈ key.seen, pair ∈ pairs) :
    keys.length ≤ 2 ^ (binders.length + pairs.length) :=
  supported_length_le binders pairs keys distinct
    (fun key member => ⟨canonical key member, typed key member, names key member, seen key member⟩)

/-- A free-map entry cannot silently point to a different Mu identity. -/
theorem foreign_mu_excluded :
    (⟨[(1, NodeRef.mu 2)], []⟩ : DomainKey) ∉ inventory [1, 2] [] := by
  intro member
  have typed := (supported_of_mem member).typed (1, NodeRef.mu 2) List.mem_cons_self
  cases typed

/-- Duplicate carrier entries increase the finite bound but do not change key membership. -/
theorem duplicate_carrier_membership (key : DomainKey) :
    key ∈ inventory [1, 0, 1] [(1, 0), (0, 1), (1, 0)] ↔
      key ∈ inventory [0, 1] [(0, 1), (1, 0)] := by
  rw [mem_inventory_iff, mem_inventory_iff]
  constructor
  · intro supported
    exact supported.mono (by intro name member; simpa [or_comm, or_left_comm, or_assoc] using member)
      (by intro pair member; simpa [or_comm, or_left_comm, or_assoc] using member)
  · intro supported
    exact supported.mono (by intro name member; simpa [or_comm, or_left_comm, or_assoc] using member)
      (by intro pair member; simpa [or_comm, or_left_comm, or_assoc] using member)

#print axioms repeated_bindings_two_pairs
#check @repeated_bindings_two_pairs
#print axioms extension_sequence
#check @extension_sequence
#print axioms arbitrary_distinct_family
#check @arbitrary_distinct_family
#print axioms foreign_mu_excluded
#check @foreign_mu_excluded
#print axioms duplicate_carrier_membership
#check @duplicate_carrier_membership
end MicroCFTA.DomainInventoryChecks
