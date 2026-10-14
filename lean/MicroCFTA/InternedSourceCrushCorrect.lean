import MicroCFTA.InternedSourceCrushSummary

/-!
# Exact constraint meaning of the actual visited-node source fold

The final visited set covers every physical descendant. Its exact local
checks therefore give both semantic directions. Repeated canonical nodes,
arbitrary nested Mu, and root unions need no separate fold assumption.
-/
namespace MicroCFTA.InternedSourceCrush
open Cache InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedBinderProtocol (NodeKey)
open InternedEdgeResidency (nodeEdges)

/-- Every source traversal child is an available protocol child. -/
theorem source_children_subset (value : Value Symbol Guard) : sourceChildren value ⊆ children value := by
  cases value <;> simp [sourceChildren, children]

/-- Physical descendants retain their complete availability in the actual source cache. -/
theorem Reaches.available (state : State Symbol Guard) (inputs : ∀ value ∈ roots, Available state value)
    (reached : Reaches roots value) : Available state value := by
  induction reached with
  | root value member => exact inputs value member
  | child parent child reached member ih => exact ih.children child (source_children_subset parent member)

/-- A record with source children has its own canonical node entry. -/
theorem source_parent_entry (value child : Value Symbol Guard) (member : child ∈ sourceChildren value) :
    ∃ entry, entryOf value = some entry := by
  cases value with
  | empty | reference => simp [sourceChildren] at member
  | node | union | mu => exact ⟨_, rfl⟩

/-- A record without a canonical entry has no local edge constraint. -/
theorem primitive_plain (plain : Guard → Bool) (value : Value Symbol Guard) (primitive : entryOf value = none) :
    localPlain plain value = true := by
  cases value <;> simp_all [entryOf, localPlain, nodeEdges]

/-- The actual completed traversal covers every canonical physical descendant. -/
theorem Summary.reachable_seen (plain : Guard → Bool) (state : State Symbol Guard)
    (roots : List (Value Symbol Guard)) (result : Bool × List Nat)
    (summary : Summary plain state roots [] result) (inputs : ∀ value ∈ roots, Available state value)
    (reached : Reaches roots value) : ∀ entry, entryOf value = some entry → entry.identity ∈ result.2 := by
  induction reached with
  | root value member => exact summary.entered value member
  | child parent child reached member ih =>
      intro entry field
      obtain ⟨parentEntry, parentField⟩ := source_parent_entry parent child member
      have parentAvailable := reached.available state inputs
      exact summary.closed parent parentEntry parentAvailable parentField (ih parentEntry parentField)
        (by simp) child member entry field

/-- An exact source summary checks precisely all local constraints of its physical descendants. -/
theorem Summary.exact (plain : Guard → Bool) (state : State Symbol Guard)
    (roots : List (Value Symbol Guard)) (result : Bool × List Nat)
    (summary : Summary plain state roots [] result) (inputs : ∀ value ∈ roots, Available state value) :
    result.1 = true ↔ ∀ value, Reaches roots value → localPlain plain value = true := by
  constructor
  · intro success value reached
    cases field : entryOf value with
    | none => exact primitive_plain plain value field
    | some entry =>
        exact (summary.checked.mp success) value entry (reached.available state inputs) field
          (summary.reachable_seen plain state roots result inputs reached entry field) (by simp)
  · intro all
    apply summary.checked.mpr
    intro value entry available field member fresh
    exact all value (summary.origins value entry available field member fresh)

/-- The concrete visited source predicate is true exactly when every physically reached ordinary edge is plain. -/
theorem unconstrained_exact (plain : Guard → Bool) (value : Value Symbol Guard) (state : State Symbol Guard)
    (coherent : Coherent state) (available : Available state value) :
    unconstrained plain value = true ↔
      ∀ record, Reaches [value] record → ∀ edge ∈ nodeEdges record, plain edge.entry.key.constraint = true := by
  have summary := visit_summary plain value [] state coherent available
  have inputs : ∀ other ∈ [value], Available state other := by
    intro other member
    exact (List.mem_singleton.mp member) ▸ available
  simpa only [unconstrained, localPlain, List.all_eq_true] using summary.exact plain state [value] _ inputs

/-- A false source predicate has an actual physically reached edge with a false local constraint test. -/
theorem unconstrained_false (plain : Guard → Bool) (value : Value Symbol Guard) (state : State Symbol Guard)
    (coherent : Coherent state) (available : Available state value) :
    unconstrained plain value = false ↔
      ∃ record, Reaches [value] record ∧ ∃ edge ∈ nodeEdges record, plain edge.entry.key.constraint = false := by
  classical
  rw [Bool.eq_false_iff]
  change (¬ unconstrained plain value = true) ↔ _
  simp only [unconstrained_exact plain value state coherent available, Classical.not_forall, exists_prop, Bool.not_eq_true]

end MicroCFTA.InternedSourceCrush
