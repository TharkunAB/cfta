import MicroCFTA.SourcePruningNativeView

/-!
# Enumeration handles for complete interned node records

Zero represents empty. Positive handles use canonical node identities plus one.
Lookup rejects missing entries and losing reservations. This model convention
does not establish native NodeId extraction or enumeration-slot realization.
-/
namespace MicroCFTA.SourcePruningEnumerationNodes
open InternedConstructorTemplates InternedProbeProvenance
local notation "Symbol" => SourcePruningTemplates.Symbol
variable {Guard : Type}

/-- Encode empty or a stored node identity. Free references have no handle. -/
def encodeNode (value : Value Symbol Guard) : Option Nat :=
  match value with
  | .empty => some 0
  | .reference _ => none
  | .node entry _ _ _ | .union entry _ _ _ | .mu entry _ _ _ => some (entry.identity + 1)

/-- Read the complete payload only for the requested canonical winner. -/
def lookupNode (heap : State Symbol Guard) (node : Nat) : Option (Value Symbol Guard) :=
  match node with
  | 0 => some .empty
  | identity + 1 =>
      match heap.nodes.issued identity with
      | none => none
      | some key =>
          match heap.nodes.table key with
          | none => none
          | some entry => if entry.identity = identity then heap.nodeRecords key else none

/-- A closed available value derives its exact handle and complete readback. -/
theorem available_readback (heap : State Symbol Guard) (value : Value Symbol Guard)
    (coherent : InternedRecordCoherence.Coherent heap)
    (available : Available heap value) (closed : value.free = []) :
    ∃ node, encodeNode value = some node ∧ lookupNode heap node = some value := by
  cases value with
  | empty => exact ⟨0, rfl, rfl⟩
  | reference => cases closed
  | node entry _ _ _ | union entry _ _ _ | mu entry _ _ _ =>
      have canonical : heap.nodes.table entry.key = some entry :=
        InternedFreshProbeKeys.resident_entry heap coherent _ available.resident entry rfl
      have issued : heap.nodes.issued entry.identity = some entry.key :=
        (coherent.valid.2.2 entry.key entry canonical).2
      refine ⟨entry.identity + 1, rfl, ?_⟩
      simpa only [lookupNode, issued, canonical, ↓reduceIte] using available.resident entry rfl

/-- Actual cache growth and issued history retain each successful lookup. -/
theorem lookupNode_keeps (before after : State Symbol Guard)
    (kept : SourceEqualityRequiredCache.Keeps before after)
    (node : Nat) (value : Value Symbol Guard)
    (present : lookupNode before node = some value) : lookupNode after node = some value := by
  cases node with
  | zero => exact present
  | succ identity =>
      cases issued : before.nodes.issued identity with
      | none =>
          simp only [lookupNode, issued] at present
          cases present
      | some key =>
          cases canonical : before.nodes.table key with
          | none =>
              simp only [lookupNode, issued, canonical] at present
              cases present
          | some entry =>
              by_cases winner : entry.identity = identity
              · simp only [lookupNode, issued, canonical, ite_eq_left winner] at present
                simpa only [lookupNode, kept.history identity key issued,
                  kept.growth.nodes key entry canonical, ite_eq_left winner] using
                  kept.growth.nodeRecords key value present
              · simp only [lookupNode, issued, canonical, ite_eq_right winner] at present
                cases present

end MicroCFTA.SourcePruningEnumerationNodes
