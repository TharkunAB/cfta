import MicroCFTA.SourceEqualityNativeCheckedMass

/-!
# Literal Work width checks from checked edge prefixes

The original resident row bounds the accepted zip length. The physical
prefix derives availability at the actual assembly heap. Rejection emits
one Empty child. No reached output size or width law is supplied.
-/
namespace MicroCFTA.SourceEqualityNativeCheckedMassInputs
open Cache InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks
open InternedBinderProtocol IntersectionFlatMemoKeyDomain
variable {Symbol Formula : Type}
local notation "Guard" => SourceSymbolicIndex.Constraint Formula

/-- The earlier actual accepted prefix derives the exact emitted Work input check. -/
theorem children_inputs (nodes : NodeCall Symbol Guard)
    (calls : Calls (fun domain left right => nodes ⟨domain, left, right⟩))
    (domain : Interned DomainKey) (left right : EdgeValue Symbol Guard)
    (combined : SourceEqualityConjoinAllocation.Constraint Formula)
    (before current : Machine Symbol Guard) (values : List (Value Symbol Guard))
    (valid : SourceRecursiveIntersectionKernel.Valid before) (known : Domain before domain)
    (leftResident : EdgeResident before.heap left) (rightResident : EdgeResident before.heap right)
    (bound : Nat) (stored : InternedValueMassHeap.Stored bound before.heap)
    (actual : WalkTrace (fun pair => nodes ⟨domain, pair.1, pair.2⟩)
      (left.children.zip right.children) before values current) :
    SourceRecursiveIntersectionWorkMass.Inputs (bound * bound) current.heap
      (makeEdge left.entry.key.symbol (SourceEqualityConjoinAllocation.readback combined) values) := by
  obtain ⟨_valid, available, length⟩ := SourceEqualityNativeCheckedMass.children_prefix nodes calls domain left right
    before current values valid known leftResident rightResident actual
  have width : values.length ≤ bound := by
    rw [length]
    exact SourceEqualityNativeCheckedMass.zip_width before.heap bound stored left right leftResident
  have square := Nat.mul_le_mul_left bound stored.positive
  exact .edge _ _ values available (by simpa only [Nat.mul_one] using Nat.le_trans width square)

/-- A positive causal store bound derives the literal rejected Work input check. -/
theorem sentinel_inputs (left : EdgeValue Symbol Guard) (before : State Symbol Guard) (bound : Nat)
    (stored : InternedValueMassHeap.Stored bound before) :
    SourceRecursiveIntersectionWorkMass.Inputs (bound * bound) before
      (makeEdge left.entry.key.symbol SourceEqualityConstraintConstructors.top [.empty]) := by
  have square := Nat.mul_le_mul_left bound stored.positive
  refine .edge _ _ [.empty] ?_ ?_
  · intro value member
    cases List.mem_singleton.mp member
    exact empty_available _
  · simp only [List.length_singleton]
    exact Nat.le_trans stored.positive (by simpa only [Nat.mul_one] using square)

end MicroCFTA.SourceEqualityNativeCheckedMassInputs
