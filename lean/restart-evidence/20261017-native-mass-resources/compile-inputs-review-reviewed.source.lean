import MicroCFTA.SourceRecursiveIntersectionCompileMass

/-!
# Width certificates for literal compiled node emitters

The original available operands bound the number of row and union requests.
The completed ordered walk retains that number. Current prefix residency
then checks the literal constructor inputs at the current numeric bound.
The initial bound must be retained by the current bound. Complete query
execution must still produce these prefix invariants.
-/
namespace MicroCFTA.SourceRecursiveIntersectionCompileMassInputs
open InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks
local notation "Stored" => InternedValueMassHeap.Stored
local notation "Inputs" => SourceRecursiveIntersectionWorkMass.Inputs
variable {Symbol Guard : Type} {initialBound currentBound : Nat}

/-- The actual row emitter fits the current square limit derived from original node payloads. -/
theorem rows [DecidableEq Symbol]
    (call : (EdgeValue Symbol Guard × EdgeValue Symbol Guard) → Machine Symbol Guard → Result Symbol Guard (EdgeValue Symbol Guard))
    (left right : Value Symbol Guard) (before after : Machine Symbol Guard) (values : List (EdgeValue Symbol Guard))
    (initial : Stored initialBound before.heap) (leftKnown : Available before.heap left) (rightKnown : Available before.heap right)
    (retained : initialBound ≤ currentBound)
    (trace : WalkTrace call (pairs (nodeEdges left) (nodeEdges right)) before values after)
    (resident : ∀ row ∈ values, EdgeResident after.heap row) :
    Inputs (currentBound * currentBound) after.heap (makeNode values) := by
  apply SourceRecursiveIntersectionWorkMass.Inputs.node values resident
  have first := Nat.le_trans (InternedValueMassHeap.available before.heap initial left leftKnown) retained
  have second := Nat.le_trans (InternedValueMassHeap.available before.heap initial right rightKnown) retained
  rw [trace.length]
  exact Nat.le_trans (SourceRecursiveIntersectionCompileMass.node_pairs_mass left right) (Nat.mul_le_mul first second)

/-- A positive payload bound fits its own square. -/
theorem le_square (bound : Nat) (positive : 1 ≤ bound) : bound ≤ bound * bound := by
  simpa only [Nat.mul_one] using Nat.mul_le_mul_left bound positive

/-- The actual union emitter fits the current square limit derived from its original payload. -/
theorem union
    (call : Value Symbol Guard → Machine Symbol Guard → Result Symbol Guard (Value Symbol Guard))
    (entry) (members : List (Value Symbol Guard)) (level free)
    (before after : Machine Symbol Guard) (values : List (Value Symbol Guard))
    (initial : Stored initialBound before.heap) (known : Available before.heap (.union entry members level free))
    (current : Stored currentBound after.heap) (retained : initialBound ≤ currentBound)
    (trace : WalkTrace call members before values after)
    (available : ∀ value ∈ values, Available after.heap value) :
    Inputs (currentBound * currentBound) after.heap (makeUnion values) := by
  apply SourceRecursiveIntersectionWorkMass.Inputs.union values available
  have original := InternedValueMassHeap.available before.heap initial (.union entry members level free) known
  have length := SourceRecursiveIntersectionCompileMass.values_length members
  have square := le_square currentBound current.positive
  rw [trace.length]
  simp only [InternedValueMass.value] at original
  omega

end MicroCFTA.SourceRecursiveIntersectionCompileMassInputs
