import MicroCFTA.SourceRowsMinimumPublic
import MicroCFTA.AutomatonAmbiguity
import MicroCFTA.SymbolicProductRows

/-!
# The ambiguity gate uses actual shared-row minima

The child test exposes the actual intersected node with toRows, then runs
the proved finite minimum recurrence. Constructor product-row readback is
the remaining intersection interface. No independent productivity oracle is
assumed. The empty state uses its separate constructor in both directions.
-/

namespace MicroCFTA.SourceRowsMinimumGate

open Language SourceInternedRows SymbolicGraphView AutomatonAmbiguity

/-- Recover the source node reference from its exact explicit-state constructor. -/
def reference : State → Ref
  | .empty => none
  | .interned identity => some identity

/-- Empty and nonempty source identities round-trip without a sentinel collision. -/
theorem state_reference (state : State) : stateOf (reference state) = state := by cases state <;> rfl

/-- The actual overlap callback applies productiveRows to the intersected node's extracted rows. -/
def test (heap : Heap Symbol Constraint) (meet : State → State → State)
    (raw : State → State → List (State × List (Transition Symbol Constraint))) (left right : State) : Bool :=
  SourceRowsMinimumPublic.productiveRows heap (reference (meet left right)) (raw left right)

/-- Actual minimum-table lookup is exactly shared finite structural support under copied product rows. -/
theorem test_exact [DecidableEq Symbol] (heap : Heap Symbol Constraint) (meet : State → State → State)
    (product : ProductRows (graph heap (fun _ _ => true)) meet)
    (fuel : State → State → Nat)
    (raw : State → State → List (State × List (Transition Symbol Constraint)))
    (readback : ∀ left right, toRows heap (fuel left right) (reference (meet left right)) = some (raw left right))
    (left right : State) : test heap meet raw left right = true ↔
      ∃ term, Accepts (graph heap (fun _ _ => true)) left term ∧ Accepts (graph heap (fun _ _ => true)) right term := by
  unfold test
  rw [SourceRowsMinimumPublic.productive_exact heap (fuel left right) _ _ (readback left right), state_reference]
  simp only [productRows_exact _ meet product]

/-- A false actual overlap scan derives pairwise disjoint accepted transition languages. -/
theorem gate_disjoint [DecidableEq Symbol] (heap : Heap Symbol Constraint) (meet : State → State → State)
    (product : ProductRows (graph heap (fun _ _ => true)) meet)
    (fuel : State → State → Nat)
    (raw : State → State → List (State × List (Transition Symbol Constraint)))
    (readback : ∀ left right, toRows heap (fuel left right) (reference (meet left right)) = some (raw left right))
    (edges : List (Language.Edge State Symbol)) (passed : ambiguous (test heap meet raw) edges = false) :
    edges.Pairwise (fun left right => ∀ term,
      EdgeLanguage (Accepts (graph heap (fun _ _ => true))) left term →
        ¬EdgeLanguage (Accepts (graph heap (fun _ _ => true))) right term) := by
  apply compact_disjoint (Accepts (graph heap (fun _ _ => true))) (test heap meet raw) _ edges passed
  intro left right term first second
  exact (test_exact heap meet product fuel raw readback left right).mpr ⟨term, first, second⟩

/-- Plain transition overlap is decided exactly by the new shared-row callback. -/
theorem overlap_exact [DecidableEq Symbol] (heap : Heap Symbol Constraint) (meet : State → State → State)
    (product : ProductRows (graph heap (fun _ _ => true)) meet)
    (fuel : State → State → Nat)
    (raw : State → State → List (State × List (Transition Symbol Constraint)))
    (readback : ∀ left right, toRows heap (fuel left right) (reference (meet left right)) = some (raw left right))
    (left right : Language.Edge State Symbol)
    (leftPlain : ∀ term, left.guard term = true) (rightPlain : ∀ term, right.guard term = true) :
    overlapping (test heap meet raw) left right = true ↔ ∃ term,
      EdgeLanguage (Accepts (graph heap (fun _ _ => true))) left term ∧
      EdgeLanguage (Accepts (graph heap (fun _ _ => true))) right term :=
  plain_overlap_exact _ _
    (fun left right term first second => (test_exact heap meet product fuel raw readback left right).mpr ⟨term, first, second⟩)
    (fun left right found => (test_exact heap meet product fuel raw readback left right).mp found)
    left right leftPlain rightPlain

/-- Mapping every constraint to unit leaves the actual ambiguity callback result unchanged. -/
theorem erased_callback (heap : Heap Symbol Constraint) (root : Ref)
    (raw : List (State × List (Transition Symbol Constraint))) :
    SourceRowsMinimumPublic.productiveRows heap root raw =
      (if (graph heap (fun _ _ => true) (stateOf root)).isEmpty then false else
        (SourceRowsMinimumAdapter.minimumSizes (SourceRowsMinimumAdapter.mapConstraints (fun _ => ()) raw) (stateOf root)).isSome) := by
  rw [SourceRowsMinimumAdapter.constraint_independent]
  rfl

end MicroCFTA.SourceRowsMinimumGate
