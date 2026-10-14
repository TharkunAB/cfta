import MicroCFTA.SourceCyclicRowsNativeGate
import MicroCFTA.DirectionalRows
import MicroCFTA.DiagonalProduct

/-!
# Actual native overlap callbacks from directional product rows

Separate directional simulations permit covered redundant product rows.
The actual finite minimum callback and ordered ambiguity scan retain the
complete reference result. Each simulation retains full guard implications
and ordered children. No exact representative of every product row is used.
-/
namespace MicroCFTA.SourceCyclicRowsNativeGate
open Language SymbolicGraphView SourceInternedRows SourceDenseRows AutomatonAmbiguity

/-- Separate directional product rows give the exact actual minimum-row overlap callback. -/
theorem directional_callback_eq [DecidableEq Source] [DecidableEq Symbol]
    (source : Automaton Source Symbol) (plain : Decoder.Plain source)
    (heap : Heap Symbol Payload) (encode : Source → State)
    (meet : State → State → State) (forward : (Source × Source) → State → Prop) (reverse : State → (Source × Source) → Prop)
    (product : DirectionalRows.Simulation (DiagonalProduct.graph source) (graph heap (fun _ _ => true)) forward)
    (covered : DirectionalRows.Simulation (graph heap (fun _ _ => true)) (DiagonalProduct.graph source) reverse)
    (roots : ∀ left right, forward (left, right) (meet (encode left) (encode right)))
    (reverseRoots : ∀ left right, reverse (meet (encode left) (encode right)) (left, right))
    (pairs : List (Source × Source)) (complete : ∀ pair, pair ∈ pairs)
    (fuel : Source → Source → Nat)
    (raw : State → State → List (State × List (Transition Symbol Payload)))
    (readback : ∀ left right, toRows heap (fuel left right)
      (SourceRowsMinimumGate.reference (meet (encode left) (encode right))) = some (raw (encode left) (encode right)))
    (left right : Source) :
    SourceRowsMinimumGate.test heap meet raw (encode left) (encode right) =
      productiveRows (Language.intersect source source) pairs complete (left, right) := by
  apply Bool.eq_iff_iff.mpr
  change SourceRowsMinimumGate.test heap meet raw (encode left) (encode right) = true ↔ _
  unfold SourceRowsMinimumGate.test
  rw [SourceRowsMinimumPublic.productive_exact heap (fuel left right) _ _ (readback left right),
    SourceRowsMinimumGate.state_reference]
  have language := fun term => (DirectionalRows.language_exact (DiagonalProduct.graph source)
    (graph heap (fun _ _ => true)) forward reverse product covered (left, right) (meet (encode left) (encode right))
    (roots left right) (reverseRoots left right) term).trans (DiagonalProduct.language_exact source left right term)
  simp only [language]
  constructor
  · rintro ⟨term, first, second⟩
    exact table_test_covers source pairs complete left right term first second
  · exact table_test_witness source plain pairs complete left right

/-- The actual ordered ambiguity scan agrees with the reference through separate directional product rows. -/
theorem directional_scan_eq [DecidableEq Symbol] (keys : List State)
    (source : Automaton (Member keys) Symbol) (plain : Decoder.Plain source)
    (heap : Heap Symbol Payload)
    (ordered : ∀ state, graph heap (fun _ _ => true) state.val = (source state).map (renameEdge Subtype.val))
    (meet : State → State → State) (forward : (Member keys × Member keys) → State → Prop) (reverse : State → (Member keys × Member keys) → Prop)
    (product : DirectionalRows.Simulation (DiagonalProduct.graph source) (graph heap (fun _ _ => true)) forward)
    (covered : DirectionalRows.Simulation (graph heap (fun _ _ => true)) (DiagonalProduct.graph source) reverse)
    (roots : ∀ left right, forward (left, right) (meet left.val right.val))
    (reverseRoots : ∀ left right, reverse (meet left.val right.val) (left, right))
    (fuel : Member keys → Member keys → Nat)
    (raw : State → State → List (State × List (Transition Symbol Payload)))
    (readback : ∀ left right, toRows heap (fuel left right)
      (SourceRowsMinimumGate.reference (meet left.val right.val)) = some (raw left.val right.val)) :
    nativeScan heap keys meet raw = keys.attach.any (fun state => ambiguous
      (fun left right => productiveRows (Language.intersect source source)
        (SourceCyclicRows.pairs keys) (SourceCyclicRows.pairs_complete keys) (left, right)) (source state)) := by
  have tests := directional_callback_eq source plain heap Subtype.val meet forward reverse product covered roots reverseRoots
    (SourceCyclicRows.pairs keys) (SourceCyclicRows.pairs_complete keys) fuel raw readback
  unfold nativeScan
  apply congrArg (fun predicate => keys.attach.any predicate)
  funext state
  rw [ordered, ambiguous_rename]
  congr 1
  exact funext fun left => funext fun right => tests left right

end MicroCFTA.SourceCyclicRowsNativeGate
