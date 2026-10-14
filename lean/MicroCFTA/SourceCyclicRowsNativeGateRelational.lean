import MicroCFTA.SourceCyclicRowsNativeGate
import MicroCFTA.DiagonalProduct

/-!
# Related physical product rows and the existing functional interface

The relational product theorem permits several physical representatives of
one source pair. The existing functional interface remains a special case.
Diagonal reuse supplies copied original rows. Other pairs retain the existing
membership and deletion laws. No native execution correspondence is assumed.
-/
namespace MicroCFTA.SourceCyclicRowsNativeGate
open Language SymbolicGraphView SourceInternedRows SourceDenseRows AutomatonAmbiguity

/-- Literal diagonal product rows copy the original source child identities. -/
theorem diagonal_rename [DecidableEq Source] [DecidableEq Symbol]
    (source : Automaton Source Symbol) (target : Automaton Target Symbol)
    (encode : Source → Target) (meet : Source → Source → Target)
    (view : ProductReadback source target encode meet) (edge : Edge Source Symbol) :
    renameEdge (fun pair => meet pair.1 pair.2) (renameEdge (fun state => (state, state)) edge) = renameEdge encode edge := by
  cases edge with
  | mk label children guard =>
      simp only [renameEdge, List.map_map]
      congr 1
      apply List.map_congr_left
      intro state member
      exact view.diagonal state

/-- The existing functional product contract gives normalized rows of the product with diagonal reuse. -/
def functional_normalized [DecidableEq Source] [DecidableEq Symbol]
    (source : Automaton Source Symbol) (target : Automaton Target Symbol)
    (encode : Source → Target) (copied : RowsCorrespond source target encode)
    (meet : Source → Source → Target) (view : ProductReadback source target encode meet) :
    NormalizedRows (DiagonalProduct.graph source) target (fun pair => meet pair.1 pair.2) where
  keep pair edge := if pair.1 = pair.2 then true else view.keep pair.1 pair.2 edge
  members := by
    rintro ⟨first, second⟩ row
    by_cases same : first = second
    · subst second
      rw [view.diagonal, DiagonalProduct.diagonal_rows]
      constructor
      · intro member
        obtain ⟨original, present, equal⟩ := (copied first row).mp member
        refine ⟨renameEdge (fun state => (state, state)) original, List.mem_map.mpr ⟨original, present, rfl⟩, ?_, ?_⟩
        · simp
        · rw [diagonal_rename source target encode meet view]
          exact equal
      · rintro ⟨original, member, _, equal⟩
        obtain ⟨original, present, rfl⟩ := List.mem_map.mp member
        exact (copied first row).mpr ⟨original, present, equal.trans (diagonal_rename source target encode meet view original)⟩
    · simpa only [DiagonalProduct.graph, ite_eq_right same] using view.members first second same row
  rejected := by
    rintro ⟨first, second⟩ edge member rejected
    by_cases same : first = second
    · simp only [same, ↓reduceIte, Bool.true_eq_false] at rejected
    · exact view.rejected first second same edge (by simpa only [DiagonalProduct.graph, ite_eq_right same] using member)
        (by simpa only [ite_eq_right same] using rejected)

/-- Functional product rows are a proved special case of related physical rows. -/
theorem functional_related [DecidableEq Source] [DecidableEq Symbol]
    (source : Automaton Source Symbol) (target : Automaton Target Symbol)
    (encode : Source → Target) (copied : RowsCorrespond source target encode)
    (meet : Source → Source → Target) (view : ProductReadback source target encode meet) :
    RelatedRows.Readback (DiagonalProduct.graph source) target (fun pair result => result = meet pair.1 pair.2) :=
  RelatedRows.of_normalized (DiagonalProduct.graph source) target (fun pair => meet pair.1 pair.2)
    (functional_normalized source target encode copied meet view)

/-- Related physical product rows give the exact actual minimum-row overlap callback. -/
theorem related_callback_eq [DecidableEq Source] [DecidableEq Symbol]
    (source : Automaton Source Symbol) (plain : Decoder.Plain source)
    (heap : Heap Symbol Payload) (encode : Source → State)
    (meet : State → State → State) (related : (Source × Source) → State → Prop)
    (product : RelatedRows.Readback (DiagonalProduct.graph source) (graph heap (fun _ _ => true)) related)
    (roots : ∀ left right, related (left, right) (meet (encode left) (encode right)))
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
  simp only [DiagonalProduct.related_product_exact source _ related product left right _ (roots left right)]
  constructor
  · rintro ⟨term, first, second⟩
    exact table_test_covers source pairs complete left right term first second
  · exact table_test_witness source plain pairs complete left right

/-- The actual ordered ambiguity scan agrees with the reference through related product rows. -/
theorem related_scan_eq [DecidableEq Symbol] (keys : List State)
    (source : Automaton (Member keys) Symbol) (plain : Decoder.Plain source)
    (heap : Heap Symbol Payload)
    (ordered : ∀ state, graph heap (fun _ _ => true) state.val = (source state).map (renameEdge Subtype.val))
    (meet : State → State → State) (related : (Member keys × Member keys) → State → Prop)
    (product : RelatedRows.Readback (DiagonalProduct.graph source) (graph heap (fun _ _ => true)) related)
    (roots : ∀ left right, related (left, right) (meet left.val right.val))
    (fuel : Member keys → Member keys → Nat)
    (raw : State → State → List (State × List (Transition Symbol Payload)))
    (readback : ∀ left right, toRows heap (fuel left right)
      (SourceRowsMinimumGate.reference (meet left.val right.val)) = some (raw left.val right.val)) :
    nativeScan heap keys meet raw = keys.attach.any (fun state => ambiguous
      (fun left right => productiveRows (Language.intersect source source)
        (SourceCyclicRows.pairs keys) (SourceCyclicRows.pairs_complete keys) (left, right)) (source state)) := by
  have tests := related_callback_eq source plain heap Subtype.val meet related product roots
    (SourceCyclicRows.pairs keys) (SourceCyclicRows.pairs_complete keys) fuel raw readback
  unfold nativeScan
  apply congrArg (fun predicate => keys.attach.any predicate)
  funext state
  rw [ordered, ambiguous_rename]
  congr 1
  exact funext fun left => funext fun right => tests left right

end MicroCFTA.SourceCyclicRowsNativeGate
