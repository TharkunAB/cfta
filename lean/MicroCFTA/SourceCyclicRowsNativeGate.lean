import MicroCFTA.SourceCyclicRowsNativeGateProduct
import MicroCFTA.SourceCyclicRowsReadback

/-!
# Native overlap callbacks on actual finite source keys

The constraint precheck supplies plainness. Completed source row readback
then identifies every finite child state with its structural heap language.
The callback runs actual toRows and the terminating minimum-size recurrence.
Only native intersection construction still requires product-row readback.
-/
namespace MicroCFTA.SourceCyclicRowsNativeGate
open Language SourceGuards SourceObservations SourceSymbolicIndex SourceInternedRows
open SourceDenseRows SymbolicGraphView AutomatonAmbiguity

/-- Plain interpreted finite rows equal the same rows with their guards erased. -/
theorem plain_rows (raw : List (State × List (Transition Symbol Payload)))
    (closed : SourceDenseRowsRestrict.Closed raw) (holds : Payload → Term Symbol → Bool)
    (plain : Decoder.Plain (SourceDenseRowsRestrict.automaton raw closed holds)) :
    SourceDenseRowsRestrict.automaton raw closed holds =
      SourceDenseRowsRestrict.automaton raw closed (fun _ _ => true) := by
  funext state
  apply List.map_congr_left
  intro edge member
  have guard := plain state (edge.edge holds) (List.mem_map.mpr ⟨edge, member, rfl⟩)
  have same : holds edge.constraint = fun _ => true := funext guard
  simp only [SourceSizedDecided.Row.edge, same]

/-- All finite source keys recover their structural heap rows after the real precheck. -/
theorem checked_readback [DecidableEq Formula] [Ord Key]
    (heap : Heap (Label Formula) (Constraint Formula)) (fuel : Nat) (rootRef : Ref)
    (raw : SourceCyclicRowsReadback.Table Formula) (read : toRows heap fuel rootRef = some raw)
    (noEmpty : NoEmptyBelow heap rootRef) (formulas : Formulas Formula) (solver : Entailment Formula)
    (freeVariables : List Nat)
    (active : ∀ state edge, edge ∈ lookup raw state → SourceCompactGuards.ActiveOption edge.constraint.equalities)
    (order : Label Formula → Key)
    (checked : SourceCyclicAutomaton.hasConstraints (SourceCyclicRows.preparedInput
      (SourceCyclicRowsReadback.input heap fuel rootRef raw read noEmpty freeVariables active) order (fun _ => 0)) = false)
    (state : Member (SourceDenseRows.keys raw)) :
    graph heap (fun _ _ => true) state.val =
      (SourceCyclicRows.original formulas solver
        (SourceCyclicRowsReadback.input heap fuel rootRef raw read noEmpty freeVariables active) state).map
        (renameEdge Subtype.val) := by
  have plain := SourceCyclicAutomaton.checked_plain formulas solver _ checked
  change Decoder.Plain (SourceCyclicRows.original formulas solver
    (SourceCyclicRowsReadback.input heap fuel rootRef raw read noEmpty freeVariables active)) at plain
  rw [SourceCyclicRowsReadback.original_eq] at plain ⊢
  rw [plain_rows raw _ (acceptsConstraint formulas solver) plain]
  exact SourceDenseRowsRestrict.heap_ordered_readback heap (fun _ _ => true) fuel rootRef raw read _ state

/-- Exact ordered rows imply the membership interface used by product induction. -/
theorem copied_of_ordered (source : Automaton Source Symbol) (target : Automaton Target Symbol)
    (encode : Source → Target) (ordered : ∀ state, target (encode state) = (source state).map (renameEdge encode)) :
    RowsCorrespond source target encode := by
  intro state edge
  rw [ordered]
  simp only [List.mem_map]
  constructor <;> rintro ⟨original, present, same⟩ <;> exact ⟨original, present, same.symm⟩

/-- Each callback computes the reference overlap Boolean on the finite child carrier. -/
theorem callback_eq [DecidableEq Source] [DecidableEq Symbol]
    (source : Automaton Source Symbol) (plain : Decoder.Plain source)
    (heap : Heap Symbol Payload) (encode : Source → State)
    (copied : RowsCorrespond source (graph heap (fun _ _ => true)) encode)
    (meet : State → State → State)
    (product : ProductReadback source (graph heap (fun _ _ => true)) encode
      (fun left right => meet (encode left) (encode right)))
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
  simp only [product_exact source _ encode copied _ product]
  constructor
  · rintro ⟨term, first, second⟩
    exact table_test_covers source pairs complete left right term first second
  · exact table_test_witness source plain pairs complete left right

/-- The zipped child callback scan commutes with finite key embedding. -/
theorem childOverlap_rename (test : Target → Target → Bool) (encode : Source → Target)
    (left right : List Source) :
    childOverlap test (left.map encode) (right.map encode) =
      childOverlap (fun first second => test (encode first) (encode second)) left right := by
  induction left generalizing right with
  | nil => simp [childOverlap]
  | cons first rest ih =>
    cases right with
    | nil => simp [childOverlap]
    | cons other later =>
      simpa only [List.map_cons, childOverlap, List.zip_cons_cons, List.map_cons, List.all_cons, id_eq] using
        congrArg (fun tail => test (encode first) (encode other) && tail) (ih later)

/-- Label, arity, and ordered child overlap tests survive finite key embedding. -/
theorem overlapping_rename [DecidableEq Symbol] (test : Target → Target → Bool) (encode : Source → Target)
    (left right : Language.Edge Source Symbol) :
    overlapping test (renameEdge encode left) (renameEdge encode right) =
      overlapping (fun first second => test (encode first) (encode second)) left right := by
  simp only [overlapping, renameEdge, List.length_map, childOverlap_rename]
  rfl

/-- The complete ordered pair scan has exactly the same result after embedding. -/
theorem ambiguous_rename [DecidableEq Symbol] (test : Target → Target → Bool) (encode : Source → Target)
    (edges : List (Language.Edge Source Symbol)) :
    ambiguous test (edges.map (renameEdge encode)) =
      ambiguous (fun first second => test (encode first) (encode second)) edges := by
  induction edges with
  | nil => rfl
  | cons first rest ih =>
    simp only [List.map_cons, AutomatonAmbiguity.ambiguous, List.any_map, Function.comp_def, overlapping_rename, ih]

/-- Scan actual native heap alternatives in the finite source key order. -/
def nativeScan [DecidableEq Symbol] (heap : Heap Symbol Payload) (keys : List State)
    (meet : State → State → State)
    (raw : State → State → List (State × List (Transition Symbol Payload))) : Bool :=
  keys.attach.any fun state => ambiguous (SourceRowsMinimumGate.test heap meet raw)
    (graph heap (fun _ _ => true) state.val)

/-- The complete native ambiguity scan equals the finite reference scan. -/
theorem scan_eq [DecidableEq Symbol] (keys : List State)
    (source : Automaton (Member keys) Symbol) (plain : Decoder.Plain source)
    (heap : Heap Symbol Payload)
    (ordered : ∀ state, graph heap (fun _ _ => true) state.val = (source state).map (renameEdge Subtype.val))
    (meet : State → State → State)
    (product : ProductReadback source (graph heap (fun _ _ => true)) Subtype.val
      (fun left right => meet left.val right.val))
    (fuel : Member keys → Member keys → Nat)
    (raw : State → State → List (State × List (Transition Symbol Payload)))
    (readback : ∀ left right, toRows heap (fuel left right)
      (SourceRowsMinimumGate.reference (meet left.val right.val)) = some (raw left.val right.val)) :
    nativeScan heap keys meet raw = keys.attach.any (fun state => ambiguous
      (fun left right => productiveRows (Language.intersect source source)
        (SourceCyclicRows.pairs keys) (SourceCyclicRows.pairs_complete keys) (left, right)) (source state)) := by
  have tests := callback_eq source plain heap Subtype.val (copied_of_ordered _ _ _ ordered)
    meet product (SourceCyclicRows.pairs keys) (SourceCyclicRows.pairs_complete keys) fuel raw readback
  unfold nativeScan
  apply congrArg (fun predicate => keys.attach.any predicate)
  funext state
  rw [ordered, ambiguous_rename]
  congr 1
  exact funext fun left => funext fun right => tests left right

end MicroCFTA.SourceCyclicRowsNativeGate
