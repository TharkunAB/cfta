import MicroCFTA.SourceRecursiveIntersectionNativeProductivity
import MicroCFTA.SourceFreshOrdinaryColdKeys
import MicroCFTA.AutomatonAmbiguity

/-!
# Exact actual native callbacks on the finite source carrier

The input table supplies the physical operands and their complete languages.
Actual completed native execution, root exposure, row collection, and the
finite minimum recurrence give the same Boolean as the finite product test.
No product-row relation or supplied product-language equation is required.
-/
namespace MicroCFTA.SourceFreshOrdinaryNativeKeyCallback
open Cache Language InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks
open SourceRecursiveIntersectionSemanticHeap (SemanticHeap)
open SourceColdSharedRows (Rows ResidentRows CoveredRows)
open SourceFreshOrdinaryColdSharedRows (Trace ReplayedRows keys)
open SourcePreparedSharedRows (encode)
open SourceFreshOrdinaryColdKeys (physical)

/-- Actual finite callback execution agrees with the reference product test at each pair of input keys. -/
theorem completed [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (emptyGuard : Guard) (conjoin : Guard → Guard → Guard) (fuel : Nat)
    (state after : SourceRecursiveIntersectionThunks.State width Symbol Guard) (value : Value Symbol Guard)
    (valid : SourceRecursiveIntersectionThunks.Valid width emptyGuard conjoin state)
    (semantic : SemanticHeap state.machine.heap) (covered : Covered [] state.machine.heap)
    (heap : InternedOpenDepthReadback.Heap state.machine.heap) (guarded : InternedGuardedProbeHeap.Heap state.machine.heap)
    (budgetHeap : InternedGuardedBudgetProbeHeap.Heap state.machine.heap)
    (inputRows : Rows Symbol Guard) (replayed : ReplayedRows state.machine.heap inputRows)
    (resident : ResidentRows state.machine.heap inputRows) (closedRows : CoveredRows inputRows inputRows)
    (inputKeys : List Nat) (domain : ∀ identity, (∃ edges, inputRows identity = some edges) ↔ identity ∈ inputKeys)
    (root : Value Symbol Guard) (closed : SourceDenseRowsRestrict.Closed (SourceColdSharedRows.table inputRows inputKeys root))
    (left right : SourceDenseRows.Member (SourceDenseRows.keys (SourceColdSharedRows.table inputRows inputKeys root)))
    (pairs : List ((SourceDenseRows.Member (SourceDenseRows.keys (SourceColdSharedRows.table inputRows inputKeys root))) ×
      (SourceDenseRows.Member (SourceDenseRows.keys (SourceColdSharedRows.table inputRows inputKeys root)))))
    (complete : ∀ pair, pair ∈ pairs)
    (done : SourceRecursiveIntersectionNative.execute emptyGuard conjoin fuel
      (.node ⟨IntersectionEmptyDomain.emptyDomain, physical state.machine.heap left.val, physical state.machine.heap right.val⟩ .pure) state =
        .done value after)
    (ranges : SourceRecursiveIntersectionNative.WordRanges emptyGuard conjoin
      (.node ⟨IntersectionEmptyDomain.emptyDomain, physical state.machine.heap left.val, physical state.machine.heap right.val⟩ .pure) state) :
    ∃ readFuel edges exposed rows final outer inner minimumFuel,
      MergedFreshOrdinaryExposure.nodeEdges readFuel value after.machine.heap = .done edges exposed ∧
      (∀ extra, MergedFreshOrdinaryExposure.nodeEdges (readFuel + extra) value after.machine.heap = .done edges exposed) ∧
      Trace exposed (fun _ => none) [value] rows final ∧
      (∀ largerOuter largerInner, outer ≤ largerOuter → inner ≤ largerInner →
        SourceFreshOrdinaryColdSharedRows.collect largerOuter largerInner exposed (fun _ => none) [value] = .done rows final) ∧
      (let raw := SourceColdSharedRows.table rows (keys final rows) value
       MinimumSize.sweeps (SourceRowsMinimumAdapter.automaton raw) (raw.map Prod.fst) minimumFuel (fun _ => none) =
         SourceRowsMinimumAdapter.minimumSizes raw ∧
       MinimumSize.sweep (SourceRowsMinimumAdapter.automaton raw) (raw.map Prod.fst) (SourceRowsMinimumAdapter.minimumSizes raw) =
         SourceRowsMinimumAdapter.minimumSizes raw) ∧
      (if edges.isEmpty then false else
        (SourceRowsMinimumAdapter.minimumSizes (SourceColdSharedRows.table rows (keys final rows) value) (encode value)).isSome) =
          AutomatonAmbiguity.productiveRows
            (Language.intersect
              (SourceDenseRowsRestrict.automaton (SourceColdSharedRows.table inputRows inputKeys root) closed (fun _ _ => true))
              (SourceDenseRowsRestrict.automaton (SourceColdSharedRows.table inputRows inputKeys root) closed (fun _ _ => true)))
            pairs complete (left, right) := by
  have first := SourceFreshOrdinaryColdKeys.physical_record state.machine.heap semantic inputRows resident left.val
    (SourceFreshOrdinaryColdKeys.table_declared inputRows inputKeys domain root left.val left.property)
  have second := SourceFreshOrdinaryColdKeys.physical_record state.machine.heap semantic inputRows resident right.val
    (SourceFreshOrdinaryColdKeys.table_declared inputRows inputKeys domain root right.val right.property)
  obtain ⟨readFuel, edges, exposed, rows, final, outer, inner, minimumFuel, read, readStable, trace, stable,
      minimumRun, callback⟩ :=
    SourceRecursiveIntersectionNative.done_node_productivity emptyGuard conjoin fuel
      (physical state.machine.heap left.val) (physical state.machine.heap right.val) state after value valid
      first.2.2.1 second.2.2.1 first.1 second.1 first.2.1 second.2.1 semantic covered heap guarded budgetHeap done ranges
  refine ⟨readFuel, edges, exposed, rows, final, outer, inner, minimumFuel, read, readStable, trace, stable, minimumRun, ?_⟩
  apply Bool.eq_iff_iff.mpr
  rw [callback (fun _ _ => False)]
  let source := SourceDenseRowsRestrict.automaton (SourceColdSharedRows.table inputRows inputKeys root) closed (fun _ _ => true)
  have language (key : SourceDenseRows.Member (SourceDenseRows.keys (SourceColdSharedRows.table inputRows inputKeys root))) (term : Term Symbol) :
      Accepts source key term ↔ InternedGuardedLanguage.meaning (fun _ _ => true) (fun _ _ => False) (physical state.machine.heap key.val) term :=
    SourceFreshOrdinaryColdKeys.finite_language state.machine.heap semantic covered guarded budgetHeap inputRows replayed resident closedRows
      inputKeys domain root closed key (fun _ _ => true) (fun _ _ => False) term
  have plain : Decoder.Plain source := by
    intro key edge member term
    obtain ⟨row, _, rfl⟩ := List.mem_map.mp member
    rfl
  constructor
  · rintro ⟨term, leftTerm, rightTerm⟩
    exact AutomatonAmbiguity.table_test_covers source pairs complete left right term
      ((language left term).mpr leftTerm) ((language right term).mpr rightTerm)
  · intro found
    obtain ⟨term, leftTerm, rightTerm⟩ := AutomatonAmbiguity.table_test_witness source plain pairs complete left right found
    exact ⟨term, (language left term).mp leftTerm, (language right term).mp rightTerm⟩

end MicroCFTA.SourceFreshOrdinaryNativeKeyCallback
