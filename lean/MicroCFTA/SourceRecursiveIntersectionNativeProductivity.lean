import MicroCFTA.SourceRecursiveIntersectionNativeProduct
import MicroCFTA.SourceFreshOrdinaryColdProductivity
import MicroCFTA.SourceRecursiveIntersectionNativeWarmColdExact

/-!
# Actual completed native overlap callbacks

The callback first exposes the completed native value. It then collects
the finite rows and reads the minimum table. These actual operations give
the common structural language of the original closed operands.
-/
namespace MicroCFTA.SourceRecursiveIntersectionNative
open Cache Language InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedBinderProtocol IntersectionFlatMemoKeyDomain
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceRecursiveIntersectionInputView (Original)
open SourceRecursiveIntersectionSemanticHeap (SemanticHeap)
open SourceFreshOrdinaryColdSharedRows (Trace keys)
open SourcePreparedSharedRows (encode)

/-- The actual exposure and minimum callback detects common finite terms after any checked completed native call. -/
theorem done_node_productivity [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (emptyGuard : Guard) (conjoin : Guard → Guard → Guard) (fuel : Nat)
    (left right : Value Symbol Guard) (state after : SourceRecursiveIntersectionThunks.State width Symbol Guard) (value : Value Symbol Guard)
    (valid : SourceRecursiveIntersectionThunks.Valid width emptyGuard conjoin state)
    (leftOriginal : Original left) (rightOriginal : Original right)
    (leftAvailable : Available state.machine.heap left) (rightAvailable : Available state.machine.heap right)
    (leftClosed : left.free = []) (rightClosed : right.free = [])
    (semantic : SemanticHeap state.machine.heap) (covered : Covered [] state.machine.heap)
    (heap : InternedOpenDepthReadback.Heap state.machine.heap) (guarded : InternedGuardedProbeHeap.Heap state.machine.heap)
    (budgetHeap : InternedGuardedBudgetProbeHeap.Heap state.machine.heap)
    (done : execute emptyGuard conjoin fuel (.node ⟨IntersectionEmptyDomain.emptyDomain, left, right⟩ .pure) state = .done value after)
    (ranges : WordRanges emptyGuard conjoin (.node ⟨IntersectionEmptyDomain.emptyDomain, left, right⟩ .pure) state) :
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
      ∀ ambient,
        (if edges.isEmpty then false else
          (SourceRowsMinimumAdapter.minimumSizes (SourceColdSharedRows.table rows (keys final rows) value) (encode value)).isSome) = true ↔
          ∃ term, InternedGuardedLanguage.meaning (fun _ _ => true) ambient left term ∧
            InternedGuardedLanguage.meaning (fun _ _ => true) ambient right term := by
  have ready : NodeReady state.machine ⟨IntersectionEmptyDomain.emptyDomain, left, right⟩ :=
    ⟨empty_domain state.machine, leftAvailable, rightAvailable⟩
  have evaluated := evaluation_of_done emptyGuard conjoin fuel _ state after value done
  have bounds := evaluated.bounds_of_ranges ranges
  have correct := bounds.correct (fun current value => Available current.heap value) (by intro value; trivial)
    (safe_requestNode _ left right _ ready) valid
  have certificate := semantic_requestNode IntersectionEmptyDomain.emptyDomain left right state.machine ready
  have retained := bounds.guarded_heaps (fun current value => Available current.heap value)
    (by intro value; trivial) (safe_requestNode _ left right _ ready) valid certificate semantic (by intro value; trivial) guarded
  have openRetained := bounds.open_depth_heaps (fun current value => Available current.heap value)
    (by intro value; trivial) (safe_requestNode _ left right _ ready) valid certificate semantic (by intro value; trivial) heap
  have budgetRetained := bounds.budget_heaps (fun current value => Available current.heap value)
    (by intro value; trivial) (safe_requestNode _ left right _ ready) valid certificate semantic (by intro value; trivial) budgetHeap
  obtain ⟨steps, _, nativeTrace⟩ := done_trace emptyGuard conjoin fuel _ state after value done
  have afterCovered := (nativeTrace.covered emptyGuard conjoin steps _ _ state after semantic.1.normal.facts.coherent.valid covered).2
  have scope := correct.meaning.request_scope _ _ _ _ valid.machine ready semantic
  have closed := SourceRecursiveIntersectionResultScope.empty_scope value scope
  obtain ⟨readFuel, edges, exposed, rows, final, outer, inner, read, readStable, trace, stable,
      _, _, _, _, _, _, _, _, callback⟩ :=
    SourceFreshOrdinaryColdProductivity.prechecked_table after.machine.heap retained.1 afterCovered openRetained.2
      retained.2 budgetRetained.2 value correct.result closed
  obtain ⟨minimumFuel, minimumRun, minimumStable⟩ :=
    SourceRowsMinimumAdapter.finite (SourceColdSharedRows.table rows (keys final rows) value)
  refine ⟨readFuel, edges, exposed, rows, final, outer, inner, minimumFuel, read, readStable, trace, stable,
    ⟨minimumRun, minimumStable⟩, ?_⟩
  intro ambient
  rw [callback ambient]
  apply exists_congr
  intro term
  exact native_product emptyGuard conjoin fuel left right state after value valid leftOriginal rightOriginal
    leftAvailable rightAvailable leftClosed rightClosed semantic guarded done ranges (fun _ _ => true)
    (by intros; rfl) ambient term

end MicroCFTA.SourceRecursiveIntersectionNative
