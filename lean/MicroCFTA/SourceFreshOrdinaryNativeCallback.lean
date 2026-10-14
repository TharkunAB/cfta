import MicroCFTA.SourceRecursiveIntersectionNativeWarmSuccessful
import MicroCFTA.SourceRecursiveIntersectionNativeProduct
import MicroCFTA.SourceRecursiveIntersectionNativeWarmColdExact
import MicroCFTA.SourceFreshOrdinaryColdMemoState

/-!
# Finite actual native callbacks with sequential cache state

The callback executes intersection, root exposure, row collection, and
minimum lookup in source order. Every phase has a finite actual execution.
The returned native state retains all invariants for another callback.
-/
namespace MicroCFTA.SourceFreshOrdinaryNativeCallback
open Cache Language InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedBinderProtocol IntersectionFlatMemoKeyDomain
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceRecursiveIntersectionInputView (Original)
open SourceRecursiveIntersectionSemanticHeap (SemanticHeap)
open SourceRecursiveIntersectionNative (Idle)
open SourceFreshOrdinaryColdSharedRows (keys)
open SourcePreparedSharedRows (encode)

/-- Invariants of the actual cache between complete overlap callbacks. -/
structure Ready [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (emptyGuard : Guard) (conjoin : Guard → Guard → Guard)
    (state : SourceRecursiveIntersectionThunks.State width Symbol Guard) : Prop where
  valid : SourceRecursiveIntersectionThunks.Valid width emptyGuard conjoin state
  idle : Idle state
  semantic : SemanticHeap state.machine.heap
  covered : Covered [] state.machine.heap
  openDepth : InternedOpenDepthReadback.Heap state.machine.heap
  guarded : InternedGuardedProbeHeap.Heap state.machine.heap
  budget : InternedGuardedBudgetProbeHeap.Heap state.machine.heap

/-- A complete source callback records finite execution of each actual worker and its final native cache. -/
inductive Execution [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (emptyGuard : Guard) (conjoin : Guard → Guard → Guard) (left right : Value Symbol Guard) :
    SourceRecursiveIntersectionThunks.State width Symbol Guard → Bool → SourceRecursiveIntersectionThunks.State width Symbol Guard → Prop where
  | done (fuel readFuel outer inner minimumFuel : Nat)
      (state middle : SourceRecursiveIntersectionThunks.State width Symbol Guard) (value : Value Symbol Guard)
      (edges : List (EdgeValue Symbol Guard)) (exposed final : InternedConstructorTemplates.State Symbol Guard)
      (rows : SourceColdSharedRows.Rows Symbol Guard)
      (native : SourceRecursiveIntersectionNative.execute emptyGuard conjoin fuel
        (.node ⟨IntersectionEmptyDomain.emptyDomain, left, right⟩ .pure) state = .done value middle)
      (read : MergedFreshOrdinaryExposure.nodeEdges readFuel value middle.machine.heap = .done edges exposed)
      (collected : SourceFreshOrdinaryColdSharedRows.collect outer inner exposed (fun _ => none) [value] = .done rows final)
      (minimum : let raw := SourceColdSharedRows.table rows (keys final rows) value
        MinimumSize.sweeps (SourceRowsMinimumAdapter.automaton raw) (raw.map Prod.fst) minimumFuel (fun _ => none) =
          SourceRowsMinimumAdapter.minimumSizes raw) :
      Execution emptyGuard conjoin left right state
        (if edges.isEmpty then false else
          (SourceRowsMinimumAdapter.minimumSizes (SourceColdSharedRows.table rows (keys final rows) value) (encode value)).isSome)
        (advance middle ⟨final, middle.machine.domains⟩)

/-- Closed original operands have a finite exact callback from every ready warm cache, with no supplied native completion. -/
theorem complete [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (emptyGuard : Guard) (conjoin : Guard → Guard → Guard)
    (state : SourceRecursiveIntersectionThunks.State width Symbol Guard) (ready : Ready emptyGuard conjoin state)
    (left right : Value Symbol Guard) (leftOriginal : Original left) (rightOriginal : Original right)
    (leftAvailable : Available state.machine.heap left) (rightAvailable : Available state.machine.heap right)
    (leftClosed : left.free = []) (rightClosed : right.free = [])
    (ranges : SourceRecursiveIntersectionNative.WordRanges emptyGuard conjoin
      (.node ⟨IntersectionEmptyDomain.emptyDomain, left, right⟩ .pure) state) :
    ∃ result after, Execution emptyGuard conjoin left right state result after ∧
      Ready emptyGuard conjoin after ∧ Extension state.machine after.machine ∧
      ∀ ambient, result = true ↔ ∃ term,
        InternedGuardedLanguage.meaning (fun _ _ => true) ambient left term ∧
        InternedGuardedLanguage.meaning (fun _ _ => true) ambient right term := by
  obtain ⟨fuel, value, middle, native, correct, middleSemantic, middleCovered, middleIdle, _⟩ :=
    SourceRecursiveIntersectionNative.warm_node_complete emptyGuard conjoin state ready.valid ready.idle ready.semantic ready.covered
      (fun _ _ => true) left right leftOriginal rightOriginal leftAvailable rightAvailable leftClosed rightClosed ranges
  have requestReady : NodeReady state.machine ⟨IntersectionEmptyDomain.emptyDomain, left, right⟩ :=
    ⟨empty_domain state.machine, leftAvailable, rightAvailable⟩
  have bounds := (SourceRecursiveIntersectionNative.evaluation_of_done emptyGuard conjoin fuel _ state middle value native).bounds_of_ranges ranges
  have safe := safe_requestNode IntersectionEmptyDomain.emptyDomain left right state.machine requestReady
  have certificate := semantic_requestNode IntersectionEmptyDomain.emptyDomain left right state.machine requestReady
  have middleGuarded := (bounds.guarded_heaps (fun current value => Available current.heap value)
    (by intro value; trivial) safe ready.valid certificate ready.semantic (by intro value; trivial) ready.guarded).2
  have middleOpen := (bounds.open_depth_heaps (fun current value => Available current.heap value)
    (by intro value; trivial) safe ready.valid certificate ready.semantic (by intro value; trivial) ready.openDepth).2
  have middleBudget := (bounds.budget_heaps (fun current value => Available current.heap value)
    (by intro value; trivial) safe ready.valid certificate ready.semantic (by intro value; trivial) ready.budget).2
  have closed := SourceRecursiveIntersectionResultScope.empty_scope value
    (correct.meaning.request_scope _ _ _ _ ready.valid.machine requestReady ready.semantic)
  obtain ⟨readFuel, edges, exposed, rows, final, outer, inner, read, _, _, collected,
      ⟨nextValid, _, _, nextSemantic, nextCovered, nextOpen, nextGuarded, nextBudget, extension⟩, callback⟩ :=
    SourceFreshOrdinaryColdMemoState.prechecked_advance emptyGuard conjoin middle correct.valid middleSemantic middleCovered
      middleOpen middleGuarded middleBudget value correct.result closed
  obtain ⟨minimumFuel, minimumRun, _⟩ := SourceRowsMinimumAdapter.finite (SourceColdSharedRows.table rows (keys final rows) value)
  let result := if edges.isEmpty then false else
    (SourceRowsMinimumAdapter.minimumSizes (SourceColdSharedRows.table rows (keys final rows) value) (encode value)).isSome
  let after := advance middle (⟨final, middle.machine.domains⟩ : Machine Symbol Guard)
  refine ⟨result, after, .done fuel readFuel outer inner minimumFuel state middle value edges exposed final rows
    native read (collected outer inner (Nat.le_refl _) (Nat.le_refl _)) minimumRun,
    ⟨nextValid, middleIdle.advance middle _, nextSemantic, nextCovered, nextOpen, nextGuarded, nextBudget⟩,
    correct.growth.trans extension, ?_⟩
  intro ambient
  rw [callback ambient]
  apply exists_congr
  intro term
  exact SourceRecursiveIntersectionNative.native_product emptyGuard conjoin fuel left right state middle value ready.valid
    leftOriginal rightOriginal leftAvailable rightAvailable leftClosed rightClosed ready.semantic ready.guarded native ranges
    (fun _ _ => true) (by intros; rfl) ambient term

end MicroCFTA.SourceFreshOrdinaryNativeCallback
