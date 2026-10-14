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

/-- Successful exposure bounds return the identical ordered edges and cache. -/
theorem read_unique [DecidableEq (EdgeKey Symbol Guard)]
    (firstFuel secondFuel : Nat) (value : Value Symbol Guard) (state : InternedConstructorTemplates.State Symbol Guard)
    (firstEdges secondEdges : List (EdgeValue Symbol Guard)) (firstAfter secondAfter : InternedConstructorTemplates.State Symbol Guard)
    (first : MergedFreshOrdinaryExposure.nodeEdges firstFuel value state = .done firstEdges firstAfter)
    (second : MergedFreshOrdinaryExposure.nodeEdges secondFuel value state = .done secondEdges secondAfter) :
    firstEdges = secondEdges ∧ firstAfter = secondAfter := by
  have firstStable := MergedFreshOrdinaryColdReplay.nodeEdges_stable firstFuel secondFuel value state
    (by simp only [first, MergedSourceExposure.Finished])
  have secondStable := MergedFreshOrdinaryColdReplay.nodeEdges_stable secondFuel firstFuel value state
    (by simp only [second, MergedSourceExposure.Finished])
  rw [Nat.add_comm secondFuel firstFuel] at secondStable
  apply MergedSourceExposure.Result.done.inj
  rw [← first, ← second]
  exact firstStable.symm.trans secondStable

/-- A complete source callback records finite execution of each actual worker and its final native cache. -/
inductive Execution [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (emptyGuard : Guard) (conjoin : Guard → Guard → Guard) (left right : Value Symbol Guard) :
      SourceRecursiveIntersectionThunks.State width Symbol Guard → Bool → SourceRecursiveIntersectionThunks.State width Symbol Guard → Prop where
  | empty (fuel readFuel : Nat)
      (state middle : SourceRecursiveIntersectionThunks.State width Symbol Guard) (value : Value Symbol Guard)
      (exposed : InternedConstructorTemplates.State Symbol Guard)
      (native : SourceRecursiveIntersectionNative.execute emptyGuard conjoin fuel
        (.node ⟨IntersectionEmptyDomain.emptyDomain, left, right⟩ .pure) state = .done value middle)
      (read : MergedFreshOrdinaryExposure.nodeEdges readFuel value middle.machine.heap = .done [] exposed) :
      Execution emptyGuard conjoin left right state false (advance middle ⟨exposed, middle.machine.domains⟩)
  | done (fuel readFuel outer inner minimumFuel : Nat)
      (state middle : SourceRecursiveIntersectionThunks.State width Symbol Guard) (value : Value Symbol Guard)
      (edges : List (EdgeValue Symbol Guard)) (exposed final : InternedConstructorTemplates.State Symbol Guard)
      (rows : SourceColdSharedRows.Rows Symbol Guard)
      (nonempty : edges.isEmpty = false)
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
  let result := if edges.isEmpty then false else
    (SourceRowsMinimumAdapter.minimumSizes (SourceColdSharedRows.table rows (keys final rows) value) (encode value)).isSome
  have language (ambient : InternedGuardedLanguage.Env Symbol) : result = true ↔ ∃ term,
      InternedGuardedLanguage.meaning (fun _ _ => true) ambient left term ∧
      InternedGuardedLanguage.meaning (fun _ _ => true) ambient right term := by
    rw [callback ambient]
    apply exists_congr
    intro term
    exact SourceRecursiveIntersectionNative.native_product emptyGuard conjoin fuel left right state middle value ready.valid
      leftOriginal rightOriginal leftAvailable rightAvailable leftClosed rightClosed ready.semantic ready.guarded native ranges
      (fun _ _ => true) (by intros; rfl) ambient term
  by_cases empty : edges.isEmpty = true
  · have edgesEmpty := List.isEmpty_iff.mp empty
    subst edges
    obtain ⟨otherFuel, otherEdges, otherAfter, otherRead, exposedSemantic, exposedCovered, exposedOpen, exposedGrowth, exposedHistory, _, _, _⟩ :=
      MergedFreshOrdinaryColdTermination.read_closed value middle.machine.heap middleSemantic middleCovered middleOpen correct.result closed
    obtain ⟨rfl, rfl⟩ := read_unique readFuel otherFuel value middle.machine.heap [] otherEdges exposed otherAfter read otherRead
    have exposedGuarded : InternedGuardedProbeHeap.Heap exposed := by
      simpa only [read, MergedSourceExposure.Result.state] using
        MergedFreshOrdinaryGuardedEffects.nodeEdges_heap readFuel value middle.machine.heap middleSemantic middleCovered middleGuarded correct.result closed
    have exposedBudget : InternedGuardedBudgetProbeHeap.Heap exposed := by
      simpa only [read, MergedSourceExposure.Result.state] using
        MergedFreshOrdinaryBudgetEffects.nodeEdges_heap readFuel value middle.machine.heap middleSemantic middleCovered middleBudget correct.result closed
    let after := advance middle (⟨exposed, middle.machine.domains⟩ : Machine Symbol Guard)
    have readExtension : Extension middle.machine after.machine := ⟨exposedGrowth, exposedHistory, extends_refl _⟩
    have checked : SourceRecursiveIntersectionKernel.Valid after.machine := ⟨exposedSemantic.1.normal.facts, correct.valid.machine.2⟩
    refine ⟨false, after, .empty fuel readFuel state middle value exposed native read,
      ⟨advance_valid width emptyGuard conjoin middle correct.valid _ checked readExtension, middleIdle.advance middle _,
        exposedSemantic, exposedCovered, exposedOpen, exposedGuarded, exposedBudget⟩, correct.growth.trans readExtension, ?_⟩
    exact language
  · have nonempty : edges.isEmpty = false := by
      cases found : edges.isEmpty with
      | false => rfl
      | true => exact False.elim (empty found)
    obtain ⟨minimumFuel, minimumRun, _⟩ := SourceRowsMinimumAdapter.finite (SourceColdSharedRows.table rows (keys final rows) value)
    let after := advance middle (⟨final, middle.machine.domains⟩ : Machine Symbol Guard)
    exact ⟨result, after, .done fuel readFuel outer inner minimumFuel state middle value edges exposed final rows nonempty
      native read (collected outer inner (Nat.le_refl _) (Nat.le_refl _)) minimumRun,
      ⟨nextValid, middleIdle.advance middle _, nextSemantic, nextCovered, nextOpen, nextGuarded, nextBudget⟩,
      correct.growth.trans extension, language⟩

end MicroCFTA.SourceFreshOrdinaryNativeCallback
