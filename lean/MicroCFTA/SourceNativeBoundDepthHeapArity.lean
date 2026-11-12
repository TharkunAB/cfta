import MicroCFTA.SourceNativeBoundDepthMeaning
import MicroCFTA.SourceNativeBoundDepthChildArity
import MicroCFTA.SourceNativeReadArityHeap

namespace MicroCFTA.SourceNativeBoundDepthHeapArity
open Cache Language InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
open InternedNestedProvenance (Values Edges)
open MergedColdReaderClosedInputs (ClosedValues ClosedEdges)
open SourceEqualityRequiredCache (Keeps)
open SourceEqualityRequiredSemanticCache (SemanticReady)
open SourceNativeBoundDepth (Memo Result atHeight)
open SourceNativeReadArityHeap (Heap)
open SourceNativeBoundDepthMeaning (DeepOrdinary)
open InternedGuardedLanguage (meaning)
variable {Symbol Guard : Type} {bound : Nat}

private def MemoReady (state : State Symbol Guard) (memo : Memo Symbol Guard) : Prop :=
  ∀ key value, memo key = some value → Available state value ∧ value.free = []

private theorem memo_keeps {before after : State Symbol Guard} {memo : Memo Symbol Guard}
    (keeps : Keeps before after) (ready : MemoReady before memo) : MemoReady after memo := by
  intro key value found
  obtain ⟨available, closed⟩ := ready key value found
  exact ⟨keeps.available value available, closed⟩

private theorem memo_put {state : State Symbol Guard} {memo : Memo Symbol Guard}
    (ready : MemoReady state memo) (key : Int × Nat) (value : Value Symbol Guard)
    (available : Available state value) (closed : value.free = []) :
    MemoReady state (Cache.put memo key value) := by
  intro other actual found
  by_cases same : other = key
  · subst other
    simp [Cache.put] at found
    subst actual
    exact ⟨available, closed⟩
  · exact ready other actual (by simpa only [Cache.put, ite_eq_right same] using found)

private def Observes (bound : Nat)
    (call : Value Symbol Guard → State Symbol Guard → Memo Symbol Guard → Result Symbol Guard (Value Symbol Guard)) : Prop :=
  ∀ value before memo result after finalMemo, SemanticReady before → Available before value → value.free = [] →
    MemoReady before memo → Heap bound before → call value before memo = (.done result after, finalMemo) →
    SemanticReady after ∧ Keeps before after ∧ Available after result ∧ result.free = [] ∧
      MemoReady after finalMemo ∧ Heap bound after

private theorem bind_done {actual : Result Symbol Guard First}
    {next : First → State Symbol Guard → Memo Symbol Guard → Result Symbol Guard Output}
    {result : Output} {after : State Symbol Guard} {finalMemo : Memo Symbol Guard}
    (observed : SourceNativeBoundDepth.bind actual next = (.done result after, finalMemo)) :
    ∃ value middle memo, actual = (.done value middle, memo) ∧ next value middle memo = (.done result after, finalMemo) := by
  rcases actual with ⟨outcome, memo⟩
  cases outcome with
  | done value middle => exact ⟨value, middle, memo, rfl, observed⟩
  | failed fault middle => simp [SourceNativeBoundDepth.bind] at observed

private theorem children_observed
    (copy : Value Symbol Guard → State Symbol Guard → Memo Symbol Guard → Result Symbol Guard (Value Symbol Guard))
    (observe : Observes bound copy) (original : List (Value Symbol Guard))
    (before : State Symbol Guard) (memo : Memo Symbol Guard) (result : List (Value Symbol Guard))
    (after : State Symbol Guard) (finalMemo : Memo Symbol Guard) (semantic : SemanticReady before)
    (available : Values before original) (closed : ClosedValues original) (memoReady : MemoReady before memo)
    (heap : Heap bound before)
    (observed : SourceNativeBoundDepth.children copy original before memo = (.done result after, finalMemo)) :
    SemanticReady after ∧ Keeps before after ∧ Values after result ∧ ClosedValues result ∧
      MemoReady after finalMemo ∧ Heap bound after := by
  induction original generalizing before memo result after finalMemo with
  | nil =>
      simp only [SourceNativeBoundDepth.children, Prod.mk.injEq, MergedSourceComparison.Result.done.injEq] at observed
      rcases observed with ⟨⟨resultEq, heapEq⟩, memoEq⟩
      subst result
      subst after
      subst finalMemo
      refine ⟨semantic, SourceEqualityRequiredCache.pure_keeps before semantic.ready, ?_, ?_, memoReady, heap⟩
      · intro value member
        cases member
      · intro value member
        cases member
  | cons first rest ih =>
      obtain ⟨firstResult, middle, nextMemo, firstDone, remaining⟩ := bind_done
        (by simpa only [SourceNativeBoundDepth.children] using observed)
      obtain ⟨restResult, last, saved, restDone, finished⟩ := bind_done remaining
      simp only [Prod.mk.injEq, MergedSourceComparison.Result.done.injEq] at finished
      rcases finished with ⟨⟨resultEq, heapEq⟩, memoEq⟩
      subst result
      subst after
      subst finalMemo
      obtain ⟨middleSemantic, firstKeeps, firstAvailable, firstClosed, firstMemo, firstHeap⟩ :=
        observe first before memo firstResult middle nextMemo semantic (available first List.mem_cons_self)
          (closed first List.mem_cons_self) memoReady heap firstDone
      have remainingAvailable : Values middle rest := by
        intro value member
        exact firstKeeps.available value (available value (List.mem_cons_of_mem first member))
      obtain ⟨lastSemantic, restKeeps, restAvailable, restClosed, restMemo, restHeap⟩ :=
        ih middle nextMemo restResult last saved middleSemantic remainingAvailable
          (fun value member => closed value (List.mem_cons_of_mem first member)) firstMemo firstHeap restDone
      refine ⟨lastSemantic, firstKeeps.trans restKeeps, ?_, ?_, restMemo, restHeap⟩
      · intro value member
        rcases List.mem_cons.mp member with rfl | member
        · exact restKeeps.available value firstAvailable
        · exact restAvailable value member
      · intro value member
        rcases List.mem_cons.mp member with rfl | member
        · exact firstClosed
        · exact restClosed value member

private theorem edges_observed [DecidableEq (EdgeKey Symbol Guard)]
    (copy : Value Symbol Guard → State Symbol Guard → Memo Symbol Guard → Result Symbol Guard (Value Symbol Guard))
    (observe : Observes bound copy) (original : List (EdgeValue Symbol Guard))
    (before : State Symbol Guard) (memo : Memo Symbol Guard) (result : List (EdgeValue Symbol Guard))
    (after : State Symbol Guard) (finalMemo : Memo Symbol Guard) (semantic : SemanticReady before)
    (resident : Edges before original) (closed : ClosedEdges original) (memoReady : MemoReady before memo)
    (heap : Heap bound before)
    (observed : SourceNativeBoundDepth.edges copy original before memo = (.done result after, finalMemo)) :
    SemanticReady after ∧ Keeps before after ∧ Edges after result ∧ ClosedEdges result ∧
      MemoReady after finalMemo ∧ Heap bound after := by
  induction original generalizing before memo result after finalMemo with
  | nil =>
      simp only [SourceNativeBoundDepth.edges, Prod.mk.injEq, MergedSourceComparison.Result.done.injEq] at observed
      rcases observed with ⟨⟨resultEq, heapEq⟩, memoEq⟩
      subst result
      subst after
      subst finalMemo
      refine ⟨semantic, SourceEqualityRequiredCache.pure_keeps before semantic.ready, ?_, ?_, memoReady, heap⟩
      · intro edge member
        cases member
      · intro edge member
        cases member
  | cons first rest ih =>
      obtain ⟨copiedChildren, middle, nextMemo, childrenDone, remaining⟩ := bind_done
        (by simpa only [SourceNativeBoundDepth.edges] using observed)
      let rebuilt := InternedConstructorTemplates.run
        (makeEdge first.entry.key.symbol first.entry.key.constraint copiedChildren) middle
      change SourceNativeBoundDepth.bind (SourceNativeBoundDepth.edges copy rest rebuilt.2 nextMemo)
        (fun values state saved => (.done (rebuilt.1 :: values) state, saved)) = (.done result after, finalMemo) at remaining
      obtain ⟨restResult, last, saved, restDone, finished⟩ := bind_done remaining
      simp only [Prod.mk.injEq, MergedSourceComparison.Result.done.injEq] at finished
      rcases finished with ⟨⟨resultEq, heapEq⟩, memoEq⟩
      subst result
      subst after
      subst finalMemo
      have originalChildren : Values before first.children :=
        semantic.ready.semantic.1.normal.facts.cached.edges first.entry.key first (resident first List.mem_cons_self)
      obtain ⟨middleSemantic, childKeeps, childAvailable, childClosed, childMemo, childHeap⟩ :=
        children_observed copy observe first.children before memo copiedChildren middle nextMemo semantic
          originalChildren (closed first List.mem_cons_self) memoReady heap childrenDone
      have checked := SourceEqualityRequiredCache.edge first.entry.key.symbol first.entry.key.constraint
        copiedChildren middle middleSemantic.ready childAvailable
      have edgeSemantic : SemanticReady rebuilt.2 :=
        SourceEqualityRequiredSemanticCache.edge first.entry.key.symbol first.entry.key.constraint
          copiedChildren middle middleSemantic childAvailable
      have edgeKeeps : Keeps middle rebuilt.2 := checked.1
      have edgeResident : EdgeResident rebuilt.2 rebuilt.1 := checked.2.1
      have edgeClosed : ClosedValues rebuilt.1.children := by
        rw [checked.2.2]
        exact childClosed
      have originalArity : first.children.length ≤ bound :=
        heap first.entry.key first (resident first List.mem_cons_self)
      have sameLength := SourceNativeBoundDepth.children_length copy first.children copiedChildren
        before middle memo nextMemo childrenDone
      have edgeHeap : Heap bound rebuilt.2 :=
        SourceNativeReadArityHeap.edge_heap first.entry.key.symbol first.entry.key.constraint
          copiedChildren middle childHeap (by rw [sameLength]; exact originalArity)
      have headKeeps := childKeeps.trans edgeKeeps
      have restResident : Edges rebuilt.2 rest := by
        intro edge member
        exact edge_grows before rebuilt.2 headKeeps.growth edge (resident edge (List.mem_cons_of_mem first member))
      obtain ⟨lastSemantic, restKeeps, restAvailable, restClosed, restMemo, restHeap⟩ :=
        ih rebuilt.2 nextMemo restResult last saved edgeSemantic restResident
          (fun edge member => closed edge (List.mem_cons_of_mem first member)) (memo_keeps edgeKeeps childMemo) edgeHeap restDone
      refine ⟨lastSemantic, headKeeps.trans restKeeps, ?_, ?_, restMemo, restHeap⟩
      · intro edge member
        rcases List.mem_cons.mp member with rfl | member
        · exact edge_grows rebuilt.2 last restKeeps.growth rebuilt.1 edgeResident
        · exact restAvailable edge member
      · intro edge member
        rcases List.mem_cons.mp member with rfl | member
        · exact edgeClosed
        · exact restClosed edge member

private theorem interned_observed [DecidableEq (EdgeKey Symbol Guard)] (fuel height : Nat)
    (observe : Observes bound (atHeight (Symbol := Symbol) (Guard := Guard) fuel height))
    (identity : Nat) (value : Value Symbol Guard)
    (before : State Symbol Guard) (memo : Memo Symbol Guard) (result : Value Symbol Guard)
    (after : State Symbol Guard) (finalMemo : Memo Symbol Guard) (semantic : SemanticReady before)
    (available : Available before value) (closed : value.free = []) (memoReady : MemoReady before memo)
    (heap : Heap bound before)
    (observed : SourceNativeBoundDepth.interned fuel (height : Int) identity value
      (atHeight fuel height) before memo = (.done result after, finalMemo)) :
    SemanticReady after ∧ Keeps before after ∧ Available after result ∧ result.free = [] ∧
      MemoReady after finalMemo ∧ Heap bound after := by
  cases found : memo ((height : Int), identity) with
  | some cached =>
      simp only [SourceNativeBoundDepth.interned, found, Prod.mk.injEq,
        MergedSourceComparison.Result.done.injEq] at observed
      rcases observed with ⟨⟨resultEq, heapEq⟩, memoEq⟩
      subst result
      subst after
      subst finalMemo
      obtain ⟨cachedAvailable, cachedClosed⟩ := memoReady _ _ found
      exact ⟨semantic, SourceEqualityRequiredCache.pure_keeps before semantic.ready,
        cachedAvailable, cachedClosed, memoReady, heap⟩
  | none =>
      cases readDone : MergedFreshOrdinaryExposure.nodeEdges fuel value before with
      | unresolved name stopped => simp [SourceNativeBoundDepth.interned, found, readDone] at observed
      | pending key stopped => simp [SourceNativeBoundDepth.interned, found, readDone] at observed
      | exhausted stopped => simp [SourceNativeBoundDepth.interned, found, readDone] at observed
      | done original afterRead =>
          obtain ⟨copied, middle, nextMemo, copiedDone, finished⟩ := bind_done
            (by simpa only [SourceNativeBoundDepth.interned, found, readDone] using observed)
          let bounded := InternedConstructorTemplates.run (makeNode copied) middle
          change (MergedSourceComparison.Result.done bounded.1 bounded.2,
            Cache.put nextMemo ((height : Int), identity) bounded.1) =
            (MergedSourceComparison.Result.done result after, finalMemo) at finished
          simp only [Prod.mk.injEq, MergedSourceComparison.Result.done.injEq] at finished
          rcases finished with ⟨⟨resultEq, heapEq⟩, memoEq⟩
          subst result
          subst after
          subst finalMemo
          have trace : SourceEqualityProjectionRead.Read value before original afterRead := .done fuel readDone
          obtain ⟨readKeeps, readSemantic, readResident, readClosed⟩ := trace.verified semantic available closed
          have readHeap := (SourceNativeReadArityHeap.read_arity_heap trace semantic available closed heap).1
          have retainedResident : Edges afterRead (SourceNativeBoundDepth.retained (height : Int) original) := by
            intro edge member
            exact readResident edge (List.mem_filter.mp member).1
          have retainedClosed : ClosedEdges (SourceNativeBoundDepth.retained (height : Int) original) := by
            intro edge member
            exact readClosed edge (List.mem_filter.mp member).1
          obtain ⟨middleSemantic, copiedKeeps, copiedResident, copiedClosed, copiedMemo, copiedHeap⟩ :=
            edges_observed (atHeight fuel height) observe
              (SourceNativeBoundDepth.retained (height : Int) original) afterRead memo copied middle nextMemo
              readSemantic retainedResident retainedClosed (memo_keeps readKeeps memoReady) readHeap copiedDone
          have checked := SourceEqualityRequiredCache.node copied middle middleSemantic.ready copiedResident copiedClosed
          have finalSemantic : SemanticReady bounded.2 :=
            SourceEqualityRequiredSemanticCache.node copied middle middleSemantic copiedResident copiedClosed
          have nodeKeeps : Keeps middle bounded.2 := checked.1
          have finalAvailable : Available bounded.2 bounded.1 := checked.2.1
          have finalClosed : bounded.1.free = [] := checked.2.2.1
          have finalHeap : Heap bound bounded.2 := SourceNativeReadArityHeap.node_heap copied middle copiedHeap
          exact ⟨finalSemantic, readKeeps.trans (copiedKeeps.trans nodeKeeps), finalAvailable, finalClosed,
            memo_put (memo_keeps nodeKeeps copiedMemo) ((height : Int), identity) bounded.1
              finalAvailable finalClosed, finalHeap⟩

private theorem worker_observed [DecidableEq (EdgeKey Symbol Guard)] (fuel height : Nat) :
    Observes bound (atHeight (Symbol := Symbol) (Guard := Guard) fuel height) := by
  induction height with
  | zero =>
      intro value before memo result after finalMemo semantic available closed memoReady heap observed
      cases value
      case reference name => cases closed
      all_goals
        simp only [atHeight, Prod.mk.injEq, MergedSourceComparison.Result.done.injEq] at observed
        rcases observed with ⟨⟨resultEq, heapEq⟩, memoEq⟩
        subst result
        subst after
        subst finalMemo
        exact ⟨semantic, SourceEqualityRequiredCache.pure_keeps before semantic.ready,
          empty_available before, rfl, memoReady, heap⟩
  | succ height ih =>
      intro value before memo result after finalMemo semantic available closed memoReady heap observed
      cases value with
      | reference name => cases closed
      | empty =>
          simp only [atHeight, Prod.mk.injEq, MergedSourceComparison.Result.done.injEq] at observed
          rcases observed with ⟨⟨resultEq, heapEq⟩, memoEq⟩
          subst result
          subst after
          subst finalMemo
          exact ⟨semantic, SourceEqualityRequiredCache.pure_keeps before semantic.ready,
            empty_available before, rfl, memoReady, heap⟩
      | node entry rows cachedDepth free =>
          exact interned_observed fuel height ih entry.identity (.node entry rows cachedDepth free) before memo result after
            finalMemo semantic available closed memoReady heap (by simpa only [atHeight] using observed)
      | union entry members cachedDepth free =>
          exact interned_observed fuel height ih entry.identity (.union entry members cachedDepth free) before memo result after
            finalMemo semantic available closed memoReady heap (by simpa only [atHeight] using observed)
      | mu entry body depthShape ordinaryShape =>
          exact interned_observed fuel height ih entry.identity (.mu entry body depthShape ordinaryShape) before memo result after
            finalMemo semantic available closed memoReady heap (by simpa only [atHeight] using observed)

/-- The same successful bounded copy retains every current physical edge-child cap. -/
theorem boundDepth_observed_heap [DecidableEq (EdgeKey Symbol Guard)]
    (readerFuel : Nat) (depth : Int) (root : Value Symbol Guard)
    (before : State Symbol Guard) (semantic : SemanticReady before)
    (available : Available before root) (closed : root.free = []) (heap : Heap bound before)
    {result : Value Symbol Guard} {after : State Symbol Guard} {memo : Memo Symbol Guard}
    (actual : SourceNativeBoundDepth.boundDepth readerFuel depth root before = (.done result after, memo)) :
    Heap bound after := by
  have observed : atHeight readerFuel (depth + 1).toNat root before (fun _ => none) =
      (.done result after, memo) := by
    simpa only [SourceNativeBoundDepth.boundDepth, SourceNativeBoundDepth.run] using actual
  exact (worker_observed readerFuel (depth + 1).toNat root before (fun _ => none) result after memo
    semantic available closed (by intro key value impossible; cases impossible) heap observed).2.2.2.2.2

/-- One exact completion receipt also retains the arity cap computed from its original heap. -/
theorem complete_exact_arity [DecidableEq (EdgeKey Symbol Guard)] (depth : Int) (root : Value Symbol Guard)
    (before : State Symbol Guard) (semantic : SemanticReady before)
    (available : Available before root) (closed : root.free = []) :
    ∃ cutoff result after memo,
      (∀ fuel, cutoff ≤ fuel → SourceNativeBoundDepth.boundDepth fuel depth root before = (.done result after, memo)) ∧
      SemanticReady after ∧ Keeps before after ∧ Available after root ∧ root.free = [] ∧
      Available after result ∧ result.free = [] ∧
      (∀ key value, memo key = some value → Available after value ∧ value.free = []) ∧
      DeepOrdinary result ∧ MergedOrdinaryHeight.height result ≤ (depth + 1).toNat ∧
      (∀ holds ambient term, meaning holds ambient result term ↔
        meaning holds ambient root term ∧ (term.height : Int) ≤ depth + 1) ∧
      Heap (SourceRecursiveIntersectionSourceProfile.limits before).arity after := by
  obtain ⟨cutoff, result, after, memo, stable, finalSemantic, keeps, rootAvailable, rootClosed,
      resultAvailable, resultClosed, memoAvailable, ordinary, height, languages⟩ :=
    SourceNativeBoundDepthMeaning.complete_exact depth root before semantic available closed
  have initialHeap := SourceNativeReadArityHeap.initial_heap before semantic.ready.semantic.1.normal.facts
  have finalHeap := boundDepth_observed_heap cutoff depth root before semantic available closed initialHeap
    (stable cutoff (Nat.le_refl _))
  exact ⟨cutoff, result, after, memo, stable, finalSemantic, keeps, rootAvailable, rootClosed,
    resultAvailable, resultClosed, memoAvailable, ordinary, height, languages, finalHeap⟩

end MicroCFTA.SourceNativeBoundDepthHeapArity
