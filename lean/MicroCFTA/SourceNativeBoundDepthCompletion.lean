import MicroCFTA.SourceNativeBoundDepth
import MicroCFTA.SourceEqualityProjectionRead

/-!
# Completion of native bounded-depth copying

Current closed inputs and ready native caches supply one reader cutoff.
Every larger cutoff returns the same value, native heap, and local memo.
The proof retains available closed memo values through the actual run.
Language preservation and enumeration completion remain separate.
-/
namespace MicroCFTA.SourceNativeBoundDepthCompletion
open Cache InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
open InternedNestedProvenance (Values Edges)
open MergedColdReaderClosedInputs (ClosedValues ClosedEdges)
open SourceEqualityRequiredCache (Keeps)
open SourceEqualityRequiredSemanticCache (SemanticReady)
open SourceNativeBoundDepth (Memo Result atHeight)

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

private def Complete
    (call : Nat → Value Symbol Guard → State Symbol Guard → Memo Symbol Guard → Result Symbol Guard (Value Symbol Guard)) : Prop :=
  ∀ value before memo, SemanticReady before → Available before value → value.free = [] → MemoReady before memo →
    ∃ cutoff result after finalMemo,
      (∀ fuel, cutoff ≤ fuel → call fuel value before memo = (.done result after, finalMemo)) ∧
      SemanticReady after ∧ Keeps before after ∧ Available after result ∧ result.free = [] ∧ MemoReady after finalMemo

private theorem children_complete
    (call : Nat → Value Symbol Guard → State Symbol Guard → Memo Symbol Guard → Result Symbol Guard (Value Symbol Guard))
    (complete : Complete call) (original : List (Value Symbol Guard))
    (before : State Symbol Guard) (memo : Memo Symbol Guard) (semantic : SemanticReady before)
    (available : Values before original) (closed : ClosedValues original) (memoReady : MemoReady before memo) :
    ∃ cutoff result after finalMemo,
      (∀ fuel, cutoff ≤ fuel → SourceNativeBoundDepth.children (call fuel) original before memo =
        (.done result after, finalMemo)) ∧
      SemanticReady after ∧ Keeps before after ∧ Values after result ∧ ClosedValues result ∧ MemoReady after finalMemo := by
  induction original generalizing before memo with
  | nil =>
      refine ⟨0, [], before, memo, ?_, semantic,
        SourceEqualityRequiredCache.pure_keeps before semantic.ready, ?_, ?_, memoReady⟩
      · intro fuel enough
        rfl
      · intro value member
        cases member
      · intro value member
        cases member
  | cons first rest ih =>
      obtain ⟨firstCutoff, firstResult, middle, nextMemo, firstStable, firstSemantic, firstKeeps,
          firstAvailable, firstClosed, firstMemo⟩ :=
        complete first before memo semantic (available first List.mem_cons_self)
          (closed first List.mem_cons_self) memoReady
      have remaining : Values middle rest := by
        intro value member
        exact firstKeeps.available value (available value (List.mem_cons_of_mem first member))
      obtain ⟨restCutoff, restResult, after, finalMemo, restStable, restSemantic, restKeeps,
          restAvailable, restClosed, restMemo⟩ :=
        ih middle nextMemo firstSemantic remaining
          (fun value member => closed value (List.mem_cons_of_mem first member)) firstMemo
      refine ⟨max firstCutoff restCutoff, firstResult :: restResult, after, finalMemo, ?_,
        restSemantic, firstKeeps.trans restKeeps, ?_, ?_, restMemo⟩
      · intro fuel enough
        have firstDone := firstStable fuel (Nat.le_trans (Nat.le_max_left _ _) enough)
        have restDone := restStable fuel (Nat.le_trans (Nat.le_max_right _ _) enough)
        simp only [SourceNativeBoundDepth.children, firstDone, SourceNativeBoundDepth.bind, restDone]
      · intro value member
        rcases List.mem_cons.mp member with rfl | member
        · exact restKeeps.available value firstAvailable
        · exact restAvailable value member
      · intro value member
        rcases List.mem_cons.mp member with rfl | member
        · exact firstClosed
        · exact restClosed value member

private theorem edges_complete [DecidableEq (EdgeKey Symbol Guard)]
    (call : Nat → Value Symbol Guard → State Symbol Guard → Memo Symbol Guard → Result Symbol Guard (Value Symbol Guard))
    (complete : Complete call) (original : List (EdgeValue Symbol Guard))
    (before : State Symbol Guard) (memo : Memo Symbol Guard) (semantic : SemanticReady before)
    (resident : Edges before original) (closed : ClosedEdges original) (memoReady : MemoReady before memo) :
    ∃ cutoff result after finalMemo,
      (∀ fuel, cutoff ≤ fuel → SourceNativeBoundDepth.edges (call fuel) original before memo =
        (.done result after, finalMemo)) ∧
      SemanticReady after ∧ Keeps before after ∧ Edges after result ∧ ClosedEdges result ∧ MemoReady after finalMemo := by
  induction original generalizing before memo with
  | nil =>
      refine ⟨0, [], before, memo, ?_, semantic,
        SourceEqualityRequiredCache.pure_keeps before semantic.ready, ?_, ?_, memoReady⟩
      · intro fuel enough
        rfl
      · intro edge member
        cases member
      · intro edge member
        cases member
  | cons first rest ih =>
      have originalChildren : Values before first.children :=
        semantic.ready.semantic.1.normal.facts.cached.edges first.entry.key first (resident first List.mem_cons_self)
      obtain ⟨childCutoff, copiedChildren, middle, nextMemo, childStable, middleSemantic, childKeeps,
          childAvailable, childClosed, childMemo⟩ :=
        children_complete call complete first.children before memo semantic originalChildren
          (closed first List.mem_cons_self) memoReady
      let rebuilt := InternedConstructorTemplates.run
        (makeEdge first.entry.key.symbol first.entry.key.constraint copiedChildren) middle
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
      have headKeeps := childKeeps.trans edgeKeeps
      have restResident : Edges rebuilt.2 rest := by
        intro edge member
        exact edge_grows before rebuilt.2 headKeeps.growth edge (resident edge (List.mem_cons_of_mem first member))
      obtain ⟨restCutoff, restResult, after, finalMemo, restStable, restSemantic, restKeeps,
          restAvailable, restClosed, restMemo⟩ :=
        ih rebuilt.2 nextMemo edgeSemantic restResident
          (fun edge member => closed edge (List.mem_cons_of_mem first member)) (memo_keeps edgeKeeps childMemo)
      refine ⟨max childCutoff restCutoff, rebuilt.1 :: restResult, after, finalMemo, ?_,
        restSemantic, headKeeps.trans restKeeps, ?_, ?_, restMemo⟩
      · intro fuel enough
        have childrenDone := childStable fuel (Nat.le_trans (Nat.le_max_left _ _) enough)
        have restDone := restStable fuel (Nat.le_trans (Nat.le_max_right _ _) enough)
        dsimp only [rebuilt] at restDone ⊢
        simp only [SourceNativeBoundDepth.edges, childrenDone, SourceNativeBoundDepth.bind, restDone]
      · intro edge member
        rcases List.mem_cons.mp member with rfl | member
        · exact edge_grows rebuilt.2 after restKeeps.growth rebuilt.1 edgeResident
        · exact restAvailable edge member
      · intro edge member
        rcases List.mem_cons.mp member with rfl | member
        · exact edgeClosed
        · exact restClosed edge member

private theorem interned_complete [DecidableEq (EdgeKey Symbol Guard)]
    (height : Nat) (smaller : Complete (fun fuel => atHeight (Symbol := Symbol) (Guard := Guard) fuel height))
    (identity : Nat) (value : Value Symbol Guard) (before : State Symbol Guard) (memo : Memo Symbol Guard)
    (semantic : SemanticReady before) (available : Available before value) (closed : value.free = [])
    (memoReady : MemoReady before memo) :
    ∃ cutoff result after finalMemo,
      (∀ fuel, cutoff ≤ fuel → SourceNativeBoundDepth.interned fuel (height : Int) identity value
        (atHeight (Symbol := Symbol) (Guard := Guard) fuel height) before memo = (.done result after, finalMemo)) ∧
      SemanticReady after ∧ Keeps before after ∧ Available after result ∧ result.free = [] ∧ MemoReady after finalMemo := by
  cases found : memo ((height : Int), identity) with
  | some result =>
      obtain ⟨resultAvailable, resultClosed⟩ := memoReady _ _ found
      refine ⟨0, result, before, memo, ?_, semantic,
        SourceEqualityRequiredCache.pure_keeps before semantic.ready, resultAvailable, resultClosed, memoReady⟩
      intro fuel enough
      simp only [SourceNativeBoundDepth.interned, found]
  | none =>
      obtain ⟨readCutoff, original, afterRead, readDone, _, _, _, _, _, _, _, readStable⟩ :=
        MergedFreshOrdinaryColdTermination.read_closed value before semantic.ready.semantic
          semantic.ready.covered semantic.ready.depth available closed
      have trace : SourceEqualityProjectionRead.Read value before original afterRead := .done readCutoff readDone
      obtain ⟨readKeeps, readSemantic, readResident, readClosed⟩ := trace.verified semantic available closed
      have retainedResident : Edges afterRead (SourceNativeBoundDepth.retained (height : Int) original) := by
        intro edge member
        exact readResident edge (List.mem_filter.mp member).1
      have retainedClosed : ClosedEdges (SourceNativeBoundDepth.retained (height : Int) original) := by
        intro edge member
        exact readClosed edge (List.mem_filter.mp member).1
      obtain ⟨copyCutoff, copied, middle, nextMemo, copyStable, middleSemantic, copyKeeps,
          copyResident, copyClosed, copyMemo⟩ :=
        edges_complete (fun fuel => atHeight (Symbol := Symbol) (Guard := Guard) fuel height) smaller
          (SourceNativeBoundDepth.retained (height : Int) original) afterRead memo readSemantic
          retainedResident retainedClosed (memo_keeps readKeeps memoReady)
      let bounded := InternedConstructorTemplates.run (makeNode copied) middle
      have checked := SourceEqualityRequiredCache.node copied middle middleSemantic.ready copyResident copyClosed
      have finalSemantic : SemanticReady bounded.2 :=
        SourceEqualityRequiredSemanticCache.node copied middle middleSemantic copyResident copyClosed
      have finalKeeps : Keeps middle bounded.2 := checked.1
      have finalAvailable : Available bounded.2 bounded.1 := checked.2.1
      have finalClosed : bounded.1.free = [] := checked.2.2.1
      refine ⟨max readCutoff copyCutoff, bounded.1, bounded.2,
        Cache.put nextMemo ((height : Int), identity) bounded.1, ?_, finalSemantic,
        readKeeps.trans (copyKeeps.trans finalKeeps), finalAvailable, finalClosed,
        memo_put (memo_keeps finalKeeps copyMemo) _ _ finalAvailable finalClosed⟩
      intro fuel enough
      have readEnough : readCutoff ≤ fuel := Nat.le_trans (Nat.le_max_left _ _) enough
      have copyEnough : copyCutoff ≤ fuel := Nat.le_trans (Nat.le_max_right _ _) enough
      have actualRead : MergedFreshOrdinaryExposure.nodeEdges fuel value before = .done original afterRead := by
        obtain ⟨extra, rfl⟩ := Nat.exists_eq_add_of_le readEnough
        exact readStable extra
      have actualCopy := copyStable fuel copyEnough
      simp only [SourceNativeBoundDepth.interned, found, actualRead, actualCopy, SourceNativeBoundDepth.bind]
      rfl

private theorem atHeight_complete [DecidableEq (EdgeKey Symbol Guard)] (height : Nat) :
    Complete (fun fuel => atHeight (Symbol := Symbol) (Guard := Guard) fuel height) := by
  induction height with
  | zero =>
      intro value before memo semantic available closed memoReady
      cases value
      case reference name => cases closed
      all_goals
        exact ⟨0, .empty, before, memo, by intro fuel enough; simp only [atHeight],
          semantic, SourceEqualityRequiredCache.pure_keeps before semantic.ready,
          empty_available before, rfl, memoReady⟩
  | succ height ih =>
      intro value before memo semantic available closed memoReady
      cases value with
      | empty =>
          exact ⟨0, .empty, before, memo, by intro fuel enough; simp only [atHeight],
            semantic, SourceEqualityRequiredCache.pure_keeps before semantic.ready,
            empty_available before, rfl, memoReady⟩
      | reference name => cases closed
      | node entry rows cachedDepth free =>
          simpa only [atHeight] using interned_complete height ih entry.identity
            (.node entry rows cachedDepth free) before memo semantic available closed memoReady
      | union entry members cachedDepth free =>
          simpa only [atHeight] using interned_complete height ih entry.identity
            (.union entry members cachedDepth free) before memo semantic available closed memoReady
      | mu entry body depthShape ordinaryShape =>
          simpa only [atHeight] using interned_complete height ih entry.identity
            (.mu entry body depthShape ordinaryShape) before memo semantic available closed memoReady

/-- Current closed inputs derive one exact completed copy at every sufficient reader cutoff. -/
theorem complete [DecidableEq (EdgeKey Symbol Guard)] (depth : Int) (root : Value Symbol Guard)
    (before : State Symbol Guard) (semantic : SemanticReady before)
    (available : Available before root) (closed : root.free = []) :
    ∃ cutoff result after memo,
      (∀ fuel, cutoff ≤ fuel → SourceNativeBoundDepth.boundDepth fuel depth root before = (.done result after, memo)) ∧
      SemanticReady after ∧ Keeps before after ∧ Available after root ∧ root.free = [] ∧
      Available after result ∧ result.free = [] ∧
      (∀ key value, memo key = some value → Available after value ∧ value.free = []) := by
  obtain ⟨cutoff, result, after, memo, stable, finalSemantic, keeps, resultAvailable, resultClosed, finalMemo⟩ :=
    atHeight_complete (Symbol := Symbol) (Guard := Guard) (depth + 1).toNat root before (fun _ => none)
      semantic available closed (by intro key value impossible; cases impossible)
  refine ⟨cutoff, result, after, memo, ?_, finalSemantic, keeps, keeps.available root available,
    closed, resultAvailable, resultClosed, finalMemo⟩
  intro fuel enough
  simpa only [SourceNativeBoundDepth.boundDepth, SourceNativeBoundDepth.run] using stable fuel enough

end MicroCFTA.SourceNativeBoundDepthCompletion
