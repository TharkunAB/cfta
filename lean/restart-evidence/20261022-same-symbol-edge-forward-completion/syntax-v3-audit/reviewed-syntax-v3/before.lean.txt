import MicroCFTA.SourceCurrentSameSymbolEdgeControl
import MicroCFTA.FormulaExecutable
import MicroCFTA.SourceCurrentAllocatedNativeContextualCompletion

namespace MicroCFTA.SourceCurrentSameSymbolEdgeForwardCompletion
open Cache Language IntersectSchedule InternedConstructorTemplates InternedEdgeResidency
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceRecursiveIntersectionInputView
open SourceCurrentAllocatedNativePhysicalCompletion (Good)
open SourceEqualityRequiredSemanticCache (SemanticReady)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Edge" => EdgeValue Symbol Guard
local notation "Wrapper" => SourceCurrentSameSymbolEdgeControl.State
local notation "guardHolds" => (@SourceEqualityPCSGuard.holds FullSyntax.Formula FormulaExecutable.formulaDecidableEq)
variable {width : Nat}

/-!
# Forward completion of two absent pair keys

Keep the pair memo separate from the complete checked state.
Semantic schedule completion and actual word ranges remain premises.
This result does not establish completion of every cluster comparison.
-/
open SourceCurrentSameSymbolEdgeControl (execute step)

private theorem ret_complete [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (value : Edge) (pending : List Nat) (before : Wrapper width) :
    execute (pending.length + 1) (.ret value pending) before =
      .done value {before with memo := pending.foldl
        (fun memo handle => FlatMemoThunk.finish handle value memo) before.memo} := by
  induction pending generalizing before with
  | nil => rfl
  | cons handle pending ih =>
      change execute (pending.length + 1) (.ret value pending)
        {before with memo := FlatMemoThunk.finish handle value before.memo} = _
      simpa only [List.foldl] using
        ih {before with memo := FlatMemoThunk.finish handle value before.memo}

private theorem native_complete [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (fuel : Nat) (body : SourceEqualityNativeDemand.Control Edge)
    (before after : SourceEqualityNativeDemand.State width) (value : Edge)
    (trace : SourceEqualityNativeDemand.Steps fuel body before (.code (.pure value)) after)
    (memo : FlatMemoThunk.State (Nat × Nat) (Edge × Edge) Edge) (pending : List Nat) :
    execute (fuel + pending.length + 2) (.native body pending) ⟨before, memo⟩ =
      .done value ⟨after, pending.foldl (fun current handle => FlatMemoThunk.finish handle value current) memo⟩ := by
  induction fuel generalizing body before with
  | zero =>
      cases trace
      simp only [Nat.zero_add]
      have pureStep : SourceEqualityNativeDemand.step (.code (.pure value)) after = .done value after :=
        (SourceEqualityNativeDemand.step_done_iff _ _ _ _).2 ⟨rfl, rfl⟩
      change execute ((pending.length + 1) + 1) (.native (.code (.pure value)) pending) ⟨after, memo⟩ = _
      rw [execute, step, pureStep]
      exact ret_complete value pending ⟨after, memo⟩
  | succ fuel ih =>
      cases trace with
      | cons start initial next current final reached count one rest =>
          rw [show (fuel + 1) + pending.length + 2 = (fuel + pending.length + 2) + 1 by omega,
            execute, step, one]
          exact ih next current rest

private theorem miss_prefix [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (request : Edge × Edge) (pending : List Nat) (before : Wrapper width)
    (missing : before.memo.table (request.1.entry.identity, request.2.entry.identity) = none) :
    ∃ current : Wrapper width,
      current.checked = before.checked ∧
      current.memo.table = Cache.put before.memo.table
        (request.1.entry.identity, request.2.entry.identity) before.memo.next ∧
      ∀ fuel, execute (fuel + 2) (.call request pending) before =
        execute fuel (.order before.memo.next request pending) current := by
  let published := (FlatMemoThunk.lookupOrInsert
    (request.1.entry.identity, request.2.entry.identity) request before.memo).2
  let running := FlatMemoThunk.setStatus before.memo.next .evaluating published
  let current : Wrapper width := {before with memo := running}
  have allocated := FlatMemoThunk.lookup_miss
    (request.1.entry.identity, request.2.entry.identity) request before.memo missing
  have stored : published.cells before.memo.next = some ⟨request, .suspended⟩ := allocated.2.2
  have demanded : FlatMemoThunk.demand before.memo.next published = (.evaluate request, running) := by
    simp only [FlatMemoThunk.demand, stored, running]
  have looked : step (.call request pending) before =
      .yielded (.demand before.memo.next pending) {before with memo := published} := by
    change SourceCurrentSameSymbolEdgeControl.Outcome.yielded
      (.demand (FlatMemoThunk.lookupOrInsert
        (request.1.entry.identity, request.2.entry.identity) request before.memo).1 pending)
      {before with memo := published} = _
    exact congrArg (fun handle => SourceCurrentSameSymbolEdgeControl.Outcome.yielded
      (.demand handle pending) {before with memo := published}) allocated.1
  have started : step (.demand before.memo.next pending) {before with memo := published} =
      .yielded (.order before.memo.next request pending) current := by
    simp only [step, demanded, current]
  refine ⟨current, rfl, ?_, ?_⟩
  · change running.table = _
    simp only [running, FlatMemoThunk.setStatus, stored]
    simp only [published, FlatMemoThunk.lookupOrInsert, missing]
  · intro fuel
    rw [show fuel + 2 = (fuel + 1) + 1 by rfl, execute, looked, execute, started]

/-- Complete the requested absent pair from its semantic schedule and current word plan. -/
theorem both_miss_complete [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (source : InternedConstructorTemplates.State Symbol Guard) (facts : InternedNestedFacts.Facts source)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inputModel : InputMeaning (view source (guardHolds formulas solver)))
    (inputRanked : RankedInput (view source (guardHolds formulas solver)) inputModel.valid)
    (left right : Edge) (before : Wrapper width) :
    let ordered := if right.entry.identity < left.entry.identity then (right, left) else (left, right)
    let request : EdgeRequest Symbol Guard := ⟨IntersectionEmptyDomain.emptyDomain, ordered.1, ordered.2⟩
    ∀ (_memoValid : FlatMemoThunk.Valid
        (fun (pair : Edge × Edge) (key : Nat × Nat) =>
          (pair.1.entry.identity, pair.2.entry.identity) = key) (fun _ => True) before.memo)
      (_missing : before.memo.table (left.entry.identity, right.entry.identity) = none)
      (_reverseMissing : before.memo.table (right.entry.identity, left.entry.identity) = none)
      (_scope : EdgeScope source request)
      (complete : Completes (view source (guardHolds formulas solver))
        (SourceRecursiveIntersectionNative.edgeSemantic (guardHolds formulas solver) request))
      (_good : Good before.checked)
      (_contextual : SourceCurrentAllocatedNativeContextCache.Contextual
        (view source (guardHolds formulas solver)) inputModel inputRanked
        (guardHolds formulas solver) before.checked.native)
      (_semantic : SemanticReady before.checked.native.machine.heap)
      (_symbols : request.left.entry.key.symbol = request.right.entry.key.symbol)
      (_ready : EdgeReady before.checked.native.machine request)
      (_growth : Grows source before.checked.native.machine.heap)
      (_history : Extends source.nodes.issued before.checked.native.machine.heap.nodes.issued)
      (_active : SourceRecursiveIntersectionNative.ActiveAbove
        (view source (guardHolds formulas solver)) (guardHolds formulas solver)
        (requiredFuel (view source (guardHolds formulas solver))
          (SourceRecursiveIntersectionNative.edgeSemantic (guardHolds formulas solver) request) complete)
        before.checked.native)
      (_ranges : SourceCurrentAllocatedNativeRequestBounds.WordRanges (.edgeBody request .pure) before.checked),
    ∃ (fuel nativeFuel handle : Nat) (result : Edge) (after : Wrapper width),
      SourceCurrentSameSymbolEdgeControl.execute fuel (.call (left, right) []) before = .done result after ∧
      SourceCurrentAllocatedNativeContextualCompletion.Receipt
        (semanticView := view source (guardHolds formulas solver)) (model := inputModel)
        (ranked := inputRanked) (semanticHolds := guardHolds formulas solver)
        nativeFuel (.edgeBody request .pure) before.checked result after.checked
        (fun final value => EdgeResident final.heap value)
        (fun _ value => SourceCurrentAllocatedNativeContextCache.EdgeLaw
          (view source (guardHolds formulas solver)) inputModel inputRanked
          (guardHolds formulas solver) request value) ∧
      after.memo.table (left.entry.identity, right.entry.identity) = some handle ∧
      after.memo.cells handle = some ⟨(left, right), .returned result⟩ ∧
      FlatMemoThunk.Returned before.memo after.memo ∧
      (right.entry.identity < left.entry.identity →
        ∃ reversedHandle, reversedHandle ≠ handle ∧
          after.memo.table (right.entry.identity, left.entry.identity) = some reversedHandle ∧
          after.memo.cells reversedHandle = some ⟨(right, left), .returned result⟩) := by
  dsimp only
  intro memoValid missing reverseMissing scope complete good contextual semantic symbols ready growth history active ranges
  let ordered := if right.entry.identity < left.entry.identity then (right, left) else (left, right)
  let request : EdgeRequest Symbol Guard := ⟨IntersectionEmptyDomain.emptyDomain, ordered.1, ordered.2⟩
  obtain ⟨nativeFuel, value, nativeAfter, receipt⟩ :=
    SourceCurrentAllocatedNativeContextualCompletion.edge_complete source facts formulas solver inputModel inputRanked
      request scope complete before.checked good contextual semantic symbols ready growth history active ranges
  obtain ⟨current, checked, table, prefix⟩ := miss_prefix (left, right) [] before missing
  have completed : ∃ fuel after, execute fuel (.call (left, right) []) before = .done value after ∧
      after.checked = nativeAfter := by
    by_cases reversed : right.entry.identity < left.entry.identity
    · have different : (right.entry.identity, left.entry.identity) ≠
          (left.entry.identity, right.entry.identity) := by
        intro same
        have identities := congrArg Prod.fst same
        omega
      have missingReverse : current.memo.table (right.entry.identity, left.entry.identity) = none := by
        rw [table, Cache.put, ite_eq_right different]
        exact reverseMissing
      obtain ⟨next, nextChecked, _, nextPrefix⟩ :=
        miss_prefix (right, left) [before.memo.next] current missingReverse
      have forward : ¬ left.entry.identity < right.entry.identity := by omega
      have orderStep : step (.order before.memo.next (left, right) []) current =
          .yielded (.call (right, left) [before.memo.next]) current := by
        simp only [step, reversed, ↓reduceIte]
      have nextStep : step (.order current.memo.next (right, left) [before.memo.next]) next =
          .yielded (.native (.edgeBody request .pure) [current.memo.next, before.memo.next]) next := by
        simp only [step, request, ordered, forward, reversed, ↓reduceIte]
      have nativeTrace : SourceEqualityNativeDemand.Steps nativeFuel (.edgeBody request .pure)
          next.checked (.code (.pure value)) nativeAfter := by
        rw [nextChecked, checked]
        exact receipt.trace.steps
      let after : Wrapper width := ⟨nativeAfter,
        [current.memo.next, before.memo.next].foldl (fun memo handle => FlatMemoThunk.finish handle value memo) next.memo⟩
      have nativeRun : execute (nativeFuel + 4)
          (.native (.edgeBody request .pure) [current.memo.next, before.memo.next]) next = .done value after := by
        exact native_complete nativeFuel _ next.checked nativeAfter value nativeTrace next.memo _
      refine ⟨nativeFuel + 10, after, ?_, rfl⟩
      rw [show nativeFuel + 10 = (nativeFuel + 8) + 2 by omega, prefix (nativeFuel + 8)]
      rw [execute, orderStep]
      rw [show nativeFuel + 7 = (nativeFuel + 5) + 2 by omega, nextPrefix (nativeFuel + 5)]
      rw [execute, nextStep]
      exact nativeRun
    · have orderStep : step (.order before.memo.next (left, right) []) current =
          .yielded (.native (.edgeBody request .pure) [before.memo.next]) current := by
        simp only [step, request, ordered, reversed, ↓reduceIte]
      have nativeTrace : SourceEqualityNativeDemand.Steps nativeFuel (.edgeBody request .pure)
          current.checked (.code (.pure value)) nativeAfter := by
        rw [checked]
        exact receipt.trace.steps
      let after : Wrapper width := ⟨nativeAfter,
        [before.memo.next].foldl (fun memo handle => FlatMemoThunk.finish handle value memo) current.memo⟩
      have nativeRun : execute (nativeFuel + 3) (.native (.edgeBody request .pure) [before.memo.next]) current =
          .done value after := by
        exact native_complete nativeFuel _ current.checked nativeAfter value nativeTrace current.memo _
      refine ⟨nativeFuel + 6, after, ?_, rfl⟩
      rw [show nativeFuel + 6 = (nativeFuel + 4) + 2 by omega, prefix (nativeFuel + 4)]
      rw [execute, orderStep]
      exact nativeRun
  obtain ⟨fuel, after, done, sameChecked⟩ := completed
  obtain ⟨_, handle, _, stored, cell, retained, reversed⟩ :=
    SourceCurrentSameSymbolEdgeControl.miss_readback fuel left right value before after
      memoValid missing reverseMissing done
  refine ⟨fuel, nativeFuel, handle, value, after, done, ?_, stored, cell, retained, reversed⟩
  rw [sameChecked]
  exact receipt

end MicroCFTA.SourceCurrentSameSymbolEdgeForwardCompletion
