import MicroCFTA.SourcePruningEnumerationSharedPreparedRecursive
import MicroCFTA.EnumerationCompressionFrame

/-!
# The raw bucket removed by an actual shared parked step

The actual parked prefix supplies its read, clear, cache repair, and restart.
The receipt retains the original canonical slot and the complete raw bucket.
Path compression retains the class of each indexed raw target.
The shared prepared worker restarts directly with the same native endpoint.
This receipt does not recover an earlier entry or a finite assignment.
-/
namespace MicroCFTA.SourcePruningEnumerationSharedPreparedRecursive
open EnumerationState EnumerationCorrectness EnumerationSchedule EnumerationCompressionFrame
open InternedConstructorTemplates SourcePruningEnumerationNodes
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Core" => EnumerationState.State Symbol Constraint
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Queries" => SourceEndpointMemo.Memos
local notation "Metadata" => SourcePruningRecordTypes.Metadata

set_option autoImplicit false
attribute [local instance] SourcePruningEnumerationRecursion.recursionMonadList

private theorem true_check_origin
    (heap : InternedConstructorTemplates.State Symbol Constraint)
    (fuel uv handle : Nat) (bucket : List Suspended) (before after : Core)
    (total : UnionFind.Total before.representatives)
    (observed : Success (SourcePruningEnumerationRecursion.checkRepeated
      heap fuel uv handle bucket) before true after) :
    ∃ (value : Node) (root : Nat) (resolved : Core),
      lookupNode heap handle = some value ∧
      MergedOrdinaryHeight.recursiveBoundary value = true ∧
      Success (representative fuel uv) before root resolved ∧
      Frame before resolved ∧
      recursionKey handle bucket ∈ resolved.recursionAncestry root ∧
      Success (setValue root (.unenumerated (some handle) [])) resolved () after := by
  cases decoded : lookupNode heap handle with
  | none =>
      have impossible : Success (failure .unresolvedReference) before true after := by
        simpa only [SourcePruningEnumerationRecursion.checkRepeated, decoded] using observed
      exact (success_failure .unresolvedReference before after true impossible).elim
  | some value =>
      by_cases boundary : MergedOrdinaryHeight.recursiveBoundary value = true
      · simp only [SourcePruningEnumerationRecursion.checkRepeated, decoded, boundary, ↓reduceIte] at observed
        obtain ⟨root, resolved, resolution, continued⟩ := (success_bind _ _ _ _ _).mp observed
        have frame := representative_frame fuel uv root before resolved total resolution
        obtain ⟨current, currentState, reading, continued⟩ := (success_bind _ _ _ _ _).mp continued
        obtain ⟨currentSame, stateSame⟩ := (EnumerationDriver.get_success resolved currentState current).mp reading
        subst current currentState
        by_cases seen : recursionKey handle bucket ∈ resolved.recursionAncestry root
        · simp only [seen, ↓reduceIte] at continued
          obtain ⟨token, cleared, written, returned⟩ := (success_bind _ _ _ _ _).mp continued
          cases token
          obtain ⟨_same, afterSame⟩ := (success_pure true true cleared after).mp returned
          subst after
          exact ⟨value, root, resolved, rfl, boundary, resolution, frame, seen, written⟩
        · have impossible : Success (pure false) resolved true after := by
            simpa only [seen, ↓reduceIte] using continued
          obtain ⟨impossible, _same⟩ := (success_pure false true resolved after).mp impossible
          cases impossible
      · have impossible : Success (pure false) before true after := by
          simpa only [SourcePruningEnumerationRecursion.checkRepeated, decoded, boundary,
            Bool.false_eq_true, ↓reduceIte] using observed
        obtain ⟨impossible, _same⟩ := (success_pure false true before after).mp impossible
        cases impossible

/-- The actual parked step identifies its removed raw bucket and its direct shared restart. -/
theorem parked_singleton_removed_bucket_receipt
    {Typing Key : Type} {width : Nat}
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Constraint))
    (stop : Option (Metadata Typing → Nat → Bool))
    (order : Metadata Typing → List Nat → Option Nat) (workFuel depth uv : Nat)
    (metadata updated : Metadata Typing) (caller : Caller width) (queries : Queries)
    (before parked : Cached) (checked core : Core) (next : Option Next)
    (total : UnionFind.Total before.core.representatives)
    (actual : SourcePruningEnumerationSelectedStep.runPrefix holeKey fits admits graph templates stop order
      metadata workFuel workFuel workFuel workFuel workFuel workFuel uv caller before queries =
      .parked checked (some parked) (some [.ok ((updated, next), core)])) :
    ∃ (handle : Nat) (bucket : List Suspended) (readAfter : Core)
        (value : Node) (root size : Nat) (resolved : Core),
      ExceptT.run (getValue workFuel uv before.core) =
        [.ok (.unenumerated (some handle) bucket, readAfter)] ∧
      before.core.values[root]? = some (.unenumerated (some handle) bucket) ∧
      UnionFind.Reaches before.core.representatives uv root size ∧
      Frame before.core readAfter ∧
      lookupNode caller.checked.native.machine.heap handle = some value ∧
      MergedOrdinaryHeight.recursiveBoundary value = true ∧
      ExceptT.run (SourcePruningEnumerationRecursion.checkRepeated
        caller.checked.native.machine.heap workFuel uv handle bucket readAfter) =
          [.ok (true, checked)] ∧
      Success (representative workFuel uv) readAfter root resolved ∧
      Frame readAfter resolved ∧
      recursionKey handle bucket ∈ before.core.recursionAncestry root ∧
      resolved.values[root]? = some (.unenumerated (some handle) bucket) ∧
      Success (setValue root (.unenumerated (some handle) [])) resolved () checked ∧
      checked = {resolved with values := resolved.values.set root (.unenumerated (some handle) [])} ∧
      parked.core = checked ∧
      SourcePruningEnumerationParkedRestart.adapt caller.checked.native.machine.heap
        workFuel uv handle bucket before checked = some parked ∧
      ExceptT.run (SourcePruningEnumerationRestart.run stop order metadata parked checked) =
        [.ok ((updated, next), core)] ∧
      updated = metadata ∧ core = checked ∧
      next = SourcePruningEnumerationRestart.decision stop order metadata parked ∧
      SourcePruningEnumerationRestart.decision stop order metadata parked ≠ some .stuck ∧
      (∀ (occurrence : Nat) (sc : Suspended), bucket[occurrence]? = some sc →
        ∀ other, UnionFind.SameClass checked.representatives sc.var other ↔
          UnionFind.SameClass before.core.representatives sc.var other) ∧
      resume holeKey fits admits graph templates checkEmpty edgesOf stop order workFuel (depth + 1)
        metadata caller queries before (some (.expand uv)) =
        resume holeKey fits admits graph templates checkEmpty edgesOf stop order workFuel depth
          updated caller queries (EnumerationExpandableIndex.frame core parked) next := by
  have operations : ∃ (handle : Nat) (bucket : List Suspended) (readAfter : Core),
      ExceptT.run (getValue workFuel uv before.core) =
        [.ok (.unenumerated (some handle) bucket, readAfter)] ∧
      ExceptT.run (SourcePruningEnumerationRecursion.checkRepeated
        caller.checked.native.machine.heap workFuel uv handle bucket readAfter) =
          [.ok (true, checked)] ∧
      SourcePruningEnumerationParkedRestart.adapt caller.checked.native.machine.heap
        workFuel uv handle bucket before checked = some parked ∧
      ExceptT.run (SourcePruningEnumerationRestart.run stop order metadata parked checked) =
        [.ok ((updated, next), core)] := by
    have observed := actual
    unfold SourcePruningEnumerationSelectedStep.runPrefix
      SourcePruningEnumerationSelectedStep.runPrefixWithNarrow at observed
    dsimp only at observed
    split at observed
    · rename_i handle bucket readAfter reading
      split at observed
      · rename_i actualChecked checking
        obtain ⟨checkedSame, adapted, rawSame⟩ :=
          SourcePruningEnumerationSelectedStep.Result.parked.inj observed
        subst actualChecked
        rw [adapted, Option.map_some] at rawSame
        exact ⟨handle, bucket, readAfter, reading, checking, adapted, Option.some.inj rawSame⟩
      all_goals repeat first | (solve | cases observed) | split at observed
    all_goals repeat first | (solve | cases observed) | split at observed
  obtain ⟨handle, bucket, readAfter, reading, checking, adapted, restarted⟩ := operations
  have readSuccess : Success (getValue workFuel uv) before.core
      (.unenumerated (some handle) bucket) readAfter := by
    rw [Success, reading]
    exact List.mem_singleton_self _
  obtain ⟨readFrame, readRoot, size, originalPath, readPath, originalStored⟩ :=
    getValue_frame workFuel uv before.core readAfter _ total readSuccess
  have checkSuccess : Success (SourcePruningEnumerationRecursion.checkRepeated
      caller.checked.native.machine.heap workFuel uv handle bucket) readAfter true checked := by
    rw [Success, checking]
    exact List.mem_singleton_self _
  obtain ⟨value, root, resolved, decoded, boundary, resolution, resolvedFrame, seen, written⟩ :=
    true_check_origin caller.checked.native.machine.heap workFuel uv handle bucket readAfter checked
      (readFrame.total total) checkSuccess
  obtain ⟨found, foundRoot, rootSame, _resolvedSame⟩ :=
    (representative_success workFuel uv readAfter resolved root).mp resolution
  have resolvedPath : UnionFind.Reaches readAfter.representatives uv root found.size := by
    rw [rootSame]
    exact (UnionFind.findRoot_correct workFuel readAfter.representatives uv found foundRoot).1
  have sameRoot : readRoot = root := (UnionFind.reaches_unique readPath resolvedPath).1
  subst readRoot
  have resolvedStored : resolved.values[root]? = some (.unenumerated (some handle) bucket) := by
    simpa only [resolvedFrame.values, readFrame.values] using originalStored
  have originalKey : recursionKey handle bucket ∈ before.core.recursionAncestry root := by
    simpa only [resolvedFrame.recursionAncestry, readFrame.recursionAncestry] using seen
  have writtenShape := (EnumerationDriver.modify_success _ resolved checked).mp written
  have parkedCore := SourcePruningEnumerationParkedRestart.adapt_core
    caller.checked.native.machine.heap workFuel uv handle bucket before parked checked adapted
  have notStuck : SourcePruningEnumerationRestart.decision stop order metadata parked ≠ some .stuck := by
    intro stuck
    simp only [SourcePruningEnumerationRestart.run, stuck, ↓reduceIte] at restarted
    cases restarted
  have restartSame : (metadata, SourcePruningEnumerationRestart.decision stop order metadata parked) =
      (updated, next) ∧ checked = core := by
    have exactRows : [Except.ok (ε := EnumerationState.Error)
        ((metadata, SourcePruningEnumerationRestart.decision stop order metadata parked), checked)] =
        [Except.ok (ε := EnumerationState.Error) ((updated, next), core)] := by
      simpa only [SourcePruningEnumerationRestart.run, ite_eq_right notStuck, ExceptT.run] using restarted
    exact Prod.mk.inj (Except.ok.inj (List.cons.inj exactRows).1)
  have combinedFrame := readFrame.trans resolvedFrame
  have aliases : ∀ left right, UnionFind.SameClass checked.representatives left right ↔
      UnionFind.SameClass before.core.representatives left right := by
    intro left right
    rw [writtenShape]
    constructor
    · rintro ⟨representative, weight, first, second⟩
      exact ⟨representative, weight, (combinedFrame.reaches left representative weight).mp first,
        (combinedFrame.reaches right representative weight).mp second⟩
    · rintro ⟨representative, weight, first, second⟩
      exact ⟨representative, weight, (combinedFrame.reaches left representative weight).mpr first,
        (combinedFrame.reaches right representative weight).mpr second⟩
  refine ⟨handle, bucket, readAfter, value, root, size, resolved, reading, originalStored,
    originalPath, readFrame, decoded, boundary, checking, resolution, resolvedFrame, originalKey,
    resolvedStored, written, writtenShape, parkedCore, adapted, restarted,
    (congrArg Prod.fst restartSame.1).symm, restartSame.2.symm,
    (congrArg Prod.snd restartSame.1).symm, notStuck, ?_, ?_⟩
  · intro _occurrence sc _stored other
    exact aliases sc.var other
  · simp only [resume, actual]

end MicroCFTA.SourcePruningEnumerationSharedPreparedRecursive
