import MicroCFTA.EnumerationFlatTerminalPrefix
import MicroCFTA.EnumerationFlatNativeIncomingCache
import MicroCFTA.SourcePruningEnumerationCachedTerminalAdapter

namespace MicroCFTA.EnumerationFlatNativeTerminal
open EnumerationState EnumerationCorrectness EnumerationSchedule
open EnumerationCompleteness EnumerationDependencies
open InternedConstructorTemplates InternedProbeProvenance
open SourcePruningEnumerationNodes SourcePruningEnumerationObservation
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedPartialInvariant (Context Post)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => InternedConstructorTemplates.Value Symbol Constraint
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Queries" => SourceEndpointMemo.Memos
local notation "Raw" => List (Except EnumerationState.Error
  (Unit × EnumerationFlatState.State Symbol Constraint))
local notation "PrefixRaw" => List (Except EnumerationState.Error
  ((List Nat × Nat × EnumerationWaitingIndex.Waiting) × EnumerationFlatState.State Symbol Constraint))
local notation "FoldRaw" => Raw
local notation "TerminalRaw" => List (Except EnumerationState.Error
  (Fragments.Fragment Symbol × EnumerationFlatState.State Symbol Constraint))
variable {width : Nat}
local notation "NativeOutcome" => SourceEqualityNativeDemand.Outcome width Node
local notation "WorkerOutcome" => SourceCurrentAllocatedConjunctionWorker.Outcome width
attribute [local instance] SourcePruningEnumerationTerminal.terminalMonadList

/-- Retain incoming errors and map each actual successful row to its terminal hole. -/
def wrapIncoming (winner : Nat) (moved : EnumerationWaitingIndex.Waiting)
    (observed : ((Except (NativeOutcome ⊕ WorkerOutcome) (Option Raw)) ×
      Caller width × Queries × EnumerationFlatState.State Symbol Constraint) ×
      Option (EnumerationFlatCached.Cached Symbol Constraint)) :
    ((Except (PrefixRaw ⊕ ((NativeOutcome ⊕ WorkerOutcome) ⊕ FoldRaw)) (Option TerminalRaw)) ×
      Caller width × Queries × EnumerationFlatState.State Symbol Constraint × EnumerationWaitingIndex.Waiting) ×
      Option (EnumerationFlatCached.Cached Symbol Constraint) :=
match observed with
| ((incomingResult, afterCaller, savedQueries, read), incomingCache) =>
  match incomingResult with
  | .error incomingFault =>
      ((.error (.inr (.inl incomingFault)), afterCaller, savedQueries, read, moved), none)
  | .ok none => ((.ok none, afterCaller, savedQueries, read, moved), none)
  | .ok (some incomingRaw) =>
      ((.ok (some (incomingRaw.map fun row => match row with
        | .error error => .error error
        | .ok result => .ok (.hole winner, result.2))),
        afterCaller, savedQueries, read, moved), incomingCache)

/-- Run the actual prefix, cached fold and incoming merge with independent cache recovery. -/
noncomputable def run
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]
    (checkEmpty : Bool) (nativeFuel p h : Nat)
    (first : EnumerationState.Suspended) (rest : List EnumerationState.Suspended)
    (beforeCaller : Caller width) (before : EnumerationFlatCached.Cached Symbol Constraint)
    (incoming : Node) (incomingScs : List EnumerationState.Suspended) (queries : Queries) :
    ((Except (PrefixRaw ⊕ ((NativeOutcome ⊕ WorkerOutcome) ⊕ FoldRaw)) (Option TerminalRaw)) ×
      Caller width × Queries × EnumerationFlatState.State Symbol Constraint × EnumerationWaitingIndex.Waiting) ×
      Option (EnumerationFlatCached.Cached Symbol Constraint) :=
  if incoming = .empty then
    ((.ok (some []), beforeCaller, queries, before.core, before.waiting), some before)
  else
    match ExceptT.run (EnumerationFlatTerminalPrefix.run
        first rest before.waiting before.core) with
    | [.ok ((recorded, winner, moved), joined)] =>
      match EnumerationFlatNativeCachedFold.run checkEmpty nativeFuel p h recorded
          beforeCaller ⟨joined, before.expandable, moved⟩ winner queries with
      | ((foldResult, foldCaller, foldQueries, foldOuter), foldCache) =>
        match foldResult with
        | .error foldFault =>
            ((.error (.inr (.inl foldFault)), foldCaller, foldQueries, foldOuter, moved), none)
        | .ok none => ((.ok none, foldCaller, foldQueries, foldOuter, moved), none)
        | .ok (some foldRaw) =>
          match foldRaw with
          | [] => ((.ok (some []), foldCaller, foldQueries, foldOuter, moved), foldCache)
          | [.ok ((), folded)] =>
            let incomingObserved : ((Except (NativeOutcome ⊕ WorkerOutcome) (Option Raw)) ×
                Caller width × Queries × EnumerationFlatState.State Symbol Constraint) ×
                Option (EnumerationFlatCached.Cached Symbol Constraint) :=
              match foldCache with
              | none =>
                  (EnumerationFlatNativeIncoming.run checkEmpty nativeFuel p h
                    foldCaller folded winner incoming incomingScs foldQueries, none)
              | some recovered =>
                  EnumerationFlatNativeIncomingCache.run checkEmpty nativeFuel p h
                    foldCaller (EnumerationFlatCached.frame folded recovered)
                    winner incoming incomingScs foldQueries
            wrapIncoming winner moved incomingObserved
          | stoppedRaw =>
              ((.error (.inr (.inr stoppedRaw)), foldCaller, foldQueries, foldOuter, moved), none)
    | prefixRaw => ((.error (.inl prefixRaw), beforeCaller, queries, before.core, before.waiting), none)


local notation "OldPrefixRaw" => List (Except EnumerationState.Error
  ((List Nat × Nat × EnumerationWaitingIndex.Waiting) × EnumerationState.State Symbol Constraint))
local notation "OldFoldRaw" => List (Except EnumerationState.Error
  (Unit × EnumerationState.State Symbol Constraint))
local notation "OldTerminalRaw" => List (Except EnumerationState.Error
  (Fragments.Fragment Symbol × EnumerationState.State Symbol Constraint))

/-- Preserve native effects, moved counts, raw diagnostics and optional cache recovery. -/
def ResultRelated
    (flat : ((Except (PrefixRaw ⊕ ((NativeOutcome ⊕ WorkerOutcome) ⊕ FoldRaw)) (Option TerminalRaw)) ×
      Caller width × Queries × EnumerationFlatState.State Symbol Constraint × EnumerationWaitingIndex.Waiting) ×
      Option (EnumerationFlatCached.Cached Symbol Constraint))
    (earlier : ((Except (OldPrefixRaw ⊕ ((NativeOutcome ⊕ WorkerOutcome) ⊕ OldFoldRaw)) (Option OldTerminalRaw)) ×
      Caller width × Queries × EnumerationState.State Symbol Constraint × EnumerationWaitingIndex.Waiting) ×
      Option (EnumerationExpandableIndex.Cached Symbol Constraint)) : Prop :=
  (flat.1.2.1 = earlier.1.2.1 ∧ flat.1.2.2.1 = earlier.1.2.2.1 ∧
    EnumerationFlatState.Related flat.1.2.2.2.1 earlier.1.2.2.2.1 ∧
    flat.1.2.2.2.2 = earlier.1.2.2.2.2 ∧
    match flat.1.1, earlier.1.1 with
    | .error (.inl first), .error (.inl second) =>
        EnumerationResultRelation.Results EnumerationFlatState.Related first second
    | .error (.inr (.inl first)), .error (.inr (.inl second)) => first = second
    | .error (.inr (.inr first)), .error (.inr (.inr second)) =>
        EnumerationResultRelation.Results EnumerationFlatState.Related first second
    | .ok none, .ok none => True
    | .ok (some first), .ok (some second) =>
        EnumerationResultRelation.Results EnumerationFlatState.Related first second
    | _, _ => False) ∧
    EnumerationFlatNativeIndex.WritesRelated flat.2 earlier.2

/-- Mapping incoming successes retains their order, errors and complete returned cores. -/
theorem wrapIncoming_related
    (winner : Nat) (moved : EnumerationWaitingIndex.Waiting)
    (step : EnumerationFlatNativeCachedFold.ResultRelated left right) :
    ResultRelated (wrapIncoming winner moved left)
      (match right with
      | ((incomingResult, afterCaller, savedQueries, read), incomingCache) =>
        match incomingResult with
        | .error incomingFault =>
            ((.error (.inr (.inl incomingFault)), afterCaller, savedQueries, read, moved), none)
        | .ok none => ((.ok none, afterCaller, savedQueries, read, moved), none)
        | .ok (some incomingRaw) =>
            ((.ok (some (incomingRaw.map fun row => match row with
              | .error error => .error error
              | .ok result => .ok (.hole winner, result.2))),
              afterCaller, savedQueries, read, moved), incomingCache)) := by
  obtain ⟨⟨leftResult, reachedCaller, savedQueries, readFlat⟩, leftCache⟩ := left
  obtain ⟨⟨rightResult, oldCaller, oldQueries, readEarlier⟩, rightCache⟩ := right
  obtain ⟨⟨callerSame, queriesSame, reads, rows⟩, caches⟩ := step
  dsimp only at callerSame queriesSame
  subst oldCaller oldQueries
  cases leftResult with
  | error first =>
    cases rightResult with
    | error second => exact ⟨⟨rfl, rfl, reads, rfl, rows⟩, trivial⟩
    | ok value => cases rows
  | ok leftValue =>
    cases rightResult with
    | error fault => cases leftValue <;> cases rows
    | ok rightValue =>
      cases leftValue with
      | none =>
        cases rightValue with
        | none => exact ⟨⟨rfl, rfl, reads, rfl, trivial⟩, trivial⟩
        | some raw => cases rows
      | some leftRows =>
        cases rightValue with
        | none => cases rows
        | some rightRows =>
          refine ⟨⟨rfl, rfl, reads, rfl, ?_⟩, caches⟩
          induction rows with
          | nil => exact .nil
          | cons head tail ih =>
            cases head with
            | error error => exact .cons (.error error) ih
            | ok value states => exact .cons (.ok (.hole winner) states) ih

/-- A stable actual prefix supplies sufficient old read/count bounds for every fixed native run. -/
theorem run_stable
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]
    (related : EnumerationFlatCached.Related flat earlier)
    (first : Suspended) (rest : List Suspended)
    (r : Nat) (recorded : List Nat) (winner : Nat) (moved : EnumerationWaitingIndex.Waiting)
    (joined : EnumerationState.State Symbol Constraint)
    (prefix : ∀ extra, ExceptT.run (SourcePruningEnumerationTerminalPrefix.run
      (r + extra) first rest earlier.waiting earlier.core) = [.ok ((recorded, winner, moved), joined)])
    (checkEmpty : Bool) (nativeFuel p h : Nat) (beforeCaller : Caller width)
    (incoming : Node) (incomingScs : List Suspended) (queries : Queries) :
    ∃ extraFuel indexFuel, ∀ extraRepresentative extraIndex,
      ResultRelated (run checkEmpty nativeFuel p h first rest beforeCaller flat incoming incomingScs queries)
        (SourcePruningEnumerationCachedTerminalAdapter.run checkEmpty
          (r + extraFuel + extraRepresentative) nativeFuel p h (indexFuel + extraIndex)
          first rest beforeCaller earlier incoming incomingScs queries) := by
  by_cases empty : incoming = .empty
  · refine ⟨0, 0, fun _ _ => ?_⟩
    simp only [run, SourcePruningEnumerationCachedTerminalAdapter.run, ite_eq_left empty]
    exact ⟨⟨rfl, rfl, related.core, related.waiting, .nil⟩, related⟩
  have success : Success (SourcePruningEnumerationTerminalPrefix.run r first rest earlier.waiting)
      earlier.core (recorded, winner, moved) joined := by
    simp only [Success, show ExceptT.run (SourcePruningEnumerationTerminalPrefix.run
      r first rest earlier.waiting earlier.core) = [.ok ((recorded, winner, moved), joined)] from by
        simpa only [Nat.add_zero] using prefix 0, List.mem_singleton]
  obtain ⟨joinedFlat, flatPrefix, joinedRelated⟩ :=
    EnumerationFlatTerminalPrefix.run_replays r first rest earlier.waiting
      flat.core earlier.core _ joined related.core success
  have flatPrefix' : ExceptT.run (EnumerationFlatTerminalPrefix.run
      first rest flat.waiting flat.core) = [.ok ((recorded, winner, moved), joinedFlat)] := by
    rw [related.waiting]
    exact flatPrefix
  let joinedCache : EnumerationFlatCached.Cached Symbol Constraint :=
    ⟨joinedFlat, flat.expandable, moved⟩
  let oldJoined : EnumerationExpandableIndex.Cached Symbol Constraint :=
    ⟨joined, earlier.expandable, moved⟩
  have step := EnumerationFlatNativeCachedFold.run_related
    (show EnumerationFlatCached.Related joinedCache oldJoined from
      ⟨joinedRelated, related.expandable, rfl⟩)
    checkEmpty nativeFuel p h recorded beforeCaller winner queries
  generalize flatFold : EnumerationFlatNativeCachedFold.run checkEmpty nativeFuel p h
    recorded beforeCaller joinedCache winner queries = left at step ⊢
  generalize oldFold : SourcePruningEnumerationCachedFold.run checkEmpty nativeFuel p h
    recorded beforeCaller oldJoined winner queries = right at step ⊢
  obtain ⟨⟨leftResult, reachedCaller, savedQueries, outerFlat⟩, leftCache⟩ := left
  obtain ⟨⟨rightResult, oldCaller, oldQueries, outerEarlier⟩, rightCache⟩ := right
  obtain ⟨⟨callerSame, queriesSame, outers, rows⟩, caches⟩ := step
  dsimp only at callerSame queriesSame
  subst oldCaller oldQueries
  have unfoldRun : ∀ extraFuel indexFuel extraRepresentative extraIndex,
      ExceptT.run (SourcePruningEnumerationTerminalPrefix.run
        (r + extraFuel + extraRepresentative) first rest earlier.waiting earlier.core) =
          [.ok ((recorded, winner, moved), joined)] := by
    intro extraFuel _ extraRepresentative _
    simpa only [Nat.add_assoc] using prefix (extraFuel + extraRepresentative)
  simp only [run, SourcePruningEnumerationCachedTerminalAdapter.run, ite_eq_right empty,
    flatPrefix', unfoldRun, ← joinedCache, ← oldJoined, flatFold, oldFold]
  cases leftResult with
  | error firstFault =>
    cases rightResult with
    | error secondFault => exact ⟨0, 0, fun _ _ => ⟨⟨rfl, rfl, outers, rfl, rows⟩, trivial⟩⟩
    | ok value => cases rows
  | ok leftValue =>
    cases rightResult with
    | error fault => cases leftValue <;> cases rows
    | ok rightValue =>
      cases leftValue with
      | none =>
        cases rightValue with
        | none => exact ⟨0, 0, fun _ _ => ⟨⟨rfl, rfl, outers, rfl, trivial⟩, trivial⟩⟩
        | some raw => cases rows
      | some leftRows =>
        cases rightValue with
        | none => cases rows
        | some rightRows =>
          cases rows with
          | nil => exact ⟨0, 0, fun _ _ => ⟨⟨rfl, rfl, outers, rfl, .nil⟩, caches⟩⟩
          | cons head tail =>
            cases head with
            | error error =>
              exact ⟨0, 0, fun _ _ => ⟨⟨rfl, rfl, outers, rfl, .cons (.error error) tail⟩, trivial⟩⟩
            | ok value states =>
              cases value
              cases tail with
              | cons next remaining =>
                exact ⟨0, 0, fun _ _ => ⟨⟨rfl, rfl, outers, rfl, .cons (.ok () states) (.cons next remaining)⟩, trivial⟩⟩
              | nil =>
                cases leftCache with
                | none =>
                  cases rightCache with
                  | some recovered => cases caches
                  | none =>
                    obtain ⟨incomingFuel, stable⟩ := EnumerationFlatNativeIncoming.run_stable states winner
                    refine ⟨incomingFuel, 0, ?_⟩
                    intro extraRepresentative extraIndex
                    apply wrapIncoming_related winner moved
                    refine ⟨?_, trivial⟩
                    simpa only [Nat.add_assoc, Nat.add_comm r incomingFuel,
                      Nat.add_left_comm r incomingFuel] using
                      stable (r + extraRepresentative) checkEmpty nativeFuel p h reachedCaller incoming incomingScs savedQueries
                | some recovered =>
                  cases rightCache with
                  | none => cases caches
                  | some oldRecovered =>
                    obtain ⟨incomingFuel, indexFuel, stable⟩ :=
                      EnumerationFlatNativeIncomingCache.run_stable
                        (EnumerationFlatCached.frame_related caches states)
                        checkEmpty nativeFuel p h reachedCaller winner incoming incomingScs savedQueries
                    refine ⟨incomingFuel, indexFuel, ?_⟩
                    intro extraRepresentative extraIndex
                    apply wrapIncoming_related winner moved
                    simpa only [Nat.add_assoc, Nat.add_comm r incomingFuel,
                      Nat.add_left_comm r incomingFuel] using stable (r + extraRepresentative) extraIndex

end MicroCFTA.EnumerationFlatNativeTerminal
