import MicroCFTA.SourcePruningEnumerationSharedDispatch
import MicroCFTA.SourcePruningEnumerationSharedIncomingNode
import MicroCFTA.SourcePruningEnumerationTerminalPrefix
import MicroCFTA.SourcePruningEnumerationCachedAdapter
import MicroCFTA.SourcePruningEnumerationIncomingCacheAdapter

/-!
# Cached terminal execution through the shared conjunction backend

Both fold paths use the shared dispatcher. Both incoming paths use the
shared incoming worker. The optional cache contains only derived index
metadata. Erasure preserves every raw result, full shared fault snapshot,
reached caller, query memo, outer state and moved waiting state.

The pure cache adapters and terminal prefix are unchanged. This module
proves exact bounded execution contracts. It does not derive the native
capacity needed to complete every warm terminal request.
-/
namespace MicroCFTA.SourcePruningEnumerationSharedCachedTerminal
open EnumerationState EnumerationCorrectness EnumerationSchedule
open InternedConstructorTemplates InternedProbeProvenance
open SourcePruningEnumerationNodes SourcePruningEnumerationObservation
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedPartialInvariant (Context Post)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => InternedConstructorTemplates.Value Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Queries" => SourceEndpointMemo.Memos
local notation "Raw" => List (Except EnumerationState.Error
  (Unit × EnumerationState.State Symbol Constraint))
local notation "PrefixRaw" => List (Except EnumerationState.Error
  ((List Nat × Nat × EnumerationWaitingIndex.Waiting) × EnumerationState.State Symbol Constraint))
local notation "FoldRaw" => Raw
local notation "TerminalRaw" => List (Except EnumerationState.Error
  (Fragments.Fragment Symbol × EnumerationState.State Symbol Constraint))
variable {width : Nat}
local notation "NativeOutcome" => SourceEqualityNativeDemand.Outcome width Node
local notation "WorkerOutcome" => SourcePruningEnumerationSharedEnabledEmpty.Outcome width

local instance sharedTerminalMonadList : Monad List where
  pure value := [value]
  bind values continuation := values.flatMap continuation

/-- Run the recorded source slots in order and retain each reached state. -/
noncomputable def rawFold
    [DecidableEq Symbol] [DecidableEq (InternedConstructorTemplates.EdgeKey Symbol Constraint)] [DecidableEq Node]
    (checkEmpty : Bool) (nativeFuel p h : Nat) (sources : List Nat)
    (beforeCaller : Caller width) (before : EnumerationState.State Symbol Constraint)
    (target : Nat) (queries : Queries) :
    (Except (SourceEqualityNativeDemand.Outcome width Node ⊕
      SourcePruningEnumerationSharedEnabledEmpty.Outcome width)
      (Option (List (Except EnumerationState.Error (Unit × EnumerationState.State Symbol Constraint))))) ×
      Caller width × Queries × EnumerationState.State Symbol Constraint :=
  match sources with
  | [] => (.ok (some [.ok ((), before)]), beforeCaller, queries, before)
  | source :: rest =>
    let observation :
      (Except (SourceEqualityNativeDemand.Outcome width Node ⊕
        SourcePruningEnumerationSharedEnabledEmpty.Outcome width)
        (Option (EnumerateM Symbol Constraint Unit))) × Caller width × Queries :=
      SourcePruningEnumerationSharedDispatch.dispatch checkEmpty nativeFuel p h beforeCaller before source target queries
    match observation with
    | (.error fault, reachedCaller, savedQueries) => (.error fault, reachedCaller, savedQueries, before)
    | (.ok none, reachedCaller, savedQueries) => (.ok none, reachedCaller, savedQueries, before)
    | (.ok (some action), reachedCaller, savedQueries) =>
        let raw : List (Except EnumerationState.Error (Unit × EnumerationState.State Symbol Constraint)) := ExceptT.run (action before)
        match raw with
        | [.ok ((), after)] => rawFold checkEmpty nativeFuel p h rest reachedCaller after target savedQueries
        | other => (.ok (some other), reachedCaller, savedQueries, before)

/-- Run dispatch and its captured action once, with a separate cache receipt. -/
noncomputable def cachedAdapter
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]
    (checkEmpty : Bool) (nativeFuel p h : Nat)
    (beforeCaller : Caller width) (before : EnumerationExpandableIndex.Cached Symbol Constraint)
    (source target : Nat) (queries : Queries) :
    (Except (SourceEqualityNativeDemand.Outcome width Node ⊕
      SourcePruningEnumerationSharedEnabledEmpty.Outcome width)
      (Option (List (Except EnumerationState.Error (Unit × EnumerationState.State Symbol Constraint))))) ×
      Caller width × Queries × Option (EnumerationExpandableIndex.Cached Symbol Constraint) :=
  match SourcePruningEnumerationSharedDispatch.dispatch checkEmpty nativeFuel p h
      beforeCaller before.core source target queries with
  | (.error fault, reachedCaller, savedQueries) =>
      (.error fault, reachedCaller, savedQueries, none)
  | (.ok none, reachedCaller, savedQueries) =>
      (.ok none, reachedCaller, savedQueries, none)
  | (.ok (some action), reachedCaller, savedQueries) =>
      let raw : List (Except EnumerationState.Error (Unit × EnumerationState.State Symbol Constraint)) :=
        ExceptT.run (action before.core)
      (.ok (some raw), reachedCaller, savedQueries,
        SourcePruningEnumerationCachedAdapter.adapt reachedCaller.checked.native.machine.heap before source target raw)

/-- Retain the full shared fold observation with a separate optional cache. -/
noncomputable def fold
    [DecidableEq Symbol] [DecidableEq (InternedConstructorTemplates.EdgeKey Symbol Constraint)] [DecidableEq Node]
    (checkEmpty : Bool) (nativeFuel p h : Nat) (sources : List Nat)
    (beforeCaller : Caller width) (before : EnumerationExpandableIndex.Cached Symbol Constraint)
    (target : Nat) (queries : Queries) :
    ((Except (SourceEqualityNativeDemand.Outcome width Node ⊕
      SourcePruningEnumerationSharedEnabledEmpty.Outcome width)
      (Option (List (Except EnumerationState.Error (Unit × EnumerationState.State Symbol Constraint))))) ×
      Caller width × Queries × EnumerationState.State Symbol Constraint) ×
      Option (EnumerationExpandableIndex.Cached Symbol Constraint) :=
  match sources with
  | [] => ((.ok (some [.ok ((), before.core)]), beforeCaller, queries, before.core), some before)
  | source :: rest =>
      match cachedAdapter checkEmpty nativeFuel p h
          beforeCaller before source target queries with
      | (.error fault, reachedCaller, savedQueries, _) =>
          ((.error fault, reachedCaller, savedQueries, before.core), none)
      | (.ok none, reachedCaller, savedQueries, _) =>
          ((.ok none, reachedCaller, savedQueries, before.core), none)
      | (.ok (some raw), reachedCaller, savedQueries, cache) =>
          match raw with
          | [.ok ((), core)] =>
              match cache with
              | none =>
                  (rawFold checkEmpty nativeFuel p h rest
                    reachedCaller core target savedQueries, none)
              | some recovered =>
                  fold checkEmpty nativeFuel p h rest reachedCaller
                    (EnumerationExpandableIndex.frame core recovered) target savedQueries
          | other => ((.ok (some other), reachedCaller, savedQueries, before.core), cache)

/-- Erasing cache data preserves every bounded shared fold observation. -/
theorem fold_erase
    [DecidableEq Symbol] [DecidableEq (InternedConstructorTemplates.EdgeKey Symbol Constraint)] [DecidableEq Node]
    (checkEmpty : Bool) (nativeFuel p h : Nat) (sources : List Nat)
    (beforeCaller : Caller width) (before : EnumerationExpandableIndex.Cached Symbol Constraint)
    (target : Nat) (queries : Queries) :
    (fold checkEmpty nativeFuel p h sources beforeCaller before target queries).1 =
      rawFold checkEmpty nativeFuel p h sources
        beforeCaller before.core target queries := by
  induction sources generalizing beforeCaller before queries with
  | nil => rfl
  | cons source rest ih =>
      cases dispatchResult : SourcePruningEnumerationSharedDispatch.dispatch checkEmpty nativeFuel p h
          beforeCaller before.core source target queries with
      | mk outcome saved =>
          rcases saved with ⟨reachedCaller, savedQueries⟩
          cases outcome with
          | error fault =>
              simp only [fold, cachedAdapter, dispatchResult,
                rawFold]
          | ok returned =>
              cases returned with
              | none =>
                  simp only [fold, cachedAdapter, dispatchResult,
                    rawFold]
              | some action =>
                  cases rawResult : ExceptT.run (action before.core) with
                  | nil =>
                      simp only [fold, cachedAdapter, dispatchResult,
                        rawResult, rawFold]
                  | cons first tail =>
                      cases first with
                      | error _rowError =>
                          simp only [fold, cachedAdapter, dispatchResult,
                            rawResult, rawFold]
                      | ok value =>
                          rcases value with ⟨valueUnit, core⟩
                          cases valueUnit
                          cases tail with
                          | nil =>
                              cases receipt : SourcePruningEnumerationCachedAdapter.adapt
                                  reachedCaller.checked.native.machine.heap before source target [.ok ((), core)] with
                              | none =>
                                  simp only [fold, cachedAdapter, dispatchResult,
                                    rawResult, receipt, rawFold]
                              | some recovered =>
                                  simp only [fold, cachedAdapter, dispatchResult,
                                    rawResult, receipt, rawFold]
                                  exact ih reachedCaller (EnumerationExpandableIndex.frame core recovered) savedQueries
                          | cons _second _remaining =>
                              simp only [fold, cachedAdapter, dispatchResult,
                                rawResult, rawFold]

/-- Retain one shared observation and attach its optional cache candidate. -/
noncomputable def incomingCacheAdapter
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]
    (checkEmpty : Bool) (representativeFuel nativeFuel p h indexFuel : Nat)
    (beforeCaller : Caller width) (before : EnumerationExpandableIndex.Cached Symbol Constraint)
    (target : Nat) (incoming : Node) (incomingScs : List EnumerationState.Suspended) (queries : Queries) :
    ((Except (SourceEqualityNativeDemand.Outcome width Node ⊕
      SourcePruningEnumerationSharedEnabledEmpty.Outcome width) (Option Raw)) ×
      Caller width × Queries × EnumerationState.State Symbol Constraint) ×
      Option (EnumerationExpandableIndex.Cached Symbol Constraint) :=
  let observed : (Except (SourceEqualityNativeDemand.Outcome width Node ⊕
      SourcePruningEnumerationSharedEnabledEmpty.Outcome width) (Option Raw)) ×
      Caller width × Queries × EnumerationState.State Symbol Constraint :=
    SourcePruningEnumerationSharedIncomingNode.run checkEmpty representativeFuel nativeFuel p h
      beforeCaller before.core target incoming incomingScs queries
  (observed, match observed with
    | (.ok (some raw), reachedCaller, _savedQueries, read) =>
        SourcePruningEnumerationIncomingCacheAdapter.adapt reachedCaller.checked.native.machine.heap indexFuel target incomingScs before read raw
    | _ => none)

/-- The first projection retains the shared action at every fixed bound. -/
theorem incoming_erase
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]
    (checkEmpty : Bool) (representativeFuel nativeFuel p h indexFuel : Nat)
    (beforeCaller : Caller width) (before : EnumerationExpandableIndex.Cached Symbol Constraint)
    (target : Nat) (incoming : Node) (incomingScs : List EnumerationState.Suspended) (queries : Queries) :
    (incomingCacheAdapter checkEmpty representativeFuel nativeFuel p h indexFuel beforeCaller before
      target incoming incomingScs queries).1 =
      SourcePruningEnumerationSharedIncomingNode.run checkEmpty representativeFuel nativeFuel p h
        beforeCaller before.core target incoming incomingScs queries := by
  rfl

/-- The attached cache retains the core in an actual successful singleton row. -/
theorem incoming_singleton_core
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]
    (checkEmpty : Bool) (representativeFuel nativeFuel p h indexFuel : Nat)
    (beforeCaller reachedCaller : Caller width)
    (before after : EnumerationExpandableIndex.Cached Symbol Constraint)
    (target : Nat) (incoming : Node) (incomingScs : List EnumerationState.Suspended)
    (queries savedQueries : Queries) (read returned : EnumerationState.State Symbol Constraint)
    (observed : incomingCacheAdapter checkEmpty representativeFuel nativeFuel p h indexFuel beforeCaller before
      target incoming incomingScs queries =
      ((.ok (some [.ok ((), returned)]), reachedCaller, savedQueries, read), some after)) :
    after.core = returned := by
  have original : SourcePruningEnumerationSharedIncomingNode.run checkEmpty representativeFuel nativeFuel p h
      beforeCaller before.core target incoming incomingScs queries =
      (.ok (some [.ok ((), returned)]), reachedCaller, savedQueries, read) := by
    rw [← incoming_erase checkEmpty representativeFuel nativeFuel p h indexFuel beforeCaller before
      target incoming incomingScs queries, observed]
  apply SourcePruningEnumerationIncomingCacheAdapter.adapt_singleton_core reachedCaller.checked.native.machine.heap indexFuel target
    incomingScs before after read returned
  simpa only [incomingCacheAdapter, original] using congrArg Prod.snd observed

/-- Run the terminal prefix, ordered fold and actual incoming merge. -/
noncomputable def raw
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]
    (checkEmpty : Bool) (representativeFuel nativeFuel p h : Nat)
    (first : EnumerationState.Suspended) (rest : List EnumerationState.Suspended)
    (waiting : EnumerationWaitingIndex.Waiting)
    (beforeCaller : Caller width) (before : EnumerationState.State Symbol Constraint)
    (incoming : Node) (incomingScs : List EnumerationState.Suspended) (queries : Queries) :
    (Except (PrefixRaw ⊕ ((NativeOutcome ⊕ WorkerOutcome) ⊕ FoldRaw)) (Option TerminalRaw)) ×
      Caller width × Queries × EnumerationState.State Symbol Constraint × EnumerationWaitingIndex.Waiting :=
  if incoming = .empty then (.ok (some []), beforeCaller, queries, before, waiting)
  else
    match ExceptT.run (SourcePruningEnumerationTerminalPrefix.run representativeFuel first rest waiting before) with
    | [.ok ((recorded, winner, moved), joined)] =>
      match rawFold checkEmpty nativeFuel p h recorded beforeCaller joined winner queries with
      | (foldResult, foldCaller, foldQueries, foldOuter) =>
        match foldResult with
        | .error foldFault => (.error (.inr (.inl foldFault)), foldCaller, foldQueries, foldOuter, moved)
        | .ok none => (.ok none, foldCaller, foldQueries, foldOuter, moved)
        | .ok (some foldRaw) =>
          match foldRaw with
          | [] => (.ok (some []), foldCaller, foldQueries, foldOuter, moved)
          | [.ok ((), folded)] =>
            match SourcePruningEnumerationSharedIncomingNode.run checkEmpty representativeFuel nativeFuel p h
                foldCaller folded winner incoming incomingScs foldQueries with
            | (incomingResult, afterCaller, savedQueries, read) =>
              match incomingResult with
              | .error incomingFault => (.error (.inr (.inl incomingFault)), afterCaller, savedQueries, read, moved)
              | .ok none => (.ok none, afterCaller, savedQueries, read, moved)
              | .ok (some incomingRaw) =>
                (.ok (some (incomingRaw.map fun row => match row with
                  | .error error => .error error
                  | .ok result => .ok (.hole winner, result.2))), afterCaller, savedQueries, read, moved)
          | stoppedRaw => (.error (.inr (.inr stoppedRaw)), foldCaller, foldQueries, foldOuter, moved)
    | prefixRaw => (.error (.inl prefixRaw), beforeCaller, queries, before, waiting)

/-- Attach a cache candidate to the exact shared terminal observation. -/
noncomputable def run
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]
    (checkEmpty : Bool) (representativeFuel nativeFuel p h indexFuel : Nat)
    (first : EnumerationState.Suspended) (rest : List EnumerationState.Suspended)
    (beforeCaller : Caller width) (before : EnumerationExpandableIndex.Cached Symbol Constraint)
    (incoming : Node) (incomingScs : List EnumerationState.Suspended) (queries : Queries) :
    ((Except (PrefixRaw ⊕ ((NativeOutcome ⊕ WorkerOutcome) ⊕ FoldRaw)) (Option TerminalRaw)) ×
      Caller width × Queries × EnumerationState.State Symbol Constraint × EnumerationWaitingIndex.Waiting) ×
      Option (EnumerationExpandableIndex.Cached Symbol Constraint) :=
  if incoming = .empty then
    ((.ok (some []), beforeCaller, queries, before.core, before.waiting), some before)
  else
    match ExceptT.run (SourcePruningEnumerationTerminalPrefix.run
        representativeFuel first rest before.waiting before.core) with
    | [.ok ((recorded, winner, moved), joined)] =>
      match fold checkEmpty nativeFuel p h recorded
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
                Caller width × Queries × EnumerationState.State Symbol Constraint) ×
                Option (EnumerationExpandableIndex.Cached Symbol Constraint) :=
              match foldCache with
              | none =>
                  (SourcePruningEnumerationSharedIncomingNode.run checkEmpty representativeFuel nativeFuel p h
                    foldCaller folded winner incoming incomingScs foldQueries, none)
              | some recovered =>
                  incomingCacheAdapter checkEmpty representativeFuel nativeFuel p h
                    indexFuel foldCaller (EnumerationExpandableIndex.frame folded recovered)
                    winner incoming incomingScs foldQueries
            match incomingObserved with
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
          | stoppedRaw =>
              ((.error (.inr (.inr stoppedRaw)), foldCaller, foldQueries, foldOuter, moved), none)
    | prefixRaw => ((.error (.inl prefixRaw), beforeCaller, queries, before.core, before.waiting), none)

/-- Erase the cache candidate at every fixed execution bound. -/
theorem erase
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]
    (checkEmpty : Bool) (representativeFuel nativeFuel p h indexFuel : Nat)
    (first : EnumerationState.Suspended) (rest : List EnumerationState.Suspended)
    (beforeCaller : Caller width) (before : EnumerationExpandableIndex.Cached Symbol Constraint)
    (incoming : Node) (incomingScs : List EnumerationState.Suspended) (queries : Queries) :
    (run checkEmpty representativeFuel nativeFuel p h indexFuel first rest beforeCaller before
      incoming incomingScs queries).1 =
      raw checkEmpty representativeFuel nativeFuel p h
        first rest before.waiting beforeCaller before.core incoming incomingScs queries := by
  by_cases empty : incoming = .empty
  · simp only [run, raw, ite_eq_left empty]
  · cases prefixResultEq : ExceptT.run (SourcePruningEnumerationTerminalPrefix.run
        representativeFuel first rest before.waiting before.core) with
    | nil =>
      simp only [run, raw, ite_eq_right empty, prefixResultEq]
    | cons prefixEntry prefixTail =>
      cases prefixEntry with
      | error prefixError =>
        simp only [run, raw, ite_eq_right empty, prefixResultEq]
      | ok prefixResult =>
        rcases prefixResult with ⟨⟨recorded, winner, moved⟩, joined⟩
        cases prefixTail with
        | cons prefixNext prefixRest =>
          simp only [run, raw, ite_eq_right empty, prefixResultEq]
        | nil =>
          cases cachedFoldResult : fold checkEmpty nativeFuel p h
              recorded beforeCaller ⟨joined, before.expandable, moved⟩ winner queries with
          | mk foldObservation foldCache =>
            rcases foldObservation with ⟨foldOutcome, foldCaller, foldQueries, foldOuter⟩
            have foldErased : rawFold checkEmpty nativeFuel p h recorded
                beforeCaller joined winner queries = (foldOutcome, foldCaller, foldQueries, foldOuter) := by
              rw [← fold_erase checkEmpty nativeFuel p h recorded
                beforeCaller ⟨joined, before.expandable, moved⟩ winner queries, cachedFoldResult]
            simp only [run, raw, ite_eq_right empty,
              prefixResultEq, cachedFoldResult, foldErased]
            cases foldOutcome with
            | error foldFault => rfl
            | ok foldReturned =>
              cases foldReturned with
              | none => rfl
              | some foldRaw =>
                cases foldRaw with
                | nil => rfl
                | cons foldEntry foldTail =>
                  cases foldEntry with
                  | error foldError => rfl
                  | ok foldValue =>
                    rcases foldValue with ⟨foldUnit, folded⟩
                    cases foldUnit
                    cases foldTail with
                    | cons foldNext foldRest => rfl
                    | nil =>
                      cases foldCache with
                      | none =>
                        cases fallbackIncomingResult : SourcePruningEnumerationSharedIncomingNode.run
                            checkEmpty representativeFuel nativeFuel p h foldCaller folded
                            winner incoming incomingScs foldQueries with
                        | mk incomingOutcome incomingObservation =>
                          rcases incomingObservation with ⟨afterCaller, savedQueries, read⟩
                          simp only [fallbackIncomingResult]
                          cases incomingOutcome with
                          | error incomingFault => rfl
                          | ok incomingReturned =>
                            cases incomingReturned with
                            | none => rfl
                            | some incomingRaw => rfl'
                      | some recovered =>
                        dsimp only
                        erw [← incoming_erase checkEmpty
                          representativeFuel nativeFuel p h indexFuel foldCaller
                          (EnumerationExpandableIndex.frame folded recovered)
                          winner incoming incomingScs foldQueries]
                        cases cachedIncomingResult : incomingCacheAdapter
                            checkEmpty representativeFuel nativeFuel p h indexFuel foldCaller
                            (EnumerationExpandableIndex.frame folded recovered)
                            winner incoming incomingScs foldQueries with
                        | mk incomingObservation incomingCache =>
                          rcases incomingObservation with ⟨incomingOutcome, afterCaller, savedQueries, read⟩
                          cases incomingOutcome with
                          | error incomingFault => rfl
                          | ok incomingReturned =>
                            cases incomingReturned with
                            | none => rfl
                            | some incomingRaw => rfl'

/-- A successful terminal row and its attached cache have the same core. -/
theorem singleton_core
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]
    (checkEmpty : Bool) (representativeFuel nativeFuel p h indexFuel : Nat)
    (first : Suspended) (rest : List Suspended)
    (beforeCaller reachedCaller : Caller width)
    (before after : EnumerationExpandableIndex.Cached Symbol Constraint)
    (incoming : Node) (incomingScs : List Suspended) (queries savedQueries : Queries)
    (fragment : Fragments.Fragment Symbol) (returned outer : EnumerationState.State Symbol Constraint)
    (waiting : EnumerationWaitingIndex.Waiting)
    (observed : run checkEmpty representativeFuel nativeFuel p h indexFuel
      first rest beforeCaller before incoming incomingScs queries =
      ((.ok (some [.ok (fragment, returned)]), reachedCaller, savedQueries, outer, waiting), some after)) :
    after.core = returned := by
  by_cases empty : incoming = .empty
  · simp [run, empty] at observed
  · cases prefixResultEq : ExceptT.run (SourcePruningEnumerationTerminalPrefix.run
        representativeFuel first rest before.waiting before.core) with
    | nil => simp [run, empty, prefixResultEq] at observed
    | cons prefixEntry prefixTail =>
      cases prefixEntry with
      | error prefixError => simp [run, empty, prefixResultEq] at observed
      | ok prefixResult =>
        rcases prefixResult with ⟨⟨recorded, winner, moved⟩, joined⟩
        cases prefixTail with
        | cons prefixNext prefixRest => simp [run, empty, prefixResultEq] at observed
        | nil =>
          cases foldResultEq : fold checkEmpty nativeFuel p h recorded
              beforeCaller ⟨joined, before.expandable, moved⟩ winner queries with
          | mk foldObservation foldCache =>
            rcases foldObservation with ⟨foldOutcome, foldCaller, foldQueries, foldOuter⟩
            simp only [run, ite_eq_right empty, prefixResultEq, foldResultEq] at observed
            cases foldOutcome with
            | error fault => simp at observed
            | ok foldReturned =>
              cases foldReturned with
              | none => simp at observed
              | some foldRaw =>
                cases foldRaw with
                | nil => simp at observed
                | cons foldEntry foldTail =>
                  cases foldEntry with
                  | error foldError => simp at observed
                  | ok foldValue =>
                    rcases foldValue with ⟨foldUnit, folded⟩
                    cases foldUnit
                    cases foldTail with
                    | cons foldNext foldRest => simp at observed
                    | nil =>
                      cases foldCache with
                      | none =>
                        cases resultEq : SourcePruningEnumerationSharedIncomingNode.run checkEmpty
                            representativeFuel nativeFuel p h foldCaller folded winner incoming incomingScs
                            foldQueries with
                        | mk outcome reached =>
                          rcases reached with ⟨caller, saved, read⟩
                          simp only [resultEq] at observed
                          cases outcome with
                          | error fault => simp at observed
                          | ok result => cases result <;> simp at observed
                      | some recovered =>
                        cases incomingEq : incomingCacheAdapter checkEmpty
                            representativeFuel nativeFuel p h indexFuel foldCaller
                            (EnumerationExpandableIndex.frame folded recovered) winner incoming incomingScs
                            foldQueries with
                        | mk incomingObservation incomingCache =>
                          rcases incomingObservation with ⟨outcome, caller, saved, read⟩
                          simp only [incomingEq] at observed
                          cases outcome with
                          | error fault => simp at observed
                          | ok result =>
                            cases result with
                            | none => simp at observed
                            | some raw =>
                              have mapped := congrArg (fun result => result.1.1) observed
                              simp only [Except.ok.injEq, Option.some.injEq,
                                List.map_eq_singleton_iff] at mapped
                              obtain ⟨row, rawSame, rowSame⟩ := mapped
                              cases row with
                              | error error => cases rowSame
                              | ok result =>
                                rcases result with ⟨incomingUnit, core⟩
                                cases incomingUnit
                                have coreSame : core = returned := (Prod.mk.inj (Except.ok.inj rowSame)).2
                                subst core
                                have cacheSame : incomingCache = some after := congrArg Prod.snd observed
                                apply incoming_singleton_core checkEmpty
                                  representativeFuel nativeFuel p h indexFuel foldCaller caller
                                  (EnumerationExpandableIndex.frame folded recovered) after winner incoming
                                  incomingScs foldQueries saved read returned
                                simpa only [rawSame, cacheSame] using incomingEq

/-- A stopped actual prefix retains the current caller, memo bundle and waiting state. -/
theorem prefix_failed
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (checkEmpty : Bool) (representativeFuel nativeFuel p h indexFuel : Nat)
    (first : Suspended) (rest : List Suspended)
    (beforeCaller : Caller width) (before : EnumerationExpandableIndex.Cached Symbol Constraint)
    (incoming : Node) (incomingScs : List Suspended) (memos : Memos)
    (initial : Context formulas solver inventory beforeCaller memos)
    (nonempty : incoming ≠ .empty)
    (stopped : ¬ ∃ recorded winner moved joined,
      ExceptT.run (SourcePruningEnumerationTerminalPrefix.run
        representativeFuel first rest before.waiting before.core) =
          [.ok ((recorded, winner, moved), joined)]) :
    run checkEmpty representativeFuel nativeFuel p h indexFuel first rest beforeCaller before
      incoming incomingScs memos.query =
        ((.error (.inl (ExceptT.run (SourcePruningEnumerationTerminalPrefix.run
          representativeFuel first rest before.waiting before.core))),
          beforeCaller, memos.query, before.core, before.waiting), none) ∧
      Post formulas solver inventory beforeCaller beforeCaller memos := by
  refine ⟨?_, Post.refl initial⟩
  cases observed : ExceptT.run (SourcePruningEnumerationTerminalPrefix.run
      representativeFuel first rest before.waiting before.core) with
  | nil => simp only [run, ite_eq_right nonempty, observed]
  | cons entry tail =>
      cases entry with
      | error error => simp only [run, ite_eq_right nonempty, observed]
      | ok result =>
          rcases result with ⟨⟨recorded, winner, moved⟩, joined⟩
          cases tail with
          | nil => exact (stopped ⟨recorded, winner, moved, joined, observed⟩).elim
          | cons next remaining => simp only [run, ite_eq_right nonempty, observed]

end MicroCFTA.SourcePruningEnumerationSharedCachedTerminal
