import MicroCFTA.SourcePruningEnumerationSharedCachedTerminal
import MicroCFTA.SourcePruningEnumerationSelectedStep
import MicroCFTA.SourcePruningEnumerationNativeOrdinaryContinuations

/-!
# Shared selected enumeration continuations

Every terminal child uses the shared cached terminal. Its raw fallback also
uses shared dispatch and incoming checks. The outcome retains each private
shared snapshot, completed child prefix and reached native caller.

Children continue only after an actual successful singleton with a cache.
Alternatives retain their captured enumeration input. A completed fragment
runs its continuation before the next alternative uses its returned native
endpoint. The selected prefix remains the existing heap-only operation.

These literal operations and structural trace laws do not prove adequate
driver depth, all later native capacity, complete source-size enumeration,
either signed inverse or Haskell host correspondence.
-/

namespace MicroCFTA.SourcePruningEnumerationSharedSelectedContinuations.ChildDispatch
open EnumerationState EnumerationCorrectness EnumerationSchedule
open InternedConstructorTemplates InternedProbeProvenance
open SourcePruningEnumerationNodes SourcePruningEnumerationObservation
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => InternedConstructorTemplates.Value Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Queries" => SourceEndpointMemo.Memos
local notation "PrefixRaw" => List (Except EnumerationState.Error
  ((List Nat × Nat × EnumerationWaitingIndex.Waiting) × EnumerationState.State Symbol Constraint))
local notation "FoldRaw" => List (Except EnumerationState.Error
  (Unit × EnumerationState.State Symbol Constraint))
local notation "TerminalRaw" => List (Except EnumerationState.Error
  (Fragments.Fragment Symbol × EnumerationState.State Symbol Constraint))
variable {width : Nat}
/-- Keep the complete raw child observation and its reached state. -/
abbrev Observation (width : Nat) :=
  (Except (PrefixRaw ⊕ ((SourceEqualityNativeDemand.Outcome width Node ⊕
    SourcePruningEnumerationSharedEnabledEmpty.Outcome width) ⊕ FoldRaw)) (Option TerminalRaw)) ×
    Caller width × Queries × EnumerationState.State Symbol Constraint × EnumerationWaitingIndex.Waiting
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]

/-- Dispatch the actual child partition and retain the original raw observation. -/
noncomputable def observe
    (checkEmpty : Bool) (representativeFuel nativeFuel p h : Nat)
    (scs : List Suspended) (incoming : Node)
    (beforeCaller : Caller width) (before : EnumerationState.State Symbol Constraint)
    (waiting : EnumerationWaitingIndex.Waiting) (queries : Queries) : Observation width :=
  if incoming = .empty then
    (.ok (some []), beforeCaller, queries, before, waiting)
  else
    match scs.partition (fun sc => EqualityTrie.isTerminal sc.trie) with
    | ([], _) =>
        match SourcePruningEnumerationShallowChild.prepareChild scs incoming with
        | none => (.ok none, beforeCaller, queries, before, waiting)
        | some action => (.ok (some (ExceptT.run (action before))), beforeCaller, queries, before, waiting)
    | (first :: rest, descendants) =>
        SourcePruningEnumerationSharedCachedTerminal.raw checkEmpty representativeFuel nativeFuel p h
          first rest waiting beforeCaller before incoming descendants queries

/-- Add the native cache while retaining terminal caller, query and raw effects. -/
noncomputable def run
    (checkEmpty : Bool) (representativeFuel nativeFuel p h indexFuel : Nat)
    (scs : List Suspended) (incoming : Node)
    (beforeCaller : Caller width) (before : EnumerationExpandableIndex.Cached Symbol Constraint)
    (queries : Queries) : Observation width × Option (EnumerationExpandableIndex.Cached Symbol Constraint) :=
  if incoming = .empty then
    ((.ok (some []), beforeCaller, queries, before.core, before.waiting), some before)
  else
    match scs.partition (fun sc => EqualityTrie.isTerminal sc.trie) with
    | ([], _) =>
        (observe checkEmpty representativeFuel nativeFuel p h scs incoming
          beforeCaller before.core before.waiting queries,
          match SourcePruningEnumerationCachedPrepare.prepareChild
              beforeCaller.checked.native.machine.heap indexFuel scs incoming before with
          | some [] => some before
          | some [(_, after)] => some after
          | _ => none)
    | (first :: rest, descendants) =>
        SourcePruningEnumerationSharedCachedTerminal.run
          checkEmpty representativeFuel nativeFuel p h indexFuel
          first rest beforeCaller before incoming descendants queries

/-- Cache erasure preserves every raw result and reached caller at fixed bounds. -/
theorem erase
    (checkEmpty : Bool) (representativeFuel nativeFuel p h indexFuel : Nat)
    (scs : List Suspended) (incoming : Node)
    (beforeCaller : Caller width) (before : EnumerationExpandableIndex.Cached Symbol Constraint)
    (queries : Queries) :
    (run checkEmpty representativeFuel nativeFuel p h indexFuel
      scs incoming beforeCaller before queries).1 =
      observe checkEmpty representativeFuel nativeFuel p h scs incoming
        beforeCaller before.core before.waiting queries := by
  by_cases empty : incoming = .empty
  · simp only [run, observe, ite_eq_left empty]
  · cases partitioned : scs.partition (fun sc => EqualityTrie.isTerminal sc.trie) with
    | mk here descendants =>
      cases here with
      | nil => simp only [run, ite_eq_right empty, partitioned]
      | cons first rest =>
        simpa only [run, observe, ite_eq_right empty, partitioned] using
          SourcePruningEnumerationSharedCachedTerminal.erase
            checkEmpty representativeFuel nativeFuel p h indexFuel
            first rest beforeCaller before incoming descendants queries

/-- The terminal route retains the complete existing adapter and all its receipts. -/
theorem terminal
    (checkEmpty : Bool) (representativeFuel nativeFuel p h indexFuel : Nat)
    (scs : List Suspended) (incoming : Node)
    (beforeCaller : Caller width) (before : EnumerationExpandableIndex.Cached Symbol Constraint)
    (queries : Queries) (first : Suspended) (rest descendants : List Suspended)
    (partitioned : scs.partition (fun sc => EqualityTrie.isTerminal sc.trie) =
      (first :: rest, descendants)) :
    run checkEmpty representativeFuel nativeFuel p h indexFuel scs incoming beforeCaller before queries =
      SourcePruningEnumerationSharedCachedTerminal.run
        checkEmpty representativeFuel nativeFuel p h indexFuel
        first rest beforeCaller before incoming descendants queries := by
  by_cases empty : incoming = .empty
  · simp only [run, SourcePruningEnumerationSharedCachedTerminal.run, ite_eq_left empty]
  · simp only [run, ite_eq_right empty, partitioned]

/-- Every successful singleton cache has the actual raw row core at fixed bounds. -/
theorem singleton_core
    (checkEmpty : Bool) (representativeFuel nativeFuel p h indexFuel : Nat)
    (scs : List Suspended) (incoming : Node)
    (beforeCaller reachedCaller : Caller width)
    (before after : EnumerationExpandableIndex.Cached Symbol Constraint)
    (queries savedQueries : Queries) (fragment : Fragments.Fragment Symbol)
    (returned outer : EnumerationState.State Symbol Constraint)
    (waiting : EnumerationWaitingIndex.Waiting)
    (observed : run checkEmpty representativeFuel nativeFuel p h indexFuel scs incoming
      beforeCaller before queries =
      ((.ok (some [.ok (fragment, returned)]), reachedCaller, savedQueries, outer, waiting), some after)) :
    after.core = returned := by
  by_cases empty : incoming = .empty
  · simp [run, empty] at observed
  · cases partitioned : scs.partition (fun sc => EqualityTrie.isTerminal sc.trie) with
    | mk here descendants =>
      cases here with
      | cons first rest =>
        apply SourcePruningEnumerationSharedCachedTerminal.singleton_core checkEmpty
          representativeFuel nativeFuel p h indexFuel first rest beforeCaller reachedCaller
          before after incoming descendants queries savedQueries fragment returned outer waiting
        simpa only [run, ite_eq_right empty, partitioned] using observed
      | nil =>
        cases cached : SourcePruningEnumerationCachedPrepare.prepareChild
            beforeCaller.checked.native.machine.heap indexFuel scs incoming before with
        | none => simp only [run, ite_eq_right empty, partitioned, cached, Prod.mk.injEq,
            reduceCtorEq, and_false] at observed
        | some rows =>
          have erasure := SourcePruningEnumerationCachedPrepare.erase_some
            beforeCaller.checked.native.machine.heap indexFuel scs incoming before rows cached
          cases prepared : SourcePruningEnumerationShallowChild.prepareChild
              (EnumGuard := Constraint) scs incoming with
          | none => simp only [prepared, Option.map_none, reduceCtorEq] at erasure
          | some action =>
            have raw := congrArg (fun result => result.1.1) observed
            simp only [run, observe, ite_eq_right empty, partitioned, prepared] at raw
            simp only [prepared, Option.map_some, Option.some.injEq] at erasure
            have rowsSame : rows.map (fun row => Except.ok (row.1, row.2.core)) =
                [.ok (fragment, returned)] :=
              erasure.symm.trans (Option.some.inj (Except.ok.inj raw))
            obtain ⟨row, singleton, mapped⟩ := List.map_eq_singleton_iff.mp rowsSame
            rcases row with ⟨childFragment, childCache⟩
            subst rows
            have cacheSame : childCache = after := by
              simpa only [run, ite_eq_right empty, partitioned, cached, Option.some.injEq] using
                congrArg Prod.snd observed
            subst after
            exact (Prod.mk.inj (Except.ok.inj mapped)).2

/-- Empty rejects before partition, prefix execution or any native query. -/
theorem empty
    (checkEmpty : Bool) (representativeFuel nativeFuel p h indexFuel : Nat)
    (scs : List Suspended)
    (beforeCaller : Caller width) (before : EnumerationExpandableIndex.Cached Symbol Constraint)
    (queries : Queries) :
    run checkEmpty representativeFuel nativeFuel p h indexFuel scs .empty beforeCaller before queries =
      ((.ok (some []), beforeCaller, queries, before.core, before.waiting), some before) := by
  simp only [run, ↓reduceIte]


end MicroCFTA.SourcePruningEnumerationSharedSelectedContinuations.ChildDispatch



namespace MicroCFTA.SourcePruningEnumerationSharedSelectedContinuations.ChildTraversal
open EnumerationState InternedConstructorTemplates
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => InternedConstructorTemplates.Value Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Queries" => SourceEndpointMemo.Memos
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Fragment" => Fragments.Fragment Symbol
variable {width : Nat}

/-- Complete every child or retain the completed prefix and exact stopping receipt. -/
inductive Result (width : Nat) where
  /-- All children return one successful row and a cache. -/
  | complete (fragments : List Fragment) (caller : Caller width) (queries : Queries) (after : Cached)
  /-- Keep the completed fragments and the first stopping observation. -/
  | stopped (completedPrefix : List Fragment) (observation : SourcePruningEnumerationSharedSelectedContinuations.ChildDispatch.Observation width)
      (candidate : Option Cached)

variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]

/-- Run children in order with the reached caller, queries and post-write cache. -/
noncomputable def run
    (checkEmpty : Bool) (representativeFuel nativeFuel p h indexFuel : Nat) :
    List (Node × List Suspended) → Caller width → Cached → Queries → Result width
  | [], caller, before, queries => .complete [] caller queries before
  | (value, bucket) :: rest, caller, before, queries =>
      match SourcePruningEnumerationSharedSelectedContinuations.ChildDispatch.run checkEmpty representativeFuel nativeFuel p h indexFuel
          bucket value caller before queries with
      | ((.ok (some [.ok (fragment, _returned)]), reachedCaller, savedQueries, _outer, _waiting), some after) =>
          match run checkEmpty representativeFuel nativeFuel p h indexFuel rest reachedCaller after savedQueries with
          | .complete fragments finalCaller finalQueries final =>
              .complete (fragment :: fragments) finalCaller finalQueries final
          | .stopped completedPrefix observation candidate =>
              .stopped (fragment :: completedPrefix) observation candidate
      | (observation, candidate) => .stopped [] observation candidate

/-- A complete trace records each actual child call at its exact returned core. -/
inductive Trace (checkEmpty : Bool) (representativeFuel nativeFuel p h indexFuel : Nat) :
    List (Node × List Suspended) → Caller width → Cached → Queries →
      List Fragment → Caller width → Cached → Queries → Prop
  /-- An empty child list retains its input state. -/
  | nil (caller : Caller width) (before : Cached) (queries : Queries) :
      Trace checkEmpty representativeFuel nativeFuel p h indexFuel [] caller before queries [] caller before queries
  /-- One actual child result supplies the next child state. -/
  | cons {value : Node} {bucket : List Suspended} {rest : List (Node × List Suspended)}
      {beforeCaller middleCaller afterCaller : Caller width} {before middle after : Cached}
      {queries middleQueries afterQueries : Queries} {fragment : Fragment} {fragments : List Fragment}
      {outer : EnumerationState.State Symbol Constraint} {waiting : EnumerationWaitingIndex.Waiting}
      (head : SourcePruningEnumerationSharedSelectedContinuations.ChildDispatch.run checkEmpty representativeFuel nativeFuel p h indexFuel
        bucket value beforeCaller before queries =
        ((.ok (some [.ok (fragment, middle.core)]), middleCaller, middleQueries, outer, waiting), some middle))
      (tail : Trace checkEmpty representativeFuel nativeFuel p h indexFuel rest middleCaller middle middleQueries
        fragments afterCaller after afterQueries) :
      Trace checkEmpty representativeFuel nativeFuel p h indexFuel ((value, bucket) :: rest)
        beforeCaller before queries (fragment :: fragments) afterCaller after afterQueries

/-- Every recorded native trace completes through the same ordered traversal. -/
theorem trace_complete
    (trace : Trace (width := width) checkEmpty representativeFuel nativeFuel p h indexFuel inputs beforeCaller before queries
      fragments afterCaller after afterQueries) :
    run checkEmpty representativeFuel nativeFuel p h indexFuel inputs beforeCaller before queries =
      .complete fragments afterCaller afterQueries after := by
  induction trace with
  | nil => rfl
  | cons head _tail ih => simp only [run, head, ih]

/-- Every completed traversal derives the actual ordered trace, without admission premises. -/
theorem complete_trace
    (checkEmpty : Bool) (representativeFuel nativeFuel p h indexFuel : Nat)
    (inputs : List (Node × List Suspended)) (beforeCaller afterCaller : Caller width)
    (before after : Cached) (queries afterQueries : Queries) (fragments : List Fragment)
    (completed : run checkEmpty representativeFuel nativeFuel p h indexFuel inputs beforeCaller before queries =
      .complete fragments afterCaller afterQueries after) :
    Trace checkEmpty representativeFuel nativeFuel p h indexFuel inputs beforeCaller before queries
      fragments afterCaller after afterQueries := by
  induction inputs generalizing beforeCaller before queries fragments with
  | nil =>
    cases completed
    exact .nil _ _ _
  | cons input rest ih =>
    rcases input with ⟨value, bucket⟩
    cases headEq : SourcePruningEnumerationSharedSelectedContinuations.ChildDispatch.run checkEmpty representativeFuel nativeFuel p h indexFuel
        bucket value beforeCaller before queries with
    | mk observation candidate =>
      rcases observation with ⟨outcome, middleCaller, middleQueries, outer, waiting⟩
      cases outcome with
      | error fault => simp [run, headEq] at completed
      | ok returned =>
        cases returned with
        | none => simp [run, headEq] at completed
        | some raw =>
          cases raw with
          | nil => simp [run, headEq] at completed
          | cons row rows =>
            cases row with
            | error error => simp [run, headEq] at completed
            | ok child =>
              rcases child with ⟨fragment, returnedCore⟩
              cases rows with
              | cons row rows => simp [run, headEq] at completed
              | nil =>
                cases candidate with
                | none => simp [run, headEq] at completed
                | some middle =>
                  have coreSame := SourcePruningEnumerationSharedSelectedContinuations.ChildDispatch.singleton_core checkEmpty
                    representativeFuel nativeFuel p h indexFuel bucket value beforeCaller middleCaller
                    before middle queries middleQueries fragment returnedCore outer waiting headEq
                  cases tailEq : run checkEmpty representativeFuel nativeFuel p h indexFuel
                      rest middleCaller middle middleQueries with
                  | stopped completedPrefix observation candidate => simp [run, headEq, tailEq] at completed
                  | complete tailFragments finalCaller finalQueries final =>
                    simp only [run, headEq, tailEq, Result.complete.injEq] at completed
                    obtain ⟨rfl, rfl, rfl, rfl⟩ := completed
                    rw [← coreSame] at headEq
                    exact .cons headEq (ih middleCaller middle middleQueries tailFragments tailEq)

/-- A missing cache retains the exact child observation and does not run the tail. -/
theorem uncached
    (checkEmpty : Bool) (representativeFuel nativeFuel p h indexFuel : Nat)
    (value : Node) (bucket : List Suspended) (rest : List (Node × List Suspended))
    (beforeCaller : Caller width) (before : Cached) (queries : Queries)
    (observation : SourcePruningEnumerationSharedSelectedContinuations.ChildDispatch.Observation width)
    (observed : SourcePruningEnumerationSharedSelectedContinuations.ChildDispatch.run checkEmpty representativeFuel nativeFuel p h indexFuel
      bucket value beforeCaller before queries = (observation, none)) :
    run checkEmpty representativeFuel nativeFuel p h indexFuel ((value, bucket) :: rest)
      beforeCaller before queries = .stopped [] observation none := by
  rw [run, observed]
  split <;> simp_all

/-- Every stop retains an actual completed-prefix trace and the exact next child call. -/
theorem stopped_trace
    (checkEmpty : Bool) (representativeFuel nativeFuel p h indexFuel : Nat)
    (inputs : List (Node × List Suspended)) (beforeCaller : Caller width)
    (before : Cached) (queries : Queries) (completedPrefix : List Fragment)
    (observation : SourcePruningEnumerationSharedSelectedContinuations.ChildDispatch.Observation width) (candidate : Option Cached)
    (stopped : run checkEmpty representativeFuel nativeFuel p h indexFuel inputs beforeCaller before queries =
      .stopped completedPrefix observation candidate) :
    ∃ (consumed : List (Node × List Suspended)) (value : Node) (bucket : List Suspended)
      (remaining : List (Node × List Suspended)) (stoppedCaller : Caller width)
      (stoppedBefore : Cached) (stoppedQueries : Queries),
      inputs = consumed ++ ((value, bucket) :: remaining) ∧
      Trace checkEmpty representativeFuel nativeFuel p h indexFuel consumed beforeCaller before queries
        completedPrefix stoppedCaller stoppedBefore stoppedQueries ∧
      SourcePruningEnumerationSharedSelectedContinuations.ChildDispatch.run checkEmpty representativeFuel nativeFuel p h indexFuel
        bucket value stoppedCaller stoppedBefore stoppedQueries = (observation, candidate) := by
  induction inputs generalizing beforeCaller before queries completedPrefix with
  | nil => cases stopped
  | cons input rest ih =>
    rcases input with ⟨value, bucket⟩
    cases headEq : SourcePruningEnumerationSharedSelectedContinuations.ChildDispatch.run checkEmpty representativeFuel nativeFuel p h indexFuel
        bucket value beforeCaller before queries with
    | mk headObservation headCandidate =>
      have stoppedHere (same : Result.stopped [] headObservation headCandidate =
          .stopped completedPrefix observation candidate) :
          ∃ (consumed : List (Node × List Suspended)) (stopValue : Node) (stopBucket : List Suspended)
            (remaining : List (Node × List Suspended)) (stoppedCaller : Caller width)
            (stoppedBefore : Cached) (stoppedQueries : Queries),
            (value, bucket) :: rest = consumed ++ ((stopValue, stopBucket) :: remaining) ∧
            Trace checkEmpty representativeFuel nativeFuel p h indexFuel consumed beforeCaller before queries
              completedPrefix stoppedCaller stoppedBefore stoppedQueries ∧
            SourcePruningEnumerationSharedSelectedContinuations.ChildDispatch.run checkEmpty representativeFuel nativeFuel p h indexFuel
              stopBucket stopValue stoppedCaller stoppedBefore stoppedQueries = (observation, candidate) := by
        cases same
        exact ⟨[], value, bucket, rest, beforeCaller, before, queries, rfl, .nil _ _ _, headEq⟩
      rcases headObservation with ⟨outcome, middleCaller, middleQueries, outer, waiting⟩
      cases outcome with
      | error fault => exact stoppedHere (by simpa only [run, headEq] using stopped)
      | ok returned =>
        cases returned with
        | none => exact stoppedHere (by simpa only [run, headEq] using stopped)
        | some raw =>
          cases raw with
          | nil => exact stoppedHere (by simpa only [run, headEq] using stopped)
          | cons row rows =>
            cases row with
            | error error => exact stoppedHere (by simpa only [run, headEq] using stopped)
            | ok child =>
              rcases child with ⟨fragment, returnedCore⟩
              cases rows with
              | cons row rows => exact stoppedHere (by simpa only [run, headEq] using stopped)
              | nil =>
                cases headCandidate with
                | none => exact stoppedHere (by simpa only [run, headEq] using stopped)
                | some middle =>
                  have coreSame := SourcePruningEnumerationSharedSelectedContinuations.ChildDispatch.singleton_core checkEmpty
                    representativeFuel nativeFuel p h indexFuel bucket value beforeCaller middleCaller
                    before middle queries middleQueries fragment returnedCore outer waiting headEq
                  cases tailEq : run checkEmpty representativeFuel nativeFuel p h indexFuel
                      rest middleCaller middle middleQueries with
                  | complete fragments finalCaller finalQueries final => simp [run, headEq, tailEq] at stopped
                  | stopped tailPrefix finalObservation finalCandidate =>
                    simp only [run, headEq, tailEq, Result.stopped.injEq] at stopped
                    obtain ⟨rfl, rfl, rfl⟩ := stopped
                    obtain ⟨consumed, nextValue, nextBucket, remaining, stoppedCaller,
                      stoppedBefore, stoppedQueries, shape, trace, stopEq⟩ :=
                        ih middleCaller middle middleQueries tailPrefix tailEq
                    rw [← coreSame] at headEq
                    exact ⟨(value, bucket) :: consumed, nextValue, nextBucket, remaining,
                      stoppedCaller, stoppedBefore, stoppedQueries, congrArg (List.cons (value, bucket)) shape,
                      .cons headEq trace, stopEq⟩

end MicroCFTA.SourcePruningEnumerationSharedSelectedContinuations.ChildTraversal



namespace MicroCFTA.SourcePruningEnumerationSharedSelectedContinuations.SelectedEdge
open EnumerationState EnumerationCorrectness EnumerationSchedule EnumerationDependencies
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
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Fragment" => Fragments.Fragment Symbol
variable {width : Nat}

/-- Retain prefix rejection, unsupported preparation, stopped children and a completed edge. -/
inductive Result (width : Nat) where
  /-- The prefix does not supply the supported singleton packet. -/
  | unhandled
  /-- The arity check rejects before any child runs. -/
  | rejected (caller : Caller width) (queries : Queries) (after : Cached)
  /-- Retain the exact first stopping child observation and optional cache. -/
  | stopped (completedPrefix : List Fragment)
      (observation : SourcePruningEnumerationSharedSelectedContinuations.ChildDispatch.Observation width) (candidate : Option Cached)
  /-- Keep the completed child endpoint when finalization supplies no cache. -/
  | finalizeStopped (fragment : Fragment) (caller : Caller width) (queries : Queries)
      (beforeFinalize : Cached)
  /-- Every child succeeds and the edge residual is recorded. -/
  | complete (fragment : Fragment) (caller : Caller width) (queries : Queries) (after : Cached)

/-- Record the residual in the actual completed cache. -/
def finish (residual : Option Constraint) (fragment : Fragment) (before : Cached) : Cached :=
  EnumerationExpandableIndex.frame {before.core with obligations :=
    match residual with
    | none => before.core.obligations
    | some guard => (guard, fragment) :: before.core.obligations} before

/-- Residual recording has exactly the source action's successful singleton result. -/
theorem finish_raw (residual : Option Constraint) (fragment : Fragment) (before : Cached) :
    ExceptT.run (recordResidual residual fragment before.core) = [.ok ((), (finish residual fragment before).core)] := by
  cases residual <;> rfl

/-- A bounded completed fragment permits the exact residual update. -/
theorem finish_safe (residual : Option Constraint) (fragment : Fragment) (before : Cached)
    (safe : Safe before.core) (bounded : FragmentBound before.core.counter fragment) :
    Safe (finish residual fragment before).core := by
  apply (recordResidual_safe residual fragment before.core _ safe bounded ?_).1
  rw [Success, finish_raw]
  simp

/-- Residual recording retains every existing root, its stored value and its class. -/
theorem finish_protected (residual : Option Constraint) (fragment : Fragment) (before : Cached)
    (held : Nat) (root : IsRoot before.core.representatives held) :
    EnumerationDriver.Protected held before.core (finish residual fragment before).core :=
  ⟨rfl, root, fun _ => Iff.rfl⟩

variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]

/-- Run the actual own-class prefix, ordered native children and final residual update. -/
noncomputable def run (checkEmpty : Bool) (r n p h k : Nat)
    (scs : List Suspended) (edge : EdgeValue Symbol Constraint)
    (caller : Caller width) (before : Cached) (queries : Queries) : Result width :=
  match SourcePruningEnumerationCachedOwn.prepare caller.checked.native.machine.heap scs edge before with
  | none => .unhandled
  | some [] => .rejected caller queries before
  | some [((symbol, staged, residual), middle)] =>
      match SourcePruningEnumerationSharedSelectedContinuations.ChildTraversal.run checkEmpty r n p h k
          (staged.map (fun input => (input.1, input.2.1))) caller middle queries with
      | .stopped fragments observation candidate => .stopped fragments observation candidate
      | .complete fragments afterCaller saved after =>
          let fragment := Fragments.Fragment.node symbol fragments
          .complete fragment afterCaller saved (finish residual fragment after)
  | _ => .unhandled

/-- Arity rejection retains the original caller and cache without running a child. -/
theorem arity_rejected (checkEmpty : Bool) (r n p h k : Nat) (scs : List Suspended)
    (edge : EdgeValue Symbol Constraint) (caller : Caller width) (before : Cached) (queries : Queries)
    (rejected : arityAllows edge.children.length scs = false) :
    run checkEmpty r n p h k scs edge caller before queries = .rejected caller queries before := by
  simp only [run, SourcePruningEnumerationCachedOwn.prepare, rejected, Bool.false_eq_true, ↓reduceIte]

/-- Unsupported annotations retain the explicit prefix fallback. -/
theorem unsupported (checkEmpty : Bool) (r n p h k : Nat) (scs : List Suspended)
    (edge : EdgeValue Symbol Constraint) (caller : Caller width) (before : Cached) (queries : Queries)
    (allowed : arityAllows edge.children.length scs = true)
    (projected : SourcePruningEnumerationConstraint.project edge.entry.key.constraint = none) :
    run checkEmpty r n p h k scs edge caller before queries = .unhandled := by
  simp only [run, SourcePruningEnumerationCachedOwn.prepare, allowed, ↓reduceIte, projected]

/-- Every stopped child receipt retains its prefix, observation and optional cache. -/
theorem children_stopped (checkEmpty : Bool) (r n p h k : Nat) (scs : List Suspended)
    (edge : EdgeValue Symbol Constraint) (caller : Caller width) (before : Cached) (queries : Queries)
    (symbol : Symbol) (staged : List (Node × List Suspended × Option (EnumerateM Symbol Constraint Fragment)))
    (residual : Option Constraint) (middle : Cached) (fragments : List Fragment)
    (observation : SourcePruningEnumerationSharedSelectedContinuations.ChildDispatch.Observation width) (candidate : Option Cached)
    (prepared : SourcePruningEnumerationCachedOwn.prepare caller.checked.native.machine.heap scs edge before =
      some [((symbol, staged, residual), middle)])
    (stopped : SourcePruningEnumerationSharedSelectedContinuations.ChildTraversal.run checkEmpty r n p h k
      (staged.map (fun input => (input.1, input.2.1))) caller middle queries =
        .stopped fragments observation candidate) :
    run checkEmpty r n p h k scs edge caller before queries = .stopped fragments observation candidate := by
  simp only [run, prepared, stopped]


end MicroCFTA.SourcePruningEnumerationSharedSelectedContinuations.SelectedEdge



namespace MicroCFTA.SourcePruningEnumerationSharedSelectedContinuations.CapturedEdge
open EnumerationState EnumerationCorrectness EnumerationSchedule EnumerationDependencies
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
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Fragment" => Fragments.Fragment Symbol
local notation "Result" => SourcePruningEnumerationSharedSelectedContinuations.SelectedEdge.Result
variable {width : Nat}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]

/-- Finalize each successful selected edge at the original captured raw slot. -/
noncomputable def run (checkEmpty : Bool) (r n p h k target : Nat)
    (scs : List Suspended) (edge : EdgeValue Symbol Constraint)
    (caller : Caller width) (before : Cached) (queries : Queries) : Option (Result width) :=
  match SourcePruningEnumerationSharedSelectedContinuations.SelectedEdge.run checkEmpty r n p h k scs edge caller before queries with
  | .complete fragment afterCaller saved after =>
      match SourcePruningEnumerationFinalize.run afterCaller.checked.native.machine.heap k target fragment after with
      | some finished => some (.complete fragment afterCaller saved finished)
      | none => some (.finalizeStopped fragment afterCaller saved after)
  | result => some result

/-- A stopped child does not reset ancestry or write the captured slot. -/
theorem children_stopped (checkEmpty : Bool) (r n p h k target : Nat)
    (scs : List Suspended) (edge : EdgeValue Symbol Constraint)
    (caller : Caller width) (before : Cached) (queries : Queries)
    (fragments : List Fragment) (observation : SourcePruningEnumerationSharedSelectedContinuations.ChildDispatch.Observation width)
    (candidate : Option Cached)
    (stopped : SourcePruningEnumerationSharedSelectedContinuations.SelectedEdge.run checkEmpty r n p h k scs edge caller before queries =
      .stopped fragments observation candidate) :
    run checkEmpty r n p h k target scs edge caller before queries =
      some (.stopped fragments observation candidate) := by
  rw [run, stopped]

/-- A failed finalization retains the actual completed child caller and its cache. -/
theorem finalize_stopped (checkEmpty : Bool) (r n p h k target : Nat)
    (scs : List Suspended) (edge : EdgeValue Symbol Constraint)
    (caller reached : Caller width) (before after : Cached) (queries saved : Queries)
    (fragment : Fragment)
    (selected : SourcePruningEnumerationSharedSelectedContinuations.SelectedEdge.run
      checkEmpty r n p h k scs edge caller before queries = .complete fragment reached saved after)
    (finalized : SourcePruningEnumerationFinalize.run reached.checked.native.machine.heap
      k target fragment after = none) :
    run checkEmpty r n p h k target scs edge caller before queries =
      some (.finalizeStopped fragment reached saved after) := by
  simp only [run, selected, finalized]

end MicroCFTA.SourcePruningEnumerationSharedSelectedContinuations.CapturedEdge



namespace MicroCFTA.SourcePruningEnumerationSharedSelectedContinuations.NativeContinuations
open EnumerationState InternedConstructorTemplates
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => InternedConstructorTemplates.Value Symbol Constraint
local notation "Fragment" => Fragments.Fragment Symbol
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Queries" => SourceEndpointMemo.Memos
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Receipt" => SourcePruningEnumerationSharedSelectedContinuations.SelectedEdge.Result
universe u v
variable {width : Nat} {Output : Type u} {Reason : Type v}

/-- A completed continuation supplies the native endpoint for the next alternative. -/
inductive HookResult (Output : Type u) (Reason : Type v) (width : Nat) where
  /-- Empty output includes normal pruning and a stuck restart. -/
  | complete (outputs : List Output) (caller : Caller width) (queries : Queries)
  /-- Keep the explicit stop reason and any actual reached native endpoint. -/
  | stopped (outputs : List Output) (reason : Reason) (reached : Option (Caller width × Queries))

/-- Keep the exact edge receipt or continuation stop without inventing an endpoint. -/
inductive Stop (Reason : Type v) (width : Nat) where
  /-- A missing or noncontinuable edge stops before the hook and the suffix. -/
  | edge (current : Option (Receipt width)) (reached : Caller width × Queries)
  /-- A stopped hook retains its actual completed edge receipt. -/
  | continuation (current : Receipt width) (reason : Reason)
      (reached : Option (Caller width × Queries))

/-- Retain ordered edge receipts, continuation outputs and the exact stopping context. -/
inductive Result (Output : Type u) (Reason : Type v) (width : Nat) where
  /-- Every edge and invoked continuation completed. -/
  | complete (processed : List (Receipt width)) (outputs : List Output)
      (caller : Caller width) (queries : Queries)
  /-- Retain the finished prefix and the current edge or continuation stop. -/
  | stopped (processed : List (Receipt width)) (outputs : List Output) (current : Stop Reason width)

/-- Valid rejections retain their actual caller without invoking a fragment continuation. -/
def advance : Receipt width → Option (Caller width × Queries)
  | .complete _ caller queries _ => some (caller, queries)
  | .rejected caller queries _ => some (caller, queries)
  | .stopped _ (.ok (some []), caller, queries, _outer, _waiting) (some _) => some (caller, queries)
  | _ => none

/-- Read the actual child endpoint or retain the entry endpoint of an unsupported pure prefix. -/
def endpoint (receipt : Receipt width) (caller : Caller width) (queries : Queries) : Caller width × Queries :=
  match receipt with
  | .complete _ reached saved _ => (reached, saved)
  | .rejected reached saved _ => (reached, saved)
  | .stopped _ (_, reached, saved, _, _) _ => (reached, saved)
  | .finalizeStopped _ reached saved _ => (reached, saved)
  | .unhandled => (caller, queries)

variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]

/-- Run each completed edge's continuation before the next edge at its returned native endpoint.
The captured enumeration input is fixed. The hook can close over fixed sibling metadata.
This bounded worker does not prove completion or full source-effect correspondence. -/
noncomputable def run
    (hook : Fragment → Caller width → Queries → Cached → HookResult Output Reason width)
    (checkEmpty : Bool) (r n p h k target : Nat) (scs : List Suspended) (before : Cached) :
    List (EdgeValue Symbol Constraint) → Caller width → Queries → Result Output Reason width
  | [], caller, queries => .complete [] [] caller queries
  | edge :: rest, caller, queries =>
      match SourcePruningEnumerationSharedSelectedContinuations.CapturedEdge.run checkEmpty r n p h k target scs edge caller before queries with
      | none => .stopped [] [] (.edge none (caller, queries))
      | some receipt =>
          match receipt with
          | .complete fragment reached saved after =>
              match hook fragment reached saved after with
              | .stopped outputs reason endpoint =>
                  .stopped [] outputs (.continuation receipt reason endpoint)
              | .complete outputs middleCaller middleQueries =>
                  match run hook checkEmpty r n p h k target scs before rest middleCaller middleQueries with
                  | .complete processed later finalCaller finalQueries =>
                      .complete (receipt :: processed) (outputs ++ later) finalCaller finalQueries
                  | .stopped processed later current =>
                      .stopped (receipt :: processed) (outputs ++ later) current
          | other =>
              match SourcePruningEnumerationSharedSelectedContinuations.NativeContinuations.advance other with
              | none => .stopped [] [] (.edge (some other) (endpoint other caller queries))
              | some (middleCaller, middleQueries) =>
                  match run hook checkEmpty r n p h k target scs before rest middleCaller middleQueries with
                  | .complete processed outputs finalCaller finalQueries =>
                      .complete (other :: processed) outputs finalCaller finalQueries
                  | .stopped processed outputs current => .stopped (other :: processed) outputs current

/-- A missing edge result retains its absence and does not invoke the hook or suffix. -/
theorem missing
    (hook : Fragment → Caller width → Queries → Cached → HookResult Output Reason width)
    (checkEmpty : Bool) (r n p h k target : Nat) (scs : List Suspended) (before : Cached)
    (edge : EdgeValue Symbol Constraint) (rest : List (EdgeValue Symbol Constraint))
    (caller : Caller width) (queries : Queries)
    (observed : SourcePruningEnumerationSharedSelectedContinuations.CapturedEdge.run checkEmpty r n p h k target scs edge caller before queries =
      none) :
    run hook checkEmpty r n p h k target scs before (edge :: rest) caller queries =
      .stopped [] [] (.edge none (caller, queries)) := by
  simp only [run, observed]

/-- The sibling starts at the hook's actual returned endpoint, after the head hook completes. -/
theorem completed_head
    (hook : Fragment → Caller width → Queries → Cached → HookResult Output Reason width)
    (checkEmpty : Bool) (r n p h k target : Nat) (scs : List Suspended) (before : Cached)
    (edge : EdgeValue Symbol Constraint) (rest : List (EdgeValue Symbol Constraint))
    (caller reached middleCaller : Caller width) (queries saved middleQueries : Queries)
    (fragment : Fragment) (after : Cached) (outputs : List Output)
    (observed : SourcePruningEnumerationSharedSelectedContinuations.CapturedEdge.run checkEmpty r n p h k target scs edge caller before queries =
      some (.complete fragment reached saved after))
    (continued : hook fragment reached saved after = .complete outputs middleCaller middleQueries) :
    run hook checkEmpty r n p h k target scs before (edge :: rest) caller queries =
      match run hook checkEmpty r n p h k target scs before rest middleCaller middleQueries with
      | .complete processed later finalCaller finalQueries =>
          .complete (.complete fragment reached saved after :: processed) (outputs ++ later) finalCaller finalQueries
      | .stopped processed later current =>
          .stopped (.complete fragment reached saved after :: processed) (outputs ++ later) current := by
  simp only [run, observed, continued]

/-- A stopped hook retains its output, reason and receipt without evaluating the sibling. -/
theorem stopped_hook
    (hook : Fragment → Caller width → Queries → Cached → HookResult Output Reason width)
    (checkEmpty : Bool) (r n p h k target : Nat) (scs : List Suspended) (before : Cached)
    (edge : EdgeValue Symbol Constraint) (rest : List (EdgeValue Symbol Constraint))
    (caller reached : Caller width) (queries saved : Queries) (fragment : Fragment) (after : Cached)
    (outputs : List Output) (reason : Reason) (endpoint : Option (Caller width × Queries))
    (observed : SourcePruningEnumerationSharedSelectedContinuations.CapturedEdge.run checkEmpty r n p h k target scs edge caller before queries =
      some (.complete fragment reached saved after))
    (halted : hook fragment reached saved after = .stopped outputs reason endpoint) :
    run hook checkEmpty r n p h k target scs before (edge :: rest) caller queries =
      .stopped [] outputs (.continuation (.complete fragment reached saved after) reason endpoint) := by
  simp only [run, observed, halted]

end MicroCFTA.SourcePruningEnumerationSharedSelectedContinuations.NativeContinuations



namespace MicroCFTA.SourcePruningEnumerationSharedSelectedContinuations.NativeOrdinaryContinuations
open EnumerationState InternedConstructorTemplates
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Fragment" => Fragments.Fragment Symbol
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Queries" => SourceEndpointMemo.Memos
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Raw" => List (Except EnumerationState.Error ((Nat × Nat × List Suspended × Node) ×
  EnumerationState.State Symbol Constraint))
universe u v
variable {width : Nat} {Output : Type u} {Reason : Type v}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]

/-- Enter once and run each completed edge's continuation before its next sibling. -/
noncomputable def run
    (hook : Fragment → Caller width → Queries → Cached →
      SourcePruningEnumerationSharedSelectedContinuations.NativeContinuations.HookResult Output Reason width)
    (checkEmpty : Bool) (r n p h k uv : Nat)
    (edgesOf : Node → List (EdgeValue Symbol Constraint)) (caller : Caller width)
    (before : Cached) (queries : Queries) :
    Raw × Option (SourcePruningEnumerationSharedSelectedContinuations.NativeContinuations.Result Output Reason width) :=
  let raw := ExceptT.run (SourcePruningEnumerationEntry.enter caller.checked.native.machine.heap r uv before.core)
  (raw, match raw with
    | [.ok ((target, _handle, scs, parent@(.node _ _ _ _)), entered)] =>
        if scs.any (fun sc => EqualityTrie.isTerminal sc.trie) then none
        else some (SourcePruningEnumerationSharedSelectedContinuations.NativeContinuations.run hook checkEmpty r n p h k target scs
          (EnumerationExpandableIndex.frame entered before) (edgesOf parent) caller queries)
    | _ => none)

/-- The wrapper retains every actual entry error, rejection and unsupported observation. -/
theorem entry_readback
    (hook : Fragment → Caller width → Queries → Cached →
      SourcePruningEnumerationSharedSelectedContinuations.NativeContinuations.HookResult Output Reason width)
    (checkEmpty : Bool) (r n p h k uv : Nat)
    (edgesOf : Node → List (EdgeValue Symbol Constraint)) (caller : Caller width)
    (before : Cached) (queries : Queries) :
    (run hook checkEmpty r n p h k uv edgesOf caller before queries).1 =
      ExceptT.run (SourcePruningEnumerationEntry.enter caller.checked.native.machine.heap r uv before.core) := rfl

/-- An actual nonterminal ordinary entry supplies the captured input to the hook-aware fold. -/
theorem entered
    (hook : Fragment → Caller width → Queries → Cached →
      SourcePruningEnumerationSharedSelectedContinuations.NativeContinuations.HookResult Output Reason width)
    (checkEmpty : Bool) (r n p h k uv target handle : Nat) (scs : List Suspended)
    (entry : Cache.Interned InternedBinderProtocol.NodeKey) (edges : List (EdgeValue Symbol Constraint))
    (depth : Nat) (free : List InternedBinderProtocol.Reference)
    (edgesOf : Node → List (EdgeValue Symbol Constraint)) (caller : Caller width)
    (before : Cached) (queries : Queries) (after : EnumerationState.State Symbol Constraint)
    (observed : ExceptT.run (SourcePruningEnumerationEntry.enter caller.checked.native.machine.heap r uv before.core) =
      [.ok ((target, handle, scs, .node entry edges depth free), after)])
    (nonterminal : scs.any (fun sc => EqualityTrie.isTerminal sc.trie) = false) :
    run hook checkEmpty r n p h k uv edgesOf caller before queries =
      ([.ok ((target, handle, scs, .node entry edges depth free), after)],
        some (SourcePruningEnumerationSharedSelectedContinuations.NativeContinuations.run hook checkEmpty r n p h k target scs
          (EnumerationExpandableIndex.frame after before) (edgesOf (.node entry edges depth free)) caller queries)) := by
  simp only [run, observed, nonterminal, Bool.false_eq_true, ↓reduceIte]


end MicroCFTA.SourcePruningEnumerationSharedSelectedContinuations.NativeOrdinaryContinuations
