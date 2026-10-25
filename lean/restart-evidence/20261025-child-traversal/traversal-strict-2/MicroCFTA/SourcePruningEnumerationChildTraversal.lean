import MicroCFTA.SourcePruningEnumerationChildEffects

namespace MicroCFTA.SourcePruningEnumerationChildTraversal
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
  | stopped (completedPrefix : List Fragment) (observation : SourcePruningEnumerationChildDispatch.Observation width)
      (candidate : Option Cached)

variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]

/-- Run children in order with the reached caller, queries and post-write cache. -/
noncomputable def run
    (checkEmpty : Bool) (representativeFuel nativeFuel p h indexFuel : Nat) :
    List (Node × List Suspended) → Caller width → Cached → Queries → Result width
  | [], caller, before, queries => .complete [] caller queries before
  | (value, bucket) :: rest, caller, before, queries =>
      match SourcePruningEnumerationChildDispatch.run checkEmpty representativeFuel nativeFuel p h indexFuel
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
      (head : SourcePruningEnumerationChildDispatch.run checkEmpty representativeFuel nativeFuel p h indexFuel
        bucket value beforeCaller before queries =
        ((.ok (some [.ok (fragment, middle.core)]), middleCaller, middleQueries, outer, waiting), some middle))
      (tail : Trace checkEmpty representativeFuel nativeFuel p h indexFuel rest middleCaller middle middleQueries
        fragments afterCaller after afterQueries) :
      Trace checkEmpty representativeFuel nativeFuel p h indexFuel ((value, bucket) :: rest)
        beforeCaller before queries (fragment :: fragments) afterCaller after afterQueries

/-- Every recorded native trace completes through the same ordered traversal. -/
theorem Trace.run
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
    cases headEq : SourcePruningEnumerationChildDispatch.run checkEmpty representativeFuel nativeFuel p h indexFuel
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
                  have coreSame := SourcePruningEnumerationChildDispatch.singleton_core checkEmpty
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

end MicroCFTA.SourcePruningEnumerationChildTraversal
