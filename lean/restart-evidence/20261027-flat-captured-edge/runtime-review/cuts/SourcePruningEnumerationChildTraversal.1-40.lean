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
