import MicroCFTA.SourceFlatPruningChildDispatch
import MicroCFTA.SourcePruningEnumerationChildTraversal

/-!
# Actual ordered children with direct-parent forests

Every successful singleton supplies its actual recovered cache to the suffix.
The first other observation stops the traversal and retains its completed prefix.
-/

namespace MicroCFTA.SourceFlatPruningChildTraversal

open EnumerationState InternedConstructorTemplates
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Queries" => SourceEndpointMemo.Memos
local notation "Cached" => EnumerationFlatCached.Cached Symbol Constraint
local notation "Fragment" => Fragments.Fragment Symbol
variable {width : Nat}

/-- Keep the complete child list or its first actual stopping receipt. -/
inductive Result (width : Nat) where
  /-- Every child returns a singleton and a recovered cache. -/
  | complete (fragments : List Fragment) (caller : Caller width) (queries : Queries) (after : Cached)
  /-- Keep the completed prefix and the exact first stopping observation. -/
  | stopped (completedPrefix : List Fragment)
      (observation : SourceFlatPruningChildDispatch.Observation width) (candidate : Option Cached)

variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]

/-- Execute each child at the actual caller, saved queries and recovered cache. -/
noncomputable def run (checkEmpty : Bool) (nativeFuel p h : Nat) :
    List (Node × List Suspended) → Caller width → Cached → Queries → Result width
  | [], caller, before, queries => .complete [] caller queries before
  | (value, bucket) :: rest, caller, before, queries =>
      match SourceFlatPruningChildDispatch.run checkEmpty nativeFuel p h bucket value caller before queries with
      | ((.ok (some [.ok (fragment, _returned)]), reached, saved, _outer, _waiting), some after) =>
          match run checkEmpty nativeFuel p h rest reached after saved with
          | .complete fragments finalCaller finalQueries final =>
              .complete (fragment :: fragments) finalCaller finalQueries final
          | .stopped prefix observation candidate => .stopped (fragment :: prefix) observation candidate
      | (observation, candidate) => .stopped [] observation candidate

/-- Keep fragments, native endpoints, raw diagnostics and cache correspondence. -/
def ResultRelated (flat : Result width) (earlier : SourcePruningEnumerationChildTraversal.Result width) : Prop :=
  match flat, earlier with
  | .complete fragments caller queries after, .complete oldFragments oldCaller oldQueries oldAfter =>
      fragments = oldFragments ∧ caller = oldCaller ∧ queries = oldQueries ∧
        EnumerationFlatCached.Related after oldAfter
  | .stopped prefix observation candidate, .stopped oldPrefix oldObservation oldCandidate =>
      prefix = oldPrefix ∧ SourceFlatPruningChildDispatch.ResultRelated
        (observation, candidate) (oldObservation, oldCandidate)
  | _, _ => False

end MicroCFTA.SourceFlatPruningChildTraversal
