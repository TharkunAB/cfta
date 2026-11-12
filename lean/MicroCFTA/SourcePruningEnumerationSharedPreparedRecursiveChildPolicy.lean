import MicroCFTA.SourcePruningEnumerationSharedPreparedRecursive
import MicroCFTA.SourcePruningEnumerationSharedPreparedChildPolicy

/-!
# Child policy through the actual recursive prepared callbacks

The selected prefix and both recordTypes callbacks retain their existing operations.
Every recursive continuation uses the same child policy and native endpoint.
One common preparation runs at each reached prepared branch.
The shallow specialization preserves the entire old bounded result.
This module does not change the selected-root entry or prove eager completion.
-/
namespace MicroCFTA.SourcePruningEnumerationSharedPreparedRecursiveChildPolicy
open EnumerationState InternedConstructorTemplates
open SourcePruningEnumerationSharedSelectedContinuations
open SourcePruningEnumerationSharedPreparedRecursive (Output Failure finish continueWith)
open SourcePruningEnumerationSharedChildVisitors (shallowVisit)
open SourcePruningEnumerationSharedEagerChildren (eagerChild)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Edge" => EdgeValue Symbol Constraint
local notation "Fragment" => Fragments.Fragment Symbol
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Queries" => SourceEndpointMemo.Memos
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Metadata" => SourcePruningRecordTypes.Metadata
local notation "Core" => EnumerationState.State Symbol Constraint
local notation "Observation" => ChildDispatch.Observation
variable {Typing Key : Type} {width : Nat}
local notation "Result" => NativeContinuations.HookResult (Output width Typing) (Failure width Typing) width
local notation "Fold" => NativeContinuations.Result (Output width Typing) (Failure width Typing) width
local notation "Visitor" => List Suspended → Node → Caller width → Cached → Queries →
  (Fragment → Caller width → Queries → Cached → Fold) →
  (Observation width → Option Cached → Fold) → Fold
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]

/-- Execute the actual selected prefix and pass the same child operation through every restart. -/
noncomputable def resumeWithChild
    (child : Visitor)
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Constraint))
    (stop : Option (Metadata Typing → Nat → Bool))
    (order : Metadata Typing → List Nat → Option Nat) (workFuel : Nat) :
    Nat → Metadata Typing → Caller width → Queries → Cached → Option Next → Result
  | _fuel, metadata, caller, queries, before, none => .complete [⟨some metadata, before, caller, queries⟩] caller queries
  | _fuel, _metadata, caller, queries, before, some .done => .complete [⟨none, before, caller, queries⟩] caller queries
  | _fuel, _metadata, caller, queries, _before, some .stuck => .complete [] caller queries
  | 0, metadata, caller, queries, before, some (.expand uv) =>
      .stopped [] (.exhausted uv metadata before) (some (caller, queries))
  | fuel + 1, metadata, caller, queries, before, some (.expand uv) =>
      let observed := SourcePruningEnumerationSelectedStep.runPrefix holeKey fits admits graph templates
        stop order metadata workFuel workFuel workFuel workFuel workFuel workFuel uv caller before queries
      match observed with
      | .parked _ (some _parked) (some []) => .complete [] caller queries
      | .parked _ (some parked) (some [.ok ((updated, next), core)]) =>
          resumeWithChild child holeKey fits admits graph templates checkEmpty edgesOf stop order workFuel fuel
            updated caller queries (EnumerationExpandableIndex.frame core parked) next
      | .narrowed _ _ reached saved (some []) _ _ _ => .complete [] reached saved
      | .narrowed _ _ reached saved _ _ (some [.ok ((true, _updated), _core)]) _ =>
          .complete [] reached saved
      | .narrowed _ _ reached saved _ (some after) (some [.ok ((false, updated), _core)]) none =>
          let prepared := SourcePruningEnumerationSharedPreparedChildPolicy.runWithChild child
            (continueWith (resumeWithChild child holeKey fits admits graph templates checkEmpty edgesOf stop order workFuel fuel)
              graph templates stop order workFuel updated uv)
            checkEmpty workFuel workFuel workFuel workFuel workFuel workFuel workFuel uv edgesOf reached after saved
          match prepared.2 with
          | none => .stopped [] (.preparation uv prepared.1)
              (some (SourcePruningEnumerationSharedPreparedContinuations.preparation_endpoint reached saved prepared.1))
          | some folded => finish uv folded
      | .narrowed _ _ reached saved _ _ _ _ => .stopped [] (.selected uv observed) (some (reached, saved))
      | _ => .stopped [] (.selected uv observed) (some (caller, queries))

/-- Start the child-policy worker at the same actual metadata and selection decision. -/
noncomputable def runWithChild
    (child : Visitor)
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (checkEmpty : Bool) (edgesOf : Node → List Edge)
    (stop : Option (Metadata Typing → Nat → Bool))
    (order : Metadata Typing → List Nat → Option Nat) (workFuel recursiveFuel : Nat)
    (metadata : Metadata Typing) (caller : Caller width) (queries : Queries) (before : Cached) : Result :=
  resumeWithChild child holeKey fits admits graph templates checkEmpty edgesOf stop order workFuel recursiveFuel
    metadata caller queries before (SourcePruningEnumerationRestart.decision stop order metadata before)

/-- Install eager children while retaining the existing outer recursive budget and callbacks. -/
noncomputable def runEager
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (checkEmpty : Bool) (edgesOf : Node → List Edge)
    (stop : Option (Metadata Typing → Nat → Bool))
    (order : Metadata Typing → List Nat → Option Nat) (workFuel recursiveFuel : Nat)
    (metadata : Metadata Typing) (caller : Caller width) (queries : Queries) (before : Cached) : Result :=
  runWithChild (eagerChild checkEmpty workFuel workFuel workFuel workFuel workFuel edgesOf)
    holeKey fits admits graph templates checkEmpty edgesOf stop order workFuel recursiveFuel metadata caller queries before

/-- At every depth and decision, the shallow child policy returns the entire old result. -/
theorem resumeWithChild_shallow
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (checkEmpty : Bool) (edgesOf : Node → List Edge)
    (stop : Option (Metadata Typing → Nat → Bool))
    (order : Metadata Typing → List Nat → Option Nat) (workFuel recursiveFuel : Nat)
    (metadata : Metadata Typing) (caller : Caller width) (queries : Queries) (before : Cached)
    (decision : Option Next) :
    resumeWithChild (shallowVisit checkEmpty workFuel workFuel workFuel workFuel workFuel)
        holeKey fits admits graph templates checkEmpty edgesOf stop order workFuel recursiveFuel
        metadata caller queries before decision =
      SourcePruningEnumerationSharedPreparedRecursive.resume holeKey fits admits graph templates
        checkEmpty edgesOf stop order workFuel recursiveFuel metadata caller queries before decision := by
  induction recursiveFuel generalizing metadata caller queries before decision with
  | zero =>
      cases decision with
      | none => rfl
      | some next => cases next <;> rfl
  | succ fuel ih =>
      have recurSame :
          resumeWithChild (width := width) (shallowVisit checkEmpty workFuel workFuel workFuel workFuel workFuel)
              holeKey fits admits graph templates checkEmpty edgesOf stop order workFuel fuel =
            SourcePruningEnumerationSharedPreparedRecursive.resume (width := width) holeKey fits admits graph templates
              checkEmpty edgesOf stop order workFuel fuel := by
        funext nextMetadata nextCaller nextQueries nextCache nextDecision
        exact ih nextMetadata nextCaller nextQueries nextCache nextDecision
      cases decision with
      | none => rfl
      | some next =>
          cases next with
          | done | stuck => rfl
          | expand uv =>
              rw [resumeWithChild, SourcePruningEnumerationSharedPreparedRecursive.resume]
              simp only [recurSame, SourcePruningEnumerationSharedPreparedChildPolicy.runWithChild_shallow] <;> rfl

/-- The shallow policy preserves the entire old driver observation at the same entry. -/
theorem runWithChild_shallow
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (checkEmpty : Bool) (edgesOf : Node → List Edge)
    (stop : Option (Metadata Typing → Nat → Bool))
    (order : Metadata Typing → List Nat → Option Nat) (workFuel recursiveFuel : Nat)
    (metadata : Metadata Typing) (caller : Caller width) (queries : Queries) (before : Cached) :
    runWithChild (shallowVisit checkEmpty workFuel workFuel workFuel workFuel workFuel)
        holeKey fits admits graph templates checkEmpty edgesOf stop order workFuel recursiveFuel
        metadata caller queries before =
      SourcePruningEnumerationSharedPreparedRecursive.run holeKey fits admits graph templates
        checkEmpty edgesOf stop order workFuel recursiveFuel metadata caller queries before := by
  unfold runWithChild SourcePruningEnumerationSharedPreparedRecursive.run
  exact resumeWithChild_shallow holeKey fits admits graph templates checkEmpty edgesOf stop order
    workFuel recursiveFuel metadata caller queries before (SourcePruningEnumerationRestart.decision stop order metadata before)

/-- Zero outer depth retains the exact current decision, metadata, cache and native endpoint. -/
theorem resume_zero
    (child : Visitor)
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (checkEmpty : Bool) (edgesOf : Node → List Edge)
    (stop : Option (Metadata Typing → Nat → Bool))
    (order : Metadata Typing → List Nat → Option Nat) (workFuel : Nat)
    (metadata : Metadata Typing) (caller : Caller width) (queries : Queries) (before : Cached)
    (decision : Option Next) :
    resumeWithChild child holeKey fits admits graph templates checkEmpty edgesOf stop order workFuel 0
      metadata caller queries before decision =
      match decision with
      | none => .complete [⟨some metadata, before, caller, queries⟩] caller queries
      | some .done => .complete [⟨none, before, caller, queries⟩] caller queries
      | some .stuck => .complete [] caller queries
      | some (.expand uv) => .stopped [] (.exhausted uv metadata before) (some (caller, queries)) := by
  cases decision with
  | none => rfl
  | some next => cases next <;> rfl

/-- The actual continuing Right receipt invokes one common preparation with the same child policy. -/
theorem resume_prepared
    (child : Visitor)
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (checkEmpty : Bool) (edgesOf : Node → List Edge)
    (stop : Option (Metadata Typing → Nat → Bool))
    (order : Metadata Typing → List Nat → Option Nat) (workFuel fuel uv : Nat)
    (metadata updated : Metadata Typing) (caller reached : Caller width) (queries saved : Queries)
    (before after : Cached) (checked core : Core)
    (narrowed : MergedSourceComparison.Result Symbol Constraint (Node × Option (EnumerateM Symbol Constraint Unit)))
    (actionCore : Core)
    (observedPrefix : SourcePruningEnumerationSelectedStep.runPrefix holeKey fits admits graph templates stop order
      metadata workFuel workFuel workFuel workFuel workFuel workFuel uv caller before queries =
      .narrowed checked narrowed reached saved (some [.ok ((), actionCore)]) (some after)
        (some [.ok ((false, updated), core)]) none) :
    resumeWithChild child holeKey fits admits graph templates checkEmpty edgesOf stop order workFuel (fuel + 1)
      metadata caller queries before (some (.expand uv)) =
      let prepared := SourcePruningEnumerationSharedPreparedChildPolicy.runWithChild child
        (continueWith (resumeWithChild child holeKey fits admits graph templates checkEmpty edgesOf stop order workFuel fuel)
          graph templates stop order workFuel updated uv)
        checkEmpty workFuel workFuel workFuel workFuel workFuel workFuel workFuel uv edgesOf reached after saved
      match prepared.2 with
      | none => .stopped [] (.preparation uv prepared.1)
          (some (SourcePruningEnumerationSharedPreparedContinuations.preparation_endpoint reached saved prepared.1))
      | some folded => finish uv folded := by
  simp only [resumeWithChild, observedPrefix]

end MicroCFTA.SourcePruningEnumerationSharedPreparedRecursiveChildPolicy
