import MicroCFTA.SourcePruningEnumerationRecursive
import MicroCFTA.SourcePruningCallbackExact

namespace MicroCFTA.SourcePruningEnumerationRecursive
open EnumerationState EnumerationCorrectness InternedConstructorTemplates
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Fragment" => Fragments.Fragment Symbol
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Queries" => SourceEndpointMemo.Memos
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Metadata" => SourcePruningRecordTypes.Metadata
local notation "Core" => EnumerationState.State Symbol Constraint
variable {Typing Key : Type} {width : Nat}
local notation "Result" => SourcePruningEnumerationNativeContinuations.HookResult
  (Output width Typing) (Failure width Typing) width

/-- A genuine successful callback determines the entire concrete continuation, without extra error rows. -/
theorem continueWith_exact
    (recur : Metadata Typing → Caller width → Queries → Cached → Option Next → Result)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (stop : Option (Metadata Typing → Nat → Bool))
    (order : Metadata Typing → List Nat → Option Nat)
    (callbackFuel : Nat) (metadata : Metadata Typing) (uv : Nat)
    (fragment : Fragment) (caller : Caller width) (queries : Queries) (before : Cached)
    (result : Bool × Metadata Typing) (observed : Core)
    (callback : Success (SourcePruningRecordTypes.recordTypes graph templates callbackFuel metadata uv (.inl fragment))
      before.core result observed) :
    continueWith recur graph templates stop order callbackFuel metadata uv fragment caller queries before =
      if result.1 then .complete [] caller queries
      else recur result.2 caller queries (EnumerationExpandableIndex.frame observed before)
        (SourcePruningEnumerationRestart.decision stop order result.2
          (EnumerationExpandableIndex.frame observed before)) := by
  have exactRaw := SourcePruningCallbackExact.recordTypes_exact graph templates callbackFuel metadata uv
    (.inl fragment) before.core observed result callback
  unfold continueWith
  rw [exactRaw]
  obtain ⟨flag, updated⟩ := result
  cases flag <;> rfl

variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]
variable (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
variable (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
variable (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Constraint))
variable (stop : Option (Metadata Typing → Nat → Bool))
variable (order : Metadata Typing → List Nat → Option Nat) (workFuel recursiveFuel : Nat)
variable (metadata : Metadata Typing) (caller : Caller width) (queries : Queries) (before : Cached)

/-- A stop decision retains its metadata and exact cache without spending recursive fuel. -/
theorem resume_stop :
    resume holeKey fits admits graph templates checkEmpty edgesOf stop order workFuel recursiveFuel
      metadata caller queries before none = .complete [⟨some metadata, before, caller, queries⟩] caller queries := by
  cases recursiveFuel <;> rfl

/-- Exhausted candidate selection returns the source Nothing result and exact cache. -/
theorem resume_done :
    resume holeKey fits admits graph templates checkEmpty edgesOf stop order workFuel recursiveFuel
      metadata caller queries before (some .done) = .complete [⟨none, before, caller, queries⟩] caller queries := by
  cases recursiveFuel <;> rfl

/-- Blocked work rejects this branch without changing its native endpoint. -/
theorem resume_stuck :
    resume holeKey fits admits graph templates checkEmpty edgesOf stop order workFuel recursiveFuel
      metadata caller queries before (some .stuck) = .complete [] caller queries := by
  cases recursiveFuel <;> rfl

/-- Insufficient recursive fuel is an explicit stop, rather than successful branch rejection. -/
theorem resume_exhausted (uv : Nat) :
    resume holeKey fits admits graph templates checkEmpty edgesOf stop order workFuel 0
      metadata caller queries before (some (.expand uv)) =
      .stopped [] (.exhausted uv metadata before) (some (caller, queries)) := rfl

/-- Repeated recursion consumes the exact indexed restart observation without repeating the prefix. -/
theorem resume_parked
    (uv : Nat) (checked core : Core) (parked : Cached) (updated : Metadata Typing) (next : Option Next)
    (observed : SourcePruningEnumerationSelectedStep.runPrefix holeKey fits admits graph templates stop order
      metadata workFuel workFuel workFuel workFuel workFuel workFuel uv caller before queries =
      .parked checked (some parked) (some [.ok ((updated, next), core)])) :
    resume holeKey fits admits graph templates checkEmpty edgesOf stop order workFuel (recursiveFuel + 1)
      metadata caller queries before (some (.expand uv)) =
      resume holeKey fits admits graph templates checkEmpty edgesOf stop order workFuel recursiveFuel
        updated caller queries (EnumerationExpandableIndex.frame core parked) next := by
  rw [resume, observed]

/-- A concrete callback and its completed recursion supply the native endpoint for the next sibling. -/
theorem completed_head
    (uv target r n p h k : Nat) (scs : List Suspended)
    (edge : EdgeValue Symbol Constraint) (rest : List (EdgeValue Symbol Constraint))
    (fragment : Fragment) (reached middleCaller : Caller width) (saved middleQueries : Queries)
    (after : Cached) (callbackCore : Core) (updated : Metadata Typing)
    (outputs : List (Output width Typing))
    (head : SourcePruningEnumerationCapturedEdge.run checkEmpty r n p h k target scs edge caller before queries =
      some (.complete fragment reached saved after))
    (callback : Success (SourcePruningRecordTypes.recordTypes graph templates workFuel metadata uv (.inl fragment))
      after.core (false, updated) callbackCore)
    (continued : resume holeKey fits admits graph templates checkEmpty edgesOf stop order workFuel recursiveFuel
      updated reached saved (EnumerationExpandableIndex.frame callbackCore after)
      (SourcePruningEnumerationRestart.decision stop order updated
        (EnumerationExpandableIndex.frame callbackCore after)) = .complete outputs middleCaller middleQueries) :
    let hook := continueWith
      (resume holeKey fits admits graph templates checkEmpty edgesOf stop order workFuel recursiveFuel)
      graph templates stop order workFuel metadata uv
    SourcePruningEnumerationNativeContinuations.run hook checkEmpty r n p h k target scs before
      (edge :: rest) caller queries =
      match SourcePruningEnumerationNativeContinuations.run hook checkEmpty r n p h k target scs before
        rest middleCaller middleQueries with
      | .complete processed later finalCaller finalQueries =>
          .complete (.complete fragment reached saved after :: processed) (outputs ++ later) finalCaller finalQueries
      | .stopped processed later current =>
          .stopped (.complete fragment reached saved after :: processed) (outputs ++ later) current := by
  apply SourcePruningEnumerationNativeContinuations.completed_head _ checkEmpty r n p h k target scs before
    edge rest caller reached middleCaller queries saved middleQueries fragment after outputs head
  rw [continueWith_exact _ graph templates stop order workFuel metadata uv fragment reached saved after
    (false, updated) callbackCore callback]
  exact continued

end MicroCFTA.SourcePruningEnumerationRecursive
