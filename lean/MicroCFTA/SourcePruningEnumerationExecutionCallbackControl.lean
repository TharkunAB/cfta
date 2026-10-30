import MicroCFTA.SourcePruningEnumerationExecutionPaths
import MicroCFTA.SourcePruningEnumerationPathRecordingValues

/-!
# Paths through the literal recursive callback

The singleton observation fixes the actual framed recursive input.
The result retains paths even when the callback emits no output.
-/
namespace MicroCFTA.SourcePruningEnumerationExecutionCallbackControl
open EnumerationState InternedConstructorTemplates
open SourcePruningEnumerationPathTransport (StatePaths)
open SourcePruningEnumerationPathSelectedRaw (RawPaths)
open SourcePruningEnumerationExecutionPathData
open SourcePruningEnumerationExecutionPaths
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
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]

/-- An actual recursive execution retains its literal outcome paths. -/
theorem resume_native_outcome (P : EqualityTrie.Path → Prop)
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Constraint))
    (stop : Option (Metadata Typing → Nat → Bool))
    (order : Metadata Typing → List Nat → Option Nat) (workFuel recursiveFuel : Nat)
    (metadata : Metadata Typing) (caller : Caller width) (queries : Queries) (before : Cached)
    (next : Option Next)
    (paths : ResumeNative P holeKey fits admits graph templates checkEmpty edgesOf stop order workFuel recursiveFuel metadata caller queries before next) :
    OutcomePaths P (NativeFailurePaths P)
      (SourcePruningEnumerationRecursive.resume holeKey fits admits graph templates checkEmpty edgesOf stop order workFuel recursiveFuel metadata caller queries before next) := by
  cases recursiveFuel with
  | zero => exact paths.2
  | succ fuel => exact paths.2.1

/-- An actual recursive execution retains its literal outcome paths. -/
theorem resume_prepared_outcome (P : EqualityTrie.Path → Prop)
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Constraint))
    (stop : Option (Metadata Typing → Nat → Bool))
    (order : Metadata Typing → List Nat → Option Nat) (workFuel recursiveFuel : Nat)
    (metadata : Metadata Typing) (caller : Caller width) (queries : Queries) (before : Cached)
    (next : Option Next)
    (paths : ResumePrepared P holeKey fits admits graph templates checkEmpty edgesOf stop order workFuel recursiveFuel metadata caller queries before next) :
    OutcomePaths P (PreparedFailurePaths P)
      (SourcePruningEnumerationPreparedRecursive.resume holeKey fits admits graph templates checkEmpty edgesOf stop order workFuel recursiveFuel metadata caller queries before next) := by
  cases recursiveFuel with
  | zero => exact paths.2
  | succ fuel => exact paths.2.1

/-- The actual singleton callback carries the same paths into its literal false continuation. -/
theorem native_left_of_singleton (P : EqualityTrie.Path → Prop)
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Constraint))
    (stop : Option (Metadata Typing → Nat → Bool))
    (order : Metadata Typing → List Nat → Option Nat) (workFuel recursiveFuel : Nat)
    (metadata : Metadata Typing) (uv : Nat) (fragment : Fragment)
    (caller : Caller width) (queries : Queries) (before : Cached)
    (result : Bool × Metadata Typing) (after : Core)
    (paths : StatePaths P before.core)
    (observed : ExceptT.run (SourcePruningRecordTypes.recordTypes
      graph templates workFuel metadata uv (.inl fragment) before.core) = [.ok (result, after)])
    (nested : result.1 = false → Native P holeKey fits admits graph templates checkEmpty edgesOf stop order workFuel recursiveFuel
      result.2 caller queries (EnumerationExpandableIndex.frame after before)) :
    LeftPaths P (ResumeNative P holeKey fits admits graph templates checkEmpty edgesOf stop order workFuel recursiveFuel) (NativeFailurePaths P)
      (SourcePruningEnumerationRecursive.continueWith (SourcePruningEnumerationRecursive.resume holeKey fits admits graph templates checkEmpty edgesOf stop order workFuel recursiveFuel)
        graph templates stop order workFuel metadata uv)
      graph templates stop order workFuel metadata uv fragment caller queries before := by
  refine ⟨paths, ?_, ?_, ?_⟩
  · intro actual core member
    exact SourcePruningEnumerationPathRecordingValues.recordTypes_paths
      graph templates workFuel metadata uv (.inl fragment) before.core core actual paths member
  · cases result with
    | mk keep updated =>
        cases keep with
        | false =>
            rw [SourcePruningEnumerationRecursive.continueWith, observed]
            exact resume_native_outcome P holeKey fits admits graph templates checkEmpty edgesOf stop order workFuel recursiveFuel updated caller queries
              (EnumerationExpandableIndex.frame after before)
              (SourcePruningEnumerationRestart.decision stop order updated
                (EnumerationExpandableIndex.frame after before)) (nested rfl)
        | true =>
            rw [SourcePruningEnumerationRecursive.continueWith, observed]
            intro output member
            cases member
  · intro updated core seen
    have rowSame := (List.cons.inj (observed.symm.trans seen)).1
    have pairSame := Prod.mk.inj (Except.ok.inj rowSame)
    rcases pairSame with ⟨rfl, rfl⟩
    exact nested rfl

/-- The actual singleton callback carries the same paths into its literal false continuation. -/
theorem prepared_left_of_singleton (P : EqualityTrie.Path → Prop)
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Constraint))
    (stop : Option (Metadata Typing → Nat → Bool))
    (order : Metadata Typing → List Nat → Option Nat) (workFuel recursiveFuel : Nat)
    (metadata : Metadata Typing) (uv : Nat) (fragment : Fragment)
    (caller : Caller width) (queries : Queries) (before : Cached)
    (result : Bool × Metadata Typing) (after : Core)
    (paths : StatePaths P before.core)
    (observed : ExceptT.run (SourcePruningRecordTypes.recordTypes
      graph templates workFuel metadata uv (.inl fragment) before.core) = [.ok (result, after)])
    (nested : result.1 = false → Prepared P holeKey fits admits graph templates checkEmpty edgesOf stop order workFuel recursiveFuel
      result.2 caller queries (EnumerationExpandableIndex.frame after before)) :
    LeftPaths P (ResumePrepared P holeKey fits admits graph templates checkEmpty edgesOf stop order workFuel recursiveFuel) (PreparedFailurePaths P)
      (SourcePruningEnumerationPreparedRecursive.continueWith (SourcePruningEnumerationPreparedRecursive.resume holeKey fits admits graph templates checkEmpty edgesOf stop order workFuel recursiveFuel)
        graph templates stop order workFuel metadata uv)
      graph templates stop order workFuel metadata uv fragment caller queries before := by
  refine ⟨paths, ?_, ?_, ?_⟩
  · intro actual core member
    exact SourcePruningEnumerationPathRecordingValues.recordTypes_paths
      graph templates workFuel metadata uv (.inl fragment) before.core core actual paths member
  · cases result with
    | mk keep updated =>
        cases keep with
        | false =>
            rw [SourcePruningEnumerationPreparedRecursive.continueWith, observed]
            exact resume_prepared_outcome P holeKey fits admits graph templates checkEmpty edgesOf stop order workFuel recursiveFuel updated caller queries
              (EnumerationExpandableIndex.frame after before)
              (SourcePruningEnumerationRestart.decision stop order updated
                (EnumerationExpandableIndex.frame after before)) (nested rfl)
        | true =>
            rw [SourcePruningEnumerationPreparedRecursive.continueWith, observed]
            intro output member
            cases member
  · intro updated core seen
    have rowSame := (List.cons.inj (observed.symm.trans seen)).1
    have pairSame := Prod.mk.inj (Except.ok.inj rowSame)
    rcases pairSame with ⟨rfl, rfl⟩
    exact nested rfl

end MicroCFTA.SourcePruningEnumerationExecutionCallbackControl
