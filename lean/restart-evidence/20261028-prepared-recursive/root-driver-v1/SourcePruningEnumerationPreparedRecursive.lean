import MicroCFTA.SourcePruningEnumerationSelectedStep
import MicroCFTA.SourcePruningEnumerationSelectedContinuations

namespace MicroCFTA.SourcePruningEnumerationPreparedRecursive
open EnumerationState InternedConstructorTemplates
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Fragment" => Fragments.Fragment Symbol
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Queries" => SourceEndpointMemo.Memos
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Metadata" => SourcePruningRecordTypes.Metadata
local notation "Core" => EnumerationState.State Symbol Constraint
local notation "Receipt" => SourcePruningEnumerationSelectedEdge.Result
local notation "Fold" => SourcePruningEnumerationNativeContinuations.Result
local notation "FoldStop" => SourcePruningEnumerationNativeContinuations.Stop
local notation "HookResult" => SourcePruningEnumerationNativeContinuations.HookResult
local notation "EntryRaw" => List (Except EnumerationState.Error ((Nat × Nat × List Suspended × Node) × Core))
local notation "Output" => SourcePruningEnumerationRecursive.Output
local notation "Preparation" => EntryRaw × Option (MergedSourceComparison.Result Symbol Constraint Node)
local notation "CallbackRaw" => fun Typing => List (Except EnumerationState.Error ((Bool × Metadata Typing) × Core))

/-- Retain the exact bounded or unsupported observation that prevents continuation. -/
inductive Failure (width : Nat) (Typing : Type) : Type 1 where
  /-- The recursive budget does not permit the selected expansion. -/
  | exhausted (uv : Nat) (metadata : Metadata Typing) (before : Cached)
  /-- The actual selected prefix cannot supply a supported continuation. -/
  | selected (uv : Nat) (observed : SourcePruningEnumerationSelectedStep.Result width Typing)
  /-- The actual fragment callback does not return a singleton success. -/
  | callback (uv : Nat) (raw : CallbackRaw Typing)
  /-- Preparation retains its complete entry and native result, including a fault heap. -/
  | preparation (uv : Nat) (raw : Preparation)
  /-- Retain the processed alternatives and their exact edge or recursive stop. -/
  | alternatives (uv : Nat) (processed : List (Receipt width))
      (current : FoldStop (Failure width Typing) width)

variable {Typing Key : Type} {width : Nat}
local notation "Result" => HookResult (Output width Typing) (Failure width Typing) width

/-- Read only a native endpoint supplied by the actual stopped receipt. -/
def endpoint : FoldStop (Failure width Typing) width → Option (Caller width × Queries)
  | .edge current => current.bind SourcePruningEnumerationNativeBranches.advance
  | .continuation _ _ reached => reached

/-- Convert the ordered alternative result without losing its outputs or stopped receipts. -/
def finish (uv : Nat) : Fold (Output width Typing) (Failure width Typing) width → Result
  | .complete _processed outputs caller queries => .complete outputs caller queries
  | .stopped processed outputs current =>
      .stopped outputs (.alternatives uv processed current) (endpoint current)

/-- Run the concrete Left callback once before its own recursive continuation. -/
noncomputable def continueWith
    (recur : Metadata Typing → Caller width → Queries → Cached → Option Next → Result)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (stop : Option (Metadata Typing → Nat → Bool))
    (order : Metadata Typing → List Nat → Option Nat)
    (callbackFuel : Nat) (metadata : Metadata Typing) (uv : Nat)
    (fragment : Fragment) (caller : Caller width) (queries : Queries) (before : Cached) : Result :=
  let raw := ExceptT.run (SourcePruningRecordTypes.recordTypes
    graph templates callbackFuel metadata uv (.inl fragment) before.core)
  match raw with
  | [.ok ((true, _updated), _observed)] => .complete [] caller queries
  | [.ok ((false, updated), observed)] =>
      let after := EnumerationExpandableIndex.frame observed before
      recur updated caller queries after (SourcePruningEnumerationRestart.decision stop order updated after)
  | _ => .stopped [] (.callback uv raw) (some (caller, queries))

variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]

/-- Prepare the selected value once before its actual recursive continuations.
Each sibling retains the captured metadata and enumeration input. Recursive native effects reach
the next sibling. This bounded worker does not establish whole-driver completion or language semantics. -/
noncomputable def resume
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
          resume holeKey fits admits graph templates checkEmpty edgesOf stop order workFuel fuel
            updated caller queries (EnumerationExpandableIndex.frame core parked) next
      | .narrowed _ _ reached saved (some []) _ _ _ => .complete [] reached saved
      | .narrowed _ _ reached saved _ _ (some [.ok ((true, _updated), _core)]) _ =>
          .complete [] reached saved
      | .narrowed _ _ reached saved _ (some after) (some [.ok ((false, updated), _core)]) none =>
          let prepared := SourcePruningEnumerationSelectedContinuations.run
            (continueWith (resume holeKey fits admits graph templates checkEmpty edgesOf stop order workFuel fuel)
              graph templates stop order workFuel updated uv)
            checkEmpty workFuel workFuel workFuel workFuel workFuel workFuel workFuel uv edgesOf reached after saved
          match prepared.2 with
          | none => .stopped [] (.preparation uv prepared.1) none
          | some folded => finish uv folded
      | .narrowed _ _ reached saved _ _ _ _ => .stopped [] (.selected uv observed) (some (reached, saved))
      | _ => .stopped [] (.selected uv observed) (some (caller, queries))

/-- Start from the source stop test and next selection at the supplied metadata and cache. -/
noncomputable def run
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Constraint))
    (stop : Option (Metadata Typing → Nat → Bool))
    (order : Metadata Typing → List Nat → Option Nat) (workFuel recursiveFuel : Nat)
    (metadata : Metadata Typing) (caller : Caller width) (queries : Queries) (before : Cached) : Result :=
  resume holeKey fits admits graph templates checkEmpty edgesOf stop order workFuel recursiveFuel
    metadata caller queries before (SourcePruningEnumerationRestart.decision stop order metadata before)

end MicroCFTA.SourcePruningEnumerationPreparedRecursive
