import MicroCFTA.SourcePruningEnumerationExecutionPathData
import MicroCFTA.SourcePruningEnumerationHookInvocation

/-!
# Paths through actual recursive executions

The predicates retain local observations, processed receipts, and literal
hook calls. Each recursive obligation uses the actual smaller-depth call.
These definitions do not establish an execution invariant or sufficient depth.
-/
namespace MicroCFTA.SourcePruningEnumerationExecutionPaths
open EnumerationState InternedConstructorTemplates
open SourcePruningEnumerationPathTransport (StatePaths)
open SourcePruningEnumerationPathSelectedRaw (RawPaths SelectedPrefixPaths)
open SourcePruningEnumerationExecutionPathData
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Fragment" => Fragments.Fragment Symbol
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Queries" => SourceEndpointMemo.Memos
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Metadata" => SourcePruningRecordTypes.Metadata
local notation "Output" => SourcePruningEnumerationRecursive.Output
local notation "Hook" => SourcePruningEnumerationNativeContinuations.HookResult
universe v
variable {Typing Key : Type} {width : Nat} {Reason : Type v}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]

/-- The actual Left callback retains every row and its literal false continuation. -/
noncomputable def LeftPaths (P : EqualityTrie.Path → Prop)
    (nextPaths : Metadata Typing → Caller width → Queries → Cached → Option Next → Prop)
    (reasonPaths : Reason → Prop)
    (hook : Fragment → Caller width → Queries → Cached → Hook (Output width Typing) Reason width)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (stop : Option (Metadata Typing → Nat → Bool))
    (order : Metadata Typing → List Nat → Option Nat) (workFuel : Nat)
    (metadata : Metadata Typing) (uv : Nat) (fragment : Fragment)
    (caller : Caller width) (queries : Queries) (before : Cached) : Prop :=
  let raw := ExceptT.run (SourcePruningRecordTypes.recordTypes
    graph templates workFuel metadata uv (.inl fragment) before.core)
  StatePaths P before.core ∧ RawPaths P raw ∧ OutcomePaths P reasonPaths (hook fragment caller queries before) ∧
    ∀ updated observed, raw = [.ok ((false, updated), observed)] →
      let after := EnumerationExpandableIndex.frame observed before
      nextPaths updated caller queries after (SourcePruningEnumerationRestart.decision stop order updated after)

/-- The fold retains processed data and every actual hook input in sibling order. -/
noncomputable def SiblingPaths (P : EqualityTrie.Path → Prop)
    (nextPaths : Metadata Typing → Caller width → Queries → Cached → Option Next → Prop)
    (reasonPaths : Reason → Prop)
    (hook : Fragment → Caller width → Queries → Cached → Hook (Output width Typing) Reason width)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (stop : Option (Metadata Typing → Nat → Bool))
    (order : Metadata Typing → List Nat → Option Nat) (checkEmpty : Bool) (workFuel : Nat)
    (metadata : Metadata Typing) (recordUV target : Nat) (scs : List Suspended) (before : Cached)
    (edges : List (EdgeValue Symbol Constraint)) (caller : Caller width) (queries : Queries) : Prop :=
  FoldPaths P reasonPaths (SourcePruningEnumerationNativeContinuations.run hook checkEmpty
    workFuel workFuel workFuel workFuel workFuel target scs before edges caller queries) ∧
    ∀ fragment reached saved after,
      SourcePruningEnumerationHookInvocation.Invocation hook checkEmpty
        workFuel workFuel workFuel workFuel workFuel target scs before edges caller queries
        fragment reached saved after →
      LeftPaths P nextPaths reasonPaths hook graph templates stop order workFuel metadata recordUV
        fragment reached saved after

/-- Opaque and terminal dispatch retain their receipt and its literal complete hook. -/
noncomputable def OpaquePaths (P : EqualityTrie.Path → Prop)
    (nextPaths : Metadata Typing → Caller width → Queries → Cached → Option Next → Prop)
    (reasonPaths : Reason → Prop)
    (hook : Fragment → Caller width → Queries → Cached → Hook (Output width Typing) Reason width)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (stop : Option (Metadata Typing → Nat → Bool))
    (order : Metadata Typing → List Nat → Option Nat) (checkEmpty : Bool) (workFuel : Nat)
    (metadata : Metadata Typing) (recordUV target : Nat) (scs : List Suspended) (value : Node)
    (caller : Caller width) (before : Cached) (queries : Queries) : Prop :=
  let receipt := SourcePruningEnumerationSelectedOpaqueDispatch.run checkEmpty
    workFuel workFuel workFuel workFuel workFuel target scs value caller before queries
  (∀ observed, receipt = some observed → FullReceiptPaths P observed) ∧
    FoldPaths P reasonPaths (SourcePruningEnumerationReceiptContinuation.run hook receipt) ∧
    ∀ fragment reached saved after, receipt = some (.complete fragment reached saved after) →
      LeftPaths P nextPaths reasonPaths hook graph templates stop order workFuel metadata recordUV
        fragment reached saved after

/-- Native entry retains every row and the actual nonterminal ordinary scan. -/
noncomputable def NativeStage (P : EqualityTrie.Path → Prop)
    (nextPaths : Metadata Typing → Caller width → Queries → Cached → Option Next → Prop)
    (reasonPaths : Reason → Prop)
    (hook : Fragment → Caller width → Queries → Cached → Hook (Output width Typing) Reason width)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (stop : Option (Metadata Typing → Nat → Bool))
    (order : Metadata Typing → List Nat → Option Nat) (checkEmpty : Bool) (workFuel : Nat)
    (metadata : Metadata Typing) (uv : Nat) (edgesOf : Node → List (EdgeValue Symbol Constraint))
    (caller : Caller width) (before : Cached) (queries : Queries) : Prop :=
  let actual := SourcePruningEnumerationNativeOrdinaryContinuations.run hook checkEmpty
    workFuel workFuel workFuel workFuel workFuel uv edgesOf caller before queries
  RawPaths P actual.1 ∧ (∀ folded, actual.2 = some folded → FoldPaths P reasonPaths folded) ∧
    match actual.1 with
    | [.ok ((target, _handle, scs, parent@(.node ..)), entered)] =>
        if scs.any (fun sc => EqualityTrie.isTerminal sc.trie) then True
        else SiblingPaths P nextPaths reasonPaths hook graph templates stop order checkEmpty workFuel
          metadata uv target scs (EnumerationExpandableIndex.frame entered before) (edgesOf parent) caller queries
    | _ => True

/-- Preparation retains its raw rows and both actual dispatch forms at the returned caller. -/
noncomputable def PreparedStage (P : EqualityTrie.Path → Prop)
    (nextPaths : Metadata Typing → Caller width → Queries → Cached → Option Next → Prop)
    (reasonPaths : Reason → Prop)
    (hook : Fragment → Caller width → Queries → Cached → Hook (Output width Typing) Reason width)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (stop : Option (Metadata Typing → Nat → Bool))
    (order : Metadata Typing → List Nat → Option Nat) (checkEmpty : Bool) (workFuel : Nat)
    (metadata : Metadata Typing) (uv : Nat) (edgesOf : Node → List (EdgeValue Symbol Constraint))
    (caller : Caller width) (before : Cached) (queries : Queries) : Prop :=
  let actual := SourcePruningEnumerationSelectedContinuations.run hook checkEmpty
    workFuel workFuel workFuel workFuel workFuel workFuel workFuel uv edgesOf caller before queries
  RawPaths P actual.1.1 ∧ (∀ folded, actual.2 = some folded → FoldPaths P reasonPaths folded) ∧
    match actual.1.2, actual.1.1 with
    | some (.done value heap), [.ok ((target, _handle, scs, _decoded), entered)] =>
        let captured := EnumerationExpandableIndex.frame entered before
        let reached := SourcePruningEnumerationSelectedValueCaller.advance caller heap
        if scs.any (fun sc => EqualityTrie.isTerminal sc.trie) then
          OpaquePaths P nextPaths reasonPaths hook graph templates stop order checkEmpty workFuel
            metadata uv target scs value reached captured queries
        else match value with
          | parent@(.node ..) =>
              SiblingPaths P nextPaths reasonPaths hook graph templates stop order checkEmpty workFuel
                metadata uv target scs captured (edgesOf parent) reached queries
          | _ => OpaquePaths P nextPaths reasonPaths hook graph templates stop order checkEmpty workFuel
              metadata uv target scs value reached captured queries
    | _, _ => True

/-- Retain every local operation and each literal smaller-depth native call. -/
noncomputable def ResumeNative (P : EqualityTrie.Path → Prop)
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Constraint))
    (stop : Option (Metadata Typing → Nat → Bool))
    (order : Metadata Typing → List Nat → Option Nat) (workFuel : Nat) :
    Nat → Metadata Typing → Caller width → Queries → Cached → Option Next → Prop
  | 0, metadata, caller, queries, before, next =>
      StatePaths P before.core ∧ OutcomePaths P (NativeFailurePaths P)
        (SourcePruningEnumerationRecursive.resume holeKey fits admits graph templates checkEmpty edgesOf stop order workFuel 0 metadata caller queries before next)
  | fuel + 1, metadata, caller, queries, before, next =>
      StatePaths P before.core ∧ OutcomePaths P (NativeFailurePaths P)
        (SourcePruningEnumerationRecursive.resume holeKey fits admits graph templates checkEmpty edgesOf stop order workFuel (fuel + 1) metadata caller queries before next) ∧
      match next with
      | some (.expand uv) =>
          let observed := SourcePruningEnumerationSelectedStep.runPrefix holeKey fits admits graph templates
            stop order metadata workFuel workFuel workFuel workFuel workFuel workFuel uv caller before queries
          SelectedPrefixPaths P observed ∧
            match observed with
            | .parked _ (some _parked) (some []) => True
            | .parked _ (some parked) (some [.ok ((updated, selected), core)]) =>
                ResumeNative P holeKey fits admits graph templates checkEmpty edgesOf stop order workFuel fuel
                  updated caller queries (EnumerationExpandableIndex.frame core parked) selected
            | .narrowed _ _ _reached _saved (some []) _ _ _ => True
            | .narrowed _ _ _reached _saved _ _ (some [.ok ((true, _updated), _core)]) _ => True
            | .narrowed _ _ reached saved _ (some after) (some [.ok ((false, updated), _core)]) none =>
                NativeStage P (ResumeNative P holeKey fits admits graph templates checkEmpty edgesOf stop order workFuel fuel) (NativeFailurePaths P)
                  (SourcePruningEnumerationRecursive.continueWith
                    (SourcePruningEnumerationRecursive.resume holeKey fits admits graph templates checkEmpty edgesOf stop order workFuel fuel)
                    graph templates stop order workFuel updated uv)
                  graph templates stop order checkEmpty workFuel updated uv edgesOf reached after saved
            | _ => True
      | _ => True

/-- Retain every local operation and each literal smaller-depth prepared call. -/
noncomputable def ResumePrepared (P : EqualityTrie.Path → Prop)
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Constraint))
    (stop : Option (Metadata Typing → Nat → Bool))
    (order : Metadata Typing → List Nat → Option Nat) (workFuel : Nat) :
    Nat → Metadata Typing → Caller width → Queries → Cached → Option Next → Prop
  | 0, metadata, caller, queries, before, next =>
      StatePaths P before.core ∧ OutcomePaths P (PreparedFailurePaths P)
        (SourcePruningEnumerationPreparedRecursive.resume holeKey fits admits graph templates checkEmpty edgesOf stop order workFuel 0 metadata caller queries before next)
  | fuel + 1, metadata, caller, queries, before, next =>
      StatePaths P before.core ∧ OutcomePaths P (PreparedFailurePaths P)
        (SourcePruningEnumerationPreparedRecursive.resume holeKey fits admits graph templates checkEmpty edgesOf stop order workFuel (fuel + 1) metadata caller queries before next) ∧
      match next with
      | some (.expand uv) =>
          let observed := SourcePruningEnumerationSelectedStep.runPrefix holeKey fits admits graph templates
            stop order metadata workFuel workFuel workFuel workFuel workFuel workFuel uv caller before queries
          SelectedPrefixPaths P observed ∧
            match observed with
            | .parked _ (some _parked) (some []) => True
            | .parked _ (some parked) (some [.ok ((updated, selected), core)]) =>
                ResumePrepared P holeKey fits admits graph templates checkEmpty edgesOf stop order workFuel fuel
                  updated caller queries (EnumerationExpandableIndex.frame core parked) selected
            | .narrowed _ _ _reached _saved (some []) _ _ _ => True
            | .narrowed _ _ _reached _saved _ _ (some [.ok ((true, _updated), _core)]) _ => True
            | .narrowed _ _ reached saved _ (some after) (some [.ok ((false, updated), _core)]) none =>
                PreparedStage P (ResumePrepared P holeKey fits admits graph templates checkEmpty edgesOf stop order workFuel fuel) (PreparedFailurePaths P)
                  (SourcePruningEnumerationPreparedRecursive.continueWith
                    (SourcePruningEnumerationPreparedRecursive.resume holeKey fits admits graph templates checkEmpty edgesOf stop order workFuel fuel)
                    graph templates stop order workFuel updated uv)
                  graph templates stop order checkEmpty workFuel updated uv edgesOf reached after saved
            | _ => True
      | _ => True

/-- Select the actual initial restart decision for the native execution predicate. -/
noncomputable def Native (P : EqualityTrie.Path → Prop)
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Constraint))
    (stop : Option (Metadata Typing → Nat → Bool))
    (order : Metadata Typing → List Nat → Option Nat) (workFuel : Nat) (recursiveFuel : Nat)
    (metadata : Metadata Typing) (caller : Caller width) (queries : Queries) (before : Cached) : Prop :=
  ResumeNative P holeKey fits admits graph templates checkEmpty edgesOf stop order workFuel recursiveFuel metadata caller queries before
    (SourcePruningEnumerationRestart.decision stop order metadata before)

/-- Select the actual initial restart decision for the prepared execution predicate. -/
noncomputable def Prepared (P : EqualityTrie.Path → Prop)
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Constraint))
    (stop : Option (Metadata Typing → Nat → Bool))
    (order : Metadata Typing → List Nat → Option Nat) (workFuel : Nat) (recursiveFuel : Nat)
    (metadata : Metadata Typing) (caller : Caller width) (queries : Queries) (before : Cached) : Prop :=
  ResumePrepared P holeKey fits admits graph templates checkEmpty edgesOf stop order workFuel recursiveFuel metadata caller queries before
    (SourcePruningEnumerationRestart.decision stop order metadata before)

/-- Zero recursive depth retains the input paths at every actual initial decision. -/
theorem resume_native_zero_paths (P : EqualityTrie.Path → Prop)
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Constraint))
    (stop : Option (Metadata Typing → Nat → Bool))
    (order : Metadata Typing → List Nat → Option Nat) (workFuel : Nat) (metadata : Metadata Typing)
    (caller : Caller width) (queries : Queries) (before : Cached) (next : Option Next)
    (paths : StatePaths P before.core) :
    ResumeNative P holeKey fits admits graph templates checkEmpty edgesOf stop order workFuel 0 metadata caller queries before next := by
  constructor
  · exact paths
  · cases next with
    | none =>
        intro output member
        cases List.mem_singleton.mp member
        exact paths
    | some selected =>
        cases selected with
        | done =>
            intro output member
            cases List.mem_singleton.mp member
            exact paths
        | stuck => intro output member; cases member
        | expand _ =>
            constructor
            · intro output member; cases member
            · exact paths

/-- Zero recursive depth retains the input paths at every actual initial decision. -/
theorem resume_prepared_zero_paths (P : EqualityTrie.Path → Prop)
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Constraint))
    (stop : Option (Metadata Typing → Nat → Bool))
    (order : Metadata Typing → List Nat → Option Nat) (workFuel : Nat) (metadata : Metadata Typing)
    (caller : Caller width) (queries : Queries) (before : Cached) (next : Option Next)
    (paths : StatePaths P before.core) :
    ResumePrepared P holeKey fits admits graph templates checkEmpty edgesOf stop order workFuel 0 metadata caller queries before next := by
  constructor
  · exact paths
  · cases next with
    | none =>
        intro output member
        cases List.mem_singleton.mp member
        exact paths
    | some selected =>
        cases selected with
        | done =>
            intro output member
            cases List.mem_singleton.mp member
            exact paths
        | stuck => intro output member; cases member
        | expand _ =>
            constructor
            · intro output member; cases member
            · exact paths

end MicroCFTA.SourcePruningEnumerationExecutionPaths
