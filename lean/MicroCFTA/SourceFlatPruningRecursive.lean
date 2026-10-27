import MicroCFTA.SourceFlatPruningSelectedPrefix
import MicroCFTA.SourceFlatPruningNativeOrdinaryContinuations
import MicroCFTA.SourceFlatPruningContinuation
import MicroCFTA.SourcePruningEnumerationRecursive

namespace MicroCFTA.SourceFlatPruningRecursive
open EnumerationState InternedConstructorTemplates
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Fragment" => Fragments.Fragment Symbol
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Queries" => SourceEndpointMemo.Memos
local notation "Cached" => EnumerationFlatCached.Cached Symbol Constraint
local notation "Metadata" => SourcePruningRecordTypes.Metadata
local notation "Core" => EnumerationFlatState.State Symbol Constraint
local notation "Receipt" => SourceFlatPruningSelectedEdge.Result
local notation "Fold" => SourceFlatPruningNativeContinuations.Result
local notation "FoldStop" => SourceFlatPruningNativeContinuations.Stop
local notation "HookResult" => SourceFlatPruningNativeContinuations.HookResult
local notation "EntryRaw" => List (Except EnumerationState.Error ((Nat × Nat × List Suspended × Node) × Core))
local notation "CallbackRaw" => fun Typing => List (Except EnumerationState.Error ((Bool × Metadata Typing) × Core))

/-- Retain the exact bounded or unsupported observation that prevents continuation. -/
inductive Failure (width : Nat) (Typing : Type) : Type 1 where
  /-- The recursive budget does not permit the selected expansion. -/
  | exhausted (uv : Nat) (metadata : Metadata Typing) (before : Cached)
  /-- The actual selected prefix cannot supply a supported continuation. -/
  | selected (uv : Nat) (observed : SourceFlatPruningSelectedPrefix.Result width Typing)
  /-- The actual fragment callback does not return a singleton success. -/
  | callback (uv : Nat) (raw : CallbackRaw Typing)
  /-- Entry does not supply an ordinary nonterminal alternative scan. -/
  | ordinary (uv : Nat) (raw : EntryRaw)
  /-- Retain the processed alternatives and their exact edge or recursive stop. -/
  | alternatives (uv : Nat) (processed : List (Receipt width))
      (current : FoldStop (Failure width Typing) width)

/-- Retain each source output at its own enumeration cache and native endpoint. -/
structure Output (width : Nat) (Typing : Type) where
  /-- A stop rule returns metadata. Exhausted candidate selection returns none. -/
  metadata : Option (Metadata Typing)
  /-- The enumeration cache belongs to this output branch. -/
  cache : Cached
  /-- The caller is the native endpoint when this output is emitted. -/
  caller : Caller width
  /-- The saved queries belong to the same endpoint. -/
  queries : Queries

variable {Typing Key : Type} {width : Nat}
local notation "Result" => HookResult (Output width Typing) (Failure width Typing) width

/-- Related outputs retain metadata, branch cache and the actual emission endpoint. -/
def OutputRelated (flat : Output width Typing)
    (earlier : SourcePruningEnumerationRecursive.Output width Typing) : Prop :=
  flat.metadata = earlier.metadata ∧ EnumerationFlatCached.Related flat.cache earlier.cache ∧
    flat.caller = earlier.caller ∧ flat.queries = earlier.queries

/-- Related failures retain every raw diagnostic and recursive stopping context. -/
inductive FailureRelated : Failure width Typing → SourcePruningEnumerationRecursive.Failure width Typing → Prop where
  /-- Exhaustion retains the selected variable, metadata and related captured cache. -/
  | exhausted (uv : Nat) (metadata : Metadata Typing)
      {flat : Cached} {earlier : EnumerationExpandableIndex.Cached Symbol Constraint}
      (related : EnumerationFlatCached.Related flat earlier) :
      FailureRelated (.exhausted uv metadata flat) (.exhausted uv metadata earlier)
  /-- Selected-prefix failure retains its complete actual prefix observation. -/
  | selected (uv : Nat) {flat : SourceFlatPruningSelectedPrefix.Result width Typing}
      {earlier : SourcePruningEnumerationSelectedStep.Result width Typing}
      (related : SourceFlatPruningSelectedPrefix.ResultRelated flat earlier) :
      FailureRelated (.selected uv flat) (.selected uv earlier)
  /-- Callback failure retains every raw result and error in order. -/
  | callback (uv : Nat) {flat : CallbackRaw Typing}
      {earlier : List (Except EnumerationState.Error
        ((Bool × Metadata Typing) × EnumerationState.State Symbol Constraint))}
      (related : EnumerationResultRelation.Results EnumerationFlatState.Related flat earlier) :
      FailureRelated (.callback uv flat) (.callback uv earlier)
  /-- Ordinary-entry failure retains every raw result and error in order. -/
  | ordinary (uv : Nat) {flat : EntryRaw}
      {earlier : List (Except EnumerationState.Error
        ((Nat × Nat × List Suspended × Node) × EnumerationState.State Symbol Constraint))}
      (related : EnumerationResultRelation.Results EnumerationFlatState.Related flat earlier) :
      FailureRelated (.ordinary uv flat) (.ordinary uv earlier)
  /-- A missing edge retains its absence after the same ordered processed receipts. -/
  | alternatives_none (uv : Nat) {processed : List (Receipt width)}
      {earlier : List (SourcePruningEnumerationSelectedEdge.Result width)}
      (related : SourceFlatPruningNativeBranches.ReceiptsRelated processed earlier) :
      FailureRelated (.alternatives uv processed (.edge none)) (.alternatives uv earlier (.edge none))
  /-- An edge stop retains its exact current receipt outside the processed prefix. -/
  | alternatives_edge (uv : Nat) {processed : List (Receipt width)}
      {earlier : List (SourcePruningEnumerationSelectedEdge.Result width)}
      {current : Receipt width} {oldCurrent : SourcePruningEnumerationSelectedEdge.Result width}
      (processedRelated : SourceFlatPruningNativeBranches.ReceiptsRelated processed earlier)
      (currentRelated : SourceFlatPruningSelectedEdge.ResultRelated current oldCurrent) :
      FailureRelated (.alternatives uv processed (.edge (some current)))
        (.alternatives uv earlier (.edge (some oldCurrent)))
  /-- A continuation stop retains its nested failure and exact optional native endpoint. -/
  | alternatives_continuation (uv : Nat) {processed : List (Receipt width)}
      {earlier : List (SourcePruningEnumerationSelectedEdge.Result width)}
      {current : Receipt width} {oldCurrent : SourcePruningEnumerationSelectedEdge.Result width}
      {reason : Failure width Typing} {oldReason : SourcePruningEnumerationRecursive.Failure width Typing}
      (reached : Option (Caller width × Queries))
      (processedRelated : SourceFlatPruningNativeBranches.ReceiptsRelated processed earlier)
      (currentRelated : SourceFlatPruningSelectedEdge.ResultRelated current oldCurrent)
      (reasonRelated : FailureRelated reason oldReason) :
      FailureRelated (.alternatives uv processed (.continuation current reason reached))
        (.alternatives uv earlier (.continuation oldCurrent oldReason reached))

/-- Related recursive observations retain ordered outputs, failure context and native endpoint. -/
def ResultRelated (flat : Result)
    (earlier : SourcePruningEnumerationNativeContinuations.HookResult
      (SourcePruningEnumerationRecursive.Output width Typing)
      (SourcePruningEnumerationRecursive.Failure width Typing) width) : Prop :=
  SourceFlatPruningNativeContinuations.HookResultRelated OutputRelated FailureRelated flat earlier

/-- Read only a native endpoint supplied by the actual stopped receipt. -/
def endpoint : FoldStop (Failure width Typing) width → Option (Caller width × Queries)
  | .edge current => current.bind SourceFlatPruningNativeBranches.advance
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
  SourceFlatPruningContinuation.continueWith Failure.callback recur graph templates stop order
    callbackFuel metadata uv fragment caller queries before

variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]

/-- Consume an actual restart decision and execute ordinary recursive continuations in source order.
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
      let observed := SourceFlatPruningSelectedPrefix.run holeKey fits admits graph templates
        stop order metadata workFuel workFuel uv caller before queries
      match observed with
      | .parked _ (some _parked) (some []) => .complete [] caller queries
      | .parked _ (some parked) (some [.ok ((updated, next), core)]) =>
          resume holeKey fits admits graph templates checkEmpty edgesOf stop order workFuel fuel
            updated caller queries (EnumerationFlatCached.frame core parked) next
      | .narrowed _ _ reached saved (some []) _ _ => .complete [] reached saved
      | .narrowed _ _ reached saved _ _ (some [.ok ((true, _updated), _core)]) =>
          .complete [] reached saved
      | .narrowed _ _ reached saved _ (some after) (some [.ok ((false, updated), _core)]) =>
          let ordinary := SourceFlatPruningNativeOrdinaryContinuations.run
            (continueWith (resume holeKey fits admits graph templates checkEmpty edgesOf stop order workFuel fuel)
              graph templates stop order workFuel updated uv)
            checkEmpty workFuel workFuel workFuel uv edgesOf reached after saved
          match ordinary.2 with
          | none => .stopped [] (.ordinary uv ordinary.1) (some (reached, saved))
          | some folded => finish uv folded
      | .narrowed _ _ reached saved _ _ _ => .stopped [] (.selected uv observed) (some (reached, saved))
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
    metadata caller queries before (SourceFlatPruningRestart.decision stop order metadata before)

end MicroCFTA.SourceFlatPruningRecursive
