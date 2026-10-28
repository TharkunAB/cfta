import MicroCFTA.SourcePruningEnumerationSelectedInvocation
import MicroCFTA.SourcePruningEnumerationPreparedRecursive

/-!
# Actual prepared recursive paths to emitted outputs

Each path records the selected prefix, one actual native preparation and
its ordinary or singleton receipt invocation. Every callback retains its
actual caller and cache. Outputs before a stop retain the same path.
This certificate has no resource or semantic admission. It does not imply
assignment preservation, discharge or whole-driver accepted-output coverage.
-/
namespace MicroCFTA.SourcePruningEnumerationPreparedRecursive
open EnumerationState InternedConstructorTemplates
open SourcePruningEnumerationRecursive (Output)
open SourcePruningEnumerationHookInvocation (hookOutputs foldOutputs)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Fragment" => Fragments.Fragment Symbol
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Queries" => SourceEndpointMemo.Memos
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Core" => EnumerationState.State Symbol Constraint
local notation "Metadata" => SourcePruningRecordTypes.Metadata
variable {Typing Key : Type} {width : Nat}
/-- An emitted callback output has the exact false record receipt and the same native endpoint. -/
theorem continueWith_output_restart
    (recur : Metadata Typing → Caller width → Queries → Cached → Option Next →
      SourcePruningEnumerationNativeContinuations.HookResult (SourcePruningEnumerationRecursive.Output width Typing) (Failure width Typing) width)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (stop : Option (Metadata Typing → Nat → Bool)) (order : Metadata Typing → List Nat → Option Nat)
    (fuel : Nat) (metadata : Metadata Typing) (uv : Nat) (fragment : Fragment)
    (caller : Caller width) (queries : Queries) (before : Cached) :
    ∀ output ∈ hookOutputs (continueWith recur graph templates stop order fuel metadata uv fragment caller queries before),
      ∃ updated core,
        ExceptT.run (SourcePruningRecordTypes.recordTypes graph templates fuel metadata uv (.inl fragment) before.core) =
          [.ok ((false, updated), core)] ∧
        output ∈ hookOutputs (recur updated caller queries (EnumerationExpandableIndex.frame core before)
          (SourcePruningEnumerationRestart.decision stop order updated (EnumerationExpandableIndex.frame core before))) := by
  unfold continueWith
  dsimp only
  split
  · intro output member; cases member
  · intro output member
    exact ⟨_, _, by assumption, member⟩
  · intro output member; cases member

/-- Finishing a scan retains its outputs at both complete and stopped outcomes. -/
theorem finish_hook_outputs (uv : Nat)
    (result : SourcePruningEnumerationNativeContinuations.Result
      (SourcePruningEnumerationRecursive.Output width Typing) (Failure width Typing) width) :
    hookOutputs (finish uv result) = foldOutputs result := by
  cases result <;> rfl


variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]

/-- Retain every actual operation on one recursive output path. -/
inductive OutputHistory
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Constraint))
    (stop : Option (Metadata Typing → Nat → Bool)) (order : Metadata Typing → List Nat → Option Nat)
    (workFuel : Nat) :
    Nat → Metadata Typing → Caller width → Queries → Cached → Option Next → Output width Typing → Prop where
  /-- The supplied stop decision emits its same cache and endpoint. -/
  | stopped {fuel metadata caller queries before} :
      OutputHistory holeKey fits admits graph templates checkEmpty edgesOf stop order workFuel
        fuel metadata caller queries before none ⟨some metadata, before, caller, queries⟩
  /-- The supplied done decision emits its same cache and endpoint. -/
  | done {fuel metadata caller queries before} :
      OutputHistory holeKey fits admits graph templates checkEmpty edgesOf stop order workFuel
        fuel metadata caller queries before (some .done) ⟨none, before, caller, queries⟩
  /-- The actual parked singleton supplies the exact next recursive input. -/
  | parked {fuel metadata caller queries before uv checked parked updated next core output}
      (observedPrefix : SourcePruningEnumerationSelectedStep.runPrefix holeKey fits admits graph templates stop order
        metadata workFuel workFuel workFuel workFuel workFuel workFuel uv caller before queries =
          .parked checked (some parked) (some [.ok ((updated, next), core)]))
      (tail : OutputHistory holeKey fits admits graph templates checkEmpty edgesOf stop order workFuel
        fuel updated caller queries (EnumerationExpandableIndex.frame core parked) next output) :
      OutputHistory holeKey fits admits graph templates checkEmpty edgesOf stop order workFuel
        (fuel + 1) metadata caller queries before (some (.expand uv)) output
  /-- The actual selected preparation invokes a branch receipt and its false callback. -/
  | selected {fuel metadata caller queries before uv checked prepared reached saved action after updated rightCore
        fragment headCaller headQueries headCache recorded callbackCore output}
      (observedPrefix : SourcePruningEnumerationSelectedStep.runPrefix holeKey fits admits graph templates stop order
        metadata workFuel workFuel workFuel workFuel workFuel workFuel uv caller before queries =
          .narrowed checked prepared reached saved action (some after)
            (some [.ok ((false, updated), rightCore)]) none)
      (invocation : SourcePruningEnumerationSelectedContinuations.Invocation
        (continueWith (resume holeKey fits admits graph templates checkEmpty edgesOf stop order workFuel fuel)
          graph templates stop order workFuel updated uv)
        checkEmpty workFuel workFuel workFuel workFuel workFuel workFuel workFuel uv edgesOf reached after saved
          fragment headCaller headQueries headCache)
      (callback : ExceptT.run (SourcePruningRecordTypes.recordTypes graph templates workFuel updated uv
        (.inl fragment) headCache.core) = [.ok ((false, recorded), callbackCore)])
      (tail : OutputHistory holeKey fits admits graph templates checkEmpty edgesOf stop order workFuel
        fuel recorded headCaller headQueries (EnumerationExpandableIndex.frame callbackCore headCache)
          (SourcePruningEnumerationRestart.decision stop order recorded
            (EnumerationExpandableIndex.frame callbackCore headCache)) output) :
      OutputHistory holeKey fits admits graph templates checkEmpty edgesOf stop order workFuel
        (fuel + 1) metadata caller queries before (some (.expand uv)) output

private theorem selected_finish_history
