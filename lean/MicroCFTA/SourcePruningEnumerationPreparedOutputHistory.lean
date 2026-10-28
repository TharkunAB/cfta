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
    (property : Fragment → Caller width → Queries → Cached → Output width Typing → Prop)
    (hook : Fragment → Caller width → Queries → Cached →
      SourcePruningEnumerationNativeContinuations.HookResult (Output width Typing) (Failure width Typing) width)
    (checkEmpty : Bool) (workFuel uv : Nat) (edgesOf : Node → List (EdgeValue Symbol Constraint))
    (caller : Caller width) (before : Cached) (queries : Queries)
    (continued : ∀ fragment reached saved after, ∀ output ∈ hookOutputs (hook fragment reached saved after),
      property fragment reached saved after output) :
    ∀ output ∈ hookOutputs (
      let selected := SourcePruningEnumerationSelectedContinuations.run hook checkEmpty workFuel workFuel
        workFuel workFuel workFuel workFuel workFuel uv edgesOf caller before queries
      match selected.2 with
      | none => .stopped [] (.preparation uv selected.1) none
      | some folded => finish uv folded),
      ∃ fragment reached saved after,
        SourcePruningEnumerationSelectedContinuations.Invocation hook checkEmpty workFuel workFuel
          workFuel workFuel workFuel workFuel workFuel uv edgesOf
          caller before queries fragment reached saved after ∧ property fragment reached saved after output := by
  generalize observed : SourcePruningEnumerationSelectedContinuations.run hook checkEmpty workFuel workFuel
    workFuel workFuel workFuel workFuel workFuel uv edgesOf caller before queries = selected
  obtain ⟨raw, result⟩ := selected
  cases result with
  | none => intro output member; cases member
  | some folded =>
      intro output member
      rw [finish_hook_outputs] at member
      obtain ⟨fragment, reached, saved, after, invocation, emitted⟩ :=
        SourcePruningEnumerationSelectedContinuations.output_invocation hook checkEmpty workFuel workFuel
          workFuel workFuel workFuel workFuel workFuel uv edgesOf caller before queries folded (congrArg Prod.snd observed) output member
      exact ⟨fragment, reached, saved, after, invocation, continued fragment reached saved after output emitted⟩

/-- Every actual bounded resume output has its complete operation path from that resume input. -/
theorem resume_output_history
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Constraint))
    (stop : Option (Metadata Typing → Nat → Bool)) (order : Metadata Typing → List Nat → Option Nat)
    (workFuel recursiveFuel : Nat) :
    ∀ (metadata : Metadata Typing) (caller : Caller width) (queries : Queries) (before : Cached) (next : Option Next),
      ∀ output ∈ hookOutputs (resume holeKey fits admits graph templates checkEmpty edgesOf stop order
        workFuel recursiveFuel metadata caller queries before next),
        OutputHistory holeKey fits admits graph templates checkEmpty edgesOf stop order workFuel
          recursiveFuel metadata caller queries before next output := by
  induction recursiveFuel with
  | zero =>
      intro metadata caller queries before next output member
      cases next with
      | none =>
          simp only [resume, hookOutputs, List.mem_singleton] at member
          subst output
          exact .stopped
      | some next =>
          cases next with
          | done =>
              simp only [resume, hookOutputs, List.mem_singleton] at member
              subst output
              exact .done
          | stuck | expand _ => cases member
  | succ recursiveFuel ih =>
      intro metadata caller queries before next output member
      cases next with
      | none =>
          simp only [resume, hookOutputs, List.mem_singleton] at member
          subst output
          exact .stopped
      | some next =>
          cases next with
          | done =>
              simp only [resume, hookOutputs, List.mem_singleton] at member
              subst output
              exact .done
          | stuck => cases member
          | expand uv =>
              rw [resume] at member
              dsimp only at member
              split at member
              · cases member
              · exact .parked (by assumption) (ih _ _ _ _ _ output member)
              · cases member
              · cases member
              · have continued : ∀ (updated : Metadata Typing) (fragment : Fragment)
                    (reached : Caller width) (saved : Queries) (after : Cached),
                    ∀ output ∈ hookOutputs (continueWith
                      (resume holeKey fits admits graph templates checkEmpty edgesOf stop order workFuel recursiveFuel)
                      graph templates stop order workFuel updated uv fragment reached saved after),
                      ∃ recorded core,
                        ExceptT.run (SourcePruningRecordTypes.recordTypes graph templates workFuel updated uv
                          (.inl fragment) after.core) = [.ok ((false, recorded), core)] ∧
                        OutputHistory holeKey fits admits graph templates checkEmpty edgesOf stop order workFuel
                          recursiveFuel recorded reached saved (EnumerationExpandableIndex.frame core after)
                            (SourcePruningEnumerationRestart.decision stop order recorded
                              (EnumerationExpandableIndex.frame core after)) output := by
                  intro updated fragment reached saved after current emitted
                  obtain ⟨recorded, core, callback, listed⟩ := continueWith_output_restart _ graph templates
                    stop order workFuel updated uv fragment reached saved after current emitted
                  exact ⟨recorded, core, callback, ih _ _ _ _ _ current listed⟩
                obtain ⟨fragment, headCaller, headQueries, headCache, invocation, recorded, core, callback, tail⟩ :=
                  selected_finish_history _ _ checkEmpty workFuel uv edgesOf _ _ _ (continued _) output member
                exact .selected (by assumption) invocation callback tail
              · cases member
              · cases member

/-- The actual driver supplies the original decision for every certified output path. -/
theorem run_output_history
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Constraint))
    (stop : Option (Metadata Typing → Nat → Bool)) (order : Metadata Typing → List Nat → Option Nat)
    (workFuel recursiveFuel : Nat) (metadata : Metadata Typing) (caller : Caller width)
    (queries : Queries) (before : Cached) :
    ∀ output ∈ hookOutputs (run holeKey fits admits graph templates checkEmpty edgesOf stop order
      workFuel recursiveFuel metadata caller queries before),
      OutputHistory holeKey fits admits graph templates checkEmpty edgesOf stop order workFuel recursiveFuel
        metadata caller queries before (SourcePruningEnumerationRestart.decision stop order metadata before) output :=
  resume_output_history holeKey fits admits graph templates checkEmpty edgesOf stop order workFuel recursiveFuel
    metadata caller queries before _

end MicroCFTA.SourcePruningEnumerationPreparedRecursive
