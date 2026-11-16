import MicroCFTA.SourcePruningEnumerationRealEagerCapturedCausalCallbackOrigin
import MicroCFTA.SourcePruningEnumerationInvocationRawAliasGrowth
import MicroCFTA.SourcePruningEnumerationCapturedFinalizeRawAliases

namespace MicroCFTA.SourcePruningEnumerationSharedPreparedRecursiveChildPolicy
open EnumerationState InternedConstructorTemplates
open SourcePruningEnumerationSharedSelectedContinuations
open SourcePruningEnumerationSharedPreparedRecursive (Output Failure emitted)
open SourcePruningEnumerationSharedChildVisitors (visitSelected)
open SourcePruningEnumerationSharedScanOutputOrigins (outputs)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Edge" => EdgeValue Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Queries" => SourceEndpointMemo.Memos
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Metadata" => SourcePruningRecordTypes.Metadata
local notation "Core" => EnumerationState.State Symbol Constraint
variable {Typing Key : Type} {bits : Nat}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]
set_option autoImplicit false

/- Note [Aliases at the captured restart input]
The actual captured receipt fixes the selected trace and both observations.
The alias proof uses those same fields through selection, finalization and recording.
The strengthened producer obtains its witnesses once from the checked producer.
The conclusion concerns the recursive restart input cache.
Transport to the final emitted cache still requires the actual outer recursion proof.
-/

theorem captured_callback_restart_entry_aliases
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (checkEmpty : Bool) (edgesOf : Node → List Edge)
    (stop : Option (Metadata Typing → Nat → Bool)) (order : Metadata Typing → List Nat → Option Nat)
    (workFuel recursiveDepth uv target : Nat) (metadata : Metadata Typing)
    (scs : List Suspended) (edge : Edge) (caller : Caller (bits + 2))
    (queries : Queries) (before : Cached) (index : Nat) (output : Output (bits + 2) Typing)
    (fragment : Fragments.Fragment Symbol) (reached : Caller (bits + 2)) (saved : Queries)
    (beforeFinalize finished : Cached) (updated : Metadata Typing) (callbackCore : Core)
    (earlier later : List (Output (bits + 2) Typing)) (localIndex : Nat)
    (invoked : CapturedCallbackInvocationAt holeKey fits admits graph templates checkEmpty edgesOf stop order
      workFuel recursiveDepth uv target metadata scs edge caller queries before index output
      fragment reached saved beforeFinalize finished updated callbackCore earlier later localIndex) :
    ∀ (left right : Nat), UnionFind.SameClass before.core.representatives left right →
      UnionFind.SameClass (EnumerationExpandableIndex.frame callbackCore finished).core.representatives left right
 := by
  dsimp only [CapturedCallbackInvocationAt] at invoked
  obtain ⟨selected, _whole, _hit, _offset, finalized, recorded⟩ := invoked
  have selectedAliases := SourcePruningEnumerationInvocationRawAliasGrowth.selected_complete_sameClass_forward
    checkEmpty workFuel workFuel workFuel workFuel workFuel edgesOf .eager _
    scs edge caller reached before beforeFinalize queries saved index output fragment localIndex selected
  intro left right same
  have beforeFinalization := selectedAliases left right same
  have afterFinalization := SourcePruningEnumerationCapturedFinalizeRawAliases.finalize_sameClass_forward
    reached.checked.native.machine.heap workFuel target fragment beforeFinalize finished finalized
      left right beforeFinalization
  exact SourcePruningEnumerationCapturedFinalizeRawAliases.false_recordTypes_sameClass_forward
    graph templates workFuel uv metadata updated fragment finished callbackCore recorded
      left right afterFinalization

theorem real_eager_captured_output_restart_entry_alias_origin
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (checkEmpty : Bool) (edgesOf : Node → List Edge)
    (stop : Option (Metadata Typing → Nat → Bool)) (order : Metadata Typing → List Nat → Option Nat)
    (workFuel recursiveDepth uv target : Nat) (metadata : Metadata Typing)
    (scs : List Suspended) (edge : Edge) (caller : Caller (bits + 2))
    (queries : Queries) (before : Cached) (index : Nat) (output : Output (bits + 2) Typing) :
    let child := SourcePruningEnumerationSharedEagerChildren.eagerChild
      (width := bits + 2) (Output := Output (bits + 2) Typing) (Reason := Failure (bits + 2) Typing)
      checkEmpty workFuel workFuel workFuel workFuel workFuel edgesOf
    let recur := resumeWithNarrow child (SourcePruningOuterNarrow.narrow holeKey fits admits)
      graph templates checkEmpty edgesOf stop order workFuel recursiveDepth
    let hook := SourcePruningEnumerationSharedPreparedRecursive.continueWith recur
      graph templates stop order workFuel metadata uv
    let actual := SourcePruningEnumerationSharedChildVisitors.visitCapturedWith child hook
      workFuel target scs edge caller queries before
    (outputs actual)[index]? = some output →
    ∃ (fragment : Fragments.Fragment Symbol) (reached : Caller (bits + 2)) (saved : Queries)
        (beforeFinalize finished : Cached) (updated : Metadata Typing) (callbackCore : Core)
        (earlier later : List (Output (bits + 2) Typing)) (localIndex : Nat),
      SourcePruningEnumerationFinalize.run reached.checked.native.machine.heap
        workFuel target fragment beforeFinalize = some finished ∧
      ExceptT.run (SourcePruningRecordTypes.recordTypes graph templates workFuel metadata uv
        (.inl fragment) finished.core) = [.ok ((false, updated), callbackCore)] ∧
      let resumed := recur updated reached saved (EnumerationExpandableIndex.frame callbackCore finished)
        (SourcePruningEnumerationRestart.decision stop order updated
          (EnumerationExpandableIndex.frame callbackCore finished))
      outputs actual = earlier ++ emitted resumed ++ later ∧
      (emitted resumed)[localIndex]? = some output ∧ index = earlier.length + localIndex ∧
      CapturedCallbackInvocationAt holeKey fits admits graph templates checkEmpty edgesOf stop order
        workFuel recursiveDepth uv target metadata scs edge caller queries before index output
        fragment reached saved beforeFinalize finished updated callbackCore earlier later localIndex ∧
      ∀ (left right : Nat), UnionFind.SameClass before.core.representatives left right →
        UnionFind.SameClass (EnumerationExpandableIndex.frame callbackCore finished).core.representatives left right
 := by
  dsimp only
  intro observed
  obtain ⟨fragment, reached, saved, beforeFinalize, finished, updated, callbackCore,
      earlier, later, localIndex, finalized, recorded, whole, hit, offset, invoked⟩ :=
    real_eager_captured_output_causal_callback_restart_origin
      holeKey fits admits graph templates checkEmpty edgesOf stop order
      workFuel recursiveDepth uv target metadata scs edge caller queries before index output observed
  have aliases := captured_callback_restart_entry_aliases
    holeKey fits admits graph templates checkEmpty edgesOf stop order
    workFuel recursiveDepth uv target metadata scs edge caller queries before index output
    fragment reached saved beforeFinalize finished updated callbackCore earlier later localIndex invoked
  exact ⟨fragment, reached, saved, beforeFinalize, finished, updated, callbackCore,
    earlier, later, localIndex, finalized, recorded, whole, hit, offset, invoked, aliases⟩

end MicroCFTA.SourcePruningEnumerationSharedPreparedRecursiveChildPolicy
