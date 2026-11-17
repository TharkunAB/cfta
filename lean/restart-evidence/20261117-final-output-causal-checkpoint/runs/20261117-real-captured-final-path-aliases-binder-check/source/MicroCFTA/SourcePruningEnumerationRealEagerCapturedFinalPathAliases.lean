import MicroCFTA.SourcePruningEnumerationRealEagerCapturedCausalCallbackOrigin
import MicroCFTA.SourcePruningEnumerationSelectedChildPathAliases
import MicroCFTA.SourcePruningEnumerationCapturedFinalizeRawAliases
import MicroCFTA.SourcePruningEnumerationRealEagerRawAliases

namespace MicroCFTA.SourcePruningEnumerationSharedPreparedRecursiveChildPolicy
open EnumerationState InternedConstructorTemplates
open SourcePruningEnumerationSharedSelectedContinuations
open SourcePruningEnumerationSharedPreparedRecursive (Output Failure emitted)
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
local notation "Input" => Node × List Suspended × Option (EnumerateM Symbol Constraint (Fragments.Fragment Symbol))
variable {Typing Key : Type} {bits : Nat}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]
set_option autoImplicit false

/- Note [Path aliases at the same final output]
The causal producer supplies one selected trace and one restart suffix.
This proof retains those witnesses and the exact output index.
The actual staged child creates the same-position path aliases.
The same finalizer, false recordTypes callback and restart preserve them.
The entry Total and bucket Valid facts qualify that selected invocation.
The conclusion is a raw alias fact for this event and output.
It does not supply native typing or a joint historical assignment.
-/

theorem real_eager_captured_output_final_path_alias_origin
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
      ∀ (_total : UnionFind.Total before.core.representatives)
        (_valid : ∀ sc ∈ scs, EqualityTrie.Valid sc.trie)
        (middle : Cached) (staged : List Input) (residual : Option Constraint),
        SourcePruningEnumerationCachedOwn.prepare caller.checked.native.machine.heap scs edge before =
          some [((edge.entry.key.symbol, staged, residual), middle)] →
        ∀ (position : Nat) (incoming : Node) (childBucket : List Suspended)
          (action : Option (EnumerateM Symbol Constraint (Fragments.Fragment Symbol))),
          staged[position]? = some (incoming, childBucket, action) →
          ∀ (firstIndex secondIndex : Nat) (first second : Suspended),
            scs[firstIndex]? = some first → scs[secondIndex]? = some second →
            [position] ∈ EqualityTrie.fromPathTrie first.trie →
            [position] ∈ EqualityTrie.fromPathTrie second.trie →
            UnionFind.SameClass output.cache.core.representatives first.var second.var
 := by
  dsimp only
  intro observed
  obtain ⟨fragment, reached, saved, beforeFinalize, finished, updated, callbackCore,
      earlier, later, localIndex, finalized, recorded, whole, hit, offset, invoked⟩ :=
    real_eager_captured_output_causal_callback_restart_origin
      holeKey fits admits graph templates checkEmpty edgesOf stop order
      workFuel recursiveDepth uv target metadata scs edge caller queries before index output observed
  refine ⟨fragment, reached, saved, beforeFinalize, finished, updated, callbackCore,
    earlier, later, localIndex, finalized, recorded, whole, hit, offset, invoked, ?_⟩
  intro total valid middle staged residual prepared position incoming childBucket action indexed
    firstIndex secondIndex first second firstStored secondStored firstPath secondPath
  have actualInvocation := invoked
  dsimp only [CapturedCallbackInvocationAt] at actualInvocation
  obtain ⟨selected, _rowWhole, _rowHit, _rowOffset, _actualFinalize, _actualRecorded⟩ :=
    actualInvocation
  have atSelected :=
    SourcePruningEnumerationSelectedChildPathAliases.selected_child_path_sameClass
      checkEmpty workFuel workFuel workFuel workFuel workFuel edgesOf .eager _
      scs edge caller reached before middle beforeFinalize queries saved index output
      fragment localIndex staged residual prepared total valid
      position incoming childBucket action indexed selected
      firstIndex secondIndex first second firstStored secondStored firstPath secondPath
  have atFinished :=
    SourcePruningEnumerationCapturedFinalizeRawAliases.finalize_sameClass_forward
      reached.checked.native.machine.heap workFuel target fragment beforeFinalize finished finalized
      first.var second.var atSelected
  have atCallback :=
    SourcePruningEnumerationCapturedFinalizeRawAliases.false_recordTypes_sameClass_forward
      graph templates workFuel uv metadata updated fragment finished callbackCore recorded
      first.var second.var atFinished
  exact SourcePruningEnumerationSharedEagerReservation.resumeWithNarrow_real_entry_aliases_at_any_budget
    (bits := bits) holeKey fits admits graph templates checkEmpty edgesOf stop order
    workFuel recursiveDepth updated reached saved
    (EnumerationExpandableIndex.frame callbackCore finished)
    (SourcePruningEnumerationRestart.decision stop order updated
      (EnumerationExpandableIndex.frame callbackCore finished))
    output (List.mem_of_getElem? hit) first.var second.var atCallback

end MicroCFTA.SourcePruningEnumerationSharedPreparedRecursiveChildPolicy

#check MicroCFTA.SourcePruningEnumerationSharedPreparedRecursiveChildPolicy.real_eager_captured_output_final_path_alias_origin
#print axioms MicroCFTA.SourcePruningEnumerationSharedPreparedRecursiveChildPolicy.real_eager_captured_output_final_path_alias_origin
