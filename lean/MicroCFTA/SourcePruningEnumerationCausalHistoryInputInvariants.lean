import MicroCFTA.SourcePruningEnumerationRealEagerCausalOutputHistory
import MicroCFTA.SourcePruningEnumerationPreparationEntryInvariants
import MicroCFTA.SourcePruningEnumerationInvocationCanonical
import MicroCFTA.SourcePruningEnumerationInvocationRawAliasGrowth
import MicroCFTA.SourcePruningEnumerationCapturedFinalizeRawAliases
import MicroCFTA.SourcePruningEnumerationOwnFinalizeCanonical
import MicroCFTA.SourcePruningEnumerationPathRecordingValues
import MicroCFTA.SourcePruningEnumerationSharedChildCanonical
import MicroCFTA.SourcePruningEnumerationSharedChildRawAliasGrowth

namespace MicroCFTA.SourcePruningEnumerationCausalHistoryInputInvariants
open SourcePruningEnumerationRealEagerCausalOutputHistory
open EnumerationValidity EnumerationCorrectness EnumerationSchedule EnumerationSemantics
open EnumerationState InternedConstructorTemplates
open SourcePruningEnumerationSharedSelectedContinuations
open SourcePruningEnumerationSharedPreparedRecursive (Output Failure emitted continueWith)
open SourcePruningEnumerationSharedPreparedRecursiveChildPolicy (resumeWithNarrow CapturedCallbackInvocationAt)
open SourcePruningEnumerationSharedChildVisitors (visitCapturedWith)
open SourcePruningEnumerationSharedBranching (scan)
open SourcePruningEnumerationSharedScanOutputOrigins (outputs)
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
universe u
variable {Typing Key : Type} {bits : Nat}
local notation "Fold" => NativeContinuations.Result (Output (bits + 2) Typing) (Failure (bits + 2) Typing) (bits + 2)
local notation "Prepared" => MergedSourceComparison.Result Symbol Constraint (Node × Option (EnumerateM Symbol Constraint Unit))
local notation "ActionRaw" => List (Except EnumerationState.Error (Unit × Core))
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]
set_option autoImplicit false

/- Note [Input invariants on one indexed causal derivation]
The qualification constructors retain all original receipt and index fields.
They add Canonical and Total at each recorded cache cut.
Each actual preparation also retains ValidSuspended for its own bucket.
The induction transports Total through actual raw alias retention.
It transports Canonical through the same child, finalizer and callback.
The public wrapper obtains the indexed history from actual output membership.
It requires only the two initial structural facts.

The history proof index is an association, not an identity of hidden witnesses.
Lean proof irrelevance can equate proofs with different hidden constructor data.
A consumer must obtain all event data from one qualified derivation.
It must not join witnesses from a separate unqualified history elimination.
The constructors retain row and callback list indices in the same bundle.

The four small local control proofs reuse checked source proof text.
They do not access private constants across modules.
This module adds no runtime worker and changes no supplied fuel.
These structural facts do not imply TypeIn or one accepted finite model.
-/

/-- State the two structural input invariants at one concrete cache Core. -/
def CanonicalTotal (state : Core) : Prop :=
  Canonical state ∧ UnionFind.Total state.representatives

mutual
/-- Qualify the exact outer history and each recorded cache cut. -/
inductive QualifiedOutputHistoryAt
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (checkEmpty : Bool) (edgesOf : Node → List Edge)
    (stop : Option (Metadata Typing → Nat → Bool)) (order : Metadata Typing → List Nat → Option Nat)
    (workFuel : Nat) :
    {depth : Nat} → {metadata : Metadata Typing} → {caller : Caller (bits + 2)} →
    {queries : Queries} → {before : Cached} → {decision : Option Next} →
    {index : Nat} → {output : Output (bits + 2) Typing} →
    OutputHistoryAt holeKey fits admits graph templates checkEmpty edgesOf stop order workFuel
      depth metadata caller queries before decision index output → Prop where
  | stopped (depth : Nat) (metadata : Metadata Typing) (caller : Caller (bits + 2))
      (queries : Queries) (before : Cached) (input : CanonicalTotal before.core) :
      QualifiedOutputHistoryAt holeKey fits admits graph templates checkEmpty edgesOf stop order workFuel
        (OutputHistoryAt.stopped depth metadata caller queries before)
  | done (depth : Nat) (metadata : Metadata Typing) (caller : Caller (bits + 2))
      (queries : Queries) (before : Cached) (input : CanonicalTotal before.core) :
      QualifiedOutputHistoryAt holeKey fits admits graph templates checkEmpty edgesOf stop order workFuel
        (OutputHistoryAt.done depth metadata caller queries before)
  | parked
      {depth uv index : Nat} {metadata updated : Metadata Typing}
      {caller : Caller (bits + 2)} {queries : Queries} {before parkedCache : Cached}
      {checked core : Core} {next : Option Next} {output : Output (bits + 2) Typing}
      (observed : SourcePruningEnumerationSelectedStep.runPrefixWithNarrow
        (SourcePruningOuterNarrow.narrow holeKey fits admits) graph templates stop order metadata
        workFuel workFuel workFuel workFuel workFuel workFuel uv caller before queries =
        .parked checked (some parkedCache) (some [.ok ((updated, next), core)]))
      (tail : OutputHistoryAt holeKey fits admits graph templates checkEmpty edgesOf stop order workFuel depth updated caller queries
        (EnumerationExpandableIndex.frame core parkedCache) next index output)
      (input : CanonicalTotal before.core) (check : CanonicalTotal checked)
      (candidate : CanonicalTotal parkedCache.core)
      (callback : CanonicalTotal (EnumerationExpandableIndex.frame core parkedCache).core)
      (qualifiedTail : QualifiedOutputHistoryAt holeKey fits admits graph templates checkEmpty edgesOf stop order workFuel tail) :
      QualifiedOutputHistoryAt holeKey fits admits graph templates checkEmpty edgesOf stop order workFuel
        (OutputHistoryAt.parked observed tail)
  | selected
      {depth uv index : Nat} {metadata updated : Metadata Typing}
      {caller reached : Caller (bits + 2)} {queries saved : Queries} {before after : Cached}
      {checked rightCore : Core} {prepared : Prepared} {action : Option ActionRaw}
      {output : Output (bits + 2) Typing}
      (observed : SourcePruningEnumerationSelectedStep.runPrefixWithNarrow
        (SourcePruningOuterNarrow.narrow holeKey fits admits) graph templates stop order metadata
        workFuel workFuel workFuel workFuel workFuel workFuel uv caller before queries =
        .narrowed checked prepared reached saved action (some after)
          (some [.ok ((false, updated), rightCore)]) none)
      (actionContinues : action ≠ some [])
      (preparedHistory : PreparedHistoryAt holeKey fits admits graph templates checkEmpty edgesOf stop order workFuel depth updated uv reached saved after index output)
      (input : CanonicalTotal before.core) (check : CanonicalTotal checked)
      (candidate : CanonicalTotal after.core)
      (qualifiedPreparation : QualifiedPreparedHistoryAt holeKey fits admits graph templates checkEmpty edgesOf stop order workFuel preparedHistory) :
      QualifiedOutputHistoryAt holeKey fits admits graph templates checkEmpty edgesOf stop order workFuel
        (OutputHistoryAt.selected observed actionContinues preparedHistory)

/-- Qualify the actual bucket and the exact recorded row and callback cuts. -/
inductive QualifiedPreparedHistoryAt
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (checkEmpty : Bool) (edgesOf : Node → List Edge)
    (stop : Option (Metadata Typing → Nat → Bool)) (order : Metadata Typing → List Nat → Option Nat)
    (workFuel : Nat) :
    {depth : Nat} → {metadata : Metadata Typing} → {uv : Nat} → {caller : Caller (bits + 2)} →
    {queries : Queries} → {before : Cached} → {index : Nat} → {output : Output (bits + 2) Typing} →
    PreparedHistoryAt holeKey fits admits graph templates checkEmpty edgesOf stop order workFuel
      depth metadata uv caller queries before index output → Prop where
  | opaque
      {depth uv target handle index : Nat} {metadata callbackMetadata : Metadata Typing}
      {caller completedCaller : Caller (bits + 2)} {queries saved : Queries}
      {before finished : Cached} {scs : List Suspended} {decoded value : Node}
      {heap : InternedConstructorTemplates.State Symbol Constraint} {entered callbackCore : Core}
      {fragment : Fragment} {output : Output (bits + 2) Typing}
      (preparation : SourcePruningEnumerationSelectedPreparation.run workFuel workFuel uv caller before =
        ([.ok ((target, handle, scs, decoded), entered)], some (.done value heap)))
      (mode : scs.any (fun sc => EqualityTrie.isTerminal sc.trie) = true ∨
        (match value with | .node .. => False | _ => True))
      (completed : SourcePruningEnumerationSharedSelectedOpaqueDispatch.run checkEmpty
        workFuel workFuel workFuel workFuel workFuel target scs value
        (SourcePruningEnumerationSelectedValueCaller.advance caller heap)
        (EnumerationExpandableIndex.frame entered before) queries =
        some (.complete fragment completedCaller saved finished))
      (recorded : ExceptT.run (SourcePruningRecordTypes.recordTypes graph templates workFuel metadata uv
        (.inl fragment) finished.core) = [.ok ((false, callbackMetadata), callbackCore)])
      (tail : OutputHistoryAt holeKey fits admits graph templates checkEmpty edgesOf stop order workFuel depth callbackMetadata completedCaller saved
        (EnumerationExpandableIndex.frame callbackCore finished)
        (SourcePruningEnumerationRestart.decision stop order callbackMetadata
          (EnumerationExpandableIndex.frame callbackCore finished)) index output)
      (input : CanonicalTotal before.core) (entry : CanonicalTotal entered)
      (bucket : ValidSuspended scs) (finalized : CanonicalTotal finished.core)
      (callback : CanonicalTotal (EnumerationExpandableIndex.frame callbackCore finished).core)
      (qualifiedTail : QualifiedOutputHistoryAt holeKey fits admits graph templates checkEmpty edgesOf stop order workFuel tail) :
      QualifiedPreparedHistoryAt holeKey fits admits graph templates checkEmpty edgesOf stop order workFuel
        (PreparedHistoryAt.opaque preparation mode completed recorded tail)
  | captured
      {depth uv target handle index rowIndex tailIndex : Nat}
      {metadata callbackMetadata : Metadata Typing}
      {caller rowCaller completedCaller : Caller (bits + 2)} {queries rowQueries saved : Queries}
      {before beforeFinalize finished : Cached} {scs : List Suspended} {decoded : Node}
      {entry : Cache.Interned InternedBinderProtocol.NodeKey} {rows : List Edge}
      {ordinaryDepth : Nat} {free : List InternedBinderProtocol.Reference}
      {heap : InternedConstructorTemplates.State Symbol Constraint} {entered callbackCore : Core}
      {attempted remaining : List Edge} {edge : Edge}
      {processed : List (SelectedEdge.Result (bits + 2))}
      {earlier later callbackEarlier callbackLater : List (Output (bits + 2) Typing)}
      {rowResult : Fold} {fragment : Fragment} {output : Output (bits + 2) Typing}
      (actual :
        let child := SourcePruningEnumerationSharedEagerChildren.eagerChild
          (width := bits + 2) (Output := Output (bits + 2) Typing) (Reason := Failure (bits + 2) Typing)
          checkEmpty workFuel workFuel workFuel workFuel workFuel edgesOf
        let recur := resumeWithNarrow child (SourcePruningOuterNarrow.narrow holeKey fits admits)
          graph templates checkEmpty edgesOf stop order workFuel depth
        let hook := continueWith recur graph templates stop order workFuel metadata uv
        let rootBefore := EnumerationExpandableIndex.frame entered before
        let rootCaller := SourcePruningEnumerationSelectedValueCaller.advance caller heap
        let visit := fun edge reached saved captured =>
          visitCapturedWith child hook workFuel target scs edge reached saved captured
        SourcePruningEnumerationSelectedPreparation.run workFuel workFuel uv caller before =
          ([.ok ((target, handle, scs, decoded), entered)],
            some (.done (.node entry rows ordinaryDepth free) heap)) ∧
        scs.any (fun sc => EqualityTrie.isTerminal sc.trie) = false ∧
        edgesOf (.node entry rows ordinaryDepth free) = attempted ++ edge :: remaining ∧
        scan visit rootBefore attempted rootCaller queries = .complete processed earlier rowCaller rowQueries ∧
        visit edge rowCaller rowQueries rootBefore = rowResult ∧
        (outputs rowResult)[rowIndex]? = some output ∧
        index = earlier.length + rowIndex ∧
        outputs (scan visit rootBefore (edgesOf (.node entry rows ordinaryDepth free)) rootCaller queries) =
          earlier ++ outputs rowResult ++ later ∧
        CapturedCallbackInvocationAt holeKey fits admits graph templates checkEmpty edgesOf stop order
          workFuel depth uv target metadata scs edge rowCaller rowQueries rootBefore rowIndex output
          fragment completedCaller saved beforeFinalize finished callbackMetadata callbackCore
          callbackEarlier callbackLater tailIndex ∧
        outputs rowResult = callbackEarlier ++ emitted (recur callbackMetadata completedCaller saved
          (EnumerationExpandableIndex.frame callbackCore finished)
          (SourcePruningEnumerationRestart.decision stop order callbackMetadata
            (EnumerationExpandableIndex.frame callbackCore finished))) ++ callbackLater ∧
        rowIndex = callbackEarlier.length + tailIndex)
      (tail : OutputHistoryAt holeKey fits admits graph templates checkEmpty edgesOf stop order workFuel depth callbackMetadata completedCaller saved
        (EnumerationExpandableIndex.frame callbackCore finished)
        (SourcePruningEnumerationRestart.decision stop order callbackMetadata
          (EnumerationExpandableIndex.frame callbackCore finished)) tailIndex output)
      (input : CanonicalTotal before.core) (entryFacts : CanonicalTotal entered)
      (bucket : ValidSuspended scs) (rowReturn : CanonicalTotal beforeFinalize.core)
      (finalized : CanonicalTotal finished.core)
      (callback : CanonicalTotal (EnumerationExpandableIndex.frame callbackCore finished).core)
      (qualifiedTail : QualifiedOutputHistoryAt holeKey fits admits graph templates checkEmpty edgesOf stop order workFuel tail) :
      QualifiedPreparedHistoryAt holeKey fits admits graph templates checkEmpty edgesOf stop order workFuel
        (PreparedHistoryAt.captured actual tail)
end

open SourcePruningEnumerationCapturedFinalizeRawAliases

omit [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node] in
private theorem canonical_false_recordTypes
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (fuel uv : Nat) (metadata updated : Metadata Typing) (fragment : Fragment)
    (before : Cached) (after : Core) (canonical : Canonical before.core)
    (recorded : ExceptT.run (SourcePruningRecordTypes.recordTypes graph templates fuel metadata uv
      (.inl fragment) before.core) = [.ok ((false, updated), after)]) :
    Canonical (EnumerationExpandableIndex.frame after before).core := by
  have successful : Success (SourcePruningRecordTypes.recordTypes graph templates fuel metadata uv
      (.inl fragment)) before.core (false, updated) after := by
    rw [Success, recorded]
    exact List.mem_singleton_self _
  have values := SourcePruningEnumerationPathRecordingValues.recordTypes_values
    graph templates fuel metadata uv (.inl fragment) before.core after (false, updated) successful
  intro value member
  change value ∈ after.values at member
  rw [values] at member
  exact canonical value member


private theorem canonical_opaque_complete
    (checkEmpty : Bool) (r n p h k target : Nat) (scs : List Suspended) (value : Node)
    (caller reached : Caller (bits + 2)) (before finished : Cached) (queries saved : Queries)
    (fragment : Fragment)
    (canonical : Canonical before.core) (valid : ValidSuspended scs)
    (actual : SourcePruningEnumerationSharedSelectedOpaqueDispatch.run checkEmpty r n p h k target
      scs value caller before queries = some (.complete fragment reached saved finished)) : Canonical finished.core := by
  cases terminal : scs.any (fun sc => EqualityTrie.isTerminal sc.trie) <;> cases value <;>
    simp only [SourcePruningEnumerationSharedSelectedOpaqueDispatch.run, Option.some.injEq, reduceCtorEq,
      terminal, Bool.not_true, Bool.not_false, ↓reduceIte] at actual
  all_goals
    split at actual
    · rename_i childFragment childReturned childCaller childQueries read waiting after called
      split at actual
      · rename_i finalCache finalized
        have receiptSame := Option.some.inj actual
        have cacheSame : finalCache = finished :=
          (SelectedEdge.Result.complete.inj receiptSame).2.2.2
        have childCanonical := SourcePruningEnumerationSharedChildCanonical.successful_canonical
          checkEmpty r n p h k scs _ caller childCaller before after queries childQueries
          childFragment childReturned read waiting canonical valid called
        rw [← cacheSame]
        exact SourcePruningEnumerationFinalize.run_canonical childCaller.checked.native.machine.heap
          k target childFragment after finalCache childCanonical finalized
      · cases actual
    · cases actual


omit [DecidableEq Symbol] [DecidableEq Node] in
private theorem canonical_parked_core
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (stop : Option (Metadata Typing → Nat → Bool)) (order : Metadata Typing → List Nat → Option Nat)
    (metadata updated : Metadata Typing) (workFuel uv : Nat) (caller : Caller (bits + 2))
    (queries : Queries) (before parked : Cached) (checked core : Core) (next : Option Next)
    (actual : SourcePruningEnumerationSelectedStep.runPrefix holeKey fits admits graph templates stop order metadata
      workFuel workFuel workFuel workFuel workFuel workFuel uv caller before queries =
      .parked checked (some parked) (some [.ok ((updated, next), core)])) :
    core = checked := by
  have restarted : ExceptT.run (SourcePruningEnumerationRestart.run stop order metadata parked checked) =
      [.ok ((updated, next), core)] := by
    have observed := actual
    unfold SourcePruningEnumerationSelectedStep.runPrefix
      SourcePruningEnumerationSelectedStep.runPrefixWithNarrow at observed
    dsimp only at observed
    split at observed
    · rename_i handle bucket readAfter reading
      split at observed
      · rename_i actualChecked checking
        obtain ⟨checkedSame, adapted, rawSame⟩ :=
          SourcePruningEnumerationSelectedStep.Result.parked.inj observed
        subst actualChecked
        rw [adapted, Option.map_some] at rawSame
        exact Option.some.inj rawSame
      all_goals repeat first | (solve | cases observed) | split at observed
    all_goals repeat first | (solve | cases observed) | split at observed
  change ((if SourcePruningEnumerationRestart.decision stop order metadata parked = some .stuck then []
    else [Except.ok ((metadata, SourcePruningEnumerationRestart.decision stop order metadata parked), checked)]) :
      List (Except EnumerationState.Error ((Metadata Typing × Option Next) × Core))) =
        [Except.ok ((updated, next), core)] at restarted
  split at restarted
  · cases restarted
  · have rowSame := Except.ok.inj (List.cons.inj restarted).1
    exact (congrArg Prod.snd rowSame).symm


private theorem alias_opaque_complete
    (checkEmpty : Bool) (r n p h k target : Nat) (scs : List Suspended) (value : Node)
    (caller reached : Caller (bits + 2)) (before finished : Cached) (queries saved : Queries)
    (fragment : Fragment)
    (actual : SourcePruningEnumerationSharedSelectedOpaqueDispatch.run checkEmpty r n p h k target
      scs value caller before queries = some (.complete fragment reached saved finished)) :
    ∀ left right, UnionFind.SameClass before.core.representatives left right →
      UnionFind.SameClass finished.core.representatives left right := by
  cases terminal : scs.any (fun sc => EqualityTrie.isTerminal sc.trie) <;> cases value <;>
    simp only [SourcePruningEnumerationSharedSelectedOpaqueDispatch.run, Option.some.injEq, reduceCtorEq,
      terminal, Bool.not_true, Bool.not_false, ↓reduceIte] at actual
  all_goals
    split at actual
    · rename_i childFragment childReturned childCaller childQueries read waiting after called
      split at actual
      · rename_i finalCache finalized
        have receiptSame := Option.some.inj actual
        have cacheSame : finalCache = finished :=
          (SelectedEdge.Result.complete.inj receiptSame).2.2.2
        have childAliases := SourcePruningEnumerationSharedChildRawAliasGrowth.successful_sameClass_forward
          checkEmpty r n p h k scs _ caller childCaller before after queries childQueries
          childFragment childReturned read waiting called
        have finalAliases := finalize_sameClass_forward childCaller.checked.native.machine.heap
          k target childFragment after finalCache finalized
        intro left right same
        rw [← cacheSame]
        exact finalAliases left right (childAliases.2 left right same).2
      · cases actual
    · cases actual


omit [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node] in
private theorem forward_total (before after : Core)
    (total : UnionFind.Total before.representatives)
    (aliases : ∀ left right, UnionFind.SameClass before.representatives left right →
      UnionFind.SameClass after.representatives left right) :
    UnionFind.Total after.representatives := by
  exact SourcePruningEnumerationStagedChildRoots.total_of_sameClass_forward
    before.representatives after.representatives total aliases

omit [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node] in
private theorem finalized_invariants
    (heap : InternedConstructorTemplates.State Symbol Constraint)
    (fuel target : Nat) (fragment : Fragment) (before after : Cached)
    (input : CanonicalTotal before.core)
    (observed : SourcePruningEnumerationFinalize.run heap fuel target fragment before = some after) :
    CanonicalTotal after.core := by
  exact ⟨SourcePruningEnumerationFinalize.run_canonical heap fuel target fragment before after input.1 observed,
    forward_total before.core after.core input.2
      (finalize_sameClass_forward heap fuel target fragment before after observed)⟩

omit [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node] in
private theorem callback_invariants
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (fuel uv : Nat) (metadata updated : Metadata Typing) (fragment : Fragment)
    (before : Cached) (after : Core) (input : CanonicalTotal before.core)
    (recorded : ExceptT.run (SourcePruningRecordTypes.recordTypes graph templates fuel metadata uv
      (.inl fragment) before.core) = [.ok ((false, updated), after)]) :
    CanonicalTotal (EnumerationExpandableIndex.frame after before).core := by
  exact ⟨canonical_false_recordTypes graph templates fuel uv metadata updated fragment before after input.1 recorded,
    forward_total before.core (EnumerationExpandableIndex.frame after before).core input.2
      (false_recordTypes_sameClass_forward graph templates fuel uv metadata updated fragment before after recorded)⟩

private theorem history_input_invariants
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (checkEmpty : Bool) (edgesOf : Node → List Edge)
    (stop : Option (Metadata Typing → Nat → Bool)) (order : Metadata Typing → List Nat → Option Nat)
    (workFuel : Nat) :
    (∀ (depth : Nat) (metadata : Metadata Typing) (caller : Caller (bits + 2))
      (queries : Queries) (before : Cached) (decision : Option Next)
      (index : Nat) (output : Output (bits + 2) Typing)
      (history : OutputHistoryAt holeKey fits admits graph templates checkEmpty edgesOf stop order workFuel
        depth metadata caller queries before decision index output),
      CanonicalTotal before.core →
        QualifiedOutputHistoryAt holeKey fits admits graph templates checkEmpty edgesOf stop order workFuel history) ∧
    (∀ (depth : Nat) (metadata : Metadata Typing) (uv : Nat) (caller : Caller (bits + 2))
      (queries : Queries) (before : Cached) (index : Nat) (output : Output (bits + 2) Typing)
      (history : PreparedHistoryAt holeKey fits admits graph templates checkEmpty edgesOf stop order workFuel
        depth metadata uv caller queries before index output),
      CanonicalTotal before.core →
        QualifiedPreparedHistoryAt holeKey fits admits graph templates checkEmpty edgesOf stop order workFuel history) := by
  have stoppedCase (depth : Nat) (metadata : Metadata Typing) (caller : Caller (bits + 2))
      (queries : Queries) (before : Cached) :
      CanonicalTotal before.core →
        QualifiedOutputHistoryAt holeKey fits admits graph templates checkEmpty edgesOf stop order workFuel
          (OutputHistoryAt.stopped depth metadata caller queries before) := by
    intro input
    exact .stopped depth metadata caller queries before input

  have doneCase (depth : Nat) (metadata : Metadata Typing) (caller : Caller (bits + 2))
      (queries : Queries) (before : Cached) :
      CanonicalTotal before.core →
        QualifiedOutputHistoryAt holeKey fits admits graph templates checkEmpty edgesOf stop order workFuel
          (OutputHistoryAt.done depth metadata caller queries before) := by
    intro input
    exact .done depth metadata caller queries before input

  have parkedCase
      {depth uv index : Nat} {metadata updated : Metadata Typing}
      {caller : Caller (bits + 2)} {queries : Queries} {before parkedCache : Cached}
      {checked core : Core} {next : Option Next} {output : Output (bits + 2) Typing}
      (observed : SourcePruningEnumerationSelectedStep.runPrefixWithNarrow
        (SourcePruningOuterNarrow.narrow holeKey fits admits) graph templates stop order metadata
        workFuel workFuel workFuel workFuel workFuel workFuel uv caller before queries =
        .parked checked (some parkedCache) (some [.ok ((updated, next), core)]))
      (tail : OutputHistoryAt holeKey fits admits graph templates checkEmpty edgesOf stop order workFuel depth updated caller queries
        (EnumerationExpandableIndex.frame core parkedCache) next index output)
      (tailIH : CanonicalTotal (EnumerationExpandableIndex.frame core parkedCache).core →
        QualifiedOutputHistoryAt holeKey fits admits graph templates checkEmpty edgesOf stop order workFuel tail) :
      CanonicalTotal before.core →
        QualifiedOutputHistoryAt holeKey fits admits graph templates checkEmpty edgesOf stop order workFuel
          (OutputHistoryAt.parked observed tail) := by
    intro input
    have prefixFacts := SourcePruningEnumerationPreparationEntryInvariants.runPrefix_entry_invariants
      holeKey fits admits graph templates stop order metadata
      workFuel workFuel workFuel workFuel workFuel workFuel uv caller before queries input.1 input.2
    have prefixObserved : SourcePruningEnumerationSelectedStep.runPrefix holeKey fits admits graph templates
        stop order metadata workFuel workFuel workFuel workFuel workFuel workFuel uv caller before queries =
          .parked checked (some parkedCache) (some [.ok ((updated, next), core)]) := observed
    rw [prefixObserved] at prefixFacts
    have checkedFacts : CanonicalTotal checked := ⟨prefixFacts.2.1, prefixFacts.1⟩
    have candidateFacts : CanonicalTotal parkedCache.core :=
      ⟨(prefixFacts.2.2 parkedCache rfl).2, (prefixFacts.2.2 parkedCache rfl).1⟩
    have same := canonical_parked_core holeKey fits admits graph templates stop order metadata updated
      workFuel uv caller queries before parkedCache checked core next prefixObserved
    have callbackFacts : CanonicalTotal (EnumerationExpandableIndex.frame core parkedCache).core := by
      change CanonicalTotal core
      rw [same]
      exact checkedFacts
    exact .parked observed tail input checkedFacts candidateFacts callbackFacts (tailIH callbackFacts)

  have selectedCase
      {depth uv index : Nat} {metadata updated : Metadata Typing}
      {caller reached : Caller (bits + 2)} {queries saved : Queries} {before after : Cached}
      {checked rightCore : Core} {prepared : Prepared} {action : Option ActionRaw}
      {output : Output (bits + 2) Typing}
      (observed : SourcePruningEnumerationSelectedStep.runPrefixWithNarrow
        (SourcePruningOuterNarrow.narrow holeKey fits admits) graph templates stop order metadata
        workFuel workFuel workFuel workFuel workFuel workFuel uv caller before queries =
        .narrowed checked prepared reached saved action (some after)
          (some [.ok ((false, updated), rightCore)]) none)
      (actionContinues : action ≠ some [])
      (preparedHistory : PreparedHistoryAt holeKey fits admits graph templates checkEmpty edgesOf stop order workFuel depth updated uv reached saved after index output)
      (preparedIH : CanonicalTotal after.core →
        QualifiedPreparedHistoryAt holeKey fits admits graph templates checkEmpty edgesOf stop order workFuel preparedHistory) :
      CanonicalTotal before.core →
        QualifiedOutputHistoryAt holeKey fits admits graph templates checkEmpty edgesOf stop order workFuel
          (OutputHistoryAt.selected observed actionContinues preparedHistory) := by
    intro input
    have prefixFacts := SourcePruningEnumerationPreparationEntryInvariants.runPrefix_entry_invariants
      holeKey fits admits graph templates stop order metadata
      workFuel workFuel workFuel workFuel workFuel workFuel uv caller before queries input.1 input.2
    have prefixObserved : SourcePruningEnumerationSelectedStep.runPrefix holeKey fits admits graph templates
        stop order metadata workFuel workFuel workFuel workFuel workFuel workFuel uv caller before queries =
          .narrowed checked prepared reached saved action (some after)
            (some [.ok ((false, updated), rightCore)]) none := observed
    rw [prefixObserved] at prefixFacts
    have checkedFacts : CanonicalTotal checked := ⟨prefixFacts.2.1, prefixFacts.1⟩
    have candidateFacts : CanonicalTotal after.core :=
      ⟨(prefixFacts.2.2 after rfl).2, (prefixFacts.2.2 after rfl).1⟩
    exact .selected observed actionContinues preparedHistory input checkedFacts candidateFacts
      (preparedIH candidateFacts)

  have opaqueCase
      {depth uv target handle index : Nat} {metadata callbackMetadata : Metadata Typing}
      {caller completedCaller : Caller (bits + 2)} {queries saved : Queries}
      {before finished : Cached} {scs : List Suspended} {decoded value : Node}
      {heap : InternedConstructorTemplates.State Symbol Constraint} {entered callbackCore : Core}
      {fragment : Fragment} {output : Output (bits + 2) Typing}
      (preparation : SourcePruningEnumerationSelectedPreparation.run workFuel workFuel uv caller before =
        ([.ok ((target, handle, scs, decoded), entered)], some (.done value heap)))
      (mode : scs.any (fun sc => EqualityTrie.isTerminal sc.trie) = true ∨
        (match value with | .node .. => False | _ => True))
      (completed : SourcePruningEnumerationSharedSelectedOpaqueDispatch.run checkEmpty
        workFuel workFuel workFuel workFuel workFuel target scs value
        (SourcePruningEnumerationSelectedValueCaller.advance caller heap)
        (EnumerationExpandableIndex.frame entered before) queries =
        some (.complete fragment completedCaller saved finished))
      (recorded : ExceptT.run (SourcePruningRecordTypes.recordTypes graph templates workFuel metadata uv
        (.inl fragment) finished.core) = [.ok ((false, callbackMetadata), callbackCore)])
      (tail : OutputHistoryAt holeKey fits admits graph templates checkEmpty edgesOf stop order workFuel depth callbackMetadata completedCaller saved
        (EnumerationExpandableIndex.frame callbackCore finished)
        (SourcePruningEnumerationRestart.decision stop order callbackMetadata
          (EnumerationExpandableIndex.frame callbackCore finished)) index output)
      (tailIH : CanonicalTotal (EnumerationExpandableIndex.frame callbackCore finished).core →
        QualifiedOutputHistoryAt holeKey fits admits graph templates checkEmpty edgesOf stop order workFuel tail) :
      CanonicalTotal before.core →
        QualifiedPreparedHistoryAt holeKey fits admits graph templates checkEmpty edgesOf stop order workFuel
          (PreparedHistoryAt.opaque preparation mode completed recorded tail) := by
    intro input
    have preparationFacts := SourcePruningEnumerationPreparationEntryInvariants.successful_preparation_entry_invariants
      workFuel workFuel uv target handle scs caller before entered decoded value heap input.1 input.2 preparation
    have entryFacts : CanonicalTotal entered := ⟨preparationFacts.2.1, preparationFacts.1⟩
    have bucketValid : ValidSuspended scs := preparationFacts.2.2.1
    have finishedCanonical := canonical_opaque_complete checkEmpty workFuel workFuel workFuel workFuel workFuel
      target scs value (SourcePruningEnumerationSelectedValueCaller.advance caller heap) completedCaller
      (EnumerationExpandableIndex.frame entered before) finished queries saved fragment
      entryFacts.1 bucketValid completed
    have finishedAliases := alias_opaque_complete checkEmpty workFuel workFuel workFuel workFuel workFuel
      target scs value (SourcePruningEnumerationSelectedValueCaller.advance caller heap) completedCaller
      (EnumerationExpandableIndex.frame entered before) finished queries saved fragment completed
    have finishedFacts : CanonicalTotal finished.core :=
      ⟨finishedCanonical, forward_total entered finished.core entryFacts.2 finishedAliases⟩
    have callbackFacts := callback_invariants graph templates workFuel uv metadata callbackMetadata
      fragment finished callbackCore finishedFacts recorded
    exact .opaque preparation mode completed recorded tail input entryFacts bucketValid finishedFacts
      callbackFacts (tailIH callbackFacts)

  have capturedCase
      {depth uv target handle index rowIndex tailIndex : Nat}
      {metadata callbackMetadata : Metadata Typing}
      {caller rowCaller completedCaller : Caller (bits + 2)} {queries rowQueries saved : Queries}
      {before beforeFinalize finished : Cached} {scs : List Suspended} {decoded : Node}
      {entry : Cache.Interned InternedBinderProtocol.NodeKey} {rows : List Edge}
      {ordinaryDepth : Nat} {free : List InternedBinderProtocol.Reference}
      {heap : InternedConstructorTemplates.State Symbol Constraint} {entered callbackCore : Core}
      {attempted remaining : List Edge} {edge : Edge}
      {processed : List (SelectedEdge.Result (bits + 2))}
      {earlier later callbackEarlier callbackLater : List (Output (bits + 2) Typing)}
      {rowResult : Fold} {fragment : Fragment} {output : Output (bits + 2) Typing}
      (actual :
        let child := SourcePruningEnumerationSharedEagerChildren.eagerChild
          (width := bits + 2) (Output := Output (bits + 2) Typing) (Reason := Failure (bits + 2) Typing)
          checkEmpty workFuel workFuel workFuel workFuel workFuel edgesOf
        let recur := resumeWithNarrow child (SourcePruningOuterNarrow.narrow holeKey fits admits)
          graph templates checkEmpty edgesOf stop order workFuel depth
        let hook := continueWith recur graph templates stop order workFuel metadata uv
        let rootBefore := EnumerationExpandableIndex.frame entered before
        let rootCaller := SourcePruningEnumerationSelectedValueCaller.advance caller heap
        let visit := fun edge reached saved captured =>
          visitCapturedWith child hook workFuel target scs edge reached saved captured
        SourcePruningEnumerationSelectedPreparation.run workFuel workFuel uv caller before =
          ([.ok ((target, handle, scs, decoded), entered)],
            some (.done (.node entry rows ordinaryDepth free) heap)) ∧
        scs.any (fun sc => EqualityTrie.isTerminal sc.trie) = false ∧
        edgesOf (.node entry rows ordinaryDepth free) = attempted ++ edge :: remaining ∧
        scan visit rootBefore attempted rootCaller queries = .complete processed earlier rowCaller rowQueries ∧
        visit edge rowCaller rowQueries rootBefore = rowResult ∧
        (outputs rowResult)[rowIndex]? = some output ∧
        index = earlier.length + rowIndex ∧
        outputs (scan visit rootBefore (edgesOf (.node entry rows ordinaryDepth free)) rootCaller queries) =
          earlier ++ outputs rowResult ++ later ∧
        CapturedCallbackInvocationAt holeKey fits admits graph templates checkEmpty edgesOf stop order
          workFuel depth uv target metadata scs edge rowCaller rowQueries rootBefore rowIndex output
          fragment completedCaller saved beforeFinalize finished callbackMetadata callbackCore
          callbackEarlier callbackLater tailIndex ∧
        outputs rowResult = callbackEarlier ++ emitted (recur callbackMetadata completedCaller saved
          (EnumerationExpandableIndex.frame callbackCore finished)
          (SourcePruningEnumerationRestart.decision stop order callbackMetadata
            (EnumerationExpandableIndex.frame callbackCore finished))) ++ callbackLater ∧
        rowIndex = callbackEarlier.length + tailIndex)
      (tail : OutputHistoryAt holeKey fits admits graph templates checkEmpty edgesOf stop order workFuel depth callbackMetadata completedCaller saved
        (EnumerationExpandableIndex.frame callbackCore finished)
        (SourcePruningEnumerationRestart.decision stop order callbackMetadata
          (EnumerationExpandableIndex.frame callbackCore finished)) tailIndex output)
      (tailIH : CanonicalTotal (EnumerationExpandableIndex.frame callbackCore finished).core →
        QualifiedOutputHistoryAt holeKey fits admits graph templates checkEmpty edgesOf stop order workFuel tail) :
      CanonicalTotal before.core →
        QualifiedPreparedHistoryAt holeKey fits admits graph templates checkEmpty edgesOf stop order workFuel
          (PreparedHistoryAt.captured actual tail) := by
    intro input
    have receipt := actual
    dsimp only at receipt
    obtain ⟨preparation, _nonterminal, _rowOrder, _completedPrefix, _rowRun, _rowHit,
      _rowOffset, _rowWhole, invoked, _callbackWhole, _callbackOffset⟩ := receipt
    have preparationFacts := SourcePruningEnumerationPreparationEntryInvariants.successful_preparation_entry_invariants
      workFuel workFuel uv target handle scs caller before entered decoded
      (.node entry rows ordinaryDepth free) heap input.1 input.2 preparation
    have entryFacts : CanonicalTotal entered := ⟨preparationFacts.2.1, preparationFacts.1⟩
    have bucketValid : ValidSuspended scs := preparationFacts.2.2.1
    have selectedReceipt := invoked
    dsimp only [CapturedCallbackInvocationAt] at selectedReceipt
    obtain ⟨selected, _selectedWhole, _selectedHit, _selectedOffset, finalized, recorded⟩ := selectedReceipt
    have rowCanonical := SourcePruningEnumerationInvocationCanonical.selected_complete_canonical
      checkEmpty workFuel workFuel workFuel workFuel workFuel edgesOf .eager _ scs edge
      rowCaller completedCaller (EnumerationExpandableIndex.frame entered before) beforeFinalize
      rowQueries saved rowIndex output fragment tailIndex entryFacts.1 bucketValid selected
    have rowAliases := SourcePruningEnumerationInvocationRawAliasGrowth.selected_complete_sameClass_forward
      checkEmpty workFuel workFuel workFuel workFuel workFuel edgesOf .eager _ scs edge
      rowCaller completedCaller (EnumerationExpandableIndex.frame entered before) beforeFinalize
      rowQueries saved rowIndex output fragment tailIndex selected
    have rowFacts : CanonicalTotal beforeFinalize.core :=
      ⟨rowCanonical, forward_total entered beforeFinalize.core entryFacts.2 rowAliases⟩
    have finishedFacts := finalized_invariants completedCaller.checked.native.machine.heap workFuel target
      fragment beforeFinalize finished rowFacts finalized
    have callbackFacts := callback_invariants graph templates workFuel uv metadata callbackMetadata
      fragment finished callbackCore finishedFacts recorded
    exact .captured actual tail input entryFacts bucketValid rowFacts finishedFacts callbackFacts (tailIH callbackFacts)

  constructor
  · intro depth metadata caller queries before decision index output history
    exact OutputHistoryAt.rec
      (motive_1 := fun _ _ _ _ before _ _ _ history =>
        CanonicalTotal before.core →
          QualifiedOutputHistoryAt holeKey fits admits graph templates checkEmpty edgesOf stop order workFuel history)
      (motive_2 := fun _ _ _ _ _ before _ _ history =>
        CanonicalTotal before.core →
          QualifiedPreparedHistoryAt holeKey fits admits graph templates checkEmpty edgesOf stop order workFuel history)
      @stoppedCase @doneCase @parkedCase @selectedCase @opaqueCase @capturedCase history
  · intro depth metadata uv caller queries before index output history
    exact PreparedHistoryAt.rec
      (motive_1 := fun _ _ _ _ before _ _ _ history =>
        CanonicalTotal before.core →
          QualifiedOutputHistoryAt holeKey fits admits graph templates checkEmpty edgesOf stop order workFuel history)
      (motive_2 := fun _ _ _ _ _ before _ _ history =>
        CanonicalTotal before.core →
          QualifiedPreparedHistoryAt holeKey fits admits graph templates checkEmpty edgesOf stop order workFuel history)
      @stoppedCase @doneCase @parkedCase @selectedCase @opaqueCase @capturedCase history

theorem output_history_input_invariants
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (checkEmpty : Bool) (edgesOf : Node → List Edge)
    (stop : Option (Metadata Typing → Nat → Bool)) (order : Metadata Typing → List Nat → Option Nat)
    (workFuel depth : Nat) (metadata : Metadata Typing) (caller : Caller (bits + 2))
    (queries : Queries) (before : Cached) (decision : Option Next)
    (index : Nat) (output : Output (bits + 2) Typing)
    (history : OutputHistoryAt holeKey fits admits graph templates checkEmpty edgesOf stop order workFuel
      depth metadata caller queries before decision index output)
    (canonical : Canonical before.core) (total : UnionFind.Total before.core.representatives) :
    QualifiedOutputHistoryAt holeKey fits admits graph templates checkEmpty edgesOf stop order workFuel history
 := by
  exact (history_input_invariants holeKey fits admits graph templates checkEmpty edgesOf stop order workFuel).1
    depth metadata caller queries before decision index output history ⟨canonical, total⟩

theorem prepared_history_input_invariants
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (checkEmpty : Bool) (edgesOf : Node → List Edge)
    (stop : Option (Metadata Typing → Nat → Bool)) (order : Metadata Typing → List Nat → Option Nat)
    (workFuel depth : Nat) (metadata : Metadata Typing) (uv : Nat) (caller : Caller (bits + 2))
    (queries : Queries) (before : Cached) (index : Nat) (output : Output (bits + 2) Typing)
    (history : PreparedHistoryAt holeKey fits admits graph templates checkEmpty edgesOf stop order workFuel
      depth metadata uv caller queries before index output)
    (canonical : Canonical before.core) (total : UnionFind.Total before.core.representatives) :
    QualifiedPreparedHistoryAt holeKey fits admits graph templates checkEmpty edgesOf stop order workFuel history
 := by
  exact (history_input_invariants holeKey fits admits graph templates checkEmpty edgesOf stop order workFuel).2
    depth metadata uv caller queries before index output history ⟨canonical, total⟩

theorem resumeWithNarrow_real_eager_qualified_output_history
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (checkEmpty : Bool) (edgesOf : Node → List Edge)
    (stop : Option (Metadata Typing → Nat → Bool)) (order : Metadata Typing → List Nat → Option Nat)
    (workFuel recursiveDepth : Nat) (metadata : Metadata Typing)
    (caller : Caller (bits + 2)) (queries : Queries) (before : Cached) (decision : Option Next)
    (index : Nat) (output : Output (bits + 2) Typing)
    (canonical : Canonical before.core) (total : UnionFind.Total before.core.representatives)
    (observed : (emitted (resumeWithNarrow
      (SourcePruningEnumerationSharedEagerChildren.eagerChild
        checkEmpty workFuel workFuel workFuel workFuel workFuel edgesOf)
      (SourcePruningOuterNarrow.narrow holeKey fits admits)
      graph templates checkEmpty edgesOf stop order workFuel recursiveDepth
      metadata caller queries before decision))[index]? = some output) :
    ∃ history : OutputHistoryAt holeKey fits admits graph templates checkEmpty edgesOf stop order workFuel
        recursiveDepth metadata caller queries before decision index output,
      QualifiedOutputHistoryAt holeKey fits admits graph templates checkEmpty edgesOf stop order workFuel history
 := by
  have history := resumeWithNarrow_real_eager_indexed_output_history holeKey fits admits graph templates
    checkEmpty edgesOf stop order workFuel recursiveDepth metadata caller queries before decision index output observed
  exact ⟨history, output_history_input_invariants holeKey fits admits graph templates checkEmpty edgesOf stop order
    workFuel recursiveDepth metadata caller queries before decision index output history canonical total⟩

end MicroCFTA.SourcePruningEnumerationCausalHistoryInputInvariants
