import MicroCFTA.SourcePruningEnumerationRealEagerCausalOutputHistory
import MicroCFTA.SourcePruningEnumerationOpaqueSuffixIsolation

namespace MicroCFTA.SourcePruningEnumerationParkedOuterHeldHistory
open SourcePruningEnumerationRealEagerCausalOutputHistory EnumerationDischargeHistory
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
variable {Typing Key : Type} {bits : Nat}
local notation "Fold" => NativeContinuations.Result (Output (bits + 2) Typing) (Failure (bits + 2) Typing) (bits + 2)
local notation "Prepared" => MergedSourceComparison.Result Symbol Constraint (Node × Option (EnumerateM Symbol Constraint Unit))
local notation "ActionRaw" => List (Except EnumerationState.Error (Unit × Core))
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]
set_option autoImplicit false

/- Note [Past held qualification over one outer history]
These proof-only relations retain the actual constructor fields jointly.
The relation's proof index associates it with an outer history.
Proof identity does not identify hidden constructor witnesses.
Consumers must obtain the call, row, receipt and index fields from one
held qualification derivation. They must not combine separate eliminations.
The relations assert past HeldFragmentHistory at each recorded outer entry.
This module defines the target. It proves no actual worker admission law.
-/

mutual
/-- Record the actual outer calls that produce one supplied indexed output. -/
inductive HeldOutputHistoryAt
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (checkEmpty : Bool) (edgesOf : Node → List Edge)
    (stop : Option (Metadata Typing → Nat → Bool)) (order : Metadata Typing → List Nat → Option Nat)
    (workFuel held heldHandle : Nat) (anchor : Core) :
    {depth : Nat} → {metadata : Metadata Typing} → {caller : Caller (bits + 2)} →
    {queries : Queries} → {before : Cached} → {decision : Option Next} →
    {index : Nat} → {output : Output (bits + 2) Typing} →
    OutputHistoryAt holeKey fits admits graph templates checkEmpty edgesOf stop order workFuel
      depth metadata caller queries before decision index output → Prop where
  | stopped (depth : Nat) (metadata : Metadata Typing) (caller : Caller (bits + 2))
      (queries : Queries) (before : Cached)
      (past : HeldFragmentHistory held heldHandle anchor before.core) :
      HeldOutputHistoryAt holeKey fits admits graph templates checkEmpty edgesOf stop order workFuel held heldHandle anchor
        (OutputHistoryAt.stopped depth metadata caller queries before)
  | done (depth : Nat) (metadata : Metadata Typing) (caller : Caller (bits + 2))
      (queries : Queries) (before : Cached)
      (past : HeldFragmentHistory held heldHandle anchor before.core) :
      HeldOutputHistoryAt holeKey fits admits graph templates checkEmpty edgesOf stop order workFuel held heldHandle anchor
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
      (past : HeldFragmentHistory held heldHandle anchor before.core)
      (tailPast : HeldOutputHistoryAt holeKey fits admits graph templates checkEmpty edgesOf stop order workFuel held heldHandle anchor tail) :
      HeldOutputHistoryAt holeKey fits admits graph templates checkEmpty edgesOf stop order workFuel held heldHandle anchor
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
      (past : HeldFragmentHistory held heldHandle anchor before.core)
      (preparedPast : HeldPreparedHistoryAt holeKey fits admits graph templates checkEmpty edgesOf stop order workFuel held heldHandle anchor preparedHistory) :
      HeldOutputHistoryAt holeKey fits admits graph templates checkEmpty edgesOf stop order workFuel held heldHandle anchor
        (OutputHistoryAt.selected observed actionContinues preparedHistory)

/-- Record the actual preparation and callback that supply an outer tail output. -/
inductive HeldPreparedHistoryAt
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (checkEmpty : Bool) (edgesOf : Node → List Edge)
    (stop : Option (Metadata Typing → Nat → Bool)) (order : Metadata Typing → List Nat → Option Nat)
    (workFuel held heldHandle : Nat) (anchor : Core) :
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
      (past : HeldFragmentHistory held heldHandle anchor before.core)
      (tailPast : HeldOutputHistoryAt holeKey fits admits graph templates checkEmpty edgesOf stop order workFuel held heldHandle anchor tail) :
      HeldPreparedHistoryAt holeKey fits admits graph templates checkEmpty edgesOf stop order workFuel held heldHandle anchor
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
      (past : HeldFragmentHistory held heldHandle anchor before.core)
      (tailPast : HeldOutputHistoryAt holeKey fits admits graph templates checkEmpty edgesOf stop order workFuel held heldHandle anchor tail) :
      HeldPreparedHistoryAt holeKey fits admits graph templates checkEmpty edgesOf stop order workFuel held heldHandle anchor
        (PreparedHistoryAt.captured actual tail)
end

end MicroCFTA.SourcePruningEnumerationParkedOuterHeldHistory

#check @MicroCFTA.SourcePruningEnumerationParkedOuterHeldHistory.HeldOutputHistoryAt
#print axioms MicroCFTA.SourcePruningEnumerationParkedOuterHeldHistory.HeldOutputHistoryAt
#check @MicroCFTA.SourcePruningEnumerationParkedOuterHeldHistory.HeldPreparedHistoryAt
#print axioms MicroCFTA.SourcePruningEnumerationParkedOuterHeldHistory.HeldPreparedHistoryAt
