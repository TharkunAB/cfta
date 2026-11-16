import MicroCFTA.SourcePruningEnumerationSharedPreparedLiveRoot
import MicroCFTA.SourcePruningEnumerationSharedScanOutputOrigins
import MicroCFTA.SourcePruningEnumerationSharedPreparedRecursiveChildPolicy
import MicroCFTA.SourcePruningOuterNarrow

namespace MicroCFTA.SourcePruningEnumerationSharedPreparedRecursiveChildPolicy
open EnumerationState InternedConstructorTemplates
open SourcePruningEnumerationSharedSelectedContinuations
open SourcePruningEnumerationSharedPreparedRecursive (Output Failure emitted finish)
open SourcePruningEnumerationSharedBranching (scan)
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

theorem real_prepared_eager_captured_output_origin
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (checkEmpty : Bool) (edgesOf : Node → List Edge)
    (stop : Option (Metadata Typing → Nat → Bool)) (order : Metadata Typing → List Nat → Option Nat)
    (workFuel recursiveDepth uv : Nat) (metadata : Metadata Typing)
    (caller : Caller (bits + 2)) (before : Cached) (queries : Queries)
    (target handle : Nat) (scs : List Suspended) (decoded : Node)
    (entry : Cache.Interned InternedBinderProtocol.NodeKey) (rows : List Edge)
    (ordinaryDepth : Nat) (free : List InternedBinderProtocol.Reference)
    (heap : InternedConstructorTemplates.State Symbol Constraint) (entered : Core)
    (preparation : SourcePruningEnumerationSelectedPreparation.run workFuel workFuel uv caller before =
      ([.ok ((target, handle, scs, decoded), entered)], some (.done (.node entry rows ordinaryDepth free) heap)))
    (nonterminal : scs.any (fun sc => EqualityTrie.isTerminal sc.trie) = false)
    (index : Nat) (output : Output (bits + 2) Typing) :
    let child := SourcePruningEnumerationSharedEagerChildren.eagerChild
      (width := bits + 2) (Output := Output (bits + 2) Typing) (Reason := Failure (bits + 2) Typing)
      checkEmpty workFuel workFuel workFuel workFuel workFuel edgesOf
    let recur := resumeWithNarrow child (SourcePruningOuterNarrow.narrow holeKey fits admits)
      graph templates checkEmpty edgesOf stop order workFuel recursiveDepth
    let hook := SourcePruningEnumerationSharedPreparedRecursive.continueWith recur
      graph templates stop order workFuel metadata uv
    let selected := SourcePruningEnumerationSharedPreparedChildPolicy.runWithChild child hook
      checkEmpty workFuel workFuel workFuel workFuel workFuel workFuel workFuel uv edgesOf caller before queries
    let rootBefore := EnumerationExpandableIndex.frame entered before
    let rootCaller := SourcePruningEnumerationSelectedValueCaller.advance caller heap
    let visit := fun edge reached saved captured =>
      SourcePruningEnumerationSharedChildVisitors.visitCapturedWith child hook
        workFuel target scs edge reached saved captured
    (emitted (match selected.2 with
      | none => .stopped [] (.preparation uv selected.1)
          (some (SourcePruningEnumerationSharedPreparedContinuations.preparation_endpoint caller queries selected.1))
      | some folded => finish uv folded))[index]? = some output →
    ∃ (attempted : List Edge) (edge : Edge) (remaining : List Edge)
        (rowCaller : Caller (bits + 2)) (rowQueries : Queries)
        (processed : List (SelectedEdge.Result (bits + 2)))
        (earlier : List (Output (bits + 2) Typing))
        (rowResult : NativeContinuations.Result (Output (bits + 2) Typing) (Failure (bits + 2) Typing) (bits + 2))
        (localIndex : Nat),
      edgesOf (.node entry rows ordinaryDepth free) = attempted ++ edge :: remaining ∧
      scan visit rootBefore attempted rootCaller queries = .complete processed earlier rowCaller rowQueries ∧
      SourcePruningEnumerationSharedChildVisitors.visitCapturedWith child hook
        workFuel target scs edge rowCaller rowQueries rootBefore = rowResult ∧
      (outputs rowResult)[localIndex]? = some output ∧ index = earlier.length + localIndex := by
  dsimp only
  intro observedOutput
  let child := SourcePruningEnumerationSharedEagerChildren.eagerChild
    (width := bits + 2) (Output := Output (bits + 2) Typing) (Reason := Failure (bits + 2) Typing)
    checkEmpty workFuel workFuel workFuel workFuel workFuel edgesOf
  let recur := resumeWithNarrow child (SourcePruningOuterNarrow.narrow holeKey fits admits)
    graph templates checkEmpty edgesOf stop order workFuel recursiveDepth
  let hook := SourcePruningEnumerationSharedPreparedRecursive.continueWith recur
    graph templates stop order workFuel metadata uv
  let rootBefore := EnumerationExpandableIndex.frame entered before
  let rootCaller := SourcePruningEnumerationSelectedValueCaller.advance caller heap
  let visit := fun edge reached saved captured =>
    SourcePruningEnumerationSharedChildVisitors.visitCapturedWith child hook
      workFuel target scs edge reached saved captured
  have selectedSame :
      SourcePruningEnumerationSharedPreparedChildPolicy.runWithChild child hook
        checkEmpty workFuel workFuel workFuel workFuel workFuel workFuel workFuel uv edgesOf caller before queries =
      (([.ok ((target, handle, scs, decoded), entered)],
          some (.done (.node entry rows ordinaryDepth free) heap)),
        some (scan visit rootBefore (edgesOf (.node entry rows ordinaryDepth free)) rootCaller queries)) := by
    simp only [SourcePruningEnumerationSharedPreparedChildPolicy.runWithChild, preparation,
      nonterminal, Bool.false_eq_true, ↓reduceIte]
    rfl
  change (emitted (match (SourcePruningEnumerationSharedPreparedChildPolicy.runWithChild child hook
      checkEmpty workFuel workFuel workFuel workFuel workFuel workFuel workFuel uv edgesOf caller before queries).2 with
    | none => .stopped [] (.preparation uv
        (SourcePruningEnumerationSharedPreparedChildPolicy.runWithChild child hook
          checkEmpty workFuel workFuel workFuel workFuel workFuel workFuel workFuel uv edgesOf caller before queries).1)
        (some (SourcePruningEnumerationSharedPreparedContinuations.preparation_endpoint caller queries
          (SourcePruningEnumerationSharedPreparedChildPolicy.runWithChild child hook
            checkEmpty workFuel workFuel workFuel workFuel workFuel workFuel workFuel uv edgesOf caller before queries).1))
    | some folded => finish uv folded))[index]? = some output at observedOutput
  rw [selectedSame] at observedOutput
  change (emitted (finish uv
    (scan visit rootBefore (edgesOf (.node entry rows ordinaryDepth free)) rootCaller queries)))[index]? = some output
    at observedOutput
  have finishedOutputs : emitted (finish uv
      (scan visit rootBefore (edgesOf (.node entry rows ordinaryDepth free)) rootCaller queries)) =
      outputs (scan visit rootBefore (edgesOf (.node entry rows ordinaryDepth free)) rootCaller queries) := by
    cases scan visit rootBefore (edgesOf (.node entry rows ordinaryDepth free)) rootCaller queries <;> rfl
  rw [finishedOutputs] at observedOutput
  exact SourcePruningEnumerationSharedScanOutputOrigins.scan_output_origin
    visit rootBefore (edgesOf (.node entry rows ordinaryDepth free)) rootCaller queries index output observedOutput

end MicroCFTA.SourcePruningEnumerationSharedPreparedRecursiveChildPolicy
