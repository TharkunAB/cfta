import MicroCFTA.SourcePruningEnumerationSharedEagerUnionNormalCPS
import MicroCFTA.SourcePruningEnumerationSharedPreparedRecursiveChildPolicy
import MicroCFTA.SourcePruningEnumerationSelectedPrefixUnionNormal
import MicroCFTA.SourcePruningEnumerationPreparationUnionNormal
import MicroCFTA.SourcePruningEnumerationSharedChildUnionNormal

set_option autoImplicit false

namespace MicroCFTA.SourcePruningEnumerationSharedEagerUnionNormal
open EnumerationState InternedConstructorTemplates
open SourceCurrentRequiredUnionNormal (UnionNormal)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Edge" => EdgeValue Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Queries" => SourceEndpointMemo.Memos
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Metadata" => SourcePruningRecordTypes.Metadata
variable {Typing Key : Type} {width : Nat}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]

open SourcePruningEnumerationSharedSelectedContinuations
local notation "Fragment" => Fragments.Fragment Symbol
local notation "Output" => SourcePruningEnumerationSharedPreparedRecursive.Output width Typing
local notation "Failure" => SourcePruningEnumerationSharedPreparedRecursive.Failure width Typing
local notation "Hook" => NativeContinuations.HookResult Output Failure width
local notation "Receipt" => SelectedEdge.Result width
local notation "Preparation" => SourcePruningEnumerationSharedPreparedContinuations.Preparation

omit [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node] in
private theorem whole_empty (caller : Caller width) (queries : Queries)
    (normal : UnionNormal caller.checked.native.machine.heap) :
    HookNormal (.complete [] caller queries : Hook) := by
  constructor
  · intro output impossible
    cases impossible
  · exact normal

omit [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node] in
private theorem whole_stopped (reason : Failure) (caller : Caller width) (queries : Queries)
    (normal : UnionNormal caller.checked.native.machine.heap) :
    HookNormal (.stopped [] reason (some (caller, queries)) : Hook) := by
  constructor
  · intro output impossible
    cases impossible
  · intro endpoint observed
    cases Option.some.inj observed
    exact normal

omit [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node] in
private theorem whole_single (metadata : Option (Metadata Typing)) (before : Cached)
    (caller : Caller width) (queries : Queries) (normal : UnionNormal caller.checked.native.machine.heap) :
    HookNormal (.complete [⟨metadata, before, caller, queries⟩] caller queries : Hook) := by
  constructor
  · intro output member
    have same := List.mem_singleton.mp member
    subst output
    exact normal
  · exact normal

omit [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node] in
private theorem whole_finish (uv : Nat)
    (actual : NativeContinuations.Result Output Failure width) (good : FoldNormal actual) :
    HookNormal (SourcePruningEnumerationSharedPreparedRecursive.finish uv actual) := by
  cases actual with
  | complete processed outputs caller queries => exact good
  | stopped processed outputs current =>
      cases current with
      | edge receipt endpoint =>
          constructor
          · exact good.1
          · intro reached observed
            cases Option.some.inj observed
            exact good.2
      | continuation receipt reason reached => exact good

private theorem whole_opaque_receipt
    (checkEmpty : Bool) (r n p h k target : Nat) (scs : List Suspended) (value : Node)
    (caller : Caller width) (before : Cached) (queries : Queries)
    (normal : UnionNormal caller.checked.native.machine.heap) :
    match SourcePruningEnumerationSharedSelectedOpaqueDispatch.run checkEmpty r n p h k target scs value caller before queries with
    | none => True
    | some receipt => ReceiptNormal receipt := by
  have childGood (operand : Node) :
      match (match ChildDispatch.run checkEmpty r n p h k scs operand caller before queries with
        | ((.ok (some [.ok (fragment, _returned)]), reached, saved, _outer, _waiting), some after) =>
            match SourcePruningEnumerationFinalize.run reached.checked.native.machine.heap k target fragment after with
            | some finished => some (SelectedEdge.Result.complete fragment reached saved finished)
            | none => some (SelectedEdge.Result.finalizeStopped fragment reached saved after)
        | (observation, candidate) => some (SelectedEdge.Result.stopped [] observation candidate)) with
      | none => True
      | some receipt => ReceiptNormal receipt := by
    have retained := SourcePruningEnumerationSharedChildUnionNormal.run_unionNormal
      checkEmpty r n p h k scs operand caller before queries normal
    generalize called : ChildDispatch.run checkEmpty r n p h k scs operand caller before queries = actual
      at retained ⊢
    obtain ⟨⟨result, reached, saved, outer, moved⟩, candidate⟩ := actual
    dsimp only at retained ⊢
    cases result with
    | error fault => exact retained
    | ok returned =>
        cases returned with
        | none => exact retained
        | some rows =>
            cases rows with
            | nil => exact retained
            | cons row tail =>
                cases row with
                | error rowError => exact retained
                | ok rowValue =>
                    obtain ⟨fragment, returned⟩ := rowValue
                    cases tail with
                    | cons second remaining => exact retained
                    | nil =>
                        cases candidate with
                        | none => exact retained
                        | some after =>
                            dsimp only
                            cases SourcePruningEnumerationFinalize.run reached.checked.native.machine.heap k target fragment after <;>
                              exact retained
  unfold SourcePruningEnumerationSharedSelectedOpaqueDispatch.run
  by_cases empty : value = .empty
  · rw [ite_eq_left empty]
    exact normal
  · rw [ite_eq_right empty]
    by_cases deferred : (match (generalizing := false) value with
        | .node .. => !(scs.any (fun sc => EqualityTrie.isTerminal sc.trie))
        | _ => false) = true
    · cases value <;> simp_all only [reduceCtorEq, Bool.false_eq_true, ite_true]
    · cases value <;> simp_all only [reduceCtorEq, Bool.false_eq_true, ite_false]
      all_goals exact childGood _

private theorem whole_opaque_hook
    (hook : Fragment → Caller width → Queries → Cached → Hook)
    (checkEmpty : Bool) (r n p h k target : Nat) (scs : List Suspended) (value : Node)
    (caller : Caller width) (before : Cached) (queries : Queries)
    (normal : UnionNormal caller.checked.native.machine.heap)
    (hookNormal : ∀ (fragment : Fragment) (reached : Caller width) (saved : Queries) (after : Cached),
      UnionNormal reached.checked.native.machine.heap → HookNormal (hook fragment reached saved after)) :
    FoldNormal (SourcePruningEnumerationSharedReceiptContinuation.run hook caller queries
      (SourcePruningEnumerationSharedSelectedOpaqueDispatch.run checkEmpty r n p h k target scs value caller before queries)) := by
  have good := whole_opaque_receipt checkEmpty r n p h k target scs value caller before queries normal
  cases observed : SourcePruningEnumerationSharedSelectedOpaqueDispatch.run checkEmpty r n p h k target scs value caller before queries with
  | none =>
      constructor
      · intro output impossible
        cases impossible
      · exact normal
  | some receipt =>
      rw [observed] at good
      exact receipt_continuation_unionNormal hook caller queries receipt normal good hookNormal

private theorem whole_prepared
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (checkEmpty : Bool) (edgesOf : Node → List Edge)
    (stop : Option (Metadata Typing → Nat → Bool)) (order : Metadata Typing → List Nat → Option Nat)
    (workFuel recursiveFuel : Nat) (metadata : Metadata Typing) (uv : Nat)
    (caller : Caller width) (queries : Queries) (before : Cached)
    (normal : UnionNormal caller.checked.native.machine.heap)
    (smallerDepth : ∀ (currentMetadata : Metadata Typing) (currentCaller : Caller width)
        (currentQueries : Queries) (currentCache : Cached) (currentDecision : Option Next),
        UnionNormal currentCaller.checked.native.machine.heap →
        HookNormal (SourcePruningEnumerationSharedPreparedRecursiveChildPolicy.resumeWithNarrow
          (SourcePruningEnumerationSharedEagerChildren.eagerChild
          checkEmpty workFuel workFuel workFuel workFuel workFuel edgesOf) (SourcePruningOuterNarrow.narrow holeKey fits admits)
          graph templates checkEmpty edgesOf stop order workFuel recursiveFuel currentMetadata currentCaller currentQueries currentCache currentDecision)) :
    let child := SourcePruningEnumerationSharedEagerChildren.eagerChild
          checkEmpty workFuel workFuel workFuel workFuel workFuel edgesOf
    let lower := SourcePruningEnumerationSharedPreparedRecursiveChildPolicy.resumeWithNarrow
          (SourcePruningEnumerationSharedEagerChildren.eagerChild
          checkEmpty workFuel workFuel workFuel workFuel workFuel edgesOf) (SourcePruningOuterNarrow.narrow holeKey fits admits)
          graph templates checkEmpty edgesOf stop order workFuel recursiveFuel
    let hook := SourcePruningEnumerationSharedPreparedRecursive.continueWith lower
      graph templates stop order workFuel metadata uv
    let actual := SourcePruningEnumerationSharedPreparedChildPolicy.runWithChild child hook
      checkEmpty workFuel workFuel workFuel workFuel workFuel workFuel workFuel uv edgesOf caller before queries
    UnionNormal (SourcePruningEnumerationSharedPreparedContinuations.preparation_endpoint caller queries actual.1).1.checked.native.machine.heap ∧
      ∀ folded, actual.2 = some folded → FoldNormal folded := by
  dsimp only
  have preparedNormal := SourcePruningEnumerationPreparationUnionNormal.run_endpoint_unionNormal
    workFuel workFuel uv caller before queries normal
  unfold SourcePruningEnumerationSharedPreparedChildPolicy.runWithChild
  dsimp only
  generalize prepared : SourcePruningEnumerationSelectedPreparation.run workFuel workFuel uv caller before = observation
    at preparedNormal ⊢
  constructor
  · exact preparedNormal
  · intro folded observed
    obtain ⟨raw, native⟩ := observation
    cases native with
    | none => cases observed
    | some actual =>
        cases actual with
        | failed fault heap => cases observed
        | done value heap =>
            have reachedNormal : UnionNormal
                (SourcePruningEnumerationSelectedValueCaller.advance caller heap).checked.native.machine.heap := preparedNormal
            have hookNormal : ∀ (fragment : Fragment) (reached : Caller width) (saved : Queries) (after : Cached),
                UnionNormal reached.checked.native.machine.heap →
                HookNormal (SourcePruningEnumerationSharedPreparedRecursive.continueWith
                  (SourcePruningEnumerationSharedPreparedRecursiveChildPolicy.resumeWithNarrow
                    (SourcePruningEnumerationSharedEagerChildren.eagerChild
                      checkEmpty workFuel workFuel workFuel workFuel workFuel edgesOf)
                    (SourcePruningOuterNarrow.narrow holeKey fits admits)
                    graph templates checkEmpty edgesOf stop order workFuel recursiveFuel)
                  graph templates stop order workFuel metadata uv fragment reached saved after) := by
              intro fragment reached saved after good
              exact continueWith_smaller_depth_unionNormal holeKey fits admits graph templates checkEmpty edgesOf
                stop order workFuel recursiveFuel metadata uv fragment reached saved after good smallerDepth
            cases raw with
            | nil => cases observed
            | cons row tail =>
                cases row with
                | error rowError => cases observed
                | ok rowValue =>
                    obtain ⟨⟨target, handle, scs, decoded⟩, entered⟩ := rowValue
                    cases tail with
                    | cons second remaining => cases observed
                    | nil =>
                        dsimp only at observed
                        have opaqueGood := whole_opaque_hook _ checkEmpty workFuel workFuel workFuel workFuel workFuel
                          target scs value (SourcePruningEnumerationSelectedValueCaller.advance caller heap)
                          (EnumerationExpandableIndex.frame entered before) queries reachedNormal hookNormal
                        cases terminal : scs.any (fun sc => EqualityTrie.isTerminal sc.trie) with
                        | true =>
                            rw [terminal] at observed
                            simp only [ite_true] at observed
                            cases Option.some.inj observed
                            exact opaqueGood
                        | false =>
                            rw [terminal] at observed
                            simp only [Bool.false_eq_true, ite_false] at observed
                            cases value with
                            | node entry rows depth free =>
                                cases Option.some.inj observed
                                exact configured_lower_depth_rows_unionNormal holeKey fits admits graph templates
                                  checkEmpty edgesOf stop order workFuel recursiveFuel metadata uv target scs
                                  (edgesOf (.node entry rows depth free))
                                  (SourcePruningEnumerationSelectedValueCaller.advance caller heap) queries
                                  (EnumerationExpandableIndex.frame entered before) reachedNormal smallerDepth
                            | empty | reference _ | union _ _ _ _ | mu _ _ _ _ =>
                                cases Option.some.inj observed
                                exact opaqueGood

private theorem whole_resume
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (checkEmpty : Bool) (edgesOf : Node → List Edge)
    (stop : Option (Metadata Typing → Nat → Bool)) (order : Metadata Typing → List Nat → Option Nat)
    (workFuel recursiveFuel : Nat) :
    ∀ (metadata : Metadata Typing) (caller : Caller width) (queries : Queries) (before : Cached) (decision : Option Next),
      UnionNormal caller.checked.native.machine.heap →
      HookNormal (SourcePruningEnumerationSharedPreparedRecursiveChildPolicy.resumeWithNarrow
        (SourcePruningEnumerationSharedEagerChildren.eagerChild
          checkEmpty workFuel workFuel workFuel workFuel workFuel edgesOf)
        (SourcePruningOuterNarrow.narrow holeKey fits admits)
        graph templates checkEmpty edgesOf stop order workFuel recursiveFuel metadata caller queries before decision) := by
  induction recursiveFuel with
  | zero =>
      intro metadata caller queries before decision normal
      cases decision with
      | none => exact whole_single (some metadata) before caller queries normal
      | some decision =>
          cases decision with
          | done => exact whole_single none before caller queries normal
          | stuck => exact whole_empty caller queries normal
          | expand uv => exact whole_stopped _ caller queries normal
  | succ fuel ih =>
      intro metadata caller queries before decision normal
      cases decision with
      | none => exact whole_single (some metadata) before caller queries normal
      | some decision =>
          cases decision with
          | done => exact whole_single none before caller queries normal
          | stuck => exact whole_empty caller queries normal
          | expand uv =>
              rw [SourcePruningEnumerationSharedPreparedRecursiveChildPolicy.resumeWithNarrow]
              dsimp only
              have prefixNormal := SourcePruningEnumerationSelectedPrefixUnionNormal.runPrefix_unionNormal
                holeKey fits admits graph templates stop order metadata
                workFuel workFuel workFuel workFuel workFuel workFuel uv caller before queries normal
              dsimp only [SourcePruningEnumerationSelectedStep.runPrefix] at prefixNormal
              generalize prefixObserved : SourcePruningEnumerationSelectedStep.runPrefixWithNarrow
                (SourcePruningOuterNarrow.narrow holeKey fits admits) graph templates stop order metadata
                workFuel workFuel workFuel workFuel workFuel workFuel uv caller before queries = actual at prefixNormal ⊢
              cases actual with
              | stopped read checked => exact whole_stopped _ caller queries normal
              | parked checked candidate raw =>
                  cases candidate with
                  | none => exact whole_stopped _ caller queries normal
                  | some parked =>
                      cases raw with
                      | none => exact whole_stopped _ caller queries normal
                      | some rows =>
                          cases rows with
                          | nil => exact whole_empty caller queries normal
                          | cons row tail =>
                              cases row with
                              | error rowError => exact whole_stopped _ caller queries normal
                              | ok rowValue =>
                                  obtain ⟨⟨updated, next⟩, core⟩ := rowValue
                                  cases tail with
                                  | nil => exact ih updated caller queries (EnumerationExpandableIndex.frame core parked) next normal
                                  | cons second remaining => exact whole_stopped _ caller queries normal
              | narrowed checked prepared reached saved action candidate right ordinary =>
                  have reachedNormal := prefixNormal.2
                  rcases action with _ | (_ | ⟨actionHead, actionTail⟩)
                  all_goals first | exact whole_empty reached saved reachedNormal | skip
                  all_goals
                    cases right with
                    | none => exact whole_stopped _ reached saved reachedNormal
                    | some rows =>
                        cases rows with
                        | nil => exact whole_stopped _ reached saved reachedNormal
                        | cons row tail =>
                            cases row with
                            | error rowError => exact whole_stopped _ reached saved reachedNormal
                            | ok rowValue =>
                                obtain ⟨⟨pruned, updated⟩, core⟩ := rowValue
                                cases pruned with
                                | true =>
                                    cases tail with
                                    | nil => exact whole_empty reached saved reachedNormal
                                    | cons second remaining => exact whole_stopped _ reached saved reachedNormal
                                | false =>
                                    cases tail with
                                    | cons second remaining => exact whole_stopped _ reached saved reachedNormal
                                    | nil =>
                                        cases candidate with
                                        | none => exact whole_stopped _ reached saved reachedNormal
                                        | some after =>
                                            cases ordinary with
                                            | some other => exact whole_stopped _ reached saved reachedNormal
                                            | none =>
                                                have good := whole_prepared holeKey fits admits graph templates checkEmpty
                                                  edgesOf stop order workFuel fuel updated uv reached saved after reachedNormal ih
                                                dsimp only at good ⊢
                                                generalize dispatched : SourcePruningEnumerationSharedPreparedChildPolicy.runWithChild
                                                  (SourcePruningEnumerationSharedEagerChildren.eagerChild
                                                    checkEmpty workFuel workFuel workFuel workFuel workFuel edgesOf)
                                                  (SourcePruningEnumerationSharedPreparedRecursive.continueWith
                                                    (SourcePruningEnumerationSharedPreparedRecursiveChildPolicy.resumeWithNarrow
                                                      (SourcePruningEnumerationSharedEagerChildren.eagerChild
                                                        checkEmpty workFuel workFuel workFuel workFuel workFuel edgesOf)
                                                      (SourcePruningOuterNarrow.narrow holeKey fits admits)
                                                      graph templates checkEmpty edgesOf stop order workFuel fuel)
                                                    graph templates stop order workFuel updated uv)
                                                  checkEmpty workFuel workFuel workFuel workFuel workFuel workFuel workFuel uv
                                                  edgesOf reached after saved = executed at good ⊢
                                                obtain ⟨preparation, folded⟩ := executed
                                                dsimp only at good ⊢
                                                cases folded with
                                                | none =>
                                                    exact whole_stopped _
                                                      (SourcePruningEnumerationSharedPreparedContinuations.preparation_endpoint
                                                        reached saved preparation).1
                                                      (SourcePruningEnumerationSharedPreparedContinuations.preparation_endpoint
                                                        reached saved preparation).2 good.1
                                                | some folded => exact whole_finish uv folded (good.2 folded rfl)

/-- Every real eager emission and returned endpoint retains the original heap normality. -/
theorem runEager_real_unionNormal_at_any_budget
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (checkEmpty : Bool) (edgesOf : Node → List Edge)
    (stop : Option (Metadata Typing → Nat → Bool)) (order : Metadata Typing → List Nat → Option Nat)
    (workFuel recursiveFuel : Nat) (metadata : Metadata Typing)
    (caller : Caller width) (queries : Queries) (before : Cached)
    (normal : UnionNormal caller.checked.native.machine.heap) :
    let actual := SourcePruningEnumerationSharedPreparedRecursiveChildPolicy.runEagerWithNarrow
      (SourcePruningOuterNarrow.narrow holeKey fits admits) graph templates checkEmpty edgesOf stop order
      workFuel recursiveFuel metadata caller queries before
    match actual with
    | .complete outputs reached _ =>
        (∀ output, output ∈ outputs → UnionNormal output.caller.checked.native.machine.heap) ∧
          UnionNormal reached.checked.native.machine.heap
    | .stopped outputs _ reached =>
        (∀ output, output ∈ outputs → UnionNormal output.caller.checked.native.machine.heap) ∧
          ∀ endpoint, reached = some endpoint → UnionNormal endpoint.1.checked.native.machine.heap := by
  change HookNormal (SourcePruningEnumerationSharedPreparedRecursiveChildPolicy.runEagerWithNarrow
    (SourcePruningOuterNarrow.narrow holeKey fits admits) graph templates checkEmpty edgesOf stop order
    workFuel recursiveFuel metadata caller queries before)
  unfold SourcePruningEnumerationSharedPreparedRecursiveChildPolicy.runEagerWithNarrow
    SourcePruningEnumerationSharedPreparedRecursiveChildPolicy.runWithNarrow
  exact whole_resume holeKey fits admits graph templates checkEmpty edgesOf stop order workFuel recursiveFuel
    metadata caller queries before (SourcePruningEnumerationRestart.decision stop order metadata before) normal

end MicroCFTA.SourcePruningEnumerationSharedEagerUnionNormal
