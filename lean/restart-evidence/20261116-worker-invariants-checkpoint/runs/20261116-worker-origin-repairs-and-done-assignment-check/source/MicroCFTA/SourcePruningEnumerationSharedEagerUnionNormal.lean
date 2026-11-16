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

/-- Zero recursive depth retains normality at every actual real worker output and endpoint. -/
theorem runEager_real_zero_depth_unionNormal
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (checkEmpty : Bool) (edgesOf : Node → List Edge)
    (stop : Option (Metadata Typing → Nat → Bool)) (order : Metadata Typing → List Nat → Option Nat)
    (workFuel : Nat) (metadata : Metadata Typing)
    (caller : Caller width) (queries : Queries) (before : Cached)
    (normal : UnionNormal caller.checked.native.machine.heap) :
    let actual := SourcePruningEnumerationSharedPreparedRecursiveChildPolicy.runEagerWithNarrow
      (SourcePruningOuterNarrow.narrow holeKey fits admits) graph templates checkEmpty edgesOf stop order
      workFuel 0 metadata caller queries before
    match actual with
    | .complete outputs reached _ =>
        (∀ output, output ∈ outputs → UnionNormal output.caller.checked.native.machine.heap) ∧
          UnionNormal reached.checked.native.machine.heap
    | .stopped outputs _ reached =>
        (∀ output, output ∈ outputs → UnionNormal output.caller.checked.native.machine.heap) ∧
          ∀ endpoint, reached = some endpoint → UnionNormal endpoint.1.checked.native.machine.heap := by
  dsimp only
  unfold SourcePruningEnumerationSharedPreparedRecursiveChildPolicy.runEagerWithNarrow
    SourcePruningEnumerationSharedPreparedRecursiveChildPolicy.runWithNarrow
  cases selected : SourcePruningEnumerationRestart.decision stop order metadata before with
  | none =>
      constructor
      · intro output member
        have same := List.mem_singleton.mp member
        subst output
        exact normal
      · exact normal
  | some decision =>
      cases decision with
      | done =>
          constructor
          · intro output member
            have same := List.mem_singleton.mp member
            subst output
            exact normal
          · exact normal
      | stuck =>
          constructor
          · intro output impossible
            cases impossible
          · exact normal
      | expand uv =>
          constructor
          · intro output impossible
            cases impossible
          · intro endpoint observed
            have same : (caller, queries) = endpoint := Option.some.inj observed
            cases same
            exact normal

/-- The actual recordTypes callback retains normality from the same configured lower-depth worker. -/
theorem continueWith_smaller_depth_unionNormal
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (checkEmpty : Bool) (edgesOf : Node → List Edge)
    (stop : Option (Metadata Typing → Nat → Bool)) (order : Metadata Typing → List Nat → Option Nat)
    (workFuel recursiveFuel : Nat) (metadata : Metadata Typing) (uv : Nat)
    (fragment : Fragments.Fragment Symbol) (caller : Caller width) (queries : Queries) (before : Cached)
    (normal : UnionNormal caller.checked.native.machine.heap)
    (smallerDepth : ∀ (currentMetadata : Metadata Typing) (currentCaller : Caller width)
        (currentQueries : Queries) (currentCache : Cached) (currentDecision : Option Next),
        UnionNormal currentCaller.checked.native.machine.heap →
        let actual := SourcePruningEnumerationSharedPreparedRecursiveChildPolicy.resumeWithNarrow
          (SourcePruningEnumerationSharedEagerChildren.eagerChild
            checkEmpty workFuel workFuel workFuel workFuel workFuel edgesOf)
          (SourcePruningOuterNarrow.narrow holeKey fits admits)
          graph templates checkEmpty edgesOf stop order workFuel recursiveFuel currentMetadata currentCaller currentQueries currentCache currentDecision
        match actual with
        | .complete outputs reached _ =>
            (∀ output, output ∈ outputs → UnionNormal output.caller.checked.native.machine.heap) ∧
              UnionNormal reached.checked.native.machine.heap
        | .stopped outputs _ reached =>
            (∀ output, output ∈ outputs → UnionNormal output.caller.checked.native.machine.heap) ∧
              ∀ endpoint, reached = some endpoint → UnionNormal endpoint.1.checked.native.machine.heap) :
    let lower := SourcePruningEnumerationSharedPreparedRecursiveChildPolicy.resumeWithNarrow
          (SourcePruningEnumerationSharedEagerChildren.eagerChild
            checkEmpty workFuel workFuel workFuel workFuel workFuel edgesOf)
          (SourcePruningOuterNarrow.narrow holeKey fits admits)
          graph templates checkEmpty edgesOf stop order workFuel recursiveFuel
    let actual := SourcePruningEnumerationSharedPreparedRecursive.continueWith lower
      graph templates stop order workFuel metadata uv fragment caller queries before
    match actual with
    | .complete outputs reached _ =>
        (∀ output, output ∈ outputs → UnionNormal output.caller.checked.native.machine.heap) ∧
          UnionNormal reached.checked.native.machine.heap
    | .stopped outputs _ reached =>
        (∀ output, output ∈ outputs → UnionNormal output.caller.checked.native.machine.heap) ∧
          ∀ endpoint, reached = some endpoint → UnionNormal endpoint.1.checked.native.machine.heap := by
  dsimp only
  unfold SourcePruningEnumerationSharedPreparedRecursive.continueWith
  generalize callbackObserved : ExceptT.run (SourcePruningRecordTypes.recordTypes
    graph templates workFuel metadata uv (.inl fragment) before.core) = raw
  cases raw with
  | nil =>
      constructor
      · intro output impossible
        cases impossible
      · intro endpoint observed
        have same : (caller, queries) = endpoint := Option.some.inj observed
        cases same
        exact normal
  | cons row tail =>
      cases tail with
      | cons second remaining =>
          cases row with
          | error rowError =>
              constructor
              · intro output impossible
                cases impossible
              · intro endpoint observed
                have same : (caller, queries) = endpoint := Option.some.inj observed
                cases same
                exact normal
          | ok rowValue =>
              obtain ⟨⟨pruned, updated⟩, callbackCore⟩ := rowValue
              cases pruned with
              | false =>
                  constructor
                  · intro output impossible
                    cases impossible
                  · intro endpoint observed
                    have same : (caller, queries) = endpoint := Option.some.inj observed
                    cases same
                    exact normal
              | true =>
                  constructor
                  · intro output impossible
                    cases impossible
                  · intro endpoint observed
                    have same : (caller, queries) = endpoint := Option.some.inj observed
                    cases same
                    exact normal
      | nil =>
          cases row with
          | error rowError =>
              constructor
              · intro output impossible
                cases impossible
              · intro endpoint observed
                have same : (caller, queries) = endpoint := Option.some.inj observed
                cases same
                exact normal
          | ok rowValue =>
              obtain ⟨⟨pruned, updated⟩, callbackCore⟩ := rowValue
              cases pruned with
              | true =>
                  constructor
                  · intro output impossible
                    cases impossible
                  · exact normal
              | false =>
                  exact smallerDepth updated caller queries
                    (EnumerationExpandableIndex.frame callbackCore before)
                    (SourcePruningEnumerationRestart.decision stop order updated
                      (EnumerationExpandableIndex.frame callbackCore before)) normal

end MicroCFTA.SourcePruningEnumerationSharedEagerUnionNormal

#check MicroCFTA.SourcePruningEnumerationSharedEagerUnionNormal.runEager_real_zero_depth_unionNormal
#print axioms MicroCFTA.SourcePruningEnumerationSharedEagerUnionNormal.runEager_real_zero_depth_unionNormal
#check MicroCFTA.SourcePruningEnumerationSharedEagerUnionNormal.continueWith_smaller_depth_unionNormal
#print axioms MicroCFTA.SourcePruningEnumerationSharedEagerUnionNormal.continueWith_smaller_depth_unionNormal
