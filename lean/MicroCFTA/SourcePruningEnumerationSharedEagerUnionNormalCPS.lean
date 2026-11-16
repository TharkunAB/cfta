import MicroCFTA.SourcePruningEnumerationSharedEagerUnionNormal
import MicroCFTA.SourcePruningEnumerationSharedChildUnionNormal
import MicroCFTA.SourcePruningEnumerationSharedReceiptContinuation

set_option autoImplicit false

namespace MicroCFTA.SourcePruningEnumerationSharedEagerUnionNormal
open EnumerationState InternedConstructorTemplates
open SourceCurrentRequiredUnionNormal (UnionNormal)
open SourcePruningEnumerationSharedSelectedContinuations
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Edge" => EdgeValue Symbol Constraint
local notation "Fragment" => Fragments.Fragment Symbol
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Queries" => SourceEndpointMemo.Memos
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Metadata" => SourcePruningRecordTypes.Metadata
variable {Typing Key : Type} {width : Nat}
local notation "Output" => SourcePruningEnumerationSharedPreparedRecursive.Output width Typing
local notation "Failure" => SourcePruningEnumerationSharedPreparedRecursive.Failure width Typing
local notation "Hook" => NativeContinuations.HookResult Output Failure width
local notation "Fold" => NativeContinuations.Result Output Failure width
local notation "Receipt" => SelectedEdge.Result width
local notation "Observation" => ChildDispatch.Observation width
local notation "Visitor" => List Suspended → Node → Caller width → Cached → Queries →
  (Fragment → Caller width → Queries → Cached → Fold) →
  (Observation → Option Cached → Fold) → Fold

/-- Read the exact output and native endpoint fields of an actual hook result. -/
def HookNormal (actual : Hook) : Prop :=
  match actual with
  | .complete outputs reached _ =>
      (∀ output, output ∈ outputs → UnionNormal output.caller.checked.native.machine.heap) ∧
        UnionNormal reached.checked.native.machine.heap
  | .stopped outputs _ reached =>
      (∀ output, output ∈ outputs → UnionNormal output.caller.checked.native.machine.heap) ∧
        ∀ endpoint, reached = some endpoint → UnionNormal endpoint.1.checked.native.machine.heap

/-- Read the exact outputs and complete or stopping native endpoint of an actual row fold. -/
def FoldNormal (actual : Fold) : Prop :=
  match actual with
  | .complete _ outputs reached _ =>
      (∀ output, output ∈ outputs → UnionNormal output.caller.checked.native.machine.heap) ∧
        UnionNormal reached.checked.native.machine.heap
  | .stopped _ outputs current =>
      (∀ output, output ∈ outputs → UnionNormal output.caller.checked.native.machine.heap) ∧
        match current with
        | .edge _ endpoint => UnionNormal endpoint.1.checked.native.machine.heap
        | .continuation _ _ reached =>
            ∀ endpoint, reached = some endpoint → UnionNormal endpoint.1.checked.native.machine.heap

/-- Read only the native caller retained by the actual selected receipt. -/
def ReceiptNormal (receipt : Receipt) : Prop :=
  match receipt with
  | .unhandled => True
  | .rejected reached _ _ | .finalizeStopped _ reached _ _ | .complete _ reached _ _ =>
      UnionNormal reached.checked.native.machine.heap
  | .stopped _ observation _ => UnionNormal observation.2.1.checked.native.machine.heap

/-- State the local CPS transfer law used inside the actual height and depth inductions. -/
def ChildPreserves (visit : Visitor) : Prop :=
  ∀ (scs : List Suspended) (incoming : Node) (caller : Caller width) (before : Cached) (queries : Queries)
    (done : Fragment → Caller width → Queries → Cached → Fold)
    (stopped : Observation → Option Cached → Fold),
    UnionNormal caller.checked.native.machine.heap →
    (∀ (fragment : Fragment) (reached : Caller width) (saved : Queries) (after : Cached), UnionNormal reached.checked.native.machine.heap →
      FoldNormal (done fragment reached saved after)) →
    (∀ (observation : Observation) (candidate : Option Cached), UnionNormal observation.2.1.checked.native.machine.heap →
      FoldNormal (stopped observation candidate)) →
    FoldNormal (visit scs incoming caller before queries done stopped)

private theorem empty_outputs :
    ∀ output, output ∈ ([] : List Output) → UnionNormal output.caller.checked.native.machine.heap := by
  intro output impossible
  cases impossible

private theorem advance_endpoint
    (receipt : Receipt) (caller : Caller width) (queries : Queries) (next : Caller width × Queries)
    (observed : NativeContinuations.advance receipt = some next) :
    NativeContinuations.endpoint receipt caller queries = next := by
  cases receipt with
  | unhandled => cases observed
  | rejected reached saved after => exact Option.some.inj observed
  | complete fragment reached saved after => exact Option.some.inj observed
  | finalizeStopped fragment reached saved after => cases observed
  | stopped completed observation candidate =>
      obtain ⟨result, reached, saved, outer, moved⟩ := observation
      cases result with
      | error fault => cases observed
      | ok returned =>
          cases returned with
          | none => cases observed
          | some rows =>
              cases rows with
              | cons row rest => cases observed
              | nil =>
                  cases candidate with
                  | none => cases observed
                  | some after => exact Option.some.inj observed

theorem receipt_continuation_unionNormal
    (hook : Fragment → Caller width → Queries → Cached → Hook)
    (caller : Caller width) (queries : Queries) (receipt : Receipt)
    (normal : UnionNormal caller.checked.native.machine.heap) (good : ReceiptNormal receipt)
    (hookNormal : ∀ (fragment : Fragment) (reached : Caller width) (saved : Queries) (after : Cached),
      UnionNormal reached.checked.native.machine.heap → HookNormal (hook fragment reached saved after)) :
    FoldNormal (SourcePruningEnumerationSharedReceiptContinuation.run hook caller queries (some receipt)) := by
  cases receipt with
  | unhandled => exact ⟨empty_outputs, normal⟩
  | rejected reached saved after => exact ⟨empty_outputs, good⟩
  | finalizeStopped fragment reached saved after => exact ⟨empty_outputs, good⟩
  | complete fragment reached saved after =>
      have retained := hookNormal fragment reached saved after good
      unfold SourcePruningEnumerationSharedReceiptContinuation.run
      dsimp only
      generalize called : hook fragment reached saved after = actual at retained ⊢
      cases actual <;> exact retained
  | stopped completed observation candidate =>
      cases advanced : NativeContinuations.advance (.stopped completed observation candidate) with
      | none =>
          simpa only [SourcePruningEnumerationSharedReceiptContinuation.run, advanced,
            NativeContinuations.endpoint, FoldNormal] using
            (show (∀ output, output ∈ ([] : List Output) → UnionNormal output.caller.checked.native.machine.heap) ∧
              UnionNormal observation.2.1.checked.native.machine.heap from ⟨empty_outputs, good⟩)
      | some next =>
          obtain ⟨reached, saved⟩ := next
          have same := advance_endpoint (.stopped completed observation candidate) caller queries (reached, saved) advanced
          have reachedNormal : UnionNormal
              (NativeContinuations.endpoint (.stopped completed observation candidate) caller queries).1.checked.native.machine.heap := good
          rw [same] at reachedNormal
          simpa only [SourcePruningEnumerationSharedReceiptContinuation.run, advanced, FoldNormal] using
            (show (∀ output, output ∈ ([] : List Output) → UnionNormal output.caller.checked.native.machine.heap) ∧
              UnionNormal reached.checked.native.machine.heap from ⟨empty_outputs, reachedNormal⟩)

/-- The actual ordered scan retains every emitted prefix and its native stopping endpoint. -/
theorem scan_unionNormal
    (visit : Edge → Caller width → Queries → Cached → Fold)
    (before : Cached) (rows : List Edge) (caller : Caller width) (queries : Queries)
    (normal : UnionNormal caller.checked.native.machine.heap)
    (visitNormal : ∀ (edge : Edge) (reached : Caller width) (saved : Queries) (captured : Cached), UnionNormal reached.checked.native.machine.heap →
      FoldNormal (visit edge reached saved captured)) :
    FoldNormal (SourcePruningEnumerationSharedBranching.scan visit before rows caller queries) := by
  induction rows generalizing caller queries with
  | nil => exact ⟨empty_outputs, normal⟩
  | cons edge rest ih =>
      have firstNormal := visitNormal edge caller queries before normal
      generalize visited : visit edge caller queries before = first at firstNormal
      cases first with
      | stopped processed outputs current =>
          simpa only [SourcePruningEnumerationSharedBranching.scan, visited] using firstNormal
      | complete processed outputs reached saved =>
          obtain ⟨outputsNormal, reachedNormal⟩ := firstNormal
          have laterNormal := ih reached saved reachedNormal
          rw [SourcePruningEnumerationSharedBranching.scan, visited]
          dsimp only
          cases laterObserved : SourcePruningEnumerationSharedBranching.scan visit before rest reached saved with
          | complete later remaining finalCaller finalQueries =>
              have finalNormal :
                  (∀ output, output ∈ remaining → UnionNormal output.caller.checked.native.machine.heap) ∧
                    UnionNormal finalCaller.checked.native.machine.heap := by
                simpa only [laterObserved, FoldNormal] using laterNormal
              constructor
              · intro output member
                rcases List.mem_append.mp member with firstMember | laterMember
                · exact outputsNormal output firstMember
                · exact finalNormal.1 output laterMember
              · exact finalNormal.2
          | stopped later remaining current =>
              have finalNormal := laterNormal
              rw [laterObserved] at finalNormal
              constructor
              · intro output member
                rcases List.mem_append.mp member with firstMember | laterMember
                · exact outputsNormal output firstMember
                · exact finalNormal.1 output laterMember
              · exact finalNormal.2

/-- Actual child tails compose their local callbacks at the returned native caller. -/
theorem visitChildren_unionNormal
    (visit : Visitor) (preserves : ChildPreserves visit)
    (done : List Fragment → Caller width → Queries → Cached → Fold)
    (stopped : List Fragment → Observation → Option Cached → Fold)
    (inputs : List (Node × List Suspended)) (caller : Caller width) (before : Cached) (queries : Queries)
    (normal : UnionNormal caller.checked.native.machine.heap)
    (doneNormal : ∀ (fragments : List Fragment) (reached : Caller width) (saved : Queries) (after : Cached), UnionNormal reached.checked.native.machine.heap →
      FoldNormal (done fragments reached saved after))
    (stopNormal : ∀ (fragments : List Fragment) (observation : Observation) (candidate : Option Cached), UnionNormal observation.2.1.checked.native.machine.heap →
      FoldNormal (stopped fragments observation candidate)) :
    FoldNormal (SourcePruningEnumerationSharedChildVisitors.visitChildren visit done stopped inputs caller before queries) := by
  induction inputs generalizing caller before queries done stopped with
  | nil => exact doneNormal [] caller queries before normal
  | cons input rest ih =>
      obtain ⟨value, bucket⟩ := input
      rw [SourcePruningEnumerationSharedChildVisitors.visitChildren]
      apply preserves bucket value caller before queries _ _ normal
      · intro fragment reached saved after reachedNormal
        apply ih _ _ _ _ _ reachedNormal
        · intro fragments current memos cache currentNormal
          exact doneNormal (fragment :: fragments) current memos cache currentNormal
        · intro completed observation candidate observationNormal
          exact stopNormal (fragment :: completed) observation candidate observationNormal
      · intro observation candidate observationNormal
        exact stopNormal [] observation candidate observationNormal

/-- The actual own-row prefix and child traversal preserve its receipt consumer. -/
theorem visitSelected_unionNormal
    (visit : Visitor) (preserves : ChildPreserves visit)
    (consume : Receipt → Fold) (scs : List Suspended) (edge : Edge)
    (caller : Caller width) (before : Cached) (queries : Queries)
    (normal : UnionNormal caller.checked.native.machine.heap)
    (consumeNormal : ∀ (receipt : Receipt), ReceiptNormal receipt → FoldNormal (consume receipt)) :
    FoldNormal (SourcePruningEnumerationSharedChildVisitors.visitSelected visit consume scs edge caller before queries) := by
  unfold SourcePruningEnumerationSharedChildVisitors.visitSelected
  generalize prepared : SourcePruningEnumerationCachedOwn.prepare caller.checked.native.machine.heap scs edge before = actual
  cases actual with
  | none => exact consumeNormal .unhandled True.intro
  | some rows =>
      cases rows with
      | nil => exact consumeNormal (.rejected caller queries before) normal
      | cons row tail =>
          cases tail with
          | cons second remaining => exact consumeNormal .unhandled True.intro
          | nil =>
              obtain ⟨⟨symbol, staged, residual⟩, middle⟩ := row
              apply visitChildren_unionNormal visit preserves _ _ _ caller middle queries normal
              · intro fragments reached saved after reachedNormal
                exact consumeNormal (.complete (Fragments.Fragment.node symbol fragments) reached saved
                  (SelectedEdge.finish residual (Fragments.Fragment.node symbol fragments) after)) reachedNormal
              · intro completed observation candidate observationNormal
                exact consumeNormal (.stopped completed observation candidate) observationNormal

/-- Actual captured finalization invokes its hook at the actual completed child endpoint. -/
theorem visitCapturedWith_unionNormal
    (visit : Visitor) (preserves : ChildPreserves visit)
    (hook : Fragment → Caller width → Queries → Cached → Hook)
    (k target : Nat) (scs : List Suspended) (edge : Edge)
    (caller : Caller width) (queries : Queries) (before : Cached)
    (normal : UnionNormal caller.checked.native.machine.heap)
    (hookNormal : ∀ (fragment : Fragment) (reached : Caller width) (saved : Queries) (after : Cached), UnionNormal reached.checked.native.machine.heap →
      HookNormal (hook fragment reached saved after)) :
    FoldNormal (SourcePruningEnumerationSharedChildVisitors.visitCapturedWith visit hook k target scs edge caller queries before) := by
  rw [SourcePruningEnumerationSharedChildVisitors.visitCapturedWith_eq_receipts]
  apply visitSelected_unionNormal visit preserves _ scs edge caller before queries normal
  intro receipt good
  cases receipt with
  | complete fragment reached saved after =>
      dsimp only
      cases finalized : SourcePruningEnumerationFinalize.run reached.checked.native.machine.heap k target fragment after with
      | none =>
          exact receipt_continuation_unionNormal hook caller queries
            (.finalizeStopped fragment reached saved after) normal good hookNormal
      | some finished =>
          exact receipt_continuation_unionNormal hook caller queries
            (.complete fragment reached saved finished) normal good hookNormal
  | unhandled =>
      exact receipt_continuation_unionNormal hook caller queries .unhandled normal good hookNormal
  | rejected reached saved after =>
      exact receipt_continuation_unionNormal hook caller queries
        (.rejected reached saved after) normal good hookNormal
  | stopped completed observation candidate =>
      exact receipt_continuation_unionNormal hook caller queries
        (.stopped completed observation candidate) normal good hookNormal
  | finalizeStopped fragment reached saved after =>
      exact receipt_continuation_unionNormal hook caller queries
        (.finalizeStopped fragment reached saved after) normal good hookNormal

private theorem shallow_preserves
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]
    (checkEmpty : Bool) (r n p h k : Nat) :
    ChildPreserves (Typing := Typing) (width := width)
      (SourcePruningEnumerationSharedChildVisitors.shallowVisit checkEmpty r n p h k) := by
  intro scs incoming caller before queries done stopped normal doneNormal stopNormal
  have retained := SourcePruningEnumerationSharedChildUnionNormal.run_unionNormal
    checkEmpty r n p h k scs incoming caller before queries normal
  unfold SourcePruningEnumerationSharedChildVisitors.shallowVisit
  generalize dispatched : ChildDispatch.run checkEmpty r n p h k scs incoming caller before queries = actual
    at retained ⊢
  obtain ⟨⟨result, reached, saved, outer, moved⟩, candidate⟩ := actual
  dsimp only at retained ⊢
  cases result with
  | error fault => exact stopNormal _ _ retained
  | ok returned =>
      cases returned with
      | none => exact stopNormal _ _ retained
      | some rows =>
          cases rows with
          | nil => exact stopNormal _ _ retained
          | cons row tail =>
              cases row with
              | error rowError => exact stopNormal _ _ retained
              | ok rowValue =>
                  obtain ⟨fragment, returned⟩ := rowValue
                  cases tail with
                  | cons second remaining => exact stopNormal _ _ retained
                  | nil =>
                      cases candidate with
                      | none => exact stopNormal _ _ retained
                      | some after => exact doneNormal fragment reached saved after retained

private theorem consume_selected_unionNormal
    (done : Fragment → Caller width → Queries → Cached → Fold)
    (caller : Caller width) (queries : Queries) (receipt : Receipt)
    (normal : UnionNormal caller.checked.native.machine.heap) (good : ReceiptNormal receipt)
    (doneNormal : ∀ (fragment : Fragment) (reached : Caller width) (saved : Queries) (after : Cached),
      UnionNormal reached.checked.native.machine.heap → FoldNormal (done fragment reached saved after)) :
    FoldNormal (SourcePruningEnumerationSharedEagerChildren.consumeSelected done caller queries receipt) := by
  cases receipt with
  | unhandled => exact ⟨empty_outputs, normal⟩
  | rejected reached saved after => exact ⟨empty_outputs, good⟩
  | finalizeStopped fragment reached saved after => exact ⟨empty_outputs, good⟩
  | complete fragment reached saved after =>
      have retained := doneNormal fragment reached saved after good
      unfold SourcePruningEnumerationSharedEagerChildren.consumeSelected
      dsimp only
      generalize called : done fragment reached saved after = actual at retained ⊢
      cases actual <;> exact retained
  | stopped completed observation candidate =>
      cases advanced : NativeContinuations.advance (.stopped completed observation candidate) with
      | none =>
          simpa only [SourcePruningEnumerationSharedEagerChildren.consumeSelected, advanced,
            NativeContinuations.endpoint, FoldNormal] using
            (show (∀ output, output ∈ ([] : List Output) → UnionNormal output.caller.checked.native.machine.heap) ∧
              UnionNormal observation.2.1.checked.native.machine.heap from ⟨empty_outputs, good⟩)
      | some next =>
          obtain ⟨reached, saved⟩ := next
          have same := advance_endpoint (.stopped completed observation candidate) caller queries (reached, saved) advanced
          have reachedNormal : UnionNormal
              (NativeContinuations.endpoint (.stopped completed observation candidate) caller queries).1.checked.native.machine.heap := good
          rw [same] at reachedNormal
          simpa only [SourcePruningEnumerationSharedEagerChildren.consumeSelected, advanced, FoldNormal] using
            (show (∀ output, output ∈ ([] : List Output) → UnionNormal output.caller.checked.native.machine.heap) ∧
              UnionNormal reached.checked.native.machine.heap from ⟨empty_outputs, reachedNormal⟩)

private theorem eagerChild_at_height
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]
    (checkEmpty : Bool) (r n p h k : Nat) (edgesOf : Node → List Edge) (bound : Nat) :
    ∀ (incoming : Node), MergedOrdinaryHeight.height incoming = bound →
    ∀ (scs : List Suspended) (caller : Caller width) (before : Cached) (queries : Queries)
      (done : Fragment → Caller width → Queries → Cached → Fold)
      (stopped : Observation → Option Cached → Fold),
      UnionNormal caller.checked.native.machine.heap →
      (∀ (fragment : Fragment) (reached : Caller width) (saved : Queries) (after : Cached),
        UnionNormal reached.checked.native.machine.heap → FoldNormal (done fragment reached saved after)) →
      (∀ (observation : Observation) (candidate : Option Cached),
        UnionNormal observation.2.1.checked.native.machine.heap → FoldNormal (stopped observation candidate)) →
      FoldNormal (SourcePruningEnumerationSharedEagerChildren.eagerChild checkEmpty r n p h k edgesOf
        scs incoming caller before queries done stopped) := by
  induction bound using Nat.strongRecOn with
  | ind bound ih =>
      intro incoming heightEq scs caller before queries done stopped normal doneNormal stopNormal
      cases ordinary : SourcePruningEnumerationSharedEagerChildren.ordinaryNonterminal scs incoming with
      | false =>
          rw [SourcePruningEnumerationSharedEagerChildren.eagerChild_fallback
            checkEmpty r n p h k edgesOf scs incoming caller before queries done stopped ordinary]
          exact shallow_preserves checkEmpty r n p h k scs incoming caller before queries
            done stopped normal doneNormal stopNormal
      | true =>
          rw [SourcePruningEnumerationSharedEagerChildren.eagerChild_ordinary
            checkEmpty r n p h k edgesOf scs incoming caller before queries done stopped ordinary]
          refine scan_unionNormal _ _ _ _ _ normal ?_
          intro edge reached saved captured reachedNormal
          refine visitSelected_unionNormal _ ?_ _ scs edge reached captured saved reachedNormal ?_
          · intro bucket child current cache memos yes no childNormal yesNormal noNormal
            dsimp only
            split
            · rename_i lower
              have childLt : MergedOrdinaryHeight.height child < bound := by omega
              exact ih (MergedOrdinaryHeight.height child) childLt child rfl bucket current cache memos
                yes no childNormal yesNormal noNormal
            · exact shallow_preserves checkEmpty r n p h k bucket child current cache memos
                yes no childNormal yesNormal noNormal
          · intro receipt good
            exact consume_selected_unionNormal done reached saved receipt reachedNormal good doneNormal

/-- The literal eager child satisfies its CPS transfer law by strict ordinary height. -/
theorem eagerChild_preserves
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]
    (checkEmpty : Bool) (r n p h k : Nat) (edgesOf : Node → List Edge) :
    ChildPreserves (Typing := Typing) (width := width)
      (SourcePruningEnumerationSharedEagerChildren.eagerChild checkEmpty r n p h k edgesOf) := by
  intro scs incoming caller before queries done stopped normal doneNormal stopNormal
  exact eagerChild_at_height checkEmpty r n p h k edgesOf (MergedOrdinaryHeight.height incoming)
    incoming rfl scs caller before queries done stopped normal doneNormal stopNormal

/-- The actual prepared ordinary row scan uses only the same configured lower-depth IH. -/
theorem configured_lower_depth_rows_unionNormal
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (checkEmpty : Bool) (edgesOf : Node → List Edge)
    (stop : Option (Metadata Typing → Nat → Bool)) (order : Metadata Typing → List Nat → Option Nat)
    (workFuel recursiveFuel : Nat) (metadata : Metadata Typing) (uv target : Nat)
    (scs : List Suspended) (rows : List Edge) (caller : Caller width) (queries : Queries) (before : Cached)
    (normal : UnionNormal caller.checked.native.machine.heap)
    (smallerDepth : ∀ (currentMetadata : Metadata Typing) (currentCaller : Caller width)
        (currentQueries : Queries) (currentCache : Cached) (currentDecision : Option Next),
        UnionNormal currentCaller.checked.native.machine.heap →
        HookNormal (SourcePruningEnumerationSharedPreparedRecursiveChildPolicy.resumeWithNarrow
          (SourcePruningEnumerationSharedEagerChildren.eagerChild
            checkEmpty workFuel workFuel workFuel workFuel workFuel edgesOf)
          (SourcePruningOuterNarrow.narrow holeKey fits admits)
          graph templates checkEmpty edgesOf stop order workFuel recursiveFuel currentMetadata currentCaller currentQueries currentCache currentDecision)) :
    let lower := SourcePruningEnumerationSharedPreparedRecursiveChildPolicy.resumeWithNarrow
          (SourcePruningEnumerationSharedEagerChildren.eagerChild
            checkEmpty workFuel workFuel workFuel workFuel workFuel edgesOf)
          (SourcePruningOuterNarrow.narrow holeKey fits admits)
          graph templates checkEmpty edgesOf stop order workFuel recursiveFuel
    let hook := SourcePruningEnumerationSharedPreparedRecursive.continueWith lower
      graph templates stop order workFuel metadata uv
    FoldNormal (SourcePruningEnumerationSharedBranching.scan
      (SourcePruningEnumerationSharedChildVisitors.visitCapturedWith
        (SourcePruningEnumerationSharedEagerChildren.eagerChild
          checkEmpty workFuel workFuel workFuel workFuel workFuel edgesOf)
        hook workFuel target scs) before rows caller queries) := by
  dsimp only
  refine scan_unionNormal _ _ _ _ _ normal ?_
  intro edge reached saved captured reachedNormal
  apply visitCapturedWith_unionNormal _
    (eagerChild_preserves checkEmpty workFuel workFuel workFuel workFuel workFuel edgesOf)
    _ workFuel target scs edge reached saved captured reachedNormal
  intro fragment current memos after currentNormal
  exact continueWith_smaller_depth_unionNormal holeKey fits admits graph templates checkEmpty edgesOf stop order
    workFuel recursiveFuel metadata uv fragment current memos after currentNormal smallerDepth

end MicroCFTA.SourcePruningEnumerationSharedEagerUnionNormal
