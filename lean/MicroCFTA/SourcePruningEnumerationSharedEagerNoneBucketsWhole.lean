import MicroCFTA.SourcePruningEnumerationSharedChildNoneBuckets
import MicroCFTA.SourcePruningEnumerationRealPrefixNoneBuckets
import MicroCFTA.SourcePruningEnumerationPreparationNoneBuckets
import MicroCFTA.SourcePruningEnumerationRecordTypesValues
import MicroCFTA.SourcePruningEnumerationSharedEagerNoneCachedWriters
import MicroCFTA.SourcePruningEnumerationSharedEagerUnionNormalCPS

set_option autoImplicit false
namespace MicroCFTA.SourcePruningEnumerationSharedEagerNoneBuckets
open EnumerationState InternedConstructorTemplates
open SourcePruningEnumerationSharedSelectedContinuations
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Edge" => EdgeValue Symbol Constraint
local notation "Core" => EnumerationState.State Symbol Constraint
local notation "Fragment" => Fragments.Fragment Symbol
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Queries" => SourceEndpointMemo.Memos
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Metadata" => SourcePruningRecordTypes.Metadata
variable {Typing Key : Type} {width : Nat}
local notation "OwnOutput" => SourcePruningEnumerationSharedPreparedRecursive.Output width Typing
local notation "OwnFailure" => SourcePruningEnumerationSharedPreparedRecursive.Failure width Typing
local notation "Hook" => NativeContinuations.HookResult OwnOutput OwnFailure width
local notation "Fold" => NativeContinuations.Result OwnOutput OwnFailure width
local notation "Receipt" => SelectedEdge.Result width
local notation "Observation" => ChildDispatch.Observation width
local notation "Visitor" => List Suspended → Node → Caller width → Cached → Queries →
  (Fragment → Caller width → Queries → Cached → Fold) →
  (Observation → Option Cached → Fold) → Fold

private def ReceiptNone (receipt : Receipt) : Prop :=
  ∀ state ∈ receiptCores receipt, NoneBucketsEmpty state
private def ObservationNone (observation : Observation) : Prop :=
  ∀ state ∈ childCores observation, NoneBucketsEmpty state
private def CandidateNone (candidate : Option Cached) : Prop :=
  ∀ after, candidate = some after → NoneBucketsEmpty after.core
private def OutputsNone (outputs : List OwnOutput) : Prop :=
  ∀ output ∈ outputs, NoneBucketsEmpty output.cache.core
private def ReceiptsNone (receipts : List Receipt) : Prop :=
  ∀ receipt ∈ receipts, ReceiptNone receipt
private def ReasonNone (reason : OwnFailure) : Prop :=
  ∀ state ∈ failureCores reason, NoneBucketsEmpty state
private def StopNone : NativeContinuations.Stop OwnFailure width → Prop
  | .edge receipt _ => ∀ retained ∈ receipt.toList, ReceiptNone retained
  | .continuation receipt reason _ => ReceiptNone receipt ∧ ReasonNone reason
private def FoldNone : Fold → Prop
  | .complete receipts outputs _ _ => ReceiptsNone receipts ∧ OutputsNone outputs
  | .stopped receipts outputs current => ReceiptsNone receipts ∧ OutputsNone outputs ∧ StopNone current
private def ChildNone (visit : Visitor) : Prop :=
  ∀ (scs : List Suspended) (incoming : Node) (caller : Caller width) (before : Cached) (queries : Queries)
    (done : Fragment → Caller width → Queries → Cached → Fold) (stopped : Observation → Option Cached → Fold),
    NoneBucketsEmpty before.core →
    (∀ (fragment : Fragment) (reached : Caller width) (saved : Queries) (after : Cached), NoneBucketsEmpty after.core → FoldNone (done fragment reached saved after)) →
    (∀ (observation : Observation) (candidate : Option Cached), ObservationNone observation → CandidateNone candidate → FoldNone (stopped observation candidate)) →
    FoldNone (visit scs incoming caller before queries done stopped)

universe u

private theorem list_empty {α : Type u} (P : α → Prop) : ∀ x ∈ ([] : List α), P x := by
  intro x impossible
  cases impossible
private theorem list_single {α : Type u} (P : α → Prop) (x : α) (valid : P x) : ∀ y ∈ [x], P y := by
  intro y member
  have same := List.mem_singleton.mp member
  subst y
  exact valid
private theorem list_append {α : Type u} (P : α → Prop) (left right : List α)
    (first : ∀ x ∈ left, P x) (later : ∀ x ∈ right, P x) : ∀ x ∈ left ++ right, P x := by
  intro x member
  rcases List.mem_append.mp member with member | member
  · exact first x member
  · exact later x member
private theorem list_cons {α : Type u} (P : α → Prop) (x : α) (xs : List α)
    (head : P x) (tail : ∀ y ∈ xs, P y) : ∀ y ∈ x :: xs, P y := by
  intro y member
  rcases List.mem_cons.mp member with same | member
  · subst y
    exact head
  · exact tail y member
private theorem one_state (state : Core) (good : NoneBucketsEmpty state) : ∀ current ∈ [state], NoneBucketsEmpty current :=
  list_single NoneBucketsEmpty state good

private theorem receipt_continuation_none
    (hook : Fragment → Caller width → Queries → Cached → Hook)
    (caller : Caller width) (queries : Queries) (receipt : Receipt) (good : ReceiptNone receipt)
    (hookGood : ∀ (fragment : Fragment) (reached : Caller width) (saved : Queries) (after : Cached), NoneBucketsEmpty after.core → Preserved (hook fragment reached saved after)) :
    FoldNone (SourcePruningEnumerationSharedReceiptContinuation.run hook caller queries (some receipt)) := by
  cases receipt with
  | complete fragment reached saved after =>
      have continued := hookGood fragment reached saved after (good after.core (List.mem_singleton_self _))
      unfold SourcePruningEnumerationSharedReceiptContinuation.run
      dsimp only
      generalize called : hook fragment reached saved after = actual at continued ⊢
      cases actual with
      | complete outputs finalCaller finalQueries => exact ⟨list_single ReceiptNone _ good, continued⟩
      | stopped outputs reason endpoint => exact ⟨list_empty ReceiptNone, continued.1, good, continued.2⟩
  | unhandled => exact ⟨list_empty ReceiptNone, list_empty _, list_single ReceiptNone _ good⟩
  | rejected reached saved after => exact ⟨list_single ReceiptNone _ good, list_empty _⟩
  | finalizeStopped fragment reached saved after => exact ⟨list_empty ReceiptNone, list_empty _, list_single ReceiptNone _ good⟩
  | stopped completed observation candidate =>
      cases advanced : NativeContinuations.advance (.stopped completed observation candidate) with
      | none =>
          simpa only [SourcePruningEnumerationSharedReceiptContinuation.run, advanced, FoldNone, StopNone, Option.toList_some] using
            (show ReceiptsNone [] ∧ OutputsNone [] ∧ (∀ retained ∈ [SelectedEdge.Result.stopped completed observation candidate], ReceiptNone retained) from
              ⟨list_empty ReceiptNone, list_empty _, list_single ReceiptNone _ good⟩)
      | some next =>
          obtain ⟨reached, saved⟩ := next
          simpa only [SourcePruningEnumerationSharedReceiptContinuation.run, advanced, FoldNone] using
            (show ReceiptsNone [.stopped completed observation candidate] ∧ OutputsNone [] from
              ⟨list_single ReceiptNone _ good, list_empty _⟩)

private theorem scan_none
    (visit : Edge → Caller width → Queries → Cached → Fold) (before : Cached) (rows : List Edge)
    (caller : Caller width) (queries : Queries) (initial : NoneBucketsEmpty before.core)
    (visitGood : ∀ (edge : Edge) (reached : Caller width) (saved : Queries) (captured : Cached), NoneBucketsEmpty captured.core → FoldNone (visit edge reached saved captured)) :
    FoldNone (SourcePruningEnumerationSharedBranching.scan visit before rows caller queries) := by
  induction rows generalizing caller queries with
  | nil => exact ⟨list_empty _, list_empty _⟩
  | cons edge rest ih =>
      have firstGood := visitGood edge caller queries before initial
      generalize visited : visit edge caller queries before = first at firstGood
      cases first with
      | stopped receipts outputs current =>
          simpa only [SourcePruningEnumerationSharedBranching.scan, visited] using firstGood
      | complete receipts outputs reached saved =>
          have laterGood := ih reached saved
          rw [SourcePruningEnumerationSharedBranching.scan, visited]
          dsimp only
          cases laterObserved : SourcePruningEnumerationSharedBranching.scan visit before rest reached saved with
          | complete later remaining finalCaller finalQueries =>
              rw [laterObserved] at laterGood
              exact ⟨list_append _ _ _ firstGood.1 laterGood.1, list_append _ _ _ firstGood.2 laterGood.2⟩
          | stopped later remaining current =>
              rw [laterObserved] at laterGood
              exact ⟨list_append _ _ _ firstGood.1 laterGood.1,
                list_append _ _ _ firstGood.2 laterGood.2.1, laterGood.2.2⟩

private theorem visit_children_none
    (visit : Visitor) (preserves : ChildNone visit)
    (done : List Fragment → Caller width → Queries → Cached → Fold)
    (stopped : List Fragment → Observation → Option Cached → Fold)
    (inputs : List (Node × List Suspended)) (caller : Caller width) (before : Cached) (queries : Queries)
    (initial : NoneBucketsEmpty before.core)
    (doneGood : ∀ (fragments : List Fragment) (reached : Caller width) (saved : Queries) (after : Cached), NoneBucketsEmpty after.core → FoldNone (done fragments reached saved after))
    (stopGood : ∀ (fragments : List Fragment) (observation : Observation) (candidate : Option Cached), ObservationNone observation → CandidateNone candidate → FoldNone (stopped fragments observation candidate)) :
    FoldNone (SourcePruningEnumerationSharedChildVisitors.visitChildren visit done stopped inputs caller before queries) := by
  induction inputs generalizing caller before queries done stopped with
  | nil => exact doneGood [] caller queries before initial
  | cons input rest ih =>
      obtain ⟨value, bucket⟩ := input
      rw [SourcePruningEnumerationSharedChildVisitors.visitChildren]
      apply preserves bucket value caller before queries _ _ initial
      · intro fragment reached saved after afterGood
        apply ih _ _ _ _ _ afterGood
        · intro fragments current memos cache cacheGood
          exact doneGood (fragment :: fragments) current memos cache cacheGood
        · intro fragments observation candidate observationGood candidateGood
          exact stopGood (fragment :: fragments) observation candidate observationGood candidateGood
      · intro observation candidate observationGood candidateGood
        exact stopGood [] observation candidate observationGood candidateGood

private theorem visit_selected_none
    (visit : Visitor) (preserves : ChildNone visit) (consume : Receipt → Fold)
    (scs : List Suspended) (edge : Edge) (caller : Caller width) (before : Cached) (queries : Queries)
    (initial : NoneBucketsEmpty before.core) (consumeGood : ∀ receipt, ReceiptNone receipt → FoldNone (consume receipt)) :
    FoldNone (SourcePruningEnumerationSharedChildVisitors.visitSelected visit consume scs edge caller before queries) := by
  unfold SourcePruningEnumerationSharedChildVisitors.visitSelected
  generalize prepared : SourcePruningEnumerationCachedOwn.prepare caller.checked.native.machine.heap scs edge before = actual
  cases actual with
  | none => exact consumeGood .unhandled (list_empty _)
  | some rows =>
      cases rows with
      | nil => exact consumeGood (.rejected caller queries before) (one_state before.core initial)
      | cons row tail =>
          cases tail with
          | cons second remaining => exact consumeGood .unhandled (list_empty _)
          | nil =>
              obtain ⟨⟨symbol, staged, residual⟩, middle⟩ := row
              have middleGood := SourcePruningEnumerationSharedEagerNoneCachedWriters.own_prefix_none_buckets
                caller.checked.native.machine.heap scs edge before _ initial prepared
                _ (List.mem_singleton_self _)
              apply visit_children_none visit preserves _ _ _ caller middle queries middleGood
              · intro fragments reached saved after afterGood
                exact consumeGood (.complete (.node symbol fragments) reached saved
                  (SelectedEdge.finish residual (.node symbol fragments) after)) (one_state _ afterGood)
              · intro fragments observation candidate observationGood candidateGood
                apply consumeGood (.stopped fragments observation candidate)
                intro state member
                rcases List.mem_append.mp member with seen | seen
                · exact observationGood state seen
                · cases candidate with
                  | none => cases seen
                  | some after =>
                      have same : state = after.core := List.mem_singleton.mp seen
                      subst state
                      exact candidateGood after rfl

private theorem captured_none
    (visit : Visitor) (preserves : ChildNone visit)
    (hook : Fragment → Caller width → Queries → Cached → Hook)
    (k target : Nat) (scs : List Suspended) (edge : Edge)
    (caller : Caller width) (queries : Queries) (before : Cached) (initial : NoneBucketsEmpty before.core)
    (hookGood : ∀ (fragment : Fragment) (reached : Caller width) (saved : Queries) (after : Cached), NoneBucketsEmpty after.core → Preserved (hook fragment reached saved after)) :
    FoldNone (SourcePruningEnumerationSharedChildVisitors.visitCapturedWith visit hook k target scs edge caller queries before) := by
  rw [SourcePruningEnumerationSharedChildVisitors.visitCapturedWith_eq_receipts]
  apply visit_selected_none visit preserves _ scs edge caller before queries initial
  intro receipt good
  cases receipt with
  | complete fragment reached saved after =>
      dsimp only
      cases finalized : SourcePruningEnumerationFinalize.run reached.checked.native.machine.heap k target fragment after with
      | none => exact receipt_continuation_none hook caller queries (.finalizeStopped fragment reached saved after) good hookGood
      | some finished =>
          have finishedGood := SourcePruningEnumerationSharedEagerNoneCachedWriters.finalize_none_buckets
            reached.checked.native.machine.heap k target fragment after finished
            (good after.core (List.mem_singleton_self _)) finalized
          exact receipt_continuation_none hook caller queries (.complete fragment reached saved finished) (one_state _ finishedGood) hookGood
  | unhandled => exact receipt_continuation_none hook caller queries .unhandled good hookGood
  | rejected reached saved after => exact receipt_continuation_none hook caller queries (.rejected reached saved after) good hookGood
  | stopped completed observation candidate => exact receipt_continuation_none hook caller queries (.stopped completed observation candidate) good hookGood
  | finalizeStopped fragment reached saved after => exact receipt_continuation_none hook caller queries (.finalizeStopped fragment reached saved after) good hookGood

private theorem shallow_none
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]
    (checkEmpty : Bool) (r n p h k : Nat) (scs : List Suspended) (incoming : Node)
    (caller : Caller width) (before : Cached) (queries : Queries)
    (done : Fragment → Caller width → Queries → Cached → Fold) (stopped : Observation → Option Cached → Fold)
    (initial : NoneBucketsEmpty before.core)
    (doneGood : ∀ (fragment : Fragment) (reached : Caller width) (saved : Queries) (after : Cached), NoneBucketsEmpty after.core → FoldNone (done fragment reached saved after))
    (stopGood : ∀ (observation : Observation) (candidate : Option Cached), ObservationNone observation → CandidateNone candidate → FoldNone (stopped observation candidate)) :
    FoldNone (SourcePruningEnumerationSharedChildVisitors.shallowVisit checkEmpty r n p h k scs incoming caller before queries done stopped) := by
  have retained := child_none_buckets checkEmpty r n p h k scs incoming caller before queries initial
  unfold SourcePruningEnumerationSharedChildVisitors.shallowVisit
  generalize called : ChildDispatch.run checkEmpty r n p h k scs incoming caller before queries = actual at retained ⊢
  split
  · exact doneGood _ _ _ _ (retained.2 _ rfl)
  · exact stopGood _ _ retained.1 retained.2

private theorem consume_none
    (done : Fragment → Caller width → Queries → Cached → Fold) (caller : Caller width) (queries : Queries)
    (receipt : Receipt) (good : ReceiptNone receipt)
    (doneGood : ∀ (fragment : Fragment) (reached : Caller width) (saved : Queries) (after : Cached), NoneBucketsEmpty after.core → FoldNone (done fragment reached saved after)) :
    FoldNone (SourcePruningEnumerationSharedEagerChildren.consumeSelected done caller queries receipt) := by
  cases receipt with
  | complete fragment reached saved after =>
      have actualGood := doneGood fragment reached saved after (good after.core (List.mem_singleton_self _))
      unfold SourcePruningEnumerationSharedEagerChildren.consumeSelected
      dsimp only
      generalize completed : done fragment reached saved after = actual at actualGood ⊢
      cases actual with
      | complete processed outputs finalCaller finalQueries =>
          exact ⟨list_cons ReceiptNone _ _ good actualGood.1, actualGood.2⟩
      | stopped processed outputs current =>
          exact ⟨list_cons ReceiptNone _ _ good actualGood.1, actualGood.2.1, actualGood.2.2⟩
  | unhandled => exact ⟨list_empty _, list_empty _, list_single ReceiptNone _ good⟩
  | rejected reached saved after => exact ⟨list_single ReceiptNone _ good, list_empty _⟩
  | finalizeStopped fragment reached saved after => exact ⟨list_empty _, list_empty _, list_single ReceiptNone _ good⟩
  | stopped completed observation candidate =>
      cases advanced : NativeContinuations.advance (.stopped completed observation candidate) with
      | none =>
          simpa only [SourcePruningEnumerationSharedEagerChildren.consumeSelected, advanced, FoldNone, StopNone, Option.toList_some] using
            (show ReceiptsNone [] ∧ OutputsNone [] ∧ (∀ retained ∈ [.stopped completed observation candidate], ReceiptNone retained) from
              ⟨list_empty _, list_empty _, list_single ReceiptNone _ good⟩)
      | some next =>
          obtain ⟨reached, saved⟩ := next
          simpa only [SourcePruningEnumerationSharedEagerChildren.consumeSelected, advanced, FoldNone] using
            (show ReceiptsNone [.stopped completed observation candidate] ∧ OutputsNone [] from
              ⟨list_single ReceiptNone _ good, list_empty _⟩)

private theorem eager_at_height
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]
    (checkEmpty : Bool) (r n p h k : Nat) (edgesOf : Node → List Edge) (bound : Nat) :
    ∀ (incoming : Node), MergedOrdinaryHeight.height incoming = bound →
    ∀ (scs : List Suspended) (caller : Caller width) (before : Cached) (queries : Queries)
      (done : Fragment → Caller width → Queries → Cached → Fold) (stopped : Observation → Option Cached → Fold),
      NoneBucketsEmpty before.core →
      (∀ (fragment : Fragment) (reached : Caller width) (saved : Queries) (after : Cached), NoneBucketsEmpty after.core → FoldNone (done fragment reached saved after)) →
      (∀ (observation : Observation) (candidate : Option Cached), ObservationNone observation → CandidateNone candidate → FoldNone (stopped observation candidate)) →
      FoldNone (SourcePruningEnumerationSharedEagerChildren.eagerChild checkEmpty r n p h k edgesOf
        scs incoming caller before queries done stopped) := by
  induction bound using Nat.strongRecOn with
  | ind bound ih =>
      intro incoming heightEq scs caller before queries done stopped initial doneGood stopGood
      cases ordinary : SourcePruningEnumerationSharedEagerChildren.ordinaryNonterminal scs incoming with
      | false =>
          rw [SourcePruningEnumerationSharedEagerChildren.eagerChild_fallback
            checkEmpty r n p h k edgesOf scs incoming caller before queries done stopped ordinary]
          exact shallow_none checkEmpty r n p h k scs incoming caller before queries done stopped initial doneGood stopGood
      | true =>
          rw [SourcePruningEnumerationSharedEagerChildren.eagerChild_ordinary
            checkEmpty r n p h k edgesOf scs incoming caller before queries done stopped ordinary]
          refine scan_none _ _ _ _ _ initial ?_
          intro edge reached saved captured capturedGood
          refine visit_selected_none _ ?_ _ scs edge reached captured saved capturedGood ?_
          · intro bucket child current cache memos yes no childGood yesGood noGood
            dsimp only
            split
            · rename_i lower
              have childLt : MergedOrdinaryHeight.height child < bound := by omega
              exact ih (MergedOrdinaryHeight.height child) childLt child rfl bucket current cache memos
                yes no childGood yesGood noGood
            · exact shallow_none checkEmpty r n p h k bucket child current cache memos yes no childGood yesGood noGood
          · intro receipt good
            exact consume_none done reached saved receipt good doneGood

private theorem eager_none
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]
    (checkEmpty : Bool) (r n p h k : Nat) (edgesOf : Node → List Edge) :
    ChildNone (Typing := Typing) (width := width)
      (SourcePruningEnumerationSharedEagerChildren.eagerChild checkEmpty r n p h k edgesOf) := by
  intro scs incoming caller before queries done stopped initial doneGood stopGood
  exact eager_at_height checkEmpty r n p h k edgesOf (MergedOrdinaryHeight.height incoming)
    incoming rfl scs caller before queries done stopped initial doneGood stopGood

private theorem hook_empty (caller : Caller width) (queries : Queries) :
    Preserved (.complete [] caller queries : Hook) := list_empty _

private theorem hook_single (metadata : Option (Metadata Typing)) (before : Cached)
    (caller : Caller width) (queries : Queries) (initial : NoneBucketsEmpty before.core) :
    Preserved (.complete [⟨metadata, before, caller, queries⟩] caller queries : Hook) := by
  exact list_single (fun output : OwnOutput => NoneBucketsEmpty output.cache.core) _ initial

private theorem hook_stopped (reason : OwnFailure) (endpoint : Option (Caller width × Queries))
    (good : ReasonNone reason) : Preserved (.stopped [] reason endpoint : Hook) :=
  ⟨list_empty _, good⟩

private theorem whole_finish (uv : Nat) (actual : Fold) (good : FoldNone actual) :
    Preserved (SourcePruningEnumerationSharedPreparedRecursive.finish uv actual) := by
  cases actual with
  | complete processed outputs caller queries => exact good.2
  | stopped processed outputs current =>
      constructor
      · exact good.2.1
      · cases current with
        | edge receipt endpoint =>
            intro state member
            change state ∈ processed.flatMap receiptCores ++ receipt.toList.flatMap receiptCores at member
            rcases List.mem_append.mp member with old | stopped
            · obtain ⟨retained, receiptMember, stateMember⟩ := List.mem_flatMap.mp old
              exact good.1 retained receiptMember state stateMember
            · obtain ⟨retained, receiptMember, stateMember⟩ := List.mem_flatMap.mp stopped
              exact good.2.2 retained receiptMember state stateMember
        | continuation receipt reason endpoint =>
            intro state member
            change state ∈ processed.flatMap receiptCores ++ receiptCores receipt ++ failureCores reason at member
            rcases List.mem_append.mp member with earlier | fromReason
            · rcases List.mem_append.mp earlier with fromProcessed | fromReceipt
              · obtain ⟨retained, receiptMember, stateMember⟩ := List.mem_flatMap.mp fromProcessed
                exact good.1 retained receiptMember state stateMember
              · exact good.2.2.1 state fromReceipt
            · exact good.2.2.2 state fromReason

private theorem callback_raw_none (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (fuel : Nat) (metadata : Metadata Typing) (uv : Nat) (fragment : Fragment) (before : Core)
    (initial : NoneBucketsEmpty before) :
    ∀ state ∈ rawCores (ExceptT.run (SourcePruningRecordTypes.recordTypes graph templates fuel metadata uv (.inl fragment) before)),
      NoneBucketsEmpty state := by
  intro state member
  obtain ⟨row, rawMember, retained⟩ := List.mem_flatMap.mp member
  cases row with
  | error fault => cases retained
  | ok payload =>
      obtain ⟨result, after⟩ := payload
      have same := List.mem_singleton.mp retained
      subst state
      exact SourcePruningEnumerationRecordTypesValues.record_types_none_buckets
        graph templates fuel metadata uv (.inl fragment) before after result initial rawMember

private theorem continue_none
    (recur : Metadata Typing → Caller width → Queries → Cached → Option Next → Hook)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (stop : Option (Metadata Typing → Nat → Bool)) (order : Metadata Typing → List Nat → Option Nat)
    (fuel : Nat) (metadata : Metadata Typing) (uv : Nat) (fragment : Fragment)
    (caller : Caller width) (queries : Queries) (before : Cached) (initial : NoneBucketsEmpty before.core)
    (lower : ∀ (metadata : Metadata Typing) (caller : Caller width) (queries : Queries) (before : Cached) (decision : Option Next), NoneBucketsEmpty before.core → Preserved (recur metadata caller queries before decision)) :
    Preserved (SourcePruningEnumerationSharedPreparedRecursive.continueWith recur graph templates stop order fuel metadata uv fragment caller queries before) := by
  have rawGood := callback_raw_none graph templates fuel metadata uv fragment before.core initial
  unfold SourcePruningEnumerationSharedPreparedRecursive.continueWith
  generalize observed : ExceptT.run (SourcePruningRecordTypes.recordTypes
    graph templates fuel metadata uv (.inl fragment) before.core) = raw at rawGood ⊢
  cases raw with
  | nil => exact hook_stopped _ _ rawGood
  | cons row tail =>
      cases tail with
      | cons second remaining =>
          cases row with
          | error fault => exact hook_stopped _ _ rawGood
          | ok payload =>
              obtain ⟨⟨answer, updated⟩, after⟩ := payload
              cases answer <;> exact hook_stopped _ _ rawGood
      | nil =>
          cases row with
          | error fault => exact hook_stopped _ _ rawGood
          | ok payload =>
              obtain ⟨⟨answer, updated⟩, after⟩ := payload
              cases answer with
              | true => exact hook_empty caller queries
              | false =>
                  apply lower
                  exact rawGood after (List.mem_singleton_self _)


private theorem stopped_receipt_none (fragments : List Fragment) (observation : Observation) (candidate : Option Cached)
    (observed : ObservationNone observation) (cached : CandidateNone candidate) :
    ReceiptNone (.stopped fragments observation candidate) := by
  intro state member
  rcases List.mem_append.mp member with fromObservation | fromCache
  · exact observed state fromObservation
  · cases candidate with
    | none => cases fromCache
    | some after =>
        have same : state = after.core := List.mem_singleton.mp fromCache
        subst state
        exact cached after rfl

private theorem opaque_receipt_none
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]
    (checkEmpty : Bool) (r n p h k target : Nat) (scs : List Suspended) (value : Node)
    (caller : Caller width) (before : Cached) (queries : Queries) (initial : NoneBucketsEmpty before.core) :
    match SourcePruningEnumerationSharedSelectedOpaqueDispatch.run checkEmpty r n p h k target scs value caller before queries with
    | none => True
    | some receipt => ReceiptNone receipt := by
  have childGood (operand : Node) :
      match (match ChildDispatch.run checkEmpty r n p h k scs operand caller before queries with
        | ((.ok (some [.ok (fragment, _returned)]), reached, saved, _outer, _waiting), some after) =>
            match SourcePruningEnumerationFinalize.run reached.checked.native.machine.heap k target fragment after with
            | some finished => some (SelectedEdge.Result.complete fragment reached saved finished)
            | none => some (SelectedEdge.Result.finalizeStopped fragment reached saved after)
        | (observation, candidate) => some (SelectedEdge.Result.stopped [] observation candidate)) with
      | none => True
      | some receipt => ReceiptNone receipt := by
    have retained := child_none_buckets checkEmpty r n p h k scs operand caller before queries initial
    generalize called : ChildDispatch.run checkEmpty r n p h k scs operand caller before queries = actual at retained ⊢
    obtain ⟨⟨result, reached, saved, outer, moved⟩, candidate⟩ := actual
    have stoppedGood := stopped_receipt_none [] (result, reached, saved, outer, moved) candidate retained.1 retained.2
    cases result with
    | error fault => exact stoppedGood
    | ok returned =>
        cases returned with
        | none => exact stoppedGood
        | some rows =>
            cases rows with
            | nil => exact stoppedGood
            | cons row tail =>
                cases row with
                | error fault => exact stoppedGood
                | ok rowValue =>
                    obtain ⟨fragment, returned⟩ := rowValue
                    cases tail with
                    | cons second remaining => exact stoppedGood
                    | nil =>
                        cases candidate with
                        | none => exact stoppedGood
                        | some after =>
                            have afterGood := retained.2 after rfl
                            dsimp only
                            cases finalized : SourcePruningEnumerationFinalize.run reached.checked.native.machine.heap k target fragment after with
                            | none => exact one_state after.core afterGood
                            | some finished =>
                                exact one_state finished.core
                                  (SourcePruningEnumerationSharedEagerNoneCachedWriters.finalize_none_buckets
                                    reached.checked.native.machine.heap k target fragment after finished afterGood finalized)
  unfold SourcePruningEnumerationSharedSelectedOpaqueDispatch.run
  by_cases empty : value = .empty
  · rw [ite_eq_left empty]
    exact one_state before.core initial
  · rw [ite_eq_right empty]
    by_cases deferred : (match (generalizing := false) value with
        | .node .. => !(scs.any (fun sc => EqualityTrie.isTerminal sc.trie))
        | _ => false) = true
    · cases value <;> simp_all only [reduceCtorEq, Bool.false_eq_true, ite_true]
    · cases value <;> simp_all only [reduceCtorEq, Bool.false_eq_true, ite_false]
      all_goals exact childGood _

private theorem opaque_hook_none
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]
    (hook : Fragment → Caller width → Queries → Cached → Hook)
    (checkEmpty : Bool) (r n p h k target : Nat) (scs : List Suspended) (value : Node)
    (caller : Caller width) (before : Cached) (queries : Queries) (initial : NoneBucketsEmpty before.core)
    (hookGood : ∀ (fragment : Fragment) (reached : Caller width) (saved : Queries) (after : Cached), NoneBucketsEmpty after.core → Preserved (hook fragment reached saved after)) :
    FoldNone (SourcePruningEnumerationSharedReceiptContinuation.run hook caller queries
      (SourcePruningEnumerationSharedSelectedOpaqueDispatch.run checkEmpty r n p h k target scs value caller before queries)) := by
  have good := opaque_receipt_none checkEmpty r n p h k target scs value caller before queries initial
  cases observed : SourcePruningEnumerationSharedSelectedOpaqueDispatch.run checkEmpty r n p h k target scs value caller before queries with
  | none => exact ⟨list_empty _, list_empty _, list_empty _⟩
  | some receipt =>
      rw [observed] at good
      exact receipt_continuation_none hook caller queries receipt good hookGood

private theorem prepared_none
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (checkEmpty : Bool) (edgesOf : Node → List Edge)
    (stop : Option (Metadata Typing → Nat → Bool)) (order : Metadata Typing → List Nat → Option Nat)
    (workFuel recursiveFuel : Nat) (metadata : Metadata Typing) (uv : Nat)
    (caller : Caller width) (queries : Queries) (before : Cached) (initial : NoneBucketsEmpty before.core)
    (lower : ∀ (currentMetadata : Metadata Typing) (currentCaller : Caller width) (currentQueries : Queries) (currentCache : Cached) (currentDecision : Option Next),
      NoneBucketsEmpty currentCache.core →
      Preserved (SourcePruningEnumerationSharedPreparedRecursiveChildPolicy.resumeWithNarrow
        (SourcePruningEnumerationSharedEagerChildren.eagerChild checkEmpty workFuel workFuel workFuel workFuel workFuel edgesOf)
        (SourcePruningOuterNarrow.narrow holeKey fits admits) graph templates checkEmpty edgesOf stop order
        workFuel recursiveFuel currentMetadata currentCaller currentQueries currentCache currentDecision)) :
    let child := SourcePruningEnumerationSharedEagerChildren.eagerChild checkEmpty workFuel workFuel workFuel workFuel workFuel edgesOf
    let lower := SourcePruningEnumerationSharedPreparedRecursiveChildPolicy.resumeWithNarrow child
      (SourcePruningOuterNarrow.narrow holeKey fits admits) graph templates checkEmpty edgesOf stop order workFuel recursiveFuel
    let hook := SourcePruningEnumerationSharedPreparedRecursive.continueWith lower graph templates stop order workFuel metadata uv
    let actual := SourcePruningEnumerationSharedPreparedChildPolicy.runWithChild child hook
      checkEmpty workFuel workFuel workFuel workFuel workFuel workFuel workFuel uv edgesOf caller before queries
    (∀ state ∈ rawCores actual.1.1, NoneBucketsEmpty state) ∧
      ∀ folded, actual.2 = some folded → FoldNone folded := by
  dsimp only
  have preparedGood := SourcePruningEnumerationPreparationNoneBuckets.preparation_none_buckets
    workFuel workFuel uv caller before initial
  unfold SourcePruningEnumerationSharedPreparedChildPolicy.runWithChild
  dsimp only
  generalize prepared : SourcePruningEnumerationSelectedPreparation.run workFuel workFuel uv caller before = observation at preparedGood ⊢
  constructor
  · exact preparedGood
  · intro folded observed
    obtain ⟨raw, native⟩ := observation
    cases native with
    | none => cases observed
    | some actual =>
        cases actual with
        | failed fault heap => cases observed
        | done value heap =>
            have hookGood : ∀ (fragment : Fragment) (reached : Caller width) (saved : Queries) (after : Cached), NoneBucketsEmpty after.core →
                Preserved (SourcePruningEnumerationSharedPreparedRecursive.continueWith
                  (SourcePruningEnumerationSharedPreparedRecursiveChildPolicy.resumeWithNarrow
                    (SourcePruningEnumerationSharedEagerChildren.eagerChild checkEmpty workFuel workFuel workFuel workFuel workFuel edgesOf)
                    (SourcePruningOuterNarrow.narrow holeKey fits admits) graph templates checkEmpty edgesOf stop order workFuel recursiveFuel)
                  graph templates stop order workFuel metadata uv fragment reached saved after) := by
              intro fragment reached saved after good
              exact continue_none _ graph templates stop order workFuel metadata uv fragment reached saved after good lower
            cases raw with
            | nil => cases observed
            | cons row tail =>
                cases row with
                | error fault => cases observed
                | ok rowValue =>
                    obtain ⟨⟨target, handle, scs, decoded⟩, entered⟩ := rowValue
                    cases tail with
                    | cons second remaining => cases observed
                    | nil =>
                        have enteredGood : NoneBucketsEmpty entered := preparedGood entered (List.mem_singleton_self _)
                        dsimp only at observed
                        have opaqueGood := opaque_hook_none _ checkEmpty workFuel workFuel workFuel workFuel workFuel
                          target scs value (SourcePruningEnumerationSelectedValueCaller.advance caller heap)
                          (EnumerationExpandableIndex.frame entered before) queries enteredGood hookGood
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
                                apply scan_none _ _ _ _ _ enteredGood
                                intro edge reached saved captured capturedGood
                                exact captured_none _ (eager_none checkEmpty workFuel workFuel workFuel workFuel workFuel edgesOf)
                                  _ workFuel target scs edge reached saved captured capturedGood hookGood
                            | empty | reference _ | union _ _ _ _ | mu _ _ _ _ =>
                                cases Option.some.inj observed
                                exact opaqueGood


private theorem resume_none
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (checkEmpty : Bool) (edgesOf : Node → List Edge)
    (stop : Option (Metadata Typing → Nat → Bool)) (order : Metadata Typing → List Nat → Option Nat)
    (workFuel recursiveFuel : Nat) :
    ∀ (metadata : Metadata Typing) (caller : Caller width) (queries : Queries) (before : Cached) (decision : Option Next),
      NoneBucketsEmpty before.core →
      Preserved (SourcePruningEnumerationSharedPreparedRecursiveChildPolicy.resumeWithNarrow
        (SourcePruningEnumerationSharedEagerChildren.eagerChild checkEmpty workFuel workFuel workFuel workFuel workFuel edgesOf)
        (SourcePruningOuterNarrow.narrow holeKey fits admits) graph templates checkEmpty edgesOf stop order
        workFuel recursiveFuel metadata caller queries before decision) := by
  induction recursiveFuel with
  | zero =>
      intro metadata caller queries before decision initial
      cases decision with
      | none => exact hook_single (some metadata) before caller queries initial
      | some decision =>
          cases decision with
          | done => exact hook_single none before caller queries initial
          | stuck => exact hook_empty caller queries
          | expand uv => exact hook_stopped _ _ (one_state before.core initial)
  | succ fuel ih =>
      intro metadata caller queries before decision initial
      cases decision with
      | none => exact hook_single (some metadata) before caller queries initial
      | some decision =>
          cases decision with
          | done => exact hook_single none before caller queries initial
          | stuck => exact hook_empty caller queries
          | expand uv =>
              rw [SourcePruningEnumerationSharedPreparedRecursiveChildPolicy.resumeWithNarrow]
              dsimp only
              have prefixGood := SourcePruningEnumerationRealPrefixNoneBuckets.real_prefix_none_buckets
                holeKey fits admits graph templates stop order metadata
                workFuel workFuel workFuel workFuel workFuel workFuel uv caller before queries initial
              dsimp only [SourcePruningEnumerationSelectedStep.runPrefix] at prefixGood
              generalize prefixObserved : SourcePruningEnumerationSelectedStep.runPrefixWithNarrow
                (SourcePruningOuterNarrow.narrow holeKey fits admits) graph templates stop order metadata
                workFuel workFuel workFuel workFuel workFuel workFuel uv caller before queries = actual at prefixGood ⊢
              cases actual with
              | stopped read checked => exact hook_stopped _ _ prefixGood
              | parked checked candidate raw =>
                  cases candidate with
                  | none => exact hook_stopped _ _ prefixGood
                  | some parked =>
                      cases raw with
                      | none => exact hook_stopped _ _ prefixGood
                      | some rows =>
                          cases rows with
                          | nil => exact hook_empty caller queries
                          | cons row tail =>
                              cases row with
                              | error fault => exact hook_stopped _ _ prefixGood
                              | ok rowValue =>
                                  obtain ⟨⟨updated, next⟩, core⟩ := rowValue
                                  cases tail with
                                  | nil =>
                                      apply ih updated caller queries (EnumerationExpandableIndex.frame core parked) next
                                      exact prefixGood core (by simp [selectedCores, rawCores])
                                  | cons second remaining => exact hook_stopped _ _ prefixGood
              | narrowed checked prepared reached saved action candidate right ordinary =>
                  rcases action with _ | (_ | ⟨actionHead, actionTail⟩)
                  all_goals first | exact hook_empty reached saved | skip
                  all_goals
                    cases right with
                    | none => exact hook_stopped _ _ prefixGood
                    | some rows =>
                        cases rows with
                        | nil => exact hook_stopped _ _ prefixGood
                        | cons row tail =>
                            cases row with
                            | error fault => exact hook_stopped _ _ prefixGood
                            | ok rowValue =>
                                obtain ⟨⟨pruned, updated⟩, core⟩ := rowValue
                                cases pruned with
                                | true =>
                                    cases tail with
                                    | nil => exact hook_empty reached saved
                                    | cons second remaining => exact hook_stopped _ _ prefixGood
                                | false =>
                                    cases tail with
                                    | cons second remaining => exact hook_stopped _ _ prefixGood
                                    | nil =>
                                        cases candidate with
                                        | none => exact hook_stopped _ _ prefixGood
                                        | some after =>
                                            cases ordinary with
                                            | some other => exact hook_stopped _ _ prefixGood
                                            | none =>
                                                have afterGood : NoneBucketsEmpty after.core := prefixGood after.core (by simp [selectedCores])
                                                have good := prepared_none holeKey fits admits graph templates checkEmpty edgesOf
                                                  stop order workFuel fuel updated uv reached saved after afterGood ih
                                                dsimp only at good ⊢
                                                generalize dispatched : SourcePruningEnumerationSharedPreparedChildPolicy.runWithChild
                                                  (SourcePruningEnumerationSharedEagerChildren.eagerChild checkEmpty workFuel workFuel workFuel workFuel workFuel edgesOf)
                                                  (SourcePruningEnumerationSharedPreparedRecursive.continueWith
                                                    (SourcePruningEnumerationSharedPreparedRecursiveChildPolicy.resumeWithNarrow
                                                      (SourcePruningEnumerationSharedEagerChildren.eagerChild checkEmpty workFuel workFuel workFuel workFuel workFuel edgesOf)
                                                      (SourcePruningOuterNarrow.narrow holeKey fits admits) graph templates checkEmpty edgesOf stop order workFuel fuel)
                                                    graph templates stop order workFuel updated uv)
                                                  checkEmpty workFuel workFuel workFuel workFuel workFuel workFuel workFuel uv edgesOf reached after saved = executed at good ⊢
                                                obtain ⟨preparation, folded⟩ := executed
                                                dsimp only at good ⊢
                                                cases folded with
                                                | none => exact hook_stopped _ _ good.1
                                                | some folded => exact whole_finish uv folded (good.2 folded rfl)

theorem runEager_real_none_buckets_at_any_budget
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (checkEmpty : Bool) (edgesOf : Node → List Edge)
    (stop : Option (Metadata Typing → Nat → Bool)) (order : Metadata Typing → List Nat → Option Nat)
    (workFuel recursiveFuel : Nat) (metadata : Metadata Typing)
    (caller : Caller width) (queries : Queries) (before : Cached)
    (initial : NoneBucketsEmpty before.core) :
    Preserved (SourcePruningEnumerationSharedPreparedRecursiveChildPolicy.runEagerWithNarrow
      (SourcePruningOuterNarrow.narrow holeKey fits admits) graph templates checkEmpty edgesOf stop order
      workFuel recursiveFuel metadata caller queries before)
 := by
  unfold SourcePruningEnumerationSharedPreparedRecursiveChildPolicy.runEagerWithNarrow
    SourcePruningEnumerationSharedPreparedRecursiveChildPolicy.runWithNarrow
  exact resume_none holeKey fits admits graph templates checkEmpty edgesOf stop order workFuel recursiveFuel
    metadata caller queries before (SourcePruningEnumerationRestart.decision stop order metadata before) initial

end MicroCFTA.SourcePruningEnumerationSharedEagerNoneBuckets
