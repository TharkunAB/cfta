import MicroCFTA.SourcePruningEnumerationSharedEagerChildren
import MicroCFTA.SourcePruningEnumerationSharedScanOutputOrigins

namespace MicroCFTA.SourcePruningEnumerationSharedCallbackOutputBlocks
open EnumerationState InternedConstructorTemplates
open SourcePruningEnumerationSharedSelectedContinuations
open SourcePruningEnumerationSharedSelectedContinuations.NativeContinuations (Result)
open SourcePruningEnumerationSharedChildVisitors (visitChildren visitSelected shallowVisit)
open SourcePruningEnumerationSharedEagerChildren (consumeSelected)
open SourcePruningEnumerationSharedScanOutputOrigins (outputs)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Edge" => EdgeValue Symbol Constraint
local notation "Fragment" => Fragments.Fragment Symbol
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Queries" => SourceEndpointMemo.Memos
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Receipt" => SelectedEdge.Result
local notation "Observation" => ChildDispatch.Observation
universe u v
variable {width : Nat} {Output : Type u} {Reason : Type v}
local notation "Visitor" => List Suspended → Node → Caller width → Cached → Queries →
  (Fragment → Caller width → Queries → Cached → Result Output Reason width) →
  (Observation width → Option Cached → Result Output Reason width) → Result Output Reason width
set_option autoImplicit false

/-- A callback contributes its whole output block at the original indexed occurrence. -/
def OutputBlock (whole block : List Output) (index : Nat) (output : Output) : Prop :=
  ∃ (earlier later : List Output) (localIndex : Nat),
    whole = earlier ++ block ++ later ∧ block[localIndex]? = some output ∧
      index = earlier.length + localIndex

/-- A fixed child visitor emits only whole blocks from its actual continuations. -/
def CallbackBlocksAt (visit : Visitor) (incoming : Node) : Prop :=
  ∀ (scs : List Suspended) (caller : Caller width) (before : Cached) (queries : Queries)
      (done : Fragment → Caller width → Queries → Cached → Result Output Reason width)
      (stopped : Observation width → Option Cached → Result Output Reason width)
      (index : Nat) (output : Output),
    (outputs (visit scs incoming caller before queries done stopped))[index]? = some output →
    (∃ (fragment : Fragment) (reached : Caller width) (saved : Queries) (after : Cached),
      OutputBlock (outputs (visit scs incoming caller before queries done stopped))
        (outputs (done fragment reached saved after)) index output) ∨
    (∃ (observation : Observation width) (candidate : Option Cached),
      OutputBlock (outputs (visit scs incoming caller before queries done stopped))
        (outputs (stopped observation candidate)) index output)

theorem OutputBlock.refl (whole : List Output) (index : Nat) (output : Output)
    (observed : whole[index]? = some output) : OutputBlock whole whole index output := by
  exact ⟨[], [], index, by simp, observed, by simp⟩

theorem OutputBlock.wrap
    (whole middle block earlier later : List Output) (index localIndex : Nat) (output : Output)
    (decomposition : whole = earlier ++ middle ++ later)
    (offset : index = earlier.length + localIndex)
    (inner : OutputBlock middle block localIndex output) : OutputBlock whole block index output := by
  obtain ⟨prefix, suffix, selected, middleSame, found, innerOffset⟩ := inner
  refine ⟨earlier ++ prefix, suffix ++ later, selected, ?_, found, ?_⟩
  · rw [decomposition, middleSame]
    simp only [List.append_assoc]
  · simp only [List.length_append]
    omega

theorem visit_children_output_block_origin
    (visit : Visitor) (blocks : ∀ incoming, CallbackBlocksAt visit incoming)
    (done : List Fragment → Caller width → Queries → Cached → Result Output Reason width)
    (stopped : List Fragment → Observation width → Option Cached → Result Output Reason width)
    (inputs : List (Node × List Suspended)) (caller : Caller width) (before : Cached) (queries : Queries)
    (index : Nat) (output : Output)
    (observed : (outputs (visitChildren visit done stopped inputs caller before queries))[index]? = some output) :
    (∃ (fragments : List Fragment) (reached : Caller width) (saved : Queries) (after : Cached),
      OutputBlock (outputs (visitChildren visit done stopped inputs caller before queries))
        (outputs (done fragments reached saved after)) index output) ∨
    (∃ (completed : List Fragment) (observation : Observation width) (candidate : Option Cached),
      OutputBlock (outputs (visitChildren visit done stopped inputs caller before queries))
        (outputs (stopped completed observation candidate)) index output) := by
  induction inputs generalizing caller before queries done stopped index with
  | nil =>
      exact Or.inl ⟨[], caller, queries, before, OutputBlock.refl _ index output observed⟩
  | cons input rest ih =>
      rcases input with ⟨incoming, bucket⟩
      let yes := fun fragment reached saved after =>
        visitChildren visit (fun fragments => done (fragment :: fragments))
          (fun completed => stopped (fragment :: completed)) rest reached after saved
      let no := fun observation candidate => stopped [] observation candidate
      have selected := blocks incoming bucket caller before queries yes no index output
        (by simpa only [visitChildren, yes, no] using observed)
      rcases selected with accepted | rejected
      · obtain ⟨fragment, reached, saved, after, earlier, later, localIndex,
          decomposition, found, offset⟩ := accepted
        change (outputs (visitChildren visit (fun fragments => done (fragment :: fragments))
          (fun completed => stopped (fragment :: completed)) rest reached after saved))[localIndex]? =
            some output at found
        have inherited := ih
          (done := fun fragments => done (fragment :: fragments))
          (stopped := fun completed => stopped (fragment :: completed))
          (caller := reached) (before := after) (queries := saved) (index := localIndex) found
        rcases inherited with completed | interrupted
        · obtain ⟨fragments, finalCaller, finalQueries, finalCache, block⟩ := completed
          exact Or.inl ⟨fragment :: fragments, finalCaller, finalQueries, finalCache,
            OutputBlock.wrap _ _ _ earlier later index localIndex output decomposition offset block⟩
        · obtain ⟨fragments, observation, candidate, block⟩ := interrupted
          exact Or.inr ⟨fragment :: fragments, observation, candidate,
            OutputBlock.wrap _ _ _ earlier later index localIndex output decomposition offset block⟩
      · obtain ⟨observation, candidate, block⟩ := rejected
        exact Or.inr ⟨[], observation, candidate, block⟩

theorem visit_selected_output_block_origin
    (visit : Visitor) (blocks : ∀ incoming, CallbackBlocksAt visit incoming)
    (consume : Receipt width → Result Output Reason width)
    (scs : List Suspended) (edge : Edge) (caller : Caller width) (before : Cached) (queries : Queries)
    (index : Nat) (output : Output)
    (observed : (outputs (visitSelected visit consume scs edge caller before queries))[index]? = some output) :
    ∃ receipt, OutputBlock (outputs (visitSelected visit consume scs edge caller before queries))
      (outputs (consume receipt)) index output := by
  cases prepared : SourcePruningEnumerationCachedOwn.prepare
      caller.checked.native.machine.heap scs edge before with
  | none =>
      simp only [visitSelected, prepared] at observed ⊢
      exact ⟨.unhandled, OutputBlock.refl _ index output observed⟩
  | some rows =>
      cases rows with
      | nil =>
          simp only [visitSelected, prepared] at observed ⊢
          exact ⟨.rejected caller queries before, OutputBlock.refl _ index output observed⟩
      | cons row rest =>
          cases rest with
          | cons second tail =>
              simp only [visitSelected, prepared] at observed ⊢
              exact ⟨.unhandled, OutputBlock.refl _ index output observed⟩
          | nil =>
              rcases row with ⟨⟨symbol, staged, residual⟩, middle⟩
              simp only [visitSelected, prepared] at observed ⊢
              have selected := visit_children_output_block_origin visit blocks
                (fun fragments reached saved after => consume (.complete (.node symbol fragments)
                  reached saved (SelectedEdge.finish residual (.node symbol fragments) after)))
                (fun completed observation candidate => consume (.stopped completed observation candidate))
                (staged.map (fun input => (input.1, input.2.1))) caller middle queries index output observed
              rcases selected with completed | interrupted
              · obtain ⟨fragments, reached, saved, after, block⟩ := completed
                exact ⟨.complete (.node symbol fragments) reached saved
                  (SelectedEdge.finish residual (.node symbol fragments) after), block⟩
              · obtain ⟨fragments, observation, candidate, block⟩ := interrupted
                exact ⟨.stopped fragments observation candidate, block⟩

theorem consume_selected_output_block_origin
    (done : Fragment → Caller width → Queries → Cached → Result Output Reason width)
    (caller : Caller width) (queries : Queries) (receipt : Receipt width)
    (index : Nat) (output : Output)
    (observed : (outputs (consumeSelected done caller queries receipt))[index]? = some output) :
    ∃ (fragment : Fragment) (reached : Caller width) (saved : Queries) (after : Cached),
      receipt = .complete fragment reached saved after ∧
      OutputBlock (outputs (consumeSelected done caller queries receipt))
        (outputs (done fragment reached saved after)) index output := by
  cases receipt with
  | complete fragment reached saved after =>
      have same : outputs (consumeSelected done caller queries (.complete fragment reached saved after)) =
          outputs (done fragment reached saved after) := by
        cases done fragment reached saved after <;> rfl
      rw [same] at observed
      refine ⟨fragment, reached, saved, after, rfl, ?_⟩
      rw [same]
      exact OutputBlock.refl _ index output observed
  | unhandled =>
      simp only [consumeSelected, NativeContinuations.advance, outputs, List.getElem?_nil] at observed
  | rejected reached saved after =>
      simp only [consumeSelected, NativeContinuations.advance, outputs, List.getElem?_nil] at observed
  | finalizeStopped fragment reached saved after =>
      simp only [consumeSelected, NativeContinuations.advance, outputs, List.getElem?_nil] at observed
  | stopped fragments observation candidate =>
      cases advanced : NativeContinuations.advance
          (SelectedEdge.Result.stopped fragments observation candidate) <;>
        simp only [consumeSelected, advanced, outputs, List.getElem?_nil] at observed

theorem shallow_visit_callback_blocks
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]
    (checkEmpty : Bool) (r n p h k : Nat) (incoming : Node) :
    CallbackBlocksAt (width := width) (Output := Output) (Reason := Reason) (shallowVisit checkEmpty r n p h k) incoming := by
  intro scs caller before queries done stopped index output observed
  cases actual : ChildDispatch.run checkEmpty r n p h k scs incoming caller before queries with
  | mk observation candidate =>
      rcases observation with ⟨raw, reached, saved, outer, waiting⟩
      cases raw with
      | error fault =>
          simp only [shallowVisit, actual] at observed ⊢
          exact Or.inr ⟨_, _, OutputBlock.refl _ index output observed⟩
      | ok possible =>
          cases possible with
          | none =>
              simp only [shallowVisit, actual] at observed ⊢
              exact Or.inr ⟨_, _, OutputBlock.refl _ index output observed⟩
          | some results =>
              cases results with
              | nil =>
                  simp only [shallowVisit, actual] at observed ⊢
                  exact Or.inr ⟨_, _, OutputBlock.refl _ index output observed⟩
              | cons first rest =>
                  cases first with
                  | error fault =>
                      simp only [shallowVisit, actual] at observed ⊢
                      exact Or.inr ⟨_, _, OutputBlock.refl _ index output observed⟩
                  | ok payload =>
                      rcases payload with ⟨fragment, returned⟩
                      cases rest with
                      | cons second tail =>
                          simp only [shallowVisit, actual] at observed ⊢
                          exact Or.inr ⟨_, _, OutputBlock.refl _ index output observed⟩
                      | nil =>
                          cases candidate with
                          | none =>
                              simp only [shallowVisit, actual] at observed ⊢
                              exact Or.inr ⟨_, _, OutputBlock.refl _ index output observed⟩
                          | some after =>
                              simp only [shallowVisit, actual] at observed ⊢
                              exact Or.inl ⟨fragment, reached, saved, after,
                                OutputBlock.refl _ index output observed⟩

end MicroCFTA.SourcePruningEnumerationSharedCallbackOutputBlocks

#check @MicroCFTA.SourcePruningEnumerationSharedCallbackOutputBlocks.OutputBlock.refl
#print axioms MicroCFTA.SourcePruningEnumerationSharedCallbackOutputBlocks.OutputBlock.refl
#check @MicroCFTA.SourcePruningEnumerationSharedCallbackOutputBlocks.OutputBlock.wrap
#print axioms MicroCFTA.SourcePruningEnumerationSharedCallbackOutputBlocks.OutputBlock.wrap
#check @MicroCFTA.SourcePruningEnumerationSharedCallbackOutputBlocks.visit_children_output_block_origin
#print axioms MicroCFTA.SourcePruningEnumerationSharedCallbackOutputBlocks.visit_children_output_block_origin
#check @MicroCFTA.SourcePruningEnumerationSharedCallbackOutputBlocks.visit_selected_output_block_origin
#print axioms MicroCFTA.SourcePruningEnumerationSharedCallbackOutputBlocks.visit_selected_output_block_origin
#check @MicroCFTA.SourcePruningEnumerationSharedCallbackOutputBlocks.consume_selected_output_block_origin
#print axioms MicroCFTA.SourcePruningEnumerationSharedCallbackOutputBlocks.consume_selected_output_block_origin
#check @MicroCFTA.SourcePruningEnumerationSharedCallbackOutputBlocks.shallow_visit_callback_blocks
#print axioms MicroCFTA.SourcePruningEnumerationSharedCallbackOutputBlocks.shallow_visit_callback_blocks
