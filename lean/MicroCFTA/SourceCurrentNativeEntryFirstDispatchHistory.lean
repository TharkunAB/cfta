import MicroCFTA.SourceCurrentOwnFirstChildDispatchHistory
import MicroCFTA.SourcePruningEnumerationNativeOrdinaryContinuations
import MicroCFTA.SourcePruningEnumerationCapturedEdge
import MicroCFTA.SourcePruningEnumerationChildTraversal
import MicroCFTA.SourcePruningEnumerationEntry
import MicroCFTA.MergedOrdinaryHeight

/-! Original entry admissions connect the native continuation to its actual first child call. -/
set_option autoImplicit false
namespace MicroCFTA.SourceCurrentNativeEntryFirstDispatchHistory
open EnumerationState EnumerationSchedule EnumerationCorrectness EnumerationCompressionFrame
open InternedConstructorTemplates SourcePruningEnumerationNodes SourcePruningEnumerationObservation
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Fragment" => Fragments.Fragment Symbol
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Queries" => SourceEndpointMemo.Memos
local notation "Input" => Node × List Suspended × Option (EnumerateM Symbol Constraint Fragment)
variable {width : Nat} {Output Reason : Type}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]

private def HeadHistory (checkEmpty : Bool) (r n p h k : Nat) (history : List RecursionKey)
    (staged : List Input) (caller : Caller width) (middle : Cached) (queries : Queries) : Prop :=
  match staged with
  | [] => True
  | input :: _ =>
      match input.2.1.partition (fun (sc : Suspended) => EqualityTrie.isTerminal sc.trie) with
      | ([], _) =>
          ∃ (fragment : Fragment) (reached : Caller width) (saved : Queries) (after : Cached)
            (outer : EnumerationState.State Symbol Constraint) (waiting : EnumerationWaitingIndex.Waiting),
            SourcePruningEnumerationChildDispatch.run checkEmpty r n p h k input.2.1 input.1 caller middle queries =
              ((.ok (some [.ok (fragment, after.core)]), reached, saved, outer, waiting), some after) ∧
            fragment = .hole middle.core.counter ∧ reached = caller ∧ saved = queries ∧
            after.core.expansionAncestry = history ∧
            after.core.recursionAncestry middle.core.counter =
              (history ++ middle.core.recursionAncestry middle.core.counter).eraseDups ∧
            ∀ key ∈ history, key ∈ after.core.recursionAncestry middle.core.counter
      | _ => True

private def OwnHistory (checkEmpty : Bool) (r n p h k : Nat) (history : List RecursionKey)
    (scs : List Suspended) (edge : EdgeValue Symbol Constraint)
    (caller : Caller width) (before : Cached) (queries : Queries)
    (fragment : Fragment) (reached : Caller width) (saved : Queries) (selectedAfter : Cached) : Prop :=
  ∃ (symbol : Symbol) (staged : List Input) (residual : Option Constraint) (middle : Cached)
      (fragments : List Fragment) (childAfter : Cached),
    SourcePruningEnumerationCachedOwn.prepare caller.checked.native.machine.heap scs edge before =
      some [((symbol, staged, residual), middle)] ∧
    SourcePruningEnumerationChildTraversal.run checkEmpty r n p h k
      (staged.map (fun input => (input.1, input.2.1))) caller middle queries =
        .complete fragments reached saved childAfter ∧
    fragment = .node symbol fragments ∧
    selectedAfter = SourcePruningEnumerationSelectedEdge.finish residual fragment childAfter ∧
    HeadHistory checkEmpty r n p h k history staged caller middle queries

private theorem selected_complete
    (checkEmpty : Bool) (r n p h k : Nat) (scs : List Suspended) (edge : EdgeValue Symbol Constraint)
    (caller : Caller width) (before : Cached) (queries : Queries)
    (fragment : Fragment) (reached : Caller width) (saved : Queries) (selectedAfter : Cached)
    (completed : SourcePruningEnumerationSelectedEdge.run checkEmpty r n p h k scs edge caller before queries =
      .complete fragment reached saved selectedAfter) :
    OwnHistory checkEmpty r n p h k before.core.expansionAncestry scs edge caller before queries
      fragment reached saved selectedAfter := by
  cases own : SourcePruningEnumerationCachedOwn.prepare caller.checked.native.machine.heap scs edge before with
  | none => simp [SourcePruningEnumerationSelectedEdge.run, own] at completed
  | some rows =>
      cases rows with
      | nil => simp [SourcePruningEnumerationSelectedEdge.run, own] at completed
      | cons row rest =>
          cases rest with
          | cons next tail => simp [SourcePruningEnumerationSelectedEdge.run, own] at completed
          | nil =>
              rcases row with ⟨⟨symbol, staged, residual⟩, middle⟩
              cases children : SourcePruningEnumerationChildTraversal.run checkEmpty r n p h k
                  (staged.map (fun input => (input.1, input.2.1))) caller middle queries with
              | stopped fragments observation candidate =>
                  simp [SourcePruningEnumerationSelectedEdge.run, own, children] at completed
              | complete fragments afterCaller afterQueries childAfter =>
                  have resultEq : SourcePruningEnumerationSelectedEdge.Result.complete
                      (.node symbol fragments) afterCaller afterQueries
                      (SourcePruningEnumerationSelectedEdge.finish residual (.node symbol fragments) childAfter) =
                      .complete fragment reached saved selectedAfter := by
                    simpa only [SourcePruningEnumerationSelectedEdge.run, own, children] using completed
                  cases resultEq
                  refine ⟨symbol, staged, residual, middle, fragments, childAfter, own, children, rfl, rfl, ?_⟩
                  have trace := SourcePruningEnumerationChildTraversal.complete_trace checkEmpty r n p h k
                    (staged.map (fun input => (input.1, input.2.1))) caller reached middle childAfter
                    queries saved fragments children
                  cases staged with
                  | nil => trivial
                  | cons input inputs =>
                      dsimp only [HeadHistory]
                      cases partitioned : input.2.1.partition (fun (sc : Suspended) => EqualityTrie.isTerminal sc.trie) with
                      | mk terminals descendants =>
                          cases terminals with
                          | cons first rest => trivial
                          | nil =>
                              cases trace with
                              | cons head tail =>
                                  have law := SourceCurrentOwnFirstChildDispatchHistory.own_first_dispatch_history
                                    checkEmpty r n p h k scs edge caller before queries
                                    ((symbol, input :: inputs, residual), middle) (by simp [own])
                                  dsimp only at law
                                  rw [partitioned] at law
                                  dsimp only at law
                                  rw [head] at law
                                  dsimp only at law
                                  exact ⟨_, _, _, _, _, _, head, law.1, law.2.2.1, law.2.2.2.1,
                                    law.2.2.2.2.1, law.2.2.2.2.2.1, law.2.2.2.2.2.2⟩

/-- This predicate records the actual first child of a completed captured edge. -/
def EdgeHistory (checkEmpty : Bool) (r n p h k target : Nat) (history : List RecursionKey)
    (scs : List Suspended) (edge : EdgeValue Symbol Constraint)
    (caller : Caller width) (before : Cached) (queries : Queries) : Prop :=
  match SourcePruningEnumerationCapturedEdge.run checkEmpty r n p h k target scs edge caller before queries with
  | some (.complete fragment reached saved after) =>
      ∃ selectedAfter,
        SourcePruningEnumerationSelectedEdge.run checkEmpty r n p h k scs edge caller before queries =
          .complete fragment reached saved selectedAfter ∧
        SourcePruningEnumerationFinalize.run reached.checked.native.machine.heap k target fragment selectedAfter =
          some after ∧
        OwnHistory checkEmpty r n p h k history scs edge caller before queries fragment reached saved selectedAfter
  | _ => True

theorem captured_edge_first_dispatch_history (checkEmpty : Bool) (r n p h k target : Nat) (scs : List Suspended)
    (edge : EdgeValue Symbol Constraint) (caller : Caller width) (before : Cached) (queries : Queries) :
    EdgeHistory checkEmpty r n p h k target before.core.expansionAncestry scs edge caller before queries := by
  unfold EdgeHistory
  cases selected : SourcePruningEnumerationSelectedEdge.run checkEmpty r n p h k scs edge caller before queries with
  | unhandled => simp only [SourcePruningEnumerationCapturedEdge.run, selected]
  | rejected reached saved after => simp only [SourcePruningEnumerationCapturedEdge.run, selected]
  | stopped fragments observation candidate => simp only [SourcePruningEnumerationCapturedEdge.run, selected]
  | complete fragment reached saved selectedAfter =>
      cases finished : SourcePruningEnumerationFinalize.run reached.checked.native.machine.heap
          k target fragment selectedAfter with
      | none => simp only [SourcePruningEnumerationCapturedEdge.run, selected, finished, Option.map_none]
      | some after =>
          simp only [SourcePruningEnumerationCapturedEdge.run, selected, finished, Option.map_some]
          exact ⟨selectedAfter, rfl, finished,
            selected_complete checkEmpty r n p h k scs edge caller before queries fragment reached saved selectedAfter selected⟩

/-- Original entry admissions connect the real native wrapper and its first completed edge to its literal child call. -/
theorem native_entry_first_dispatch_history
    (hook : Fragment → Caller width → Queries → Cached →
      SourcePruningEnumerationNativeContinuations.HookResult Output Reason width)
    (caller : Caller width) (before : Cached) (queries : Queries) (checkEmpty : Bool) (uv : Nat)
    (edgesOf : Node → List (EdgeValue Symbol Constraint))
    (storage : StorageValid before.core) (inside : uv < before.core.counter)
    (realized : PendingRealized caller.checked.native.machine.heap before.core) :
    ∃ fuel, ∀ extra n p h k,
      let actual := SourcePruningEnumerationNativeOrdinaryContinuations.run hook checkEmpty
        (fuel + extra) n p h k uv edgesOf caller before queries
      match actual.1 with
      | [.ok ((target, _handle, scs, parent@(.node _ _ _ _)), entered)] =>
          if scs.any (fun sc => EqualityTrie.isTerminal sc.trie) then True
          else
            actual.2 = some (SourcePruningEnumerationNativeContinuations.run hook checkEmpty
              (fuel + extra) n p h k target scs (EnumerationExpandableIndex.frame entered before)
              (edgesOf parent) caller queries) ∧
            match edgesOf parent with
            | [] => True
            | edge :: _ =>
                EdgeHistory checkEmpty (fuel + extra) n p h k target (before.core.recursionAncestry target)
                  scs edge caller (EnumerationExpandableIndex.frame entered before) queries
      | _ => True := by
  obtain ⟨fuel, readValue, readAfter, _readRun, _readFrame, entryFacts⟩ :=
    SourcePruningEnumerationEntry.complete caller.checked.native.machine.heap before.core uv storage inside realized
  refine ⟨fuel, ?_⟩
  intro extra n p h k
  dsimp only
  unfold SourcePruningEnumerationNativeOrdinaryContinuations.run
  cases readValue with
  | eliminated => simp only [entryFacts extra]
  | enumerated fragment => simp only [entryFacts extra]
  | unenumerated node scs =>
      cases node with
      | none => simp only [entryFacts extra]
      | some handle =>
          obtain ⟨target, decoded, compressed, entered, frame, _rootRun, _stored, _lookup,
            _available, _closed, enteredEq, entryRun, _storage, _realized⟩ := entryFacts
          cases decoded with
          | empty => simp only [entryRun extra]
          | reference name => simp only [entryRun extra]
          | union entry children depth free => simp only [entryRun extra]
          | mu entry body depth free => simp only [entryRun extra]
          | node entry edges depth free =>
              simp only [entryRun extra]
              cases blocked : scs.any (fun sc => EqualityTrie.isTerminal sc.trie) with
              | true => trivial
              | false =>
                  simp only [Bool.false_eq_true, ite_false]
                  refine ⟨True.intro, ?_⟩
                  have active : (EnumerationExpandableIndex.frame entered before).core.expansionAncestry =
                      before.core.recursionAncestry target := by
                    change entered.expansionAncestry = before.core.recursionAncestry target
                    rw [enteredEq]
                    simp only [MergedOrdinaryHeight.recursiveBoundary, Bool.false_eq_true, ite_false,
                      frame.recursionAncestry]
                  cases selectedEdges : edgesOf (.node entry edges depth free) with
                  | nil => trivial
                  | cons edge rest =>
                      have law := captured_edge_first_dispatch_history checkEmpty (fuel + extra) n p h k target scs edge caller
                        (EnumerationExpandableIndex.frame entered before) queries
                      simpa only [active] using law

end MicroCFTA.SourceCurrentNativeEntryFirstDispatchHistory
