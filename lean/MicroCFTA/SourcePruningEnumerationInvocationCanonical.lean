import MicroCFTA.SourcePruningEnumerationSharedInvocationTrace
import MicroCFTA.SourcePruningEnumerationSharedChildCanonical
import MicroCFTA.SourcePruningEnumerationOwnFinalizeCanonical
import MicroCFTA.SourcePruningEnumerationOwnInputShape
import MicroCFTA.SourcePruningEnumerationSelectedEdgeProper
import MicroCFTA.EnumerationValidity

namespace MicroCFTA.SourcePruningEnumerationInvocationCanonical
open EnumerationState EnumerationSemantics EnumerationValidity InternedConstructorTemplates
open SourcePruningEnumerationSharedSelectedContinuations
open SourcePruningEnumerationSharedSelectedContinuations.NativeContinuations (Result)
open SourcePruningEnumerationSharedChildVisitors (visitChildren visitSelected)
open SourcePruningEnumerationSharedEagerChildren (consumeSelected ordinaryNonterminal)
open SourcePruningEnumerationSharedBranching (scan)
open SourcePruningEnumerationSharedScanOutputOrigins (outputs)
open SourcePruningEnumerationSharedInvocationTrace
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Edge" => EdgeValue Symbol Constraint
local notation "Fragment" => Fragments.Fragment Symbol
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Queries" => SourceEndpointMemo.Memos
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Core" => EnumerationState.State Symbol Constraint
local notation "Receipt" => SelectedEdge.Result
local notation "Observation" => ChildDispatch.Observation
local notation "Input" => Node × List Suspended × Option (EnumerateM Symbol Constraint Fragment)
local notation "Row" => (Symbol × List Input × Option Constraint) × Cached
universe u v
variable {width : Nat} {Output : Type u} {Reason : Type v}
local notation "Done" => Fragment → Caller width → Queries → Cached → Result Output Reason width
local notation "Stopped" => Observation width → Option Cached → Result Output Reason width
local notation "TupleDone" => List Fragment → Caller width → Queries → Cached → Result Output Reason width
local notation "TupleStopped" => List Fragment → Observation width → Option Cached → Result Output Reason width
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]
set_option autoImplicit false

/- Note [Canonical tries through indexed invocations]
The three motives follow the actual mutual invocation relations.
The entry cache and actual input buckets supply the initial invariant.
The shallow leaf follows the literal shared dispatch.
Own preparation constructs valid tries or the empty default.
The tuple induction passes each actual completed child cache to its tail.
The ordinary case uses the same selected row and captured cache.
Residual finish changes no stored trie.
The handler signatures and recursor applications reuse the checked
InvocationRawAliasGrowth proof structure, with every handler passed by @.
No callback invariant, future cache, resource contract or model is supplied.
-/

omit [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node] in
private theorem classTrie_valid (paths : List EqualityTrie.Path) :
    EqualityTrie.Valid (EnumerationEquality.classTrie paths) := by
  cases built : EqualityTrie.toPathTrie paths.eraseDups with
  | none =>
      simp only [EnumerationEquality.classTrie, built, Option.getD_none, EqualityTrie.Valid]
  | some trie =>
      have supported := (EqualityTrie.toPathTrie_succeeds_iff paths.eraseDups).mp ⟨trie, built⟩
      obtain ⟨actual, found, valid, _⟩ := EqualityTrie.toPathTrie_correct paths.eraseDups supported
      have same : actual = trie := Option.some.inj (found.symm.trans built)
      have trieValid : EqualityTrie.Valid trie := by
        rw [← same]
        exact valid
      simpa only [EnumerationEquality.classTrie, built, Option.getD_some] using trieValid

omit [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node] in
private theorem projected_tries_valid
    (constraint : Constraint) (tries : List EqualityTrie.Trie) (residual : Option Constraint)
    (projected : SourcePruningEnumerationConstraint.project constraint = some (tries, residual)) :
    ∀ trie ∈ tries, EqualityTrie.Valid trie := by
  unfold SourcePruningEnumerationConstraint.project at projected
  cases source : SourceCompactGuards.sourceEqualities constraint with
  | none => rw [source] at projected; cases projected
  | some classes =>
      rw [source] at projected
      have same := Option.some.inj projected
      have triesSame : EnumerationEquality.readClasses classes = tries := congrArg Prod.fst same
      rw [← triesSame]
      intro trie member
      obtain ⟨paths, _present, rfl⟩ := List.mem_map.mp member
      exact classTrie_valid paths

omit [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node] in
private theorem own_preparation_canonical
    (heap : InternedConstructorTemplates.State Symbol Constraint)
    (scs : List Suspended) (edge : Edge) (before middle : Cached)
    (symbol : Symbol) (staged : List Input) (residual : Option Constraint)
    (canonical : Canonical before.core) (valid : ValidSuspended scs)
    (actual : SourcePruningEnumerationCachedOwn.prepare heap scs edge before =
      some [((symbol, staged, residual), middle)]) :
    Canonical middle.core ∧
      ∀ input ∈ staged.map (fun input => (input.1, input.2.1)), ValidSuspended input.2 := by
  have original := actual
  unfold SourcePruningEnumerationCachedOwn.prepare at actual
  split at actual
  next allowed =>
    generalize projected : SourcePruningEnumerationConstraint.project edge.entry.key.constraint = plan at actual
    cases plan with
    | none => cases actual
    | some plan =>
        rcases plan with ⟨tries, kept⟩
        dsimp only at actual
        generalize suspended : SourcePruningEnumerationCachedOwn.suspendMany heap tries before = result at actual
        cases result with
        | none => cases actual
        | some result =>
            rcases result with ⟨own, after⟩
            have rowSame := (List.cons.inj (Option.some.inj actual)).1
            have cacheSame : after = middle := congrArg (fun row : Row => row.2) rowSame
            have afterCanonical := SourcePruningEnumerationCachedOwn.suspendMany_canonical
              heap tries before after own canonical suspended
            have fields := SourcePruningEnumerationCachedOwn.prepare_inputs heap scs edge before middle
              tries kept (symbol, staged, residual) projected original
            have stagedSame := congrArg (fun row : Symbol × List Input × Option Constraint => row.2.1) fields
            dsimp only at stagedSame
            have inputsSame : staged.map (fun input => (input.1, input.2.1)) =
                SourcePruningEnumerationEdgeInputs.children edge scs before.core.counter tries := by
              rw [stagedSame]
              simp only [List.map_map]
              exact List.map_id _
            constructor
            · rw [← cacheSame]
              exact afterCanonical
            · rw [inputsSame]
              intro input member
              have proper := SourcePruningEnumerationSelectedEdge.children_proper_inputs
                edge scs before.core.counter tries valid
                (projected_tries_valid edge.entry.key.constraint tries kept projected)
                input.1 input.2 member
              exact fun sc listed => (proper sc listed).1
  next rejected => cases actual

private def ChildCanonical (before : Cached) (scs : List Suspended) (exit : ChildExit width) : Prop :=
  Canonical before.core → ValidSuspended scs →
    match exit with
    | .done _ _ _ after => Canonical after.core
    | .stopped _ _ => True

private def TupleCanonical (before : Cached) (inputs : List (Node × List Suspended))
    (exit : TupleExit width) : Prop :=
  Canonical before.core → (∀ input ∈ inputs, ValidSuspended input.2) →
    match exit with
    | .done _ _ _ after => Canonical after.core
    | .stopped _ _ _ => True

private def SelectedCanonical (before : Cached) (scs : List Suspended) (receipt : Receipt width) : Prop :=
  Canonical before.core → ValidSuspended scs →
    match receipt with
    | .complete _ _ _ after => Canonical after.core
    | _ => True

private theorem invocation_canonical
    (checkEmpty : Bool) (r n p h k : Nat) (edgesOf : Node → List Edge) :
    (∀ (policy : Policy) (scs : List Suspended) (incoming : Node) (caller : Caller width)
      (before : Cached) (queries : Queries) (done : Done) (stopped : Stopped)
      (index : Nat) (output : Output) (exit : ChildExit width) (localIndex : Nat),
      ChildInvocationAt checkEmpty r n p h k edgesOf policy
        scs incoming caller before queries done stopped index output exit localIndex → ChildCanonical before scs exit) ∧
    (∀ (policy : Policy) (done : TupleDone) (stopped : TupleStopped) (inputs : List (Node × List Suspended))
      (caller : Caller width) (before : Cached) (queries : Queries)
      (index : Nat) (output : Output) (exit : TupleExit width) (localIndex : Nat),
      ChildrenInvocationAt checkEmpty r n p h k edgesOf policy
        done stopped inputs caller before queries index output exit localIndex → TupleCanonical before inputs exit) ∧
    (∀ (policy : Policy) (consume : Receipt width → Result Output Reason width)
      (scs : List Suspended) (edge : Edge) (caller : Caller width) (before : Cached) (queries : Queries)
      (index : Nat) (output : Output) (receipt : Receipt width) (consumerIndex : Nat),
      SelectedInvocationAt checkEmpty r n p h k edgesOf policy
        consume scs edge caller before queries index output receipt consumerIndex → SelectedCanonical before scs receipt) := by
  have shallowDoneCase
      {scs : List Suspended} {incoming : Node} {caller reached : Caller width}
      {before after : Cached} {queries saved : Queries} {done : Done} {stopped : Stopped}
      {index : Nat} {output : Output} {fragment : Fragment} {returned read : Core}
      {waiting : EnumerationWaitingIndex.Waiting}
      (actual : ChildDispatch.run checkEmpty r n p h k scs incoming caller before queries =
        ((.ok (some [.ok (fragment, returned)]), reached, saved, read, waiting), some after))
      (_observed : (outputs (done fragment reached saved after))[index]? = some output) :
      ChildCanonical before scs (.done fragment reached saved after) := by
    intro canonical valid
    exact SourcePruningEnumerationSharedChildCanonical.successful_canonical
      checkEmpty r n p h k scs incoming caller reached before after queries saved
      fragment returned read waiting canonical valid actual

  have shallowStoppedCase
      {scs : List Suspended} {incoming : Node} {caller : Caller width} {before : Cached}
      {queries : Queries} {done : Done} {stopped : Stopped} {index : Nat} {output : Output}
      {observation : Observation width} {candidate : Option Cached}
      (_actual : ChildDispatch.run checkEmpty r n p h k scs incoming caller before queries =
        (observation, candidate))
      (_shape : ShallowStopped observation candidate)
      (_observed : (outputs (stopped observation candidate))[index]? = some output) :
      ChildCanonical before scs (.stopped observation candidate) := by
    intro _canonical _valid
    exact True.intro

  have guardedLowerCase
      {parent incoming : Node} {scs : List Suspended} {caller : Caller width} {before : Cached}
      {queries : Queries} {done : Done} {stopped : Stopped}
      {index localIndex : Nat} {output : Output} {exit : ChildExit width}
      (_lower : MergedOrdinaryHeight.height incoming < MergedOrdinaryHeight.height parent)
      (_child : ChildInvocationAt checkEmpty r n p h k edgesOf .eager scs incoming caller before queries
        done stopped index output exit localIndex)
      (childIH : ChildCanonical before scs exit) :
      ChildCanonical before scs exit := by
    exact childIH

  have guardedElseCase
      {parent incoming : Node} {scs : List Suspended} {caller : Caller width} {before : Cached}
      {queries : Queries} {done : Done} {stopped : Stopped}
      {index localIndex : Nat} {output : Output} {exit : ChildExit width}
      (_lower : ¬MergedOrdinaryHeight.height incoming < MergedOrdinaryHeight.height parent)
      (_child : ChildInvocationAt checkEmpty r n p h k edgesOf .shallow scs incoming caller before queries
        done stopped index output exit localIndex)
      (childIH : ChildCanonical before scs exit) :
      ChildCanonical before scs exit := by
    exact childIH

  have eagerFallbackCase
      {incoming : Node} {scs : List Suspended} {caller : Caller width} {before : Cached}
      {queries : Queries} {done : Done} {stopped : Stopped}
      {index localIndex : Nat} {output : Output} {exit : ChildExit width}
      (_fallback : ordinaryNonterminal scs incoming = false)
      (_child : ChildInvocationAt checkEmpty r n p h k edgesOf .shallow scs incoming caller before queries
        done stopped index output exit localIndex)
      (childIH : ChildCanonical before scs exit) :
      ChildCanonical before scs exit := by
    exact childIH

  have eagerOrdinaryCase
      {incoming : Node} {scs : List Suspended} {caller : Caller width} {before : Cached}
      {queries : Queries} {done : Done} {stopped : Stopped}
      {index rowIndex localIndex : Nat} {output : Output}
      {attempted remaining : List Edge} {edge : Edge} {rowCaller : Caller width} {rowQueries : Queries}
      {processed : List (Receipt width)} {earlier : List Output} {rowResult : Result Output Reason width}
      {fragment : Fragment} {reached : Caller width} {saved : Queries} {after : Cached}
      (_ordinary : ordinaryNonterminal scs incoming = true)
      (_order : edgesOf incoming = attempted ++ edge :: remaining)
      (_past : scan (fun selected current capturedQueries captured =>
        visitSelected (runPolicy checkEmpty r n p h k edgesOf (.guarded incoming))
          (consumeSelected done current capturedQueries) scs selected current captured capturedQueries)
        before attempted caller queries = .complete processed earlier rowCaller rowQueries)
      (_rowRun : visitSelected (runPolicy checkEmpty r n p h k edgesOf (.guarded incoming))
        (consumeSelected done rowCaller rowQueries) scs edge rowCaller before rowQueries = rowResult)
      (_row : SelectedInvocationAt checkEmpty r n p h k edgesOf (.guarded incoming)
        (consumeSelected done rowCaller rowQueries) scs edge rowCaller before rowQueries
        rowIndex output (.complete fragment reached saved after) localIndex)
      (_offset : index = earlier.length + rowIndex)
      (_observed : (outputs (done fragment reached saved after))[localIndex]? = some output)
      (rowIH : SelectedCanonical before scs (.complete fragment reached saved after)) :
      ChildCanonical before scs (.done fragment reached saved after) := by
    exact rowIH

  have nilCase
      {policy : Policy} {done : TupleDone} {stopped : TupleStopped}
      {caller : Caller width} {before : Cached} {queries : Queries} {index : Nat} {output : Output}
      (_observed : (outputs (done [] caller queries before))[index]? = some output) :
      TupleCanonical before [] (.done [] caller queries before) := by
    intro canonical _valid
    exact canonical

  have consDoneCase
      {policy : Policy} {done : TupleDone} {stopped : TupleStopped}
      {incoming : Node} {bucket : List Suspended} {rest : List (Node × List Suspended)}
      {caller reached : Caller width} {before after : Cached} {queries saved : Queries}
      {fragment : Fragment} {index childIndex localIndex : Nat} {output : Output} {exit : TupleExit width}
      (_child : ChildInvocationAt checkEmpty r n p h k edgesOf policy bucket incoming caller before queries
        (fun produced current capturedQueries captured =>
          visitChildren (runPolicy checkEmpty r n p h k edgesOf policy)
            (fun fragments => done (produced :: fragments))
            (fun completed => stopped (produced :: completed)) rest current captured capturedQueries)
        (fun observation candidate => stopped [] observation candidate)
        index output (.done fragment reached saved after) childIndex)
      (_tail : ChildrenInvocationAt checkEmpty r n p h k edgesOf policy
        (fun fragments => done (fragment :: fragments))
        (fun completed => stopped (fragment :: completed)) rest reached after saved
        childIndex output exit localIndex)
      (childIH : ChildCanonical before bucket (.done fragment reached saved after))
      (tailIH : TupleCanonical after rest exit) :
      TupleCanonical before ((incoming, bucket) :: rest) (TupleExit.prepend fragment exit) := by
    intro canonical valid
    have atChild := childIH canonical (valid _ List.mem_cons_self)
    have tailValid : ∀ input ∈ rest, ValidSuspended input.2 := by
      intro input member
      exact valid input (List.mem_cons_of_mem _ member)
    cases exit with
    | done _fragments _reached _saved _after => exact tailIH atChild tailValid
    | stopped _completed _observation _candidate => exact True.intro

  have consStoppedCase
      {policy : Policy} {done : TupleDone} {stopped : TupleStopped}
      {incoming : Node} {bucket : List Suspended} {rest : List (Node × List Suspended)}
      {caller : Caller width} {before : Cached} {queries : Queries}
      {observation : Observation width} {candidate : Option Cached}
      {index localIndex : Nat} {output : Output}
      (_child : ChildInvocationAt checkEmpty r n p h k edgesOf policy bucket incoming caller before queries
        (fun produced current capturedQueries captured =>
          visitChildren (runPolicy checkEmpty r n p h k edgesOf policy)
            (fun fragments => done (produced :: fragments))
            (fun completed => stopped (produced :: completed)) rest current captured capturedQueries)
        (fun current captured => stopped [] current captured)
        index output (.stopped observation candidate) localIndex)
      (_childIH : ChildCanonical before bucket (.stopped observation candidate)) :
      TupleCanonical before ((incoming, bucket) :: rest) (.stopped [] observation candidate) := by
    intro _canonical _valid
    exact True.intro

  have unhandledNoneCase
      {policy : Policy} {consume : Receipt width → Result Output Reason width}
      {scs : List Suspended} {edge : Edge} {caller : Caller width} {before : Cached} {queries : Queries}
      {index : Nat} {output : Output}
      (_actual : SourcePruningEnumerationCachedOwn.prepare caller.checked.native.machine.heap scs edge before = none)
      (_observed : (outputs (consume .unhandled))[index]? = some output) :
      SelectedCanonical (width := width) before scs .unhandled := by
    intro _canonical _valid
    exact True.intro

  have unhandledManyCase
      {policy : Policy} {consume : Receipt width → Result Output Reason width}
      {scs : List Suspended} {edge : Edge} {caller : Caller width} {before : Cached} {queries : Queries}
      {first second : Row} {rest : List Row} {index : Nat} {output : Output}
      (_actual : SourcePruningEnumerationCachedOwn.prepare caller.checked.native.machine.heap scs edge before =
        some (first :: second :: rest))
      (_observed : (outputs (consume .unhandled))[index]? = some output) :
      SelectedCanonical (width := width) before scs .unhandled := by
    intro _canonical _valid
    exact True.intro

  have rejectedCase
      {policy : Policy} {consume : Receipt width → Result Output Reason width}
      {scs : List Suspended} {edge : Edge} {caller : Caller width} {before : Cached} {queries : Queries}
      {index : Nat} {output : Output}
      (_actual : SourcePruningEnumerationCachedOwn.prepare caller.checked.native.machine.heap scs edge before = some [])
      (_observed : (outputs (consume (.rejected caller queries before)))[index]? = some output) :
      SelectedCanonical before scs (.rejected caller queries before) := by
    intro _canonical _valid
    exact True.intro

  have singletonDoneCase
      {policy : Policy} {consume : Receipt width → Result Output Reason width}
      {scs : List Suspended} {edge : Edge} {caller reached : Caller width}
      {before middle after : Cached} {queries saved : Queries}
      {symbol : Symbol} {staged : List Input} {residual : Option Constraint} {fragments : List Fragment}
      {index localIndex : Nat} {output : Output}
      (actual : SourcePruningEnumerationCachedOwn.prepare caller.checked.native.machine.heap scs edge before =
        some [((symbol, staged, residual), middle)])
      (_children : ChildrenInvocationAt checkEmpty r n p h k edgesOf policy
        (fun produced current capturedQueries captured => consume (.complete (.node symbol produced)
          current capturedQueries (SelectedEdge.finish residual (.node symbol produced) captured)))
        (fun completed observation candidate => consume (.stopped completed observation candidate))
        (staged.map (fun input => (input.1, input.2.1))) caller middle queries
        index output (.done fragments reached saved after) localIndex)
      (childrenIH : TupleCanonical middle (staged.map (fun input => (input.1, input.2.1))) (.done fragments reached saved after)) :
      SelectedCanonical before scs (.complete (.node symbol fragments) reached saved
        (SelectedEdge.finish residual (.node symbol fragments) after)) := by
    intro canonical valid
    obtain ⟨middleCanonical, stagedValid⟩ := own_preparation_canonical
      caller.checked.native.machine.heap scs edge before middle symbol staged residual canonical valid actual
    exact childrenIH middleCanonical stagedValid

  have singletonStoppedCase
      {policy : Policy} {consume : Receipt width → Result Output Reason width}
      {scs : List Suspended} {edge : Edge} {caller : Caller width}
      {before middle : Cached} {queries : Queries} {symbol : Symbol}
      {staged : List Input} {residual : Option Constraint} {completed : List Fragment}
      {observation : Observation width} {candidate : Option Cached}
      {index localIndex : Nat} {output : Output}
      (_actual : SourcePruningEnumerationCachedOwn.prepare caller.checked.native.machine.heap scs edge before =
        some [((symbol, staged, residual), middle)])
      (_children : ChildrenInvocationAt checkEmpty r n p h k edgesOf policy
        (fun produced current capturedQueries captured => consume (.complete (.node symbol produced)
          current capturedQueries (SelectedEdge.finish residual (.node symbol produced) captured)))
        (fun finished current captured => consume (.stopped finished current captured))
        (staged.map (fun input => (input.1, input.2.1))) caller middle queries
        index output (.stopped completed observation candidate) localIndex)
      (_childrenIH : TupleCanonical middle (staged.map (fun input => (input.1, input.2.1))) (.stopped completed observation candidate)) :
      SelectedCanonical before scs (.stopped completed observation candidate) := by
    intro _canonical _valid
    exact True.intro

  constructor
  · intro policy scs incoming caller before queries done stopped index output exit localIndex trace
    exact ChildInvocationAt.rec
        (motive_1 := fun _ scs _ _ before _ _ _ _ _ exit _ _ => ChildCanonical before scs exit)
        (motive_2 := fun _ _ _ inputs _ before _ _ _ exit _ _ => TupleCanonical before inputs exit)
        (motive_3 := fun _ _ scs _ _ before _ _ _ receipt _ _ => SelectedCanonical before scs receipt)
        @shallowDoneCase @shallowStoppedCase @guardedLowerCase @guardedElseCase @eagerFallbackCase @eagerOrdinaryCase
        @nilCase @consDoneCase @consStoppedCase
        @unhandledNoneCase @unhandledManyCase @rejectedCase @singletonDoneCase @singletonStoppedCase trace
  · constructor
    · intro policy done stopped inputs caller before queries index output exit localIndex trace
      exact ChildrenInvocationAt.rec
          (motive_1 := fun _ scs _ _ before _ _ _ _ _ exit _ _ => ChildCanonical before scs exit)
          (motive_2 := fun _ _ _ inputs _ before _ _ _ exit _ _ => TupleCanonical before inputs exit)
          (motive_3 := fun _ _ scs _ _ before _ _ _ receipt _ _ => SelectedCanonical before scs receipt)
          @shallowDoneCase @shallowStoppedCase @guardedLowerCase @guardedElseCase @eagerFallbackCase @eagerOrdinaryCase
          @nilCase @consDoneCase @consStoppedCase
          @unhandledNoneCase @unhandledManyCase @rejectedCase @singletonDoneCase @singletonStoppedCase trace
    · intro policy consume scs edge caller before queries index output receipt consumerIndex trace
      exact SelectedInvocationAt.rec
          (motive_1 := fun _ scs _ _ before _ _ _ _ _ exit _ _ => ChildCanonical before scs exit)
          (motive_2 := fun _ _ _ inputs _ before _ _ _ exit _ _ => TupleCanonical before inputs exit)
          (motive_3 := fun _ _ scs _ _ before _ _ _ receipt _ _ => SelectedCanonical before scs receipt)
          @shallowDoneCase @shallowStoppedCase @guardedLowerCase @guardedElseCase @eagerFallbackCase @eagerOrdinaryCase
          @nilCase @consDoneCase @consStoppedCase
          @unhandledNoneCase @unhandledManyCase @rejectedCase @singletonDoneCase @singletonStoppedCase trace

theorem child_done_canonical
    (checkEmpty : Bool) (r n p h k : Nat) (edgesOf : Node → List Edge) (policy : Policy)
    (scs : List Suspended) (incoming : Node) (caller reached : Caller width)
    (before after : Cached) (queries saved : Queries) (done : Done) (stopped : Stopped)
    (index : Nat) (output : Output) (fragment : Fragment) (localIndex : Nat)
    (canonical : Canonical before.core)
    (valid : ValidSuspended scs)
    (trace : ChildInvocationAt checkEmpty r n p h k edgesOf policy
      scs incoming caller before queries done stopped index output
        (.done fragment reached saved after) localIndex) :
    Canonical after.core
 := by
  exact (invocation_canonical checkEmpty r n p h k edgesOf).1
    policy scs incoming caller before queries done stopped index output
      (.done fragment reached saved after) localIndex trace canonical valid

theorem children_done_canonical
    (checkEmpty : Bool) (r n p h k : Nat) (edgesOf : Node → List Edge) (policy : Policy)
    (done : TupleDone) (stopped : TupleStopped) (inputs : List (Node × List Suspended))
    (caller reached : Caller width) (before after : Cached) (queries saved : Queries)
    (index : Nat) (output : Output) (fragments : List Fragment) (localIndex : Nat)
    (canonical : Canonical before.core)
    (valid : ∀ input ∈ inputs, ValidSuspended input.2)
    (trace : ChildrenInvocationAt checkEmpty r n p h k edgesOf policy
      done stopped inputs caller before queries index output
        (.done fragments reached saved after) localIndex) :
    Canonical after.core
 := by
  exact (invocation_canonical checkEmpty r n p h k edgesOf).2.1
    policy done stopped inputs caller before queries index output
      (.done fragments reached saved after) localIndex trace canonical valid

theorem selected_complete_canonical
    (checkEmpty : Bool) (r n p h k : Nat) (edgesOf : Node → List Edge) (policy : Policy)
    (consume : Receipt width → Result Output Reason width)
    (scs : List Suspended) (edge : Edge) (caller reached : Caller width)
    (before after : Cached) (queries saved : Queries) (index : Nat) (output : Output)
    (fragment : Fragment) (consumerIndex : Nat)
    (canonical : Canonical before.core)
    (valid : ValidSuspended scs)
    (trace : SelectedInvocationAt checkEmpty r n p h k edgesOf policy
      consume scs edge caller before queries index output
        (.complete fragment reached saved after) consumerIndex) :
    Canonical after.core
 := by
  exact (invocation_canonical checkEmpty r n p h k edgesOf).2.2
    policy consume scs edge caller before queries index output
      (.complete fragment reached saved after) consumerIndex trace canonical valid

end MicroCFTA.SourcePruningEnumerationInvocationCanonical
