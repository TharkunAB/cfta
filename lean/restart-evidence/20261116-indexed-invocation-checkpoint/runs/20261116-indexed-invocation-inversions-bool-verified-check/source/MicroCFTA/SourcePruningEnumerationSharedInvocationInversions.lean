import MicroCFTA.SourcePruningEnumerationSharedInvocationTrace

namespace MicroCFTA.SourcePruningEnumerationSharedInvocationTrace
open EnumerationState InternedConstructorTemplates
open SourcePruningEnumerationSharedSelectedContinuations
open SourcePruningEnumerationSharedSelectedContinuations.NativeContinuations (Result)
open SourcePruningEnumerationSharedChildVisitors (visitChildren visitSelected shallowVisit)
open SourcePruningEnumerationSharedEagerChildren (eagerChild consumeSelected ordinaryNonterminal)
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
set_option autoImplicit false

private theorem terminal_not_ordinary (scs : List Suspended) (incoming : Node)
    (terminal : scs.any (fun sc => EqualityTrie.isTerminal sc.trie) = true) :
    ordinaryNonterminal scs incoming = false := by
  cases incoming with
  | empty => rfl
  | reference name => rfl
  | mu entry body depth ordinary => rfl
  | union entry members depth free => rfl
  | node entry rows depth free =>
      change Bool.not (scs.any (fun sc => EqualityTrie.isTerminal sc.trie)) = false
      rw [terminal]
      rfl

variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]

theorem selected_complete_invocation
    (checkEmpty : Bool) (r n p h k : Nat) (edgesOf : Node → List Edge) (policy : Policy)
    (consume : Receipt width → Result Output Reason width) (scs : List Suspended) (edge : Edge)
    (caller : Caller width) (before : Cached) (queries : Queries)
    (index : Nat) (output : Output) (fragment : Fragment) (reached : Caller width)
    (saved : Queries) (beforeFinalize : Cached) (consumerIndex : Nat)
    (trace : SelectedInvocationAt checkEmpty r n p h k edgesOf policy
      consume scs edge caller before queries index output
      (.complete fragment reached saved beforeFinalize) consumerIndex) :
    ∃ (symbol : Symbol) (staged : List Input) (residual : Option Constraint)
        (middle : Cached) (fragments : List Fragment) (afterChildren : Cached),
      SourcePruningEnumerationCachedOwn.prepare caller.checked.native.machine.heap scs edge before =
        some [((symbol, staged, residual), middle)] ∧
      ChildrenInvocationAt checkEmpty r n p h k edgesOf policy
        (fun produced current capturedQueries captured => consume (.complete (.node symbol produced)
          current capturedQueries (SelectedEdge.finish residual (.node symbol produced) captured)))
        (fun completed observation candidate => consume (.stopped completed observation candidate))
        (staged.map (fun input => (input.1, input.2.1))) caller middle queries index output
        (.done fragments reached saved afterChildren) consumerIndex ∧
      fragment = .node symbol fragments ∧
      beforeFinalize = SelectedEdge.finish residual fragment afterChildren := by
  cases trace with
  | singleton_done actual children =>
      exact ⟨_, _, _, _, _, _, actual, children, rfl, rfl⟩

private theorem terminal_done_dispatch_shallow
    (checkEmpty : Bool) (r n p h k : Nat) (edgesOf : Node → List Edge)
    (scs : List Suspended) (incoming : Node) (caller : Caller width) (before : Cached) (queries : Queries)
    (done : Done) (stopped : Stopped) (index : Nat) (output : Output)
    (fragment : Fragment) (reached : Caller width) (saved : Queries) (after : Cached) (localIndex : Nat)
    (trace : ChildInvocationAt checkEmpty r n p h k edgesOf .shallow
      scs incoming caller before queries done stopped index output
      (.done fragment reached saved after) localIndex) :
    ∃ (returned read : Core) (waiting : EnumerationWaitingIndex.Waiting),
      ChildDispatch.run checkEmpty r n p h k scs incoming caller before queries =
        ((.ok (some [.ok (fragment, returned)]), reached, saved, read, waiting), some after) ∧
      index = localIndex := by
  cases trace with
  | shallow_done actual _observed =>
      exact ⟨_, _, _, actual, rfl⟩

private theorem terminal_done_dispatch_eager
    (checkEmpty : Bool) (r n p h k : Nat) (edgesOf : Node → List Edge)
    (scs : List Suspended) (incoming : Node) (caller : Caller width) (before : Cached) (queries : Queries)
    (done : Done) (stopped : Stopped) (index : Nat) (output : Output)
    (fragment : Fragment) (reached : Caller width) (saved : Queries) (after : Cached) (localIndex : Nat)
    (terminal : scs.any (fun sc => EqualityTrie.isTerminal sc.trie) = true)
    (trace : ChildInvocationAt checkEmpty r n p h k edgesOf .eager
      scs incoming caller before queries done stopped index output
      (.done fragment reached saved after) localIndex) :
    ∃ (returned read : Core) (waiting : EnumerationWaitingIndex.Waiting),
      ChildDispatch.run checkEmpty r n p h k scs incoming caller before queries =
        ((.ok (some [.ok (fragment, returned)]), reached, saved, read, waiting), some after) ∧
      index = localIndex := by
  cases trace with
  | eager_fallback _fallback child =>
      exact terminal_done_dispatch_shallow checkEmpty r n p h k edgesOf
        scs incoming caller before queries done stopped index output
        fragment reached saved after localIndex child
  | eager_ordinary ordinary _order _past _rowRun _row _offset _observed =>
      have falseRoute := terminal_not_ordinary scs incoming terminal
      have impossible : (false : Bool) = true := falseRoute.symm.trans ordinary
      cases impossible

theorem terminal_done_dispatch
    (checkEmpty : Bool) (r n p h k : Nat) (edgesOf : Node → List Edge) (policy : Policy)
    (scs : List Suspended) (incoming : Node) (caller : Caller width) (before : Cached) (queries : Queries)
    (done : Done) (stopped : Stopped) (index : Nat) (output : Output)
    (fragment : Fragment) (reached : Caller width) (saved : Queries) (after : Cached) (localIndex : Nat)
    (terminal : scs.any (fun sc => EqualityTrie.isTerminal sc.trie) = true)
    (trace : ChildInvocationAt checkEmpty r n p h k edgesOf policy
      scs incoming caller before queries done stopped index output
      (.done fragment reached saved after) localIndex) :
    ∃ (returned read : Core) (waiting : EnumerationWaitingIndex.Waiting),
      ChildDispatch.run checkEmpty r n p h k scs incoming caller before queries =
        ((.ok (some [.ok (fragment, returned)]), reached, saved, read, waiting), some after) ∧
      index = localIndex := by
  cases policy with
  | shallow =>
      exact terminal_done_dispatch_shallow checkEmpty r n p h k edgesOf
        scs incoming caller before queries done stopped index output
        fragment reached saved after localIndex trace
  | eager =>
      exact terminal_done_dispatch_eager checkEmpty r n p h k edgesOf
        scs incoming caller before queries done stopped index output
        fragment reached saved after localIndex terminal trace
  | guarded parent =>
      cases trace with
      | guarded_lower _lower child =>
          exact terminal_done_dispatch_eager checkEmpty r n p h k edgesOf
            scs incoming caller before queries done stopped index output
            fragment reached saved after localIndex terminal child
      | guarded_else _lower child =>
          exact terminal_done_dispatch_shallow checkEmpty r n p h k edgesOf
            scs incoming caller before queries done stopped index output
            fragment reached saved after localIndex child

end MicroCFTA.SourcePruningEnumerationSharedInvocationTrace

#check @MicroCFTA.SourcePruningEnumerationSharedInvocationTrace.selected_complete_invocation
#print axioms MicroCFTA.SourcePruningEnumerationSharedInvocationTrace.selected_complete_invocation
#check @MicroCFTA.SourcePruningEnumerationSharedInvocationTrace.terminal_done_dispatch
#print axioms MicroCFTA.SourcePruningEnumerationSharedInvocationTrace.terminal_done_dispatch
