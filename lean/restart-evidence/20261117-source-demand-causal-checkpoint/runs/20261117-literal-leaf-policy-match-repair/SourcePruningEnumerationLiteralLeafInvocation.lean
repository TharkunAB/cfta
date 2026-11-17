import MicroCFTA.SourcePruningEnumerationSelectedStagedChildInvocation

namespace MicroCFTA.SourcePruningEnumerationLiteralLeafInvocation
open EnumerationState InternedConstructorTemplates
open SourcePruningEnumerationSharedInvocationTrace
open SourcePruningEnumerationSharedSelectedContinuations
open SourcePruningEnumerationSharedSelectedContinuations.NativeContinuations (Result)
open SourcePruningEnumerationSharedEagerChildren (ordinaryNonterminal)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Edge" => EdgeValue Symbol Constraint
local notation "Fragment" => Fragments.Fragment Symbol
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Queries" => SourceEndpointMemo.Memos
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Receipt" => SelectedEdge.Result
local notation "Input" => Node × List Suspended × Option (EnumerateM Symbol Constraint Fragment)
local notation "Row" => (Symbol × List Input × Option Constraint) × Cached
universe u v
variable {width : Nat} {Output : Type u} {Reason : Type v}
set_option autoImplicit false

/- Note [Literal leaves at actual staged child calls]
The selected trace fixes the actual own preparation and tuple return.
A selected row without children returns its literal symbol.
The eager child law uses the actual singleton row selector and control.
A guarded child uses that law only on its actual lower-height branch.
The staged-child law derives the child trace from the same parent trace.
It preserves the parent output occurrence and all supplied primitive fuels.
The arrow marker can use this law as a leaf. It is not a Type argument.
Source proofs must still establish the marker bucket and selector facts.
-/

private theorem prepared_leaf_staged
    (heap : InternedConstructorTemplates.State Symbol Constraint) (bucket : List Suspended)
    (edge : Edge) (before middle : Cached) (symbol : Symbol) (staged : List Input)
    (residual : Option Constraint) (leaf : edge.children = [])
    (actual : SourcePruningEnumerationCachedOwn.prepare heap bucket edge before =
      some [((symbol, staged, residual), middle)]) :
    symbol = edge.entry.key.symbol ∧ staged = [] := by
  unfold SourcePruningEnumerationCachedOwn.prepare at actual
  split at actual
  next allowed =>
    generalize projected : SourcePruningEnumerationConstraint.project edge.entry.key.constraint = plan at actual
    cases plan with
    | none => cases actual
    | some plan =>
        rcases plan with ⟨tries, kept⟩
        dsimp only at actual
        generalize allocated : SourcePruningEnumerationCachedOwn.suspendMany heap tries before = allocation at actual
        cases allocation with
        | none => cases actual
        | some allocation =>
            rcases allocation with ⟨own, ownAfter⟩
            have rowSame := (List.cons.inj (Option.some.inj actual)).1
            have symbolSame := congrArg (fun row : Row => row.1.1) rowSame
            have stagedSame := congrArg (fun row : Row => row.1.2.1) rowSame
            exact ⟨symbolSame.symm, by
              simpa only [leaf, List.zipIdx_nil, List.map_nil] using stagedSame.symm⟩
  next rejected => cases actual

variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]

theorem selected_nullary_fragment
    (checkEmpty : Bool) (r n p h k : Nat) (edgesOf : Node → List Edge) (policy : Policy)
    (consume : Receipt width → Result Output Reason width)
    (bucket : List Suspended) (edge : Edge) (caller reached : Caller width)
    (before finished : Cached) (queries saved : Queries) (index : Nat) (output : Output)
    (fragment : Fragment) (consumerIndex : Nat) (leaf : edge.children = [])
    (trace : SelectedInvocationAt checkEmpty r n p h k edgesOf policy consume bucket edge caller before queries
      index output (.complete fragment reached saved finished) consumerIndex) :
    fragment = .node edge.entry.key.symbol [] := by
  obtain ⟨symbol, staged, residual, middle, fragments, afterChildren,
      prepared, children, assembled, _finishedEq⟩ :=
    selected_complete_invocation checkEmpty r n p h k edgesOf policy consume bucket edge caller before queries
      index output fragment reached saved finished consumerIndex trace
  obtain ⟨symbolSame, stagedEmpty⟩ := prepared_leaf_staged caller.checked.native.machine.heap
    bucket edge before middle symbol staged residual leaf prepared
  subst staged
  have fragmentsEmpty : fragments = [] := by
    cases children
    rfl
  simpa only [fragmentsEmpty, symbolSame] using assembled

private theorem eager_nullary_fragment
    (checkEmpty : Bool) (r n p h k : Nat) (edgesOf : Node → List Edge)
    (entry : Cache.Interned InternedBinderProtocol.NodeKey) (row : Edge)
    (depth : Nat) (free : List InternedBinderProtocol.Reference) (bucket : List Suspended)
    (caller reached : Caller width) (before finished : Cached) (queries saved : Queries)
    (done : Fragment → Caller width → Queries → Cached → Result Output Reason width)
    (stopped : ChildDispatch.Observation width → Option Cached → Result Output Reason width)
    (index consumerIndex : Nat) (output : Output) (fragment : Fragment)
    (nonterminal : bucket.any (fun sc => EqualityTrie.isTerminal sc.trie) = false)
    (selector : edgesOf (.node entry [row] depth free) = [row])
    (leaf : row.children = [])
    (trace : ChildInvocationAt checkEmpty r n p h k edgesOf .eager bucket
      (.node entry [row] depth free) caller before queries done stopped index output
      (.done fragment reached saved finished) consumerIndex) :
    fragment = .node row.entry.key.symbol [] := by
  cases trace with
  | eager_fallback fallback _child =>
      have positive : ordinaryNonterminal bucket (.node entry [row] depth free) = true := by
        simp only [ordinaryNonterminal, nonterminal, Bool.not_false]
      rw [positive] at fallback
      cases fallback
  | eager_ordinary _ordinary rowOrder _past _rowRun rowTrace _offset _observed =>
      have onlyRow : ∀ candidate ∈ edgesOf (.node entry [row] depth free), candidate = row := by
        intro candidate member
        rw [selector] at member
        exact List.mem_singleton.mp member
      have selectedSame := onlyRow _ (by
        rw [rowOrder]
        exact List.mem_append_right _ List.mem_cons_self)
      have shape := selected_nullary_fragment (trace := rowTrace)
        (leaf := by simpa only [selectedSame] using leaf)
      simpa only [selectedSame] using shape

theorem child_nullary_fragment
    (checkEmpty : Bool) (r n p h k : Nat) (edgesOf : Node → List Edge) (policy : Policy)
    (entry : Cache.Interned InternedBinderProtocol.NodeKey) (row : Edge)
    (depth : Nat) (free : List InternedBinderProtocol.Reference) (bucket : List Suspended)
    (caller reached : Caller width) (before finished : Cached) (queries saved : Queries)
    (done : Fragment → Caller width → Queries → Cached → Result Output Reason width)
    (stopped : ChildDispatch.Observation width → Option Cached → Result Output Reason width)
    (index consumerIndex : Nat) (output : Output) (fragment : Fragment)
    (nonterminal : bucket.any (fun sc => EqualityTrie.isTerminal sc.trie) = false)
    (selector : edgesOf (.node entry [row] depth free) = [row])
    (leaf : row.children = [])
    (control : match policy with
      | .eager => True
      | .guarded parent => MergedOrdinaryHeight.height (.node entry [row] depth free) < MergedOrdinaryHeight.height parent
      | .shallow => False)
    (trace : ChildInvocationAt checkEmpty r n p h k edgesOf policy bucket
      (.node entry [row] depth free) caller before queries done stopped index output
      (.done fragment reached saved finished) consumerIndex) :
    fragment = .node row.entry.key.symbol [] := by
  cases policy with
  | eager =>
      exact eager_nullary_fragment checkEmpty r n p h k edgesOf entry row depth free bucket
        caller reached before finished queries saved done stopped index consumerIndex output fragment
        nonterminal selector leaf trace
  | shallow => exact False.elim control
  | guarded parent =>
      cases trace with
      | guarded_lower _lower child =>
          exact eager_nullary_fragment checkEmpty r n p h k edgesOf entry row depth free bucket
            caller reached before finished queries saved done stopped index consumerIndex output fragment
            nonterminal selector leaf child
      | guarded_else contrary _child => exact False.elim (contrary control)

theorem selected_first_nullary_child_fragment
    (checkEmpty : Bool) (r n p h k : Nat) (edgesOf : Node → List Edge) (policy : Policy)
    (consume : Receipt width → Result Output Reason width)
    (scs : List Suspended) (edge : Edge) (caller reached : Caller width)
    (before finished : Cached) (queries saved : Queries) (index : Nat) (output : Output)
    (fragment : Fragment) (consumerIndex : Nat)
    (symbol : Symbol) (staged : List Input) (residual : Option Constraint) (middle : Cached)
    (prepared : SourcePruningEnumerationCachedOwn.prepare caller.checked.native.machine.heap scs edge before =
      some [((symbol, staged, residual), middle)])
    (entry : Cache.Interned InternedBinderProtocol.NodeKey) (row : Edge)
    (depth : Nat) (free : List InternedBinderProtocol.Reference) (bucket : List Suspended)
    (action : Option (EnumerateM Symbol Constraint Fragment))
    (first : staged[0]? = some (.node entry [row] depth free, bucket, action))
    (nonterminal : bucket.any (fun sc => EqualityTrie.isTerminal sc.trie) = false)
    (selector : edgesOf (.node entry [row] depth free) = [row]) (leaf : row.children = [])
    (control : match policy with
      | .eager => True
      | .guarded parent => MergedOrdinaryHeight.height (.node entry [row] depth free) < MergedOrdinaryHeight.height parent
      | .shallow => False)
    (trace : SelectedInvocationAt checkEmpty r n p h k edgesOf policy consume scs edge caller before queries
      index output (.complete fragment reached saved finished) consumerIndex) :
    ∃ remaining : List Fragment,
      fragment = .node symbol (.node row.entry.key.symbol [] :: remaining) := by
  obtain ⟨priorStaged, laterStaged, priorFragments, childCaller, childBefore, childQueries,
      childRootIndex, childFragment, childReached, childSaved, childAfter, childCallbackIndex,
      remaining, afterChildren, _stagedSame, _priorStagedLength, priorLength, shape,
      _finishedSame, child, _tail⟩ :=
    selected_staged_child_invocation checkEmpty r n p h k edgesOf policy consume scs edge
      caller before queries index output fragment reached saved finished consumerIndex
      symbol staged residual middle prepared 0 (.node entry [row] depth free) bucket action first trace
  have literal := child_nullary_fragment (trace := child) (nonterminal := nonterminal)
    (selector := selector) (leaf := leaf) (control := by cases policy <;> exact control)
  have priorEmpty : priorFragments = [] := List.length_eq_zero.mp priorLength
  refine ⟨remaining, ?_⟩
  simpa only [priorEmpty, List.nil_append, literal] using shape

end MicroCFTA.SourcePruningEnumerationLiteralLeafInvocation
