import MicroCFTA.SourcePruningEnumerationSharedChildVisitors
import MicroCFTA.SourcePruningEnumerationOwnInputShape
import MicroCFTA.MergedOrdinaryHeight

/-!
# Eager ordinary children on the checked shared path

Each actual ordinary child invokes its tuple continuation before the next edge.
The scan retains branch caches and threads complete native endpoints.
Ordinary height bounds direct child recursion. Actual prepared children take
only the decreasing branch when the selector retains native payload members.
Terminal and opaque inputs keep the existing shallow dispatch operation.
Canonical edge-map construction and whole source completion remain separate.
-/
namespace MicroCFTA.SourcePruningEnumerationSharedEagerChildren
open EnumerationState InternedConstructorTemplates
open SourcePruningEnumerationSharedSelectedContinuations
open SourcePruningEnumerationSharedSelectedContinuations.NativeContinuations (Result advance endpoint)
open SourcePruningEnumerationSharedChildVisitors (visitSelected shallowVisit)
open SourcePruningEnumerationSharedBranching (scan)
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
local notation "NativeState" => InternedConstructorTemplates.State Symbol Constraint
local notation "Staged" => List (Node × List Suspended × Option (EnumerateM Symbol Constraint Fragment))
universe u v
variable {width : Nat} {Output : Type u} {Reason : Type v}

/-- Select only ordinary nodes with no terminal suspended constraint. -/
def ordinaryNonterminal (scs : List Suspended) : Node → Bool
  | .node .. => !(scs.any (fun sc => EqualityTrie.isTerminal sc.trie))
  | _ => false

/-- Invoke each completed child's tuple continuation before the next ordinary edge. -/
def consumeSelected
    (done : Fragment → Caller width → Queries → Cached → Result Output Reason width)
    (caller : Caller width) (queries : Queries) (receipt : Receipt width) : Result Output Reason width :=
  match receipt with
  | .complete fragment reached saved after =>
      match done fragment reached saved after with
      | .complete processed outputs finalCaller finalQueries =>
          .complete (receipt :: processed) outputs finalCaller finalQueries
      | .stopped processed outputs current => .stopped (receipt :: processed) outputs current
  | other =>
      match advance other with
      | none => .stopped [] [] (.edge (some other) (endpoint other caller queries))
      | some (reached, saved) => .complete [other] [] reached saved

/-- An actual prepared child retains the projected guard, exact input list and strict rank. -/
theorem prepared_child_lt
    (heap : NativeState) (entry : Cache.Interned InternedBinderProtocol.NodeKey)
    (rows : List Edge) (depth : Nat) (free : List InternedBinderProtocol.Reference)
    (edge : Edge) (selected : edge ∈ rows) (scs : List Suspended) (before middle : Cached)
    (symbol : Symbol) (staged : Staged) (residual : Option Constraint)
    (actual : SourcePruningEnumerationCachedOwn.prepare heap scs edge before =
      some [((symbol, staged, residual), middle)])
    (child : Node) (bucket : List Suspended)
    (member : (child, bucket) ∈ staged.map (fun input => (input.1, input.2.1))) :
    ∃ tries, SourcePruningEnumerationConstraint.project edge.entry.key.constraint = some (tries, residual) ∧
      staged.map (fun input => (input.1, input.2.1)) =
        SourcePruningEnumerationEdgeInputs.children edge scs before.core.counter tries ∧
      MergedOrdinaryHeight.height child < MergedOrdinaryHeight.height (.node entry rows depth free) := by
  by_cases allowed : arityAllows edge.children.length scs = true
  · cases projected : SourcePruningEnumerationConstraint.project edge.entry.key.constraint with
    | none => simp [SourcePruningEnumerationCachedOwn.prepare, allowed, projected] at actual
    | some fields =>
        rcases fields with ⟨tries, savedResidual⟩
        have shape := SourcePruningEnumerationCachedOwn.prepare_inputs heap scs edge before middle
          tries savedResidual (symbol, staged, residual) projected actual
        simp only [Prod.mk.injEq] at shape
        obtain ⟨_symbolSame, stagedSame, residualSame⟩ := shape
        subst savedResidual
        have inputsSame : staged.map (fun input => (input.1, input.2.1)) =
            SourcePruningEnumerationEdgeInputs.children edge scs before.core.counter tries := by
          rw [stagedSame, List.map_map]
          exact List.map_id _
        refine ⟨tries, rfl, inputsSame, ?_⟩
        rw [inputsSame] at member
        obtain ⟨indexed, indexedMember, same⟩ := List.mem_map.mp member
        have childSame : indexed.1 = child := congrArg Prod.fst same
        have childMember : child ∈ edge.children := by
          rw [← childSame]
          exact List.fst_mem_of_mem_zipIdx indexedMember
        exact MergedOrdinaryHeight.child_lt entry rows depth free edge selected child childMember
  · simp [SourcePruningEnumerationCachedOwn.prepare, allowed] at actual

/-- Complete rows retain their entire receipt before the actual tuple continuation result. -/
theorem consume_complete
    (done : Fragment → Caller width → Queries → Cached → Result Output Reason width)
    (caller reached : Caller width) (queries saved : Queries) (after : Cached) (fragment : Fragment) :
    consumeSelected done caller queries (.complete fragment reached saved after) =
      match done fragment reached saved after with
      | .complete processed outputs finalCaller finalQueries =>
          .complete (.complete fragment reached saved after :: processed) outputs finalCaller finalQueries
      | .stopped processed outputs current =>
          .stopped (.complete fragment reached saved after :: processed) outputs current := rfl

/-- A normal rejected row retains its native endpoint without invoking the tuple continuation. -/
theorem consume_rejected
    (done : Fragment → Caller width → Queries → Cached → Result Output Reason width)
    (caller reached : Caller width) (queries saved : Queries) (after : Cached) :
    consumeSelected done caller queries (.rejected reached saved after) =
      .complete [.rejected reached saved after] [] reached saved := rfl

variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]

/-- Ordinary nonterminal dispatch has no native enabled-check rejection to bypass. -/
theorem ordinary_dispatch_checkEmpty
    (first second : Bool) (r n p h k : Nat) (scs : List Suspended)
    (entry : Cache.Interned InternedBinderProtocol.NodeKey) (rows : List Edge)
    (depth : Nat) (free : List InternedBinderProtocol.Reference)
    (caller : Caller width) (before : Cached) (queries : Queries)
    (nonterminal : scs.any (fun sc => EqualityTrie.isTerminal sc.trie) = false) :
    ChildDispatch.run first r n p h k scs (.node entry rows depth free) caller before queries =
      ChildDispatch.run second r n p h k scs (.node entry rows depth free) caller before queries := by
  have nonempty : (.node entry rows depth free : Node) ≠ .empty := by intro impossible; cases impossible
  have noHere : (scs.partition (fun sc => EqualityTrie.isTerminal sc.trie)).1 = [] := by
    simp only [List.partition_eq_filter_filter]
    exact List.filter_eq_nil_iff.mpr (fun sc member => List.any_eq_false.mp nonterminal sc member)
  cases partitioned : scs.partition (fun sc => EqualityTrie.isTerminal sc.trie) with
  | mk here descendants =>
      have hereSame : here = [] := by simpa only [partitioned] using noHere
      subst here
      simp only [ChildDispatch.run, ChildDispatch.observe, ite_eq_right nonempty, partitioned]

/-- Recurse eagerly on ordinary children and preserve the existing dispatch elsewhere. -/
noncomputable def eagerChild
    (checkEmpty : Bool) (r n p h k : Nat) (edgesOf : Node → List Edge)
    (scs : List Suspended) (incoming : Node) (caller : Caller width) (before : Cached) (queries : Queries)
    (done : Fragment → Caller width → Queries → Cached → Result Output Reason width)
    (stopped : Observation width → Option Cached → Result Output Reason width) : Result Output Reason width :=
  if ordinaryNonterminal scs incoming then
    scan (fun edge reached saved captured =>
      visitSelected
        (fun bucket child current cache memos yes no =>
          if _lower : MergedOrdinaryHeight.height child < MergedOrdinaryHeight.height incoming then
            eagerChild checkEmpty r n p h k edgesOf bucket child current cache memos yes no
          else shallowVisit checkEmpty r n p h k bucket child current cache memos yes no)
        (consumeSelected done reached saved) scs edge reached captured saved)
      before (edgesOf incoming) caller queries
  else shallowVisit checkEmpty r n p h k scs incoming caller before queries done stopped
termination_by MergedOrdinaryHeight.height incoming
decreasing_by exact _lower

/-- Every non-eager input executes the same empty, terminal, opaque or unsupported dispatch. -/
theorem eagerChild_fallback
    (checkEmpty : Bool) (r n p h k : Nat) (edgesOf : Node → List Edge)
    (scs : List Suspended) (incoming : Node) (caller : Caller width) (before : Cached) (queries : Queries)
    (done : Fragment → Caller width → Queries → Cached → Result Output Reason width)
    (stopped : Observation width → Option Cached → Result Output Reason width)
    (fallback : ordinaryNonterminal scs incoming = false) :
    eagerChild checkEmpty r n p h k edgesOf scs incoming caller before queries done stopped =
      shallowVisit checkEmpty r n p h k scs incoming caller before queries done stopped := by
  rw [eagerChild, fallback]
  exact ite_eq_right (by decide)

/-- The actual ordinary route uses the checked selected-edge path and immediate child tails. -/
theorem eagerChild_ordinary
    (checkEmpty : Bool) (r n p h k : Nat) (edgesOf : Node → List Edge)
    (scs : List Suspended) (incoming : Node) (caller : Caller width) (before : Cached) (queries : Queries)
    (done : Fragment → Caller width → Queries → Cached → Result Output Reason width)
    (stopped : Observation width → Option Cached → Result Output Reason width)
    (ordinary : ordinaryNonterminal scs incoming = true) :
    eagerChild checkEmpty r n p h k edgesOf scs incoming caller before queries done stopped =
      scan (fun edge reached saved captured =>
        visitSelected
          (fun bucket child current cache memos yes no =>
            if _lower : MergedOrdinaryHeight.height child < MergedOrdinaryHeight.height incoming then
              eagerChild checkEmpty r n p h k edgesOf bucket child current cache memos yes no
            else shallowVisit checkEmpty r n p h k bucket child current cache memos yes no)
          (consumeSelected done reached saved) scs edge reached captured saved)
        before (edgesOf incoming) caller queries := by
  rw [eagerChild, ordinary]
  exact ite_eq_left rfl

/-- Actual prepared payload children never take the shallow guard fallback. -/
theorem prepared_child_eager
    (checkEmpty : Bool) (r n p h k : Nat) (edgesOf : Node → List Edge)
    (heap : NativeState) (entry : Cache.Interned InternedBinderProtocol.NodeKey)
    (rows : List Edge) (depth : Nat) (free : List InternedBinderProtocol.Reference)
    (selects : ∀ edge ∈ edgesOf (.node entry rows depth free), edge ∈ rows)
    (edge : Edge) (selected : edge ∈ edgesOf (.node entry rows depth free))
    (scs : List Suspended) (before middle : Cached) (symbol : Symbol) (staged : Staged)
    (residual : Option Constraint)
    (actual : SourcePruningEnumerationCachedOwn.prepare heap scs edge before =
      some [((symbol, staged, residual), middle)])
    (child : Node) (bucket : List Suspended)
    (member : (child, bucket) ∈ staged.map (fun input => (input.1, input.2.1)))
    (caller : Caller width) (cache : Cached) (queries : Queries)
    (done : Fragment → Caller width → Queries → Cached → Result Output Reason width)
    (stopped : Observation width → Option Cached → Result Output Reason width) :
    (if _lower : MergedOrdinaryHeight.height child < MergedOrdinaryHeight.height (.node entry rows depth free) then
      eagerChild checkEmpty r n p h k edgesOf bucket child caller cache queries done stopped
    else shallowVisit checkEmpty r n p h k bucket child caller cache queries done stopped) =
      eagerChild checkEmpty r n p h k edgesOf bucket child caller cache queries done stopped := by
  obtain ⟨_tries, _projected, _inputsSame, lower⟩ := prepared_child_lt heap entry rows depth free
    edge (selects edge selected) scs before middle symbol staged residual actual child bucket member
  exact dite_eq_left lower

end MicroCFTA.SourcePruningEnumerationSharedEagerChildren
