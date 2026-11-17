import MicroCFTA.SourceSynthesisCurrentUniverseUnfoldedRowPreparation
import MicroCFTA.SourcePruningEnumerationStagedChildInvocation
import MicroCFTA.SourcePruningEnumerationSharedChildFinalRawTargets

namespace MicroCFTA.SourceSynthesisCurrentUniverseArrowInvocationProvenance
open Cache Language Fragments EnumerationState EnumerationSchedule
open InternedConstructorTemplates InternedNestedFacts
open InternedBinderProtocol (NodeKey)
open SourceSynthesisTypeSyntax (Library Query)
open SourceSynthesisFirstOrderConstruction (Expression)
open SourceSynthesisUniverseCallerBoundary (ordinarySymbols)
open SourcePruningEnumerationSharedInvocationTrace
open SourcePruningEnumerationSharedSelectedContinuations
open SourcePruningEnumerationSharedSelectedContinuations.NativeContinuations (Result)
open SourcePruningEnumerationSharedChildVisitors (visitChildren)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Edge" => EdgeValue Symbol Constraint
local notation "Fragment" => Fragments.Fragment Symbol
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Queries" => SourceEndpointMemo.Memos
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Core" => EnumerationState.State Symbol Constraint
local notation "Input" => Node × List Suspended × Option (EnumerateM Symbol Constraint Fragment)
local notation "literal" => SourceSynthesisLabelProgramBuildRoles.literal
universe u v
variable {width : Nat} {Output : Type u} {Reason : Type v}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]
set_option autoImplicit false

/- Note [One original arrow invocation]
The current accepted source fixes the escaped catalog and stored full U.
One actual selected trace fixes its own preparation and ordered child trace.
The Top row keeps the same cache. Its staged inputs are the marker and U twice.
The first completed child and remaining tuple come from that same trace.
A terminal first child retains its actual raw winner and original target aliases.
These facts do not assert TypeIn, native acceptance or a satisfying assignment.
-/

theorem original_universe_arrow_selected_provenance
    (lib : Library) (query : Query) (signed : Int) (whole : Expression)
    (accepted : SourceSynthesisCurrentConstruction.firstOrderRaw lib query signed = .ok whole)
    (rootValue : Node) (sourceHeap : InternedConstructorTemplates.State Symbol Constraint)
    (built : InternedFreshOrdinaryConstruction.build (ordinarySymbols whole) [] empty =
      .done rootValue sourceHeap)
    (key : NodeKey) (entry : Interned NodeKey) (body depth ordinary : Node)
    (stored : sourceHeap.nodeRecords key = some (.mu entry body depth ordinary))
    (nativeBefore nativeAfter : InternedConstructorTemplates.State Symbol Constraint)
    (facts : Facts nativeBefore) (sourceGrowth : Grows sourceHeap nativeBefore)
    (unfoldFuel : Nat) (prepared : Node)
    (unfolded : SourcePruningEnumerationSelectedValue.run unfoldFuel
      (.mu entry body depth ordinary) nativeBefore = .done prepared nativeAfter)
    (row : Edge) (present : row ∈ InternedEdgeResidency.nodeEdges prepared)
    (arrowSymbol : row.entry.key.symbol = literal "->")
    (checkEmpty : Bool) (r n p h k : Nat) (edgesOf : Node → List Edge) (policy : Policy)
    (consume : SelectedEdge.Result width → Result Output Reason width)
    (scs : List Suspended) (caller reached : Caller width) (before beforeFinalize : Cached)
    (queries saved : Queries) (index : Nat) (output : Output)
    (fragment : Fragment) (consumerIndex : Nat)
    (total : UnionFind.Total before.core.representatives)
    (trace : SelectedInvocationAt checkEmpty r n p h k edgesOf policy consume scs row
      caller before queries index output (.complete fragment reached saved beforeFinalize) consumerIndex) :
    let fullUniverse : Node := .mu entry body depth ordinary
    ∃ (marker : Node) (markerEntry : Interned NodeKey) (markerRow : Edge)
      (staged : List Input) (fragments : List Fragment) (afterChildren : Cached),
      marker = .node markerEntry [markerRow] 0 [] ∧ markerRow.children = [] ∧
      markerRow.entry.key = ⟨literal "(->)", [], SourceSynthesisGeneralizeSyntax.top⟩ ∧
      row.children = [marker, fullUniverse, fullUniverse] ∧
      row.entry.key.constraint = SourceSynthesisGeneralizeSyntax.top ∧
      SourcePruningEnumerationCachedOwn.prepare caller.checked.native.machine.heap scs row before =
        some [((literal "->", staged, none), before)] ∧
      staged = [
        (marker, descendScs 0 scs, SourcePruningEnumerationShallowChild.prepareChild
          (EnumGuard := Constraint) (descendScs 0 scs) marker),
        (fullUniverse, descendScs 1 scs, SourcePruningEnumerationShallowChild.prepareChild
          (EnumGuard := Constraint) (descendScs 1 scs) fullUniverse),
        (fullUniverse, descendScs 2 scs, SourcePruningEnumerationShallowChild.prepareChild
          (EnumGuard := Constraint) (descendScs 2 scs) fullUniverse)] ∧
      fragment = .node (literal "->") fragments ∧
      beforeFinalize = SelectedEdge.finish none fragment afterChildren ∧
      let done := fun produced current capturedQueries captured => consume
        (.complete (.node (literal "->") produced) current capturedQueries
          (SelectedEdge.finish none (.node (literal "->") produced) captured))
      let stopped := fun completed observation candidate => consume (.stopped completed observation candidate)
      let rest := [(fullUniverse, descendScs 1 scs), (fullUniverse, descendScs 2 scs)]
      ∃ (markerFragment : Fragment) (markerCaller : Caller width) (markerQueries : Queries)
        (markerAfter : Cached) (markerConsumerIndex : Nat) (remainingFragments : List Fragment),
        fragments = markerFragment :: remainingFragments ∧
        ChildInvocationAt checkEmpty r n p h k edgesOf policy (descendScs 0 scs) marker
          caller before queries
          (fun produced current capturedQueries captured =>
            visitChildren (runPolicy checkEmpty r n p h k edgesOf policy)
              (fun remaining => done (produced :: remaining))
              (fun completed => stopped (produced :: completed)) rest current captured capturedQueries)
          (fun observation candidate => stopped [] observation candidate)
          index output (.done markerFragment markerCaller markerQueries markerAfter) markerConsumerIndex ∧
        ChildrenInvocationAt checkEmpty r n p h k edgesOf policy
          (fun remaining => done (markerFragment :: remaining))
          (fun completed => stopped (markerFragment :: completed)) rest markerCaller markerAfter markerQueries
          markerConsumerIndex output (.done remainingFragments reached saved afterChildren) consumerIndex ∧
        ((descendScs 0 scs).any (fun sc => EqualityTrie.isTerminal sc.trie) = true →
          ∃ (returned read : Core) (waiting : EnumerationWaitingIndex.Waiting) (winner : Nat),
            ChildDispatch.run checkEmpty r n p h k (descendScs 0 scs) marker caller before queries =
              ((.ok (some [.ok (markerFragment, returned)]), markerCaller, markerQueries, read, waiting),
                some markerAfter) ∧
            index = markerConsumerIndex ∧ markerFragment = .hole winner ∧
            ∀ sc ∈ descendScs 0 scs, [] ∈ EqualityTrie.fromPathTrie sc.trie →
              UnionFind.SameClass returned.representatives winner sc.var)
 := by
  dsimp only
  obtain ⟨symbol, staged, residual, middle, fragments, afterChildren,
      own, tuple, fragmentSame, finishSame⟩ :=
    selected_complete_invocation checkEmpty r n p h k edgesOf policy consume scs row caller before queries
      index output fragment reached saved beforeFinalize consumerIndex trace
  have top := SourceSynthesisCurrentUniverseUnfoldedRowPreparation.original_universe_unfolded_row_top
    lib query signed whole accepted rootValue sourceHeap built key entry body depth ordinary stored
    nativeBefore nativeAfter facts sourceGrowth unfoldFuel prepared unfolded row present
  obtain ⟨_sourceRow, _sourceMember, _sourceSymbol, _sourceGuard, _sourceChildren, classification⟩ :=
    SourceSynthesisCurrentUniverseUnfoldedRowInputs.original_universe_unfolded_row_inputs
      lib query signed whole accepted rootValue sourceHeap built key entry body depth ordinary stored
      nativeBefore nativeAfter facts sourceGrowth unfoldFuel prepared unfolded row present
  have actualArrow : ∃ (marker : Node) (markerEntry : Interned NodeKey) (markerRow : Edge),
      marker = .node markerEntry [markerRow] 0 [] ∧ markerRow.children = [] ∧
      markerRow.entry.key = ⟨literal "(->)", [], SourceSynthesisGeneralizeSyntax.top⟩ ∧
      row.entry.key.symbol = literal "->" ∧
      row.children = [marker, .mu entry body depth ordinary, .mu entry body depth ordinary] := by
    rcases classification with catalog | arrow
    · obtain ⟨name, arity, described, symbolSame, _childrenSame⟩ := catalog
      have nameSame : name = "->" := congrArg Prod.fst (symbolSame.symm.trans arrowSymbol)
      subst name
      change ("->", arity) ∈ [("var1", 0), ("var2", 0), ("var3", 0), ("var4", 0)] ++
        SourceSynthesisCurrentContext.constructorCatalog lib query at described
      rcases List.mem_append.mp described with rigid | declared
      · simp at rigid
      · exact ((SourceSynthesisCurrentContext.constructorCatalog_separate lib query
          ("->", arity) declared).2.1 rfl).elim
    · exact arrow
  obtain ⟨marker, markerEntry, markerRow, markerShape, markerLeaf, markerKey, _rowSymbol, rowChildren⟩ := actualArrow
  obtain ⟨middleSame, symbolSame, residualSame, _first⟩ :=
    SourcePruningEnumerationTopArrowInput.top_arrow_preparation_first
      caller.checked.native.machine.heap scs row marker (.mu entry body depth ordinary)
      (.mu entry body depth ordinary) before middle symbol staged residual top rowChildren own
  have projected : SourcePruningEnumerationConstraint.project row.entry.key.constraint = some ([], none) := by
    rw [top]
    rfl
  have payload := SourcePruningEnumerationCachedOwn.prepare_inputs
    caller.checked.native.machine.heap scs row before middle [] none (symbol, staged, residual) projected own
  have stagedSame : staged = [
      (marker, descendScs 0 scs, SourcePruningEnumerationShallowChild.prepareChild
        (EnumGuard := Constraint) (descendScs 0 scs) marker),
      (.mu entry body depth ordinary, descendScs 1 scs, SourcePruningEnumerationShallowChild.prepareChild
        (EnumGuard := Constraint) (descendScs 1 scs) (.mu entry body depth ordinary)),
      (.mu entry body depth ordinary, descendScs 2 scs, SourcePruningEnumerationShallowChild.prepareChild
        (EnumGuard := Constraint) (descendScs 2 scs) (.mu entry body depth ordinary))] := by
    have projection := congrArg (fun value : Symbol × List Input × Option Constraint => value.2.1) payload
    dsimp only at projection
    rw [projection]
    simp [SourcePruningEnumerationEdgeInputs.children, rowChildren, suspendedVars, descendScs,
      EqualityTrie.descendScs]
  let done := fun produced current capturedQueries captured => consume
    (.complete (.node (literal "->") produced) current capturedQueries
      (SelectedEdge.finish none (.node (literal "->") produced) captured))
  let stopped := fun completed observation candidate => consume (.stopped completed observation candidate)
  let rest : List (Node × List Suspended) :=
    [(.mu entry body depth ordinary, descendScs 1 scs), (.mu entry body depth ordinary, descendScs 2 scs)]
  have tupleAt : ChildrenInvocationAt checkEmpty r n p h k edgesOf policy done stopped
      ((marker, descendScs 0 scs) :: rest) caller before queries index output
      (.done fragments reached saved afterChildren) consumerIndex := by
    simpa only [middleSame, symbolSame, residualSame, arrowSymbol, stagedSame, List.map_cons, List.map_nil]
      using tuple
  obtain ⟨markerFragment, markerCaller, markerQueries, markerAfter, markerConsumerIndex,
      remainingFragments, fragmentsSame, markerTrace, remainingTrace⟩ :=
    children_done_head_invocation checkEmpty r n p h k edgesOf policy done stopped marker
      (descendScs 0 scs) rest caller before queries index output fragments reached saved afterChildren
      consumerIndex tupleAt
  refine ⟨marker, markerEntry, markerRow, staged, fragments, afterChildren,
    markerShape, markerLeaf, markerKey, rowChildren, top, ?_, stagedSame, ?_, ?_,
    markerFragment, markerCaller, markerQueries, markerAfter, markerConsumerIndex, remainingFragments,
    fragmentsSame, markerTrace, remainingTrace, ?_⟩
  · simpa only [middleSame, symbolSame, residualSame, arrowSymbol] using own
  · simpa only [symbolSame, arrowSymbol] using fragmentSame
  · simpa only [residualSame] using finishSame
  · intro terminal
    obtain ⟨returned, read, waiting, dispatch, sameIndex⟩ :=
      terminal_done_dispatch checkEmpty r n p h k edgesOf policy (descendScs 0 scs) marker
        caller before queries _ _ index output markerFragment markerCaller markerQueries markerAfter
        markerConsumerIndex terminal markerTrace
    obtain ⟨roots, paths⟩ := roots_exist before.core.representatives total
    obtain ⟨_first, _rest, _descendants, _recorded, winner, _joined, _foldCaller, _foldQueries,
        _folded, _foldOuter, _partitioned, _prefix, _foldedCall, _foldedEndpoint, _incoming,
        _recordedSame, _joinedValues, hole, _foldForest, _readForest, aliases⟩ :=
      ChildDispatch.terminal_singleton_final_raw_target_incidence checkEmpty r n p h k
        (descendScs 0 scs) marker caller before queries terminal markerFragment markerCaller markerQueries
        read returned waiting (some markerAfter) roots paths dispatch
    exact ⟨returned, read, waiting, winner, dispatch, sameIndex, hole,
      fun sc member represented => (aliases sc member represented).2.2.2⟩

end MicroCFTA.SourceSynthesisCurrentUniverseArrowInvocationProvenance

#check MicroCFTA.SourceSynthesisCurrentUniverseArrowInvocationProvenance.original_universe_arrow_selected_provenance
#print axioms MicroCFTA.SourceSynthesisCurrentUniverseArrowInvocationProvenance.original_universe_arrow_selected_provenance
