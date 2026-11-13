import MicroCFTA.SourceSynthesisCurrentInitialFilterInterval
import MicroCFTA.SourcePruningEnumerationSharedPreparedChildPolicy
import MicroCFTA.SourceSynthesisCurrentInitialPreparationOrigin
import MicroCFTA.SourcePruningEnumerationSharedBranchingAppend

/-!
# Initial shared row visitor and original source rows

The initial preparation supplies the same captured Core and native value.
Each completed scan prefix supplies its actual caller and queries.
Each indexed row retains the original source filter construction.
The own preparation observation uses that row and reached native heap.
This result does not construct a joint finite assignment.
-/
namespace MicroCFTA.SourceSynthesisCurrentInitialSharedVisitorOrigin
open EnumerationState InternedConstructorTemplates InternedProbeProvenance
open SourcePruningEnumerationSharedSelectedContinuations
open SourcePruningEnumerationSharedSelectedContinuations.NativeContinuations (HookResult)
local notation "State" => InternedConstructorTemplates.State
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Guard
local notation "Queries" => SourceEndpointMemo.Memos
local notation "Fragment" => Fragments.Fragment Symbol
local notation "Observation" => ChildDispatch.Observation
local notation "Fold" => NativeContinuations.Result
local notation "Metadata" => SourcePruningRecordTypes.Metadata
local notation "Expression" => SourceSynthesisFirstOrderConstruction.Expression
local notation "literal" => SourceSynthesisLabelProgramBuildRoles.literal
local notation "ordinarySymbols" => SourceSynthesisUniverseCallerBoundary.ordinarySymbols
local notation "filterGuard" => SourceSynthesisGeneralizeSyntax.eqGuard [[[0], [1, 0]]]

universe u v

private theorem lookup_split {α : Type u} (values : List α) (position : Nat) (value : α)
    (found : values[position]? = some value) :
    values = values.take position ++ value :: values.drop (position + 1) := by
  induction values generalizing position with
  | nil =>
      simp only [List.getElem?_nil] at found
      cases found
  | cons first rest ih =>
      cases position with
      | zero =>
          have same : first = value := Option.some.inj found
          cases same
          rfl
      | succ position =>
          change rest[position]? = some value at found
          simpa only [List.take_succ_cons, List.drop_succ_cons, List.cons_append] using
            congrArg (List.cons first) (ih position found)

private theorem scan_at_index {Output : Type u} {Reason : Type v} {width : Nat}
    (visit : EdgeValue Symbol Guard → Caller width → Queries → Cached → Fold Output Reason width)
    (captured : Cached) (rows : List (EdgeValue Symbol Guard)) (position : Nat)
    (firstCaller rowCaller : Caller width) (queries rowQueries : Queries)
    (prior : List (SelectedEdge.Result width)) (outputs : List Output)
    (prefixRun : SourcePruningEnumerationSharedBranching.scan visit captured
      (rows.take position) firstCaller queries = .complete prior outputs rowCaller rowQueries)
    (rootRow : EdgeValue Symbol Guard) (found : rows[position]? = some rootRow) :
    SourcePruningEnumerationSharedBranching.scan visit captured rows firstCaller queries =
      (match visit rootRow rowCaller rowQueries captured with
      | .stopped processed emitted current =>
          .stopped (prior ++ processed) (outputs ++ emitted) current
      | .complete processed emitted nextCaller nextQueries =>
          match SourcePruningEnumerationSharedBranching.scan visit captured
            (rows.drop (position + 1)) nextCaller nextQueries with
          | .complete later more finalCaller finalQueries =>
              .complete (prior ++ processed ++ later) (outputs ++ emitted ++ more) finalCaller finalQueries
          | .stopped later more current =>
              .stopped (prior ++ processed ++ later) (outputs ++ emitted ++ more) current) := by
  have combined := SourcePruningEnumerationSharedBranching.scan_append visit captured
    (rows.take position) (rootRow :: rows.drop (position + 1)) firstCaller queries
  rw [← lookup_split rows position rootRow found, prefixRun] at combined
  cases headRun : visit rootRow rowCaller rowQueries captured with
  | stopped processed emitted current =>
      simpa only [SourcePruningEnumerationSharedBranching.scan, headRun] using combined
  | complete processed emitted nextCaller nextQueries =>
      cases suffixRun : SourcePruningEnumerationSharedBranching.scan visit captured
          (rows.drop (position + 1)) nextCaller nextQueries with
      | complete later more finalCaller finalQueries =>
          simpa only [SourcePruningEnumerationSharedBranching.scan, headRun, suffixRun,
            List.append_assoc] using combined
      | stopped later more current =>
          simpa only [SourcePruningEnumerationSharedBranching.scan, headRun, suffixRun,
            List.append_assoc] using combined

private theorem own_prepare_fields (heap : State Symbol Guard) (edge : EdgeValue Symbol Guard)
    (captured : Cached) :
    match SourcePruningEnumerationCachedOwn.prepare heap [] edge captured with
    | some [((symbol, staged, _residual), _ownAfter)] =>
        symbol = edge.entry.key.symbol ∧ staged.map (fun input => input.1) = edge.children
    | _ => True := by
  unfold SourcePruningEnumerationCachedOwn.prepare
  simp only [arityAllows, List.all_nil, ↓reduceIte]
  generalize projectionEq : SourcePruningEnumerationConstraint.project edge.entry.key.constraint = projection
  cases projection with
  | none => trivial
  | some projectedPair =>
      obtain ⟨tries, residual⟩ := projectedPair
      dsimp only
      cases allocated : SourcePruningEnumerationCachedOwn.suspendMany heap tries captured with
      | none => trivial
      | some allocation =>
          obtain ⟨own, after⟩ := allocation
          refine ⟨rfl, ?_⟩
          simpa only [List.map_map, Function.comp_def] using List.zipIdx_map_fst 0 edge.children

/-- Trace the observed initial shared scan through each actual sibling endpoint. -/
theorem initial_prepared_shared_root_scan_origin
    {Typing Key : Type} {Output : Type u} {Reason : Type v} {width : Nat}
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Node]
    (lib : SourceSynthesisTypeSyntax.Library) (query : SourceSynthesisTypeSyntax.Query)
    (signed : Int) (whole : SourceSynthesisFirstOrderConstruction.Expression)
    (accepted : SourceSynthesisCurrentConstruction.firstOrderRaw lib query signed = .ok whole)
    (rootValue : Node) (heap : InternedConstructorTemplates.State Symbol Guard)
    (built : InternedFreshOrdinaryConstruction.build
      (SourceSynthesisUniverseCallerBoundary.ordinarySymbols whole) []
      InternedConstructorTemplates.empty = .done rootValue heap)
    (cache : Cache.State SourceEqualityPartialConstraintKey.Key)
    (handle : Nat)
    (decoded : SourcePruningEnumerationNodes.lookupNode heap handle = some rootValue)
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool)
    (admits : Key → Node → Bool)
    (graph : Graph Symbol Guard) (templates : List (Template.Pattern Symbol))
    (stop : Option (Metadata Typing → Nat → Bool))
    (order : Metadata Typing → List Nat → Option Nat) (metadata : Metadata Typing)
    (readFuel checkFuel nativeFuel representativeFuel indexFuel callbackFuel : Nat)
    (entryFuel preparationFuel : Nat)
    (queries : SourceEndpointMemo.Memos)
    (child : List Suspended → Node → Caller width → Cached → Queries →
      (Fragment → Caller width → Queries → Cached → Fold Output Reason width) →
      (Observation width → Option Cached → Fold Output Reason width) → Fold Output Reason width)
    (hook : Fragment → Caller width → Queries → Cached → HookResult Output Reason width)
    (checkEmpty : Bool) (r n p h k : Nat) :
    let caller := SourceCurrentAllocatedPartialInitialization.caller width cache heap
    let startup : Cached :=
      ⟨EnumerationState.initial handle,
        fun slot => if slot = 0 then !MergedOrdinaryHeight.recursiveBoundary rootValue else false,
        fun _ => none⟩
    match SourcePruningEnumerationSelectedStep.runPrefix holeKey fits admits graph templates
      stop order metadata readFuel checkFuel nativeFuel representativeFuel indexFuel callbackFuel
      0 caller startup queries with
    | .narrowed _checked (.done (_narrowed, some _action) _narrowedHeap) reached saved
        (some [.ok ((), _actionCore)]) (some candidate)
        (some [.ok ((false, _updated), _callbackCore)]) none =>
        match SourcePruningEnumerationSelectedPreparation.run entryFuel preparationFuel
          0 reached candidate with
        | ([.ok ((_target, _readHandle, _scs, _decodedValue), entered)],
            some (.done parent@(.node ..) preparedHeap)) =>
            let captured := EnumerationExpandableIndex.frame entered candidate
            let firstCaller := SourcePruningEnumerationSelectedValueCaller.advance reached preparedHeap
            let rows := InternedEdgeResidency.nodeEdges parent
            let visit := SourcePruningEnumerationSharedChildVisitors.visitCapturedWith
              child hook k 0 []
            SourcePruningEnumerationSharedPreparedChildPolicy.runWithChild child hook
                checkEmpty entryFuel preparationFuel r n p h k 0
                InternedEdgeResidency.nodeEdges reached candidate saved =
              (([.ok ((_target, _readHandle, _scs, _decodedValue), entered)],
                  some (.done parent preparedHeap)),
                some (SourcePruningEnumerationSharedBranching.scan visit captured rows firstCaller saved)) ∧
            ∀ position : Nat,
              match SourcePruningEnumerationSharedBranching.scan visit captured
                (rows.take position) firstCaller saved with
              | .stopped _processed _outputs _current => True
              | .complete prior outputs rowCaller rowQueries =>
                  match rows[position]? with
                  | none => True
                  | some rootRow =>
                      rootRow ∈ InternedEdgeResidency.nodeEdges rootValue ∧
                      SourcePruningEnumerationSharedBranching.scan visit captured rows firstCaller saved =
                        (match visit rootRow rowCaller rowQueries captured with
                        | .stopped processed emitted current =>
                            .stopped (prior ++ processed) (outputs ++ emitted) current
                        | .complete processed emitted nextCaller nextQueries =>
                            match SourcePruningEnumerationSharedBranching.scan visit captured
                              (rows.drop (position + 1)) nextCaller nextQueries with
                            | .complete later more finalCaller finalQueries =>
                                .complete (prior ++ processed ++ later) (outputs ++ emitted ++ more)
                                  finalCaller finalQueries
                            | .stopped later more current =>
                                .stopped (prior ++ processed ++ later) (outputs ++ emitted ++ more) current) ∧
                      ∃ (chunks : List (List Expression))
                          (goalValue candidateValue : Node)
                          (candidateStart candidateAfter edgeAfter : State Symbol Guard),
                        (SourceSynthesisSelections.permutations
                          (SourceSynthesisCurrentContext.context lib query).argumentEdges).mapM
                          (fun selected => SourceSynthesisFirstOrderConstruction.relevantRows
                            (SourceSynthesisCurrentContext.context lib query) true signed.toNat
                            (selected.map Prod.fst)) = .ok chunks ∧
                        whole = SourceSynthesisFirstOrderConstruction.ofType (.union chunks.flatten)
                          (SourceSynthesisCurrentContext.typeNode query.queryGoal) ∧
                        rootRow.entry.key.symbol = literal "filter" ∧
                        rootRow.entry.key.constraint = filterGuard ∧
                        rootRow.children = [goalValue, candidateValue] ∧
                        InternedFreshOrdinaryConstruction.build
                          (ordinarySymbols (SourceSynthesisCurrentContext.typeNode query.queryGoal))
                          [] empty = .done goalValue candidateStart ∧
                        SourceCurrentConstrainedCapSourceHistory.Context candidateStart [] ∧
                        InternedFreshOrdinaryConstruction.build
                          (ordinarySymbols (.union chunks.flatten)) [] candidateStart =
                            .done candidateValue candidateAfter ∧
                        run (makeEdge (literal "filter") filterGuard [goalValue, candidateValue])
                          candidateAfter = (rootRow, edgeAfter) ∧
                        run (makeNode [rootRow]) edgeAfter = (rootValue, heap) ∧
                        Grows candidateAfter heap ∧
                        (match SourcePruningEnumerationCachedOwn.prepare
                            rowCaller.checked.native.machine.heap [] rootRow captured with
                        | some [((symbol, staged, _residual), _ownAfter)] =>
                            symbol = literal "filter" ∧
                              staged.map (fun input => input.1) = [goalValue, candidateValue]
                        | _ => True)
        | _ => True
    | _ => True
 := by
  let caller := SourceCurrentAllocatedPartialInitialization.caller width cache heap
  let startup : Cached :=
    ⟨EnumerationState.initial handle,
      fun slot => if slot = 0 then !MergedOrdinaryHeight.recursiveBoundary rootValue else false,
      fun _ => none⟩
  dsimp only
  split
  · rename_i checked narrowed action narrowedHeap reached saved actionCore candidate updated callbackCore prefixEq
    have origin := SourceSynthesisCurrentInitialPrefixOrigin.initial_prefix_preparation_rows
      (width := width) lib query signed whole accepted rootValue heap built cache handle decoded
      holeKey fits admits graph templates stop order metadata readFuel checkFuel nativeFuel
      representativeFuel indexFuel callbackFuel entryFuel preparationFuel queries
    dsimp only at origin
    rw [prefixEq] at origin
    obtain ⟨_savedSame, _updatedSame, _callbackSame, _reachedHeap, _ordinary,
      _newHandle, _encoded, _decoded, _stored, preparationOrigin⟩ := origin
    split
    · rename_i target readHandle scs decodedValue entered entry nativeRows depth free preparedHeap preparationEq
      rw [preparationEq] at preparationOrigin
      obtain ⟨targetSame, _handleSame, scsSame, _decodedSame, _preparedSame, _heapSame,
        _stable, _advancedHeap, included⟩ := preparationOrigin
      subst target
      subst scs
      let parent : Node := .node entry nativeRows depth free
      let captured := EnumerationExpandableIndex.frame entered candidate
      let firstCaller := SourcePruningEnumerationSelectedValueCaller.advance reached preparedHeap
      let rows := InternedEdgeResidency.nodeEdges parent
      let visit : EdgeValue Symbol Guard → Caller width → Queries → Cached → Fold Output Reason width :=
        SourcePruningEnumerationSharedChildVisitors.visitCapturedWith child hook k 0 []
      constructor
      · unfold SourcePruningEnumerationSharedPreparedChildPolicy.runWithChild
        rw [preparationEq]
        rfl
      · intro position
        cases prefixRun : SourcePruningEnumerationSharedBranching.scan visit captured
            (rows.take position) firstCaller saved with
        | stopped prior outputs current => trivial
        | complete prior outputs rowCaller rowQueries =>
            cases rowLookup : rows[position]? with
            | none => trivial
            | some rootRow =>
                have rootMember : rootRow ∈ InternedEdgeResidency.nodeEdges rootValue :=
                  included rootRow (List.mem_of_getElem? rowLookup)
                refine ⟨rootMember, ?_, ?_⟩
                · exact scan_at_index visit captured rows position firstCaller rowCaller saved rowQueries
                    prior outputs prefixRun rootRow rowLookup
                · obtain ⟨chunks, goalValue, candidateValue, candidateStart, candidateAfter, edgeAfter,
                    chunksRun, wholeShape, symbolSame, guardSame, childrenSame, goalCall,
                    sourceContext, candidateCall, edgeCall, nodeCall, growth, _factory⟩ :=
                    SourceSynthesisCurrentFirstFilterSourceLink.current_initial_filter_interval
                      lib query signed whole accepted rootValue heap built rootRow rootMember
                  refine ⟨chunks, goalValue, candidateValue, candidateStart, candidateAfter, edgeAfter,
                    chunksRun, wholeShape, symbolSame, guardSame, childrenSame, goalCall,
                    sourceContext, candidateCall, edgeCall, nodeCall, growth, ?_⟩
                  simpa only [symbolSame, childrenSame] using
                    own_prepare_fields rowCaller.checked.native.machine.heap rootRow captured
    · trivial
  · trivial

end MicroCFTA.SourceSynthesisCurrentInitialSharedVisitorOrigin
