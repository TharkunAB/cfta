import MicroCFTA.SourceSynthesisCurrentInitialSharedVisitorOrigin
import MicroCFTA.SourceSynthesisCurrentInitialEagerInvocation
import MicroCFTA.SourcePruningEnumerationSharedPreparedRecursiveChildPolicy

/-!
# Source rows in the initial eager scan

The initial eager invocation uses its canonical expansion of slot zero.
Its prepared scan retains the actual ordered prefix caller and queries.
Each reached row retains the original source filter construction.
The result uses the raw source build and configured hooks.
It does not construct a joint finite assignment.
-/
namespace MicroCFTA.SourceSynthesisCurrentInitialEagerRootScanOrigin
open EnumerationState InternedConstructorTemplates InternedProbeProvenance
local notation "State" => InternedConstructorTemplates.State
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Guard
local notation "Metadata" => SourcePruningRecordTypes.Metadata
local notation "Expression" => SourceSynthesisFirstOrderConstruction.Expression
local notation "literal" => SourceSynthesisLabelProgramBuildRoles.literal
local notation "ordinarySymbols" => SourceSynthesisUniverseCallerBoundary.ordinarySymbols
local notation "filterGuard" => SourceSynthesisGeneralizeSyntax.eqGuard [[[0], [1, 0]]]

theorem initial_runEager_prepared_root_scan_origin
    {Typing Key : Type} {width : Nat}
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
    (checkEmpty : Bool) (workFuel depth : Nat)
    (queries : SourceEndpointMemo.Memos) :
    let caller := SourceCurrentAllocatedPartialInitialization.caller width cache heap
    let startup : Cached :=
      ⟨EnumerationState.initial handle,
        fun slot => if slot = 0 then !MergedOrdinaryHeight.recursiveBoundary rootValue else false,
        fun _ => none⟩
    let child := SourcePruningEnumerationSharedEagerChildren.eagerChild checkEmpty
      workFuel workFuel workFuel workFuel workFuel InternedEdgeResidency.nodeEdges
    let firstDecision := SourcePruningEnumerationRestart.decision stop order metadata startup
    (∀ uv, firstDecision = some (.expand uv) → uv = 0) ∧
    (match firstDecision with
    | some (.expand _) =>
        match SourcePruningEnumerationSelectedStep.runPrefix holeKey fits admits graph templates
          stop order metadata workFuel workFuel workFuel workFuel workFuel workFuel
          0 caller startup queries with
        | .narrowed _checked (.done (_narrowed, some _action) _narrowedHeap) reached saved
            (some [.ok ((), _actionCore)]) (some candidate)
            (some [.ok ((false, updated), _callbackCore)]) none =>
            let recur := SourcePruningEnumerationSharedPreparedRecursiveChildPolicy.resumeWithChild
              (width := width) child holeKey fits admits graph templates checkEmpty
              InternedEdgeResidency.nodeEdges stop order workFuel depth
            let hook := SourcePruningEnumerationSharedPreparedRecursive.continueWith
              recur graph templates stop order workFuel updated 0
            match SourcePruningEnumerationSelectedPreparation.run workFuel workFuel
              0 reached candidate with
            | ([.ok ((_target, _readHandle, _scs, _decodedValue), entered)],
                some (.done parent@(.node ..) preparedHeap)) =>
                let captured := EnumerationExpandableIndex.frame entered candidate
                let firstCaller := SourcePruningEnumerationSelectedValueCaller.advance reached preparedHeap
                let rows := InternedEdgeResidency.nodeEdges parent
                let visit := SourcePruningEnumerationSharedChildVisitors.visitCapturedWith
                  child hook workFuel 0 []
                SourcePruningEnumerationSharedPreparedRecursiveChildPolicy.runEager
                    holeKey fits admits graph templates checkEmpty InternedEdgeResidency.nodeEdges
                    stop order workFuel (depth + 1) metadata caller queries startup =
                  SourcePruningEnumerationSharedPreparedRecursive.finish 0
                    (SourcePruningEnumerationSharedBranching.scan visit captured rows firstCaller saved) ∧
                SourcePruningEnumerationSharedPreparedChildPolicy.runWithChild child hook
                    checkEmpty workFuel workFuel workFuel workFuel workFuel workFuel workFuel 0
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
    | _ => True)
 := by
  let caller := SourceCurrentAllocatedPartialInitialization.caller width cache heap
  let startup : Cached :=
    ⟨EnumerationState.initial handle,
      fun slot => if slot = 0 then !MergedOrdinaryHeight.recursiveBoundary rootValue else false,
      fun _ => none⟩
  let child := SourcePruningEnumerationSharedEagerChildren.eagerChild
    (width := width)
    (Output := SourcePruningEnumerationSharedPreparedRecursive.Output width Typing)
    (Reason := SourcePruningEnumerationSharedPreparedRecursive.Failure width Typing)
    checkEmpty workFuel workFuel workFuel workFuel workFuel InternedEdgeResidency.nodeEdges
  have canonical := SourceSynthesisCurrentProgramEagerOutputs.initial_runEager_canonical
    (width := width) cache rootValue heap handle holeKey fits admits graph templates
    checkEmpty stop order workFuel (depth + 1) metadata queries
  dsimp only at canonical
  dsimp only
  refine ⟨canonical.1, ?_⟩
  split
  · rename_i uv firstEq
    have wholeRun := canonical.2
    rw [firstEq] at wholeRun
    split
    · rename_i checked narrowed action narrowedHeap reached saved actionCore candidate
        updated callbackCore prefixEq
      let recur := SourcePruningEnumerationSharedPreparedRecursiveChildPolicy.resumeWithChild
        (width := width) child holeKey fits admits graph templates checkEmpty
        InternedEdgeResidency.nodeEdges stop order workFuel depth
      let hook := SourcePruningEnumerationSharedPreparedRecursive.continueWith
        recur graph templates stop order workFuel updated 0
      have observed := SourceSynthesisCurrentInitialSharedVisitorOrigin.initial_prepared_shared_root_scan_origin
        (width := width) lib query signed whole accepted rootValue heap built cache handle decoded
        holeKey fits admits graph templates stop order metadata
        workFuel workFuel workFuel workFuel workFuel workFuel workFuel workFuel
        queries child hook checkEmpty workFuel workFuel workFuel workFuel workFuel
      dsimp only at observed
      rw [prefixEq] at observed
      dsimp only at observed
      split
      · rename_i target readHandle scs decodedValue entered entry nativeRows nodeDepth free
          preparedHeap preparationEq
        rw [preparationEq] at observed
        obtain ⟨preparedRun, indexed⟩ := observed
        have transition := SourcePruningEnumerationSharedPreparedRecursiveChildPolicy.resume_prepared
          (width := width) child holeKey fits admits graph templates checkEmpty
          InternedEdgeResidency.nodeEdges stop order workFuel depth 0 metadata updated
          caller reached queries saved startup candidate checked callbackCore
          (.done (narrowed, some action) narrowedHeap) actionCore prefixEq
        refine ⟨wholeRun.trans (transition.trans ?_), preparedRun, ?_⟩
        · rw [preparedRun]
        · intro position
          have observedAt := indexed position
          split
          · trivial
          · rename_i prior outputs rowCaller rowQueries scanEq
            rw [scanEq] at observedAt
            dsimp only at observedAt
            split
            · trivial
            · rename_i rootRow rowLookup
              rw [rowLookup] at observedAt
              dsimp only at observedAt
              obtain ⟨member, ordered, chunks, goalValue, candidateValue,
                  candidateStart, candidateAfter, edgeAfter, chunksRun, wholeShape,
                  symbolSame, guardSame, childrenSame, goalCall, sourceContext,
                  candidateCall, edgeCall, nodeCall, growth, ownFields⟩ := observedAt
              refine ⟨member, ?_, chunks, goalValue, candidateValue,
                candidateStart, candidateAfter, edgeAfter, chunksRun, wholeShape,
                symbolSame, guardSame, childrenSame, goalCall, sourceContext,
                candidateCall, edgeCall, nodeCall, growth, ?_⟩
              · split
                · rename_i processed emitted current headEq
                  rw [headEq] at ordered
                  dsimp only at ordered
                  exact ordered
                · rename_i processed emitted nextCaller nextQueries headEq
                  rw [headEq] at ordered
                  dsimp only at ordered
                  split
                  · rename_i later more finalCaller finalQueries tailEq
                    rw [tailEq] at ordered
                    dsimp only at ordered
                    exact ordered
                  · rename_i later more current tailEq
                    rw [tailEq] at ordered
                    dsimp only at ordered
                    exact ordered
              · split
                · rename_i symbol staged residual ownAfter ownEq
                  rw [ownEq] at ownFields
                  dsimp only at ownFields
                  exact ownFields
                · trivial
      · trivial
    · trivial
  · trivial

end MicroCFTA.SourceSynthesisCurrentInitialEagerRootScanOrigin
