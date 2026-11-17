import MicroCFTA.SourceCurrentNativeNumericalSingletonProfiles
import MicroCFTA.SourceSynthesisCurrentUniverseThirdQueryEdgeSeed

namespace MicroCFTA.SourceCurrentNativeNumericalSingletonEdgeProfiles
open Cache InternedConstructorTemplates InternedNestedFacts InternedProbeProvenance
open InternedBinderProtocol (NodeKey Reference)
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceEqualityNativeDemand
open SourceCurrentAllocatedNativeSourceWarmEntry (MixedQualifiedAt)
open SourceCurrentNativeWarmCMDefinitions (Qualified NodeResult EdgeResult)
open SourceCurrentAllocatedNativeContextCache (Returned)
open SourceCurrentAllocatedNativePhysicalTraceCompletion (Trace)
open SourceCurrentAllocatedNativePhysicalExecution (InputsThrough)
open SourceEqualityNativeDemandOperations (FieldsThrough)
open SourceSynthesisTypeSyntax (Library Query)
open SourceSynthesisFirstOrderConstruction (Expression)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSynthesisGeneralizeSyntax.Guard
local notation "Node" => Value Symbol Guard
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Physical" => SourceCurrentAllocatedNativePhysicalCache.Valid
local notation "Profile" => SourceCurrentAllocatedNativeClosedResetProfile.Profile
local notation "ordinarySymbols" => SourceSynthesisUniverseCallerBoundary.ordinarySymbols
open SourceCurrentNativeNumericalSeedInvariant (Seeds)
open SourceRecursiveIntersectionControl (identity pair)
open SourceRecursiveIntersectionDomain (extend)
set_option autoImplicit false

/- Note [Singleton edge children from actual retained node cells]
Inherited edge cells use the past query invariant.
Each new edge child has one actual node query in the current history.
That query supplies its own source admission and complete memo key.
Its exact returned cell remains at the current prefix.
The derived singleton node law applies to that same cell.
The checked edge body retains arity mismatch and sentinel behavior.
-/

private theorem third_edge_closed_codec (value : Value Symbol Guard) (closed : value.free = []) :
    ∃ input, IntersectionFlatMemoKey.input value.referenceOf = some input := by
  cases value <;> simp_all [Value.free, Value.referenceOf, IntersectionFlatMemoKey.input]

private theorem third_edge_key_of_codecs {width : Nat} (request : NodeRequest Symbol Guard)
    (left : ∃ input, IntersectionFlatMemoKey.input request.left.referenceOf = some input)
    (right : ∃ input, IntersectionFlatMemoKey.input request.right.referenceOf = some input) :
    ∃ key, SourceRecursiveIntersectionMemo.requestKey width request.domain request.left request.right = some key := by
  obtain ⟨first, firstInput⟩ := left
  obtain ⟨second, secondInput⟩ := right
  exact ⟨_, IntersectionFlatMemoKeyDomain.sourceKey_complete width request.domain _ _
    first second firstInput secondInput⟩

private theorem third_edge_qualified_key
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat}
    (rootRequest : NodeRequest Symbol Guard) (start : Checked width) (wholeCount : Nat)
    (entry : Interned NodeKey) (body depth ordinary : Value Symbol Guard)
    (bodyCodec : ∃ input, IntersectionFlatMemoKey.input body.referenceOf = some input)
    (request : NodeRequest Symbol Guard)
    (qualified : Qualified (width := width) rootRequest start wholeCount entry body depth ordinary request) :
    ∃ key, SourceRecursiveIntersectionMemo.requestKey width request.domain request.left request.right = some key := by
  rcases qualified with closed | mixed
  · exact third_edge_key_of_codecs (width := width) request (third_edge_closed_codec _ closed.1.1) (third_edge_closed_codec _ closed.2.1.1)
  · obtain ⟨pattern, patternId, openAlias, operand, _authentic, alias, operandProfile,
      _height, _strict, ordered⟩ := mixed
    have aliasCodec : ∃ input, IntersectionFlatMemoKey.input openAlias.referenceOf = some input := by
      rcases alias with rfl | rfl
      · exact bodyCodec
      · exact ⟨.ref entry.identity, rfl⟩
    have operandCodec := third_edge_closed_codec _ operandProfile.1
    rcases ordered with ⟨left, right⟩ | ⟨left, right⟩
    · exact third_edge_key_of_codecs (width := width) request (by rw [left]; exact aliasCodec) (by rw [right]; exact operandCodec)
    · exact third_edge_key_of_codecs (width := width) request (by rw [left]; exact operandCodec) (by rw [right]; exact aliasCodec)

theorem singleton_edges_at_every_actual_prefix_of_past_seeds
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat}
    (lib : Library) (query : Query) (signed : Int) (whole : Expression)
    (accepted : SourceSynthesisCurrentConstruction.firstOrderRaw lib query signed = .ok whole)
    (rootValue : Value Symbol Guard) (sourceHeap : InternedConstructorTemplates.State Symbol Guard)
    (built : InternedFreshOrdinaryConstruction.build (ordinarySymbols whole) [] empty =
      .done rootValue sourceHeap)
    (key : NodeKey) (entry : Interned NodeKey) (body depth ordinary : Value Symbol Guard)
    (stored : sourceHeap.nodeRecords key = some (.mu entry body depth ordinary))
    (bodyId : Nat) (bodyIdentity : identity body = some bodyId)
    (rootRequest : NodeRequest Symbol Guard) (start : Checked width)
    (initialPhysical : Physical start.native)
    (sourceGrowth : Grows sourceHeap start.native.machine.heap)
    (operationsValid : SourceEqualityConstraintMemoAllocation.Valid start.operations)
    (pastSeeds : Seeds sourceHeap entry body depth ordinary bodyId start)
    (rootDomain : rootRequest.domain = IntersectionEmptyDomain.emptyDomain)
    (leftAvailable : Available start.native.machine.heap rootRequest.left)
    (rightAvailable : Available start.native.machine.heap rootRequest.right)
    (leftClosed : rootRequest.left.free = []) (rightClosed : rootRequest.right.free = [])
    (fuel wholeCount : Nat) (rest : Control (Value Symbol Guard)) (reader : Checked width)
    (wholeBound : wholeCount ≤ fuel)
    (inputs : InputsThrough fuel (.code (.node rootRequest .pure)) start)
    (fields : FieldsThrough fuel (.code (.node rootRequest .pure)) start)
    (wholeActual : Trace wholeCount (.code (.node rootRequest .pure)) start rest reader) :
    Returned (fun (request : EdgeRequest Symbol Guard) (row : EdgeValue Symbol Guard) =>
      ∀ patternId : Nat, request.domain.key =
        extend IntersectionEmptyDomain.emptyKey [entry.identity] (pair entry.identity patternId) →
      ∀ child ∈ row.children, Profile entry.identity child) reader.native.edges ∧
    ∀ (used : Nat) (currentControl : Control (Value Symbol Guard)) (current : Checked width),
      used ≤ wholeCount →
      Trace used (.code (.node rootRequest .pure)) start currentControl current →
      Returned (fun (request : EdgeRequest Symbol Guard) (row : EdgeValue Symbol Guard) =>
        ∀ patternId : Nat, request.domain.key =
          extend IntersectionEmptyDomain.emptyKey [entry.identity] (pair entry.identity patternId) →
        ∀ child ∈ row.children, Profile entry.identity child) current.native.edges := by
  have nodeSeeds := SourceCurrentNativeNumericalSingletonProfiles.singleton_nodes_at_every_actual_prefix_of_past_seeds
    lib query signed whole accepted rootValue sourceHeap built key entry body depth ordinary stored
    bodyId bodyIdentity rootRequest start initialPhysical sourceGrowth operationsValid pastSeeds
    rootDomain leftAvailable rightAvailable leftClosed rightClosed
    fuel wholeCount rest reader wholeBound inputs fields wholeActual
  have inheritedFacts := pastSeeds
  dsimp only [Seeds] at inheritedFacts
  obtain ⟨inventory, _closedNodes, _closedEdges, _inheritedNodes, inheritedEdges, _auxiliary⟩ := inheritedFacts
  obtain ⟨bodyEntry, _marker, arrow, rows, bodyShape, _bodyAvailable, _markerShape,
      _arrowChildren, _arrowKey, _catalog, _markerClosed, _markerAvailable, _markerAtoms,
      _rowKinds, _arrowRetained⟩ :=
    SourceSynthesisCurrentUniverseBodyChildClassification.current_stored_universe_body_physical_children_after_growth
      lib query signed whole accepted rootValue sourceHeap built key entry body depth ordinary stored
      start.native.machine.heap initialPhysical.machine.1 sourceGrowth
  have actualBodyIdentity : identity body = some bodyEntry.identity := by
    rw [bodyShape]
    rfl
  have bodyCodec : ∃ input, IntersectionFlatMemoKey.input body.referenceOf = some input := by
    rw [bodyShape]
    exact ⟨.node bodyEntry.identity, rfl⟩
  have atPrefix (used : Nat) (currentControl : Control (Value Symbol Guard)) (current : Checked width)
      (within : used ≤ wholeCount)
      (actual : Trace used (.code (.node rootRequest .pure)) start currentControl current) :
      Returned (fun (request : EdgeRequest Symbol Guard) (row : EdgeValue Symbol Guard) =>
        ∀ patternId : Nat, request.domain.key =
          extend IntersectionEmptyDomain.emptyKey [entry.identity] (SourceRecursiveIntersectionControl.pair entry.identity patternId) →
        ∀ child ∈ row.children, Profile entry.identity child) current.native.edges := by
    intro handle request row currentCell targetPatternId singletonKey
    rcases SourceCurrentAllocatedNativeEdgeReturnOrigin.returned_edge_cell_or_finish_prefix
        actual handle request row currentCell with inherited | produced
    · exact inheritedEdges handle request row inherited targetPatternId singletonKey
    · obtain ⟨finishUsed, _suffixCount, beforeFinish, continuation, finishTotal,
        finishActual, owner, _finishEvent, _finished, _suffix⟩ := produced
      obtain ⟨queryUsed, bodyCount, queryBefore, beforeBody, queryResume, total,
          _querySmaller, _queryBound, queryPrefix, _actualDispatch, isolatedDispatch,
          queryPhysical, _queryReady, _querySafe, _bodyOwner, rawBody, _queryRest⟩ :=
        SourceCurrentAllocatedNativeEdgeQueryDispatchOrigin.actual_edge_query_dispatch_from_warm_query_finish
          rootRequest start initialPhysical fuel finishUsed handle request row continuation
          beforeFinish (by omega) finishActual owner
      have queryOrigin : Steps queryUsed (.code (.node rootRequest .pure)) start
          ((Control.code (.edge request .pure)).bind queryResume) queryBefore := by
        simpa only [Control.bind, Code.bind] using queryPrefix.steps
      obtain ⟨_checkedQuery, _queryPhysicalAgain, _queryExtension, queryGrowth, queryOperations,
          _queryOperationsGrowth, _queryBoundInputs, queryInputs, _queryBoundFields, queryFields⟩ :=
        SourceCurrentAllocatedNativePrefixOperations.prefix_operations_before_bind
          fuel queryUsed (.code (.node rootRequest .pure)) (.code (.edge request .pure)) queryResume
          start queryBefore sourceHeap initialPhysical inputs fields operationsValid sourceGrowth
          queryOrigin (by omega)
      have trueReturned :
          Returned (fun (_ : NodeRequest Symbol Guard) (_ : Node) => True) current.native.nodes ∧
          Returned (fun (_ : EdgeRequest Symbol Guard) (_ : EdgeValue Symbol Guard) => True)
            current.native.edges :=
        ⟨fun _ _ _ _ => True.intro, fun _ _ _ _ => True.intro⟩
      have observed := SourceCurrentAllocatedNativeCheckedEdgeBodyProfile.edge_body_children_profile_of_fuel_induction
        sourceHeap entry.identity request queryBefore beforeBody beforeFinish (fuel - queryUsed) bodyCount row
        (fun result => .finishEdge handle result (.pure result))
        queryPhysical queryGrowth queryOperations queryInputs queryFields isolatedDispatch (by omega) rawBody (by
          intro pair member childUsed childFuel childCount _positive _childSmaller _childFuelBound
            _childCountBound childSpan next first last value origin _childPhysical _childGrowth
            _childOperations _childInputs _childFields _leftAvailable _rightAvailable childActual
          let child : NodeRequest Symbol Guard := ⟨request.domain, pair.1, pair.2⟩
          let lifted : Node → Code Symbol Guard Node := fun result => (next result).bind queryResume
          have appended := origin.bind _ _ _ _ _ queryResume
          change Steps childUsed (.code (.edge request queryResume)) queryBefore
            (.code (((requestNode request.domain pair.1 pair.2).bind next).bind queryResume)) first at appended
          have tail : Steps childUsed (.code (.edge request queryResume)) queryBefore
              (.code ((requestNode request.domain pair.1 pair.2).bind lifted)) first := by
            simpa only [Code.bind_assoc, lifted] using appended
          have outer : Steps (queryUsed + childUsed) (.code (.node rootRequest .pure)) start
              (.code ((requestNode request.domain pair.1 pair.2).bind lifted)) first :=
            queryPrefix.steps.trans _ _ _ _ _ _ _ _ tail
          have outerBound : queryUsed + childUsed ≤ wholeCount := by omega
          have childOrigin : Steps (queryUsed + childUsed) (.code (.node rootRequest .pure)) start
              ((Control.code (.node child .pure)).bind lifted) first := by
            simpa only [Control.bind, Code.bind, requestNode, child] using outer
          have checkedChild := SourceCurrentAllocatedNativePrefixOperations.prefix_operations_before_bind
            fuel (queryUsed + childUsed) (.code (.node rootRequest .pure)) (.code (.node child .pure))
            lifted start first sourceHeap initialPhysical inputs fields operationsValid sourceGrowth
            childOrigin (by omega)
          have childPrefix : Trace (queryUsed + childUsed) (.code (.node rootRequest .pure)) start
              (.code (.node child lifted)) first := by
            simpa only [Control.bind, Code.bind] using checkedChild.1
          obtain ⟨selectedBodyId, selectedBodyIdentity, admitted⟩ :=
            SourceSynthesisCurrentUniverseNativeAllocation.original_universe_warm_node_query_prefix_full_admission
              lib query signed whole accepted rootValue sourceHeap built key entry body depth ordinary stored
              rootRequest start initialPhysical sourceGrowth inventory rootDomain
              leftAvailable rightAvailable leftClosed rightClosed
              fuel wholeCount (queryUsed + childUsed) wholeBound inputs fields
              child lifted first outerBound childPrefix
          have qualified : Qualified (width := width) rootRequest start wholeCount entry body depth ordinary child := by
            rcases admitted with qualified | auxiliary
            · exact qualified
            · have bodyIdSame : selectedBodyId = bodyEntry.identity :=
                Option.some.inj (selectedBodyIdentity.symm.trans actualBodyIdentity)
              subst selectedBodyId
              obtain ⟨pattern, patternId, domain, authentic, alternatives⟩ := auxiliary
              dsimp only at alternatives
              have keys :
                  child.domain.key = extend domain.key [entry.identity] (SourceRecursiveIntersectionControl.pair bodyEntry.identity entry.identity) ∨
                  child.domain.key = extend (extend domain.key [entry.identity] (SourceRecursiveIntersectionControl.pair bodyEntry.identity entry.identity))
                    [entry.identity] (SourceRecursiveIntersectionControl.pair entry.identity entry.identity) ∨
                  child.domain.key = extend domain.key [entry.identity] (SourceRecursiveIntersectionControl.pair entry.identity entry.identity) ∨
                  child.domain.key = extend (extend domain.key [entry.identity] (SourceRecursiveIntersectionControl.pair entry.identity entry.identity))
                    [entry.identity] (SourceRecursiveIntersectionControl.pair bodyEntry.identity entry.identity) := by
                rcases alternatives with ⟨same, _⟩ | ⟨same, _, _⟩ | ⟨same, _⟩ | ⟨same, _⟩
                · exact Or.inl same
                · exact Or.inr (Or.inl same)
                · exact Or.inr (Or.inr (Or.inl same))
                · exact Or.inr (Or.inr (Or.inr same))
              have different := SourceSynthesisCurrentUniverseNativeAllocation.actual_auxiliary_domain_ne_singleton_base
                rootRequest start initialPhysical wholeCount entry body depth ordinary
                bodyEntry (canonicalEdges (arrow :: rows)) bodyShape pattern patternId domain authentic
                child.domain keys (SourceRecursiveIntersectionControl.pair entry.identity targetPatternId)
              exact (different singletonKey).elim
          obtain ⟨childKey, keyed⟩ := third_edge_qualified_key rootRequest start wholeCount
            entry body depth ordinary bodyCodec child qualified
          have receipt := SourceCurrentAllocatedNativeSamePrefixKeyedChildResult.keyed_child_law_at_actual_warm_reader
            (fun (_ : NodeRequest Symbol Guard) (_ : Node) => True)
            (fun (_ : EdgeRequest Symbol Guard) (_ : EdgeValue Symbol Guard) => True)
            rootRequest start initialPhysical fuel used (queryUsed + childUsed) childCount
            currentControl current (by omega) actual trueReturned child childKey keyed
            lifted first last value (by omega) outer childActual
          obtain ⟨childHandle, _childAtReturn, childAtCurrent, _actualChildSuffix, _childRetention⟩ := receipt.2
          exact (nodeSeeds.2 used currentControl current within actual)
            childHandle child value childAtCurrent targetPatternId singletonKey)
      exact observed.1
  exact ⟨atPrefix wholeCount rest reader (Nat.le_refl _) wholeActual, atPrefix⟩

end MicroCFTA.SourceCurrentNativeNumericalSingletonEdgeProfiles
