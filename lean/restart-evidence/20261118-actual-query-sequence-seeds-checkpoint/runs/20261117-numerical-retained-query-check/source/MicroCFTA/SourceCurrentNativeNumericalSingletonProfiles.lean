import MicroCFTA.SourceCurrentNativeNumericalCMHistory
import MicroCFTA.SourceSynthesisCurrentUniverseThirdQueryNodeSeed

namespace MicroCFTA.SourceCurrentNativeNumericalSingletonProfiles
open Cache InternedConstructorTemplates InternedProbeProvenance
open InternedBinderProtocol (NodeKey)
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceRecursiveIntersectionControl (identity pair)
open SourceRecursiveIntersectionDomain (extend)
open SourceEqualityNativeDemand
open SourceCurrentNativeNumericalSeedInvariant (Seeds)
open SourceCurrentAllocatedNativeContextCache (Returned)
open SourceCurrentAllocatedNativePhysicalTraceCompletion (Trace)
open SourceCurrentAllocatedNativePhysicalExecution (InputsThrough)
open SourceEqualityNativeDemandOperations (FieldsThrough)
open SourceSynthesisTypeSyntax (Library Query)
open SourceSynthesisFirstOrderConstruction (Expression)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Physical" => SourceCurrentAllocatedNativePhysicalCache.Valid
local notation "Profile" => SourceCurrentAllocatedNativeClosedResetProfile.Profile
local notation "ordinarySymbols" => SourceSynthesisUniverseCallerBoundary.ordinarySymbols
set_option autoImplicit false

/- Note [Singleton node cells from their actual producers]
Inherited returned cells use the past query invariant.
Each new returned cell has one actual query prefix in this history.
Source call admission gives a qualified call or an auxiliary call.
The qualified call uses the derived prefix cache law.
An auxiliary domain cannot equal any singleton domain.
-/

theorem singleton_nodes_at_every_actual_prefix_of_past_seeds
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
    Returned (fun (request : NodeRequest Symbol Guard) (value : Value Symbol Guard) =>
      ∀ patternId : Nat, request.domain.key =
        extend IntersectionEmptyDomain.emptyKey [entry.identity] (pair entry.identity patternId) →
      Profile entry.identity value) reader.native.nodes ∧
    ∀ (used : Nat) (currentControl : Control (Value Symbol Guard)) (current : Checked width),
      used ≤ wholeCount →
      Trace used (.code (.node rootRequest .pure)) start currentControl current →
      Returned (fun (request : NodeRequest Symbol Guard) (value : Value Symbol Guard) =>
        ∀ patternId : Nat, request.domain.key =
          extend IntersectionEmptyDomain.emptyKey [entry.identity] (pair entry.identity patternId) →
        Profile entry.identity value) current.native.nodes := by
  have gamma := SourceCurrentNativeNumericalCMHistory.returned_at_every_actual_prefix_of_past_seeds
    lib query signed whole accepted rootValue sourceHeap built key entry body depth ordinary stored
    bodyId bodyIdentity rootRequest start initialPhysical sourceGrowth operationsValid
    fuel wholeCount rest reader wholeBound inputs fields wholeActual pastSeeds
  have inheritedFacts := pastSeeds
  dsimp only [Seeds] at inheritedFacts
  obtain ⟨inventory, _closedNodes, _closedEdges, inheritedNodes, _inheritedEdges, _auxiliary⟩ := inheritedFacts
  obtain ⟨bodyEntry, _marker, arrow, rows, bodyShape, _bodyAvailable, _markerShape,
      _arrowChildren, _arrowKey, _catalog, _markerClosed, _markerAvailable, _markerAtoms,
      _rowKinds, _arrowRetained⟩ :=
    SourceSynthesisCurrentUniverseBodyChildClassification.current_stored_universe_body_physical_children_after_growth
      lib query signed whole accepted rootValue sourceHeap built key entry body depth ordinary stored
      start.native.machine.heap initialPhysical.machine.1 sourceGrowth
  have actualBodyIdentity : identity body = some bodyEntry.identity := by
    rw [bodyShape]
    rfl
  have atPrefix (used : Nat) (currentControl : Control (Value Symbol Guard)) (current : Checked width)
      (within : used ≤ wholeCount)
      (actual : Trace used (.code (.node rootRequest .pure)) start currentControl current) :
      Returned (fun (request : NodeRequest Symbol Guard) (value : Value Symbol Guard) =>
        ∀ patternId : Nat, request.domain.key =
          extend IntersectionEmptyDomain.emptyKey [entry.identity] (pair entry.identity patternId) →
        Profile entry.identity value) current.native.nodes := by
    intro handle request value currentCell targetPatternId singletonKey
    rcases SourceCurrentAllocatedNativeNodeReturnOrigin.returned_node_cell_or_finish_prefix
        actual handle request value currentCell with inherited | produced
    · exact inheritedNodes handle request value inherited targetPatternId singletonKey
    · obtain ⟨finishUsed, _suffixCount, beforeFinish, continuation, total,
        finishActual, owner, _finishEvent, _finished, _suffix⟩ := produced
      obtain ⟨queryUsed, _bodyCount, queryBefore, _beforeBody, queryNext, queryTotal,
          _querySmall, _queryFuel, queryActual, _dispatch, _isolated, _queryPhysical,
          _ready, _safe, _bodyOwner, _bodyActual, _nextSame⟩ :=
        SourceCurrentAllocatedNativeNodeQueryDispatchOrigin.actual_node_query_dispatch_from_warm_query_finish
          rootRequest start initialPhysical fuel finishUsed handle request value continuation
          beforeFinish (by omega) finishActual owner
      obtain ⟨selectedBodyId, selectedBodyIdentity, admitted⟩ :=
        SourceSynthesisCurrentUniverseNativeAllocation.original_universe_warm_node_query_prefix_full_admission
          lib query signed whole accepted rootValue sourceHeap built key entry body depth ordinary stored
          rootRequest start initialPhysical sourceGrowth inventory rootDomain
          leftAvailable rightAvailable leftClosed rightClosed
          fuel wholeCount queryUsed wholeBound inputs fields request queryNext queryBefore (by omega) queryActual
      rcases admitted with qualified | auxiliary
      · have resultLaw := (gamma.2 used currentControl current within actual).1 handle request value currentCell
        rcases qualified with closed | mixed
        · exact resultLaw.1 closed
        · exact resultLaw.2 mixed
      · have bodyIdSame : selectedBodyId = bodyEntry.identity :=
          Option.some.inj (selectedBodyIdentity.symm.trans actualBodyIdentity)
        subst selectedBodyId
        obtain ⟨pattern, patternId, domain, authentic, alternatives⟩ := auxiliary
        dsimp only at alternatives
        have keys :
            request.domain.key = extend domain.key [entry.identity] (pair bodyEntry.identity entry.identity) ∨
            request.domain.key = extend (extend domain.key [entry.identity] (pair bodyEntry.identity entry.identity))
              [entry.identity] (pair entry.identity entry.identity) ∨
            request.domain.key = extend domain.key [entry.identity] (pair entry.identity entry.identity) ∨
            request.domain.key = extend (extend domain.key [entry.identity] (pair entry.identity entry.identity))
              [entry.identity] (pair bodyEntry.identity entry.identity) := by
          rcases alternatives with ⟨same, _⟩ | ⟨same, _, _⟩ | ⟨same, _⟩ | ⟨same, _⟩
          · exact Or.inl same
          · exact Or.inr (Or.inl same)
          · exact Or.inr (Or.inr (Or.inl same))
          · exact Or.inr (Or.inr (Or.inr same))
        have different :=
          SourceSynthesisCurrentUniverseNativeAllocation.actual_auxiliary_domain_ne_singleton_base
            rootRequest start initialPhysical wholeCount entry body depth ordinary
            bodyEntry (canonicalEdges (arrow :: rows)) bodyShape pattern patternId domain authentic
            request.domain keys (pair entry.identity targetPatternId)
        exact (different singletonKey).elim
  exact ⟨atPrefix wholeCount rest reader (Nat.le_refl _) wholeActual, atPrefix⟩

end MicroCFTA.SourceCurrentNativeNumericalSingletonProfiles

#print axioms MicroCFTA.SourceCurrentNativeNumericalSingletonProfiles.singleton_nodes_at_every_actual_prefix_of_past_seeds
