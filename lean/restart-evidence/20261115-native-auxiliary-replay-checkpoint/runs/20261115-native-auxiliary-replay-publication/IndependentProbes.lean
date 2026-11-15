import MicroCFTA.SourceCurrentAllocatedNativeRawMuCutoffReplay
import MicroCFTA.SourceCurrentAllocatedNativeSourceBodyFirstActualMuCutoff
import MicroCFTA.SourceCurrentAllocatedNativeMuCutoffQueryGlobalLaws

#check @MicroCFTA.SourceCurrentAllocatedNativeRawMuCutoffReplay.left_mu_cutoff_trace_result
#print axioms MicroCFTA.SourceCurrentAllocatedNativeRawMuCutoffReplay.left_mu_cutoff_trace_result
#check @MicroCFTA.SourceCurrentAllocatedNativeSourceBodyFirstActualMuCutoff.current_stored_universe_body_first_actual_mu_cutoff
#print axioms MicroCFTA.SourceCurrentAllocatedNativeSourceBodyFirstActualMuCutoff.current_stored_universe_body_first_actual_mu_cutoff
#check @MicroCFTA.SourceCurrentAllocatedNativeMuCutoffQueryGlobalLaws.query_returned_and_raw_results
#print axioms MicroCFTA.SourceCurrentAllocatedNativeMuCutoffQueryGlobalLaws.query_returned_and_raw_results
#check @MicroCFTA.SourceCurrentAllocatedNativeMuCutoffQueryGlobalLaws.initial_node_query_returned_and_raw_results
#print axioms MicroCFTA.SourceCurrentAllocatedNativeMuCutoffQueryGlobalLaws.initial_node_query_returned_and_raw_results
#check @MicroCFTA.SourceCurrentAllocatedNativeMuCutoffQueryGlobalLaws.initial_edge_query_returned_and_raw_results
#print axioms MicroCFTA.SourceCurrentAllocatedNativeMuCutoffQueryGlobalLaws.initial_edge_query_returned_and_raw_results

namespace MicroCFTA.SourceCurrentAllocatedNativeBodyFirstMuIntegrationProbe
open Cache InternedConstructorTemplates InternedNestedFacts InternedProbeProvenance
open InternedBinderProtocol (NodeKey Reference)
open SourceRecursiveIntersectionControl SourceRecursiveIntersectionDomain
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceSynthesisTypeSyntax (Library Query)
open SourceSynthesisFirstOrderConstruction (Expression)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "ordinarySymbols" => SourceSynthesisUniverseCallerBoundary.ordinarySymbols

open SourceEqualityNativeDemand
open SourceCurrentAllocatedNativeContextCache (Returned)
open SourceCurrentAllocatedNativePhysicalExecution (InputsThrough)
open SourceEqualityNativeDemandOperations (FieldsThrough)
open SourceCurrentAllocatedNativeMuCutoffQueryGlobalLaws (NodeResult)
open SourceCurrentAllocatedNativeTopRowQueryGlobalLaws (EdgeResult)
set_option autoImplicit false

example
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat}
    (lib : Library) (query : Query) (signed : Int) (whole : Expression)
    (accepted : SourceSynthesisCurrentConstruction.firstOrderRaw lib query signed = .ok whole)
    (rootValue : Value Symbol Guard) (sourceHeap : InternedConstructorTemplates.State Symbol Guard)
    (built : InternedFreshOrdinaryConstruction.build (ordinarySymbols whole) [] empty =
      .done rootValue sourceHeap)
    (key : NodeKey) (entry : Interned NodeKey) (body depth ordinary : Value Symbol Guard)
    (stored : sourceHeap.nodeRecords key = some (.mu entry body depth ordinary))
    (machine : SourceRecursiveIntersectionKernel.Machine Symbol Guard)
    (machineValid : SourceRecursiveIntersectionKernel.Valid machine)
    (facts : Facts machine.heap) (growth : Grows sourceHeap machine.heap)
    (domains : Cache.State IntersectionFlatMemoKeyDomain.DomainKey) (cacheValid : Cache.Valid domains)
    (pattern : Value Symbol Guard) (_patternAvailable : Available machine.heap pattern)
    (_patternClosed : pattern.free = []) (patternId : Nat)
    (_patternIdentity : identity pattern = some patternId)
    (_patternKind : tag pattern = 1 ∨ tag pattern = 3) :
    ∃ (bodyEntry : Interned NodeKey) (bodyRows : List (EdgeValue Symbol Guard)),
      body = .node bodyEntry bodyRows 0 [.interned entry.identity] ∧
      let universeValue : Value Symbol Guard := .mu entry body depth ordinary
      let referenceValue : Value Symbol Guard := .reference (.interned entry.identity)
      let original := SourceRecursiveIntersectionEnvironment.enter domains IntersectionEmptyDomain.emptyKey
        universeValue pattern entry.identity patternId
      let bodyFirst := SourceRecursiveIntersectionEnvironment.enter original.2 original.1.key
        body universeValue bodyEntry.identity entry.identity
      let target : NodeRequest Symbol Guard := ⟨bodyFirst.1, universeValue, referenceValue⟩
      let cutoff : Value Symbol Guard := repeatedValue (pair bodyEntry.identity entry.identity)
      ∀ (operations : SourceEqualityConstraintMemoAllocation.State)
        (_operationsValid : SourceEqualityConstraintMemoAllocation.Valid operations) (fuel : Nat),
      let start : SourceEqualityNativeDemand.State width :=
        ⟨SourceRecursiveIntersectionThunks.initial width machine, operations⟩
      InputsThrough fuel (.code (.node target .pure)) start →
      FieldsThrough fuel (.code (.node target .pure)) start →
      Returned (NodeResult target cutoff) (execute fuel (.code (.node target .pure)) start).state.native.nodes ∧
      Returned EdgeResult (execute fuel (.code (.node target .pure)) start).state.native.edges ∧
      ∀ (count : Nat) (result : Value Symbol Guard) (after : SourceEqualityNativeDemand.State width),
        count ≤ fuel → Steps count (.code (.node target .pure)) start (.code (.pure result)) after →
        result = cutoff := by
  obtain ⟨bodyEntry, bodyRows, bodyShape, _bodyApart, sourceFacts⟩ :=
    SourceCurrentAllocatedNativeSourceBodyFirstActualMuCutoff.current_stored_universe_body_first_actual_mu_cutoff
      (width := width) lib query signed whole accepted rootValue sourceHeap built key entry body depth ordinary
      stored machine.heap facts growth domains cacheValid pattern _patternAvailable _patternClosed
      patternId _patternIdentity _patternKind
  let universeValue : Value Symbol Guard := .mu entry body depth ordinary
  let referenceValue : Value Symbol Guard := .reference (.interned entry.identity)
  let original := SourceRecursiveIntersectionEnvironment.enter domains IntersectionEmptyDomain.emptyKey
    universeValue pattern entry.identity patternId
  let bodyFirst := SourceRecursiveIntersectionEnvironment.enter original.2 original.1.key
    body universeValue bodyEntry.identity entry.identity
  let target : NodeRequest Symbol Guard := ⟨bodyFirst.1, universeValue, referenceValue⟩
  let cutoff : Value Symbol Guard := repeatedValue (pair bodyEntry.identity entry.identity)
  have selected : decision target.domain.key target.left target.right = .leftMu := sourceFacts.1
  have leftIdentity : identity target.left = some entry.identity := rfl
  have rightIdentity : identity target.right = some entry.identity := rfl
  have childPure : ∀ current : Cache.State IntersectionFlatMemoKeyDomain.DomainKey, Cache.Valid current →
      compileNode ⟨(SourceRecursiveIntersectionEnvironment.enter current target.domain.key
        target.left target.right entry.identity entry.identity).1,
        SourceRecursiveIntersectionKernel.body target.left,
        SourceRecursiveIntersectionKernel.body target.right⟩ = .pure cutoff := by
    intro current valid
    exact (sourceFacts.2.2.2.1 current valid).2.2
  have absent : let binder := pair entry.identity entry.identity
      Reference.intersection binder.1 binder.2 ∉ cutoff.free := sourceFacts.2.2.1
  refine ⟨bodyEntry, bodyRows, bodyShape, ?_⟩
  dsimp only
  intro operations operationsValid fuel plan fields
  have completed := SourceCurrentAllocatedNativeMuCutoffQueryGlobalLaws.initial_node_query_returned_and_raw_results
    target cutoff entry.identity entry.identity selected leftIdentity rightIdentity childPure absent
    sourceHeap machine machineValid growth operations operationsValid fuel target plan fields
  refine ⟨completed.1.1, completed.1.2, ?_⟩
  intro count result after bounded actual
  exact (completed.2 count result after bounded actual).2 rfl

end MicroCFTA.SourceCurrentAllocatedNativeBodyFirstMuIntegrationProbe
