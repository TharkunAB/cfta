import MicroCFTA.SourceCurrentNativeNumericalCMHistory
import MicroCFTA.SourceSynthesisCurrentUniverseWarmNoNewMu
import MicroCFTA.SourceCurrentNativeNumericalSingletonProfiles
import MicroCFTA.SourceCurrentNativeNumericalSingletonEdgeProfiles
import MicroCFTA.SourceCurrentNativeTerminalReturnedLaws

namespace MicroCFTA.SourceCurrentNativeNumericalSeedInvariant
open Cache InternedConstructorTemplates InternedProbeProvenance
open InternedBinderProtocol (NodeKey)
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceRecursiveIntersectionControl SourceRecursiveIntersectionDomain
open SourceEqualityNativeDemand
open SourceCurrentAllocatedNativeContextCache (Returned)
open SourceCurrentAllocatedNativeGeneralCMHistory (ClosedQualified)
open SourceCurrentAllocatedNativeClosedResetProfile (Profile)
open SourceCurrentAllocatedNativePhysicalTraceCompletion (Trace)
open SourceCurrentAllocatedNativePhysicalExecution (InputsThrough)
open SourceEqualityNativeDemandOperations (FieldsThrough)
open SourceSynthesisTypeSyntax (Library Query)
open SourceSynthesisFirstOrderConstruction (Expression)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Physical" => SourceCurrentAllocatedNativePhysicalCache.Valid
local notation "ordinarySymbols" => SourceSynthesisUniverseCallerBoundary.ordinarySymbols
set_option autoImplicit false

/- Note [One-query numerical seed closure]
Past Seeds is an internal smaller-query hypothesis.
Actual prefix laws supply every cache field at that same prefix.
A terminal step can change publication or demand status before it stops.
The terminal Returned bridge covers that last original step.
The source NoNewMu theorem covers every execute outcome at the original fuel.
This module adds no runtime query evaluator or history representation.
-/

private theorem execute_returned_of_actual_prefixes
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {width : Nat} {Output : Type}
    (nodeLaw : NodeRequest Symbol Guard → Value Symbol Guard → Prop)
    (edgeLaw : EdgeRequest Symbol Guard → EdgeValue Symbol Guard → Prop)
    (fuel : Nat) (control : Control Output) (before : Checked width)
    (inputs : InputsThrough fuel control before)
    (prefixes : ∀ (count : Nat) (rest : Control Output) (after : Checked width),
      count ≤ fuel → Trace count control before rest after →
      Returned nodeLaw after.native.nodes ∧ Returned edgeLaw after.native.edges) :
    Returned nodeLaw (SourceEqualityNativeDemand.execute fuel control before).state.native.nodes ∧
      Returned edgeLaw (SourceEqualityNativeDemand.execute fuel control before).state.native.edges := by
  induction fuel generalizing control before with
  | zero =>
      exact prefixes 0 control before (Nat.le_refl _) (.refl _ _)
  | succ fuel ih =>
      cases one : SourceEqualityNativeDemand.step control before with
      | yielded next after =>
          have nextInputs : InputsThrough fuel next after := by
            simpa only [one] using inputs.2
          have nextPrefixes : ∀ (count : Nat) (rest : Control Output) (current : Checked width),
              count ≤ fuel → Trace count next after rest current →
              Returned nodeLaw current.native.nodes ∧ Returned edgeLaw current.native.edges := by
            intro count rest current bounded actual
            exact prefixes (count + 1) rest current (by omega)
              (.cons control before next after rest current count inputs.1 one actual)
          simpa only [SourceEqualityNativeDemand.execute, one] using
            ih next after nextInputs nextPrefixes
      | done | failed | constraintError | blocked =>
          have current := prefixes 0 control before (by omega) (.refl _ _)
          have terminal : ∀ (next : Control Output) (after : Checked width),
              SourceEqualityNativeDemand.step control before ≠ .yielded next after := by
            intro next after observed
            rw [one] at observed
            cases observed
          have kept := SourceCurrentNativeTerminalReturnedLaws.terminal_step_preserves_returned
            nodeLaw edgeLaw control before current.1 current.2 terminal
          simpa only [SourceEqualityNativeDemand.execute, one, Outcome.state] using kept

private theorem seeds_preserved_at_every_actual_query_endpoint
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat}
    (lib : Library) (query : Query) (signed : Int) (whole : Expression)
    (accepted : SourceSynthesisCurrentConstruction.firstOrderRaw lib query signed = .ok whole)
    (rootValue : Value Symbol Guard) (sourceHeap : InternedConstructorTemplates.State Symbol Guard)
    (built : InternedFreshOrdinaryConstruction.build (ordinarySymbols whole) [] empty =
      .done rootValue sourceHeap)
    (key : NodeKey) (entry : Interned NodeKey) (body depth ordinary : Value Symbol Guard)
    (stored : sourceHeap.nodeRecords key = some (.mu entry body depth ordinary))
    (bodyId : Nat) (bodyIdentity : identity body = some bodyId)
    (rootRequest : NodeRequest Symbol Guard) (before : Checked width)
    (initialPhysical : Physical before.native)
    (sourceGrowth : Grows sourceHeap before.native.machine.heap)
    (operationsValid : SourceEqualityConstraintMemoAllocation.Valid before.operations)
    (pastSeeds : Seeds sourceHeap entry body depth ordinary bodyId before)
    (rootDomain : rootRequest.domain = IntersectionEmptyDomain.emptyDomain)
    (rootAvailable : Available before.native.machine.heap rootRequest.left ∧
      Available before.native.machine.heap rootRequest.right)
    (rootClosed : rootRequest.left.free = [] ∧ rootRequest.right.free = [])
    (fuel : Nat)
    (inputs : InputsThrough fuel (.code (.node rootRequest .pure)) before)
    (fields : FieldsThrough fuel (.code (.node rootRequest .pure)) before) :
    Seeds sourceHeap entry body depth ordinary bodyId
      (SourceEqualityNativeDemand.execute fuel (.code (.node rootRequest .pure)) before).state ∧
    ∀ (count : Nat) (rest : Control (Value Symbol Guard)) (after : Checked width),
      count ≤ fuel → Trace count (.code (.node rootRequest .pure)) before rest after →
      Seeds sourceHeap entry body depth ordinary bodyId after := by
  have inventory := SourceSynthesisCurrentUniverseNativeAllocation.original_universe_retained_query_no_new_mu_of_past_seeds
    lib query signed whole accepted rootValue sourceHeap built key entry body depth ordinary stored
    bodyId bodyIdentity rootRequest before initialPhysical sourceGrowth operationsValid pastSeeds
    rootDomain rootAvailable rootClosed fuel inputs fields
  have prefixSeeds : ∀ (count : Nat) (rest : Control (Value Symbol Guard)) (after : Checked width),
      count ≤ fuel → Trace count (.code (.node rootRequest .pure)) before rest after →
      Seeds sourceHeap entry body depth ordinary bodyId after := by
    intro count rest after bounded actual
    have gamma := SourceCurrentNativeNumericalCMHistory.returned_at_every_actual_prefix_of_past_seeds
      lib query signed whole accepted rootValue sourceHeap built key entry body depth ordinary stored
      bodyId bodyIdentity rootRequest before initialPhysical sourceGrowth operationsValid
      fuel count rest after bounded inputs fields actual pastSeeds
    have singletonNodes :=
      SourceCurrentNativeNumericalSingletonProfiles.singleton_nodes_at_every_actual_prefix_of_past_seeds
        lib query signed whole accepted rootValue sourceHeap built key entry body depth ordinary stored
        bodyId bodyIdentity rootRequest before initialPhysical sourceGrowth operationsValid pastSeeds
        rootDomain rootAvailable.1 rootAvailable.2 rootClosed.1 rootClosed.2
        fuel count rest after bounded inputs fields actual
    have singletonEdges :=
      SourceCurrentNativeNumericalSingletonEdgeProfiles.singleton_edges_at_every_actual_prefix_of_past_seeds
        lib query signed whole accepted rootValue sourceHeap built key entry body depth ordinary stored
        bodyId bodyIdentity rootRequest before initialPhysical sourceGrowth operationsValid pastSeeds
        rootDomain rootAvailable.1 rootAvailable.2 rootClosed.1 rootClosed.2
        fuel count rest after bounded inputs fields actual
    refine ⟨InternedShallowHeap.noNewMu_trans pastSeeds.1 (inventory.2 count rest after bounded actual),
      ?_, ?_, singletonNodes.1, singletonEdges.1, ?_⟩
    · intro handle request value found closed
      exact (gamma.1.1 handle request value found).1 closed
    · intro handle request row found childrenClosed
      apply gamma.1.2 handle request row found
      intro pair member
      exact Or.inl (childrenClosed pair member)
    · exact SourceCurrentNativeNumericalCMHistory.numerical_auxiliary_payloads_at_actual_prefix_of_past_seeds
        lib query signed whole accepted rootValue sourceHeap built key entry body depth ordinary stored
        bodyId bodyIdentity rootRequest before initialPhysical sourceGrowth operationsValid
        fuel count rest after bounded inputs fields actual pastSeeds
  have closedAtEnd := execute_returned_of_actual_prefixes
    (fun (request : NodeRequest Symbol Guard) (value : Value Symbol Guard) =>
      ClosedQualified entry.identity request → Profile entry.identity value)
    (fun (request : EdgeRequest Symbol Guard) (row : EdgeValue Symbol Guard) =>
      (∀ pair ∈ request.left.children.zip request.right.children,
        ClosedQualified entry.identity ⟨request.domain, pair.1, pair.2⟩) →
      ∀ child ∈ row.children, Profile entry.identity child)
    fuel (.code (.node rootRequest .pure)) before inputs
    (by
      intro count rest after bounded actual
      have kept := prefixSeeds count rest after bounded actual
      exact ⟨kept.2.1, kept.2.2.1⟩)
  have singletonAtEnd := execute_returned_of_actual_prefixes
    (fun (request : NodeRequest Symbol Guard) (value : Value Symbol Guard) =>
      ∀ patternId : Nat, request.domain.key =
        extend IntersectionEmptyDomain.emptyKey [entry.identity] (pair entry.identity patternId) →
      Profile entry.identity value)
    (fun (request : EdgeRequest Symbol Guard) (row : EdgeValue Symbol Guard) =>
      ∀ patternId : Nat, request.domain.key =
        extend IntersectionEmptyDomain.emptyKey [entry.identity] (pair entry.identity patternId) →
      ∀ child ∈ row.children, Profile entry.identity child)
    fuel (.code (.node rootRequest .pure)) before inputs
    (by
      intro count rest after bounded actual
      have kept := prefixSeeds count rest after bounded actual
      exact ⟨kept.2.2.2.1, kept.2.2.2.2.1⟩)
  refine ⟨?_, prefixSeeds⟩
  refine ⟨InternedShallowHeap.noNewMu_trans pastSeeds.1 inventory.1,
    closedAtEnd.1, closedAtEnd.2, singletonAtEnd.1, singletonAtEnd.2, ?_⟩
  intro patternId apartUniverse apartBody
  let universeValue : Value Symbol Guard := .mu entry body depth ordinary
  let domain := extend IntersectionEmptyDomain.emptyKey [entry.identity] (pair entry.identity patternId)
  let bodyFirst := extend domain [entry.identity] (pair bodyId entry.identity)
  let diagonalFirst := extend domain [entry.identity] (pair entry.identity entry.identity)
  let diagonalTerminal := extend diagonalFirst [entry.identity] (pair bodyId entry.identity)
  have bodyFirstAtEnd := execute_returned_of_actual_prefixes
    (SourceCurrentAllocatedNativeBodyFirstKeyQueryGlobalLaws.NodeResult
      entry.identity bodyId bodyFirst body universeValue)
    (SourceCurrentAllocatedNativeBodyFirstKeyQueryGlobalLaws.EdgeResult
      entry.identity bodyId bodyFirst universeValue)
    fuel (.code (.node rootRequest .pure)) before inputs
    (by
      intro count rest after bounded actual
      have kept := (prefixSeeds count rest after bounded actual).2.2.2.2.2
        patternId apartUniverse apartBody
      exact ⟨kept.1, kept.2.1⟩)
  have coherentAtEnd := execute_returned_of_actual_prefixes
    (SourceCurrentAllocatedNativeCoherentOpenBodyQueryGlobalLaws.NodeResult
      entry.identity entry.identity entry.identity diagonalTerminal diagonalFirst body universeValue)
    SourceCurrentAllocatedNativeTopRowQueryGlobalLaws.EdgeResult
    fuel (.code (.node rootRequest .pure)) before inputs
    (by
      intro count rest after bounded actual
      have kept := (prefixSeeds count rest after bounded actual).2.2.2.2.2
        patternId apartUniverse apartBody
      exact ⟨kept.2.2.1, kept.2.2.2⟩)
  exact ⟨bodyFirstAtEnd.1, bodyFirstAtEnd.2, coherentAtEnd.1, coherentAtEnd.2⟩

end MicroCFTA.SourceCurrentNativeNumericalSeedInvariant
