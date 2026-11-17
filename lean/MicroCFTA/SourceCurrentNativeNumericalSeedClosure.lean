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

namespace MicroCFTA.SourceCurrentNativeNumericalSeedInvariant
open Cache InternedConstructorTemplates InternedProbeProvenance
open InternedBinderProtocol (NodeKey)
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceRecursiveIntersectionControl SourceRecursiveIntersectionDomain
open SourceEqualityNativeDemand
open SourceCurrentAllocatedNativeContextCache (Returned)
open SourceCurrentAllocatedNativePhysicalTraceCompletion (Trace)
open SourceCurrentAllocatedNativePhysicalExecution (Inputs InputsThrough)
open SourceEqualityNativeDemandOperations (FieldsThrough)
open SourceSynthesisTypeSyntax (Library Query)
open SourceSynthesisFirstOrderConstruction (Expression)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Physical" => SourceCurrentAllocatedNativePhysicalCache.Valid
local notation "ordinarySymbols" => SourceSynthesisUniverseCallerBoundary.ordinarySymbols
set_option autoImplicit false

/- Note [Seeds along the actual query sequence]
The two native memo tables are empty only at the initial state.
Each next state is the literal previous query outcome state.
The query-count induction derives Seeds before each query.
The one-query closure supplies its endpoint and every bounded prefix.
Physical and operation effects retain the premises for the next query.
No query is restarted with empty tables or a larger fuel.
-/

private theorem query_sequence_execute_physical_extension
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {width : Nat} {Output : Type}
    (fuel : Nat) (control : Control Output) (before : Checked width)
    (physical : Physical before.native)
    (inputs : InputsThrough fuel control before) :
    Physical (SourceEqualityNativeDemand.execute fuel control before).state.native ∧
      Extension before.native.machine
        (SourceEqualityNativeDemand.execute fuel control before).state.native.machine := by
  induction fuel generalizing control before with
  | zero => exact ⟨physical, .refl _⟩
  | succ fuel ih =>
      have physicalStep := SourceCurrentAllocatedNativePhysicalExecution.step_valid
        control before physical inputs.1
      have extensionStep := SourceCurrentAllocatedNativePhysicalExecution.step_extension
        control before physical.machine inputs.1
      cases observed : SourceEqualityNativeDemand.step control before with
      | yielded next after =>
          have afterPhysical : Physical after.native := by
            simpa only [observed, Outcome.state] using physicalStep
          have afterExtension : Extension before.native.machine after.native.machine := by
            simpa only [observed, Outcome.state] using extensionStep
          have afterInputs : InputsThrough fuel next after := by
            simpa only [InputsThrough, observed] using inputs.2
          have later := ih next after afterPhysical afterInputs
          simpa only [SourceEqualityNativeDemand.execute, observed] using
            And.intro later.1 (afterExtension.trans later.2)
      | done | failed | constraintError | blocked =>
          simpa only [SourceEqualityNativeDemand.execute, observed, Outcome.state] using
            And.intro physicalStep extensionStep

theorem original_universe_actual_query_sequence_seeds
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat}
    (lib : Library) (query : Query) (signed : Int) (whole : Expression)
    (accepted : SourceSynthesisCurrentConstruction.firstOrderRaw lib query signed = .ok whole)
    (rootValue : Value Symbol Guard) (sourceHeap : InternedConstructorTemplates.State Symbol Guard)
    (built : InternedFreshOrdinaryConstruction.build (ordinarySymbols whole) [] empty =
      .done rootValue sourceHeap)
    (key : NodeKey) (entry : Interned NodeKey) (body depth ordinary : Value Symbol Guard)
    (stored : sourceHeap.nodeRecords key = some (.mu entry body depth ordinary))
    (bodyId : Nat) (bodyIdentity : identity body = some bodyId)
    (machine : Machine Symbol Guard)
    (machineValid : SourceRecursiveIntersectionKernel.Valid machine)
    (sourceGrowth : Grows sourceHeap machine.heap)
    (pastInventory : InternedShallowHeap.NoNewMu sourceHeap machine.heap)
    (operations : SourceEqualityConstraintMemoAllocation.State)
    (operationsValid : SourceEqualityConstraintMemoAllocation.Valid operations)
    (queryCount : Nat)
    (roots : Nat → NodeRequest Symbol Guard) (queryFuel : Nat → Nat)
    (states : Nat → Checked width)
    (initialState : states 0 = ⟨initial width machine, operations⟩)
    (actual : ∀ index : Nat, index < queryCount →
      states (index + 1) =
        (SourceEqualityNativeDemand.execute (queryFuel index)
          (.code (.node (roots index) .pure)) (states index)).state)
    (rootDomains : ∀ index : Nat, index < queryCount →
      (roots index).domain = IntersectionEmptyDomain.emptyDomain)
    (rootClosed : ∀ index : Nat, index < queryCount →
      (roots index).left.free = [] ∧ (roots index).right.free = [])
    (inputs : ∀ index : Nat, index < queryCount →
      InputsThrough (queryFuel index) (.code (.node (roots index) .pure)) (states index))
    (fields : ∀ index : Nat, index < queryCount →
      FieldsThrough (queryFuel index) (.code (.node (roots index) .pure)) (states index)) :
    (∀ index : Nat, index ≤ queryCount →
      Physical (states index).native ∧
      Grows sourceHeap (states index).native.machine.heap ∧
      SourceEqualityConstraintMemoAllocation.Valid (states index).operations ∧
      Seeds sourceHeap entry body depth ordinary bodyId (states index)) ∧
    ∀ index : Nat, index < queryCount →
      ∀ (used : Nat) (rest : Control (Value Symbol Guard)) (after : Checked width),
        used ≤ queryFuel index →
        Trace used (.code (.node (roots index) .pure)) (states index) rest after →
        Seeds sourceHeap entry body depth ordinary bodyId after := by
  have initialSeeds : Seeds sourceHeap entry body depth ordinary bodyId
      (⟨initial width machine, operations⟩ : Checked width) := by
    refine ⟨pastInventory, ?_, ?_, ?_, ?_, ?_⟩
    · exact SourceCurrentAllocatedNativeContextCache.returned_empty _
    · exact SourceCurrentAllocatedNativeContextCache.returned_empty _
    · exact SourceCurrentAllocatedNativeContextCache.returned_empty _
    · exact SourceCurrentAllocatedNativeContextCache.returned_empty _
    · intro patternId _apartUniverse _apartBody
      exact ⟨SourceCurrentAllocatedNativeContextCache.returned_empty _,
        SourceCurrentAllocatedNativeContextCache.returned_empty _,
        SourceCurrentAllocatedNativeContextCache.returned_empty _,
        SourceCurrentAllocatedNativeContextCache.returned_empty _⟩
  have rootAvailable (index : Nat) (bounded : index < queryCount) :
      Available (states index).native.machine.heap (roots index).left ∧
      Available (states index).native.machine.heap (roots index).right := by
    have plan := inputs index bounded
    have head : Inputs (.code (.node (roots index) .pure)) (states index) := by
      cases observedFuel : queryFuel index with
      | zero => simpa only [observedFuel, InputsThrough] using plan
      | succ fuel =>
          have selected : InputsThrough (fuel + 1)
              (.code (.node (roots index) .pure)) (states index) := by
            simpa only [observedFuel] using plan
          exact selected.1
    exact head.1.2
  have endpoint : ∀ index : Nat, index ≤ queryCount →
      Physical (states index).native ∧
      Grows sourceHeap (states index).native.machine.heap ∧
      SourceEqualityConstraintMemoAllocation.Valid (states index).operations ∧
      Seeds sourceHeap entry body depth ordinary bodyId (states index) := by
    intro index
    induction index with
    | zero =>
        intro _bounded
        rw [initialState]
        exact ⟨SourceCurrentAllocatedNativePhysicalCache.initial_valid machine machineValid,
          sourceGrowth, operationsValid, initialSeeds⟩
    | succ index ih =>
        intro bounded
        have within : index < queryCount := by omega
        have previous := ih (by omega)
        have closed := seeds_preserved_at_every_actual_query_endpoint
          lib query signed whole accepted rootValue sourceHeap built key entry body depth ordinary stored
          bodyId bodyIdentity (roots index) (states index) previous.1 previous.2.1 previous.2.2.1
          previous.2.2.2 (rootDomains index within) (rootAvailable index within)
          (rootClosed index within) (queryFuel index) (inputs index within) (fields index within)
        have physical := query_sequence_execute_physical_extension
          (queryFuel index) (.code (.node (roots index) .pure)) (states index)
          previous.1 (inputs index within)
        have operations := SourceEqualityNativeDemandOperations.execute_operations
          (queryFuel index) (.code (.node (roots index) .pure)) (states index)
          previous.2.2.1 (fields index within)
        have next :
            Physical (SourceEqualityNativeDemand.execute (queryFuel index)
              (.code (.node (roots index) .pure)) (states index)).state.native ∧
            Grows sourceHeap (SourceEqualityNativeDemand.execute (queryFuel index)
              (.code (.node (roots index) .pure)) (states index)).state.native.machine.heap ∧
            SourceEqualityConstraintMemoAllocation.Valid
              (SourceEqualityNativeDemand.execute (queryFuel index)
                (.code (.node (roots index) .pure)) (states index)).state.operations ∧
            Seeds sourceHeap entry body depth ordinary bodyId
              (SourceEqualityNativeDemand.execute (queryFuel index)
                (.code (.node (roots index) .pure)) (states index)).state :=
          ⟨physical.1, grows_trans previous.2.1 physical.2.heap, operations.1, closed.1⟩
        simpa only [Nat.succ_eq_add_one, actual index within] using next
  refine ⟨endpoint, ?_⟩
  intro index within used rest after bounded actualPrefix
  have previous := endpoint index (by omega)
  exact (seeds_preserved_at_every_actual_query_endpoint
    lib query signed whole accepted rootValue sourceHeap built key entry body depth ordinary stored
    bodyId bodyIdentity (roots index) (states index) previous.1 previous.2.1 previous.2.2.1
    previous.2.2.2 (rootDomains index within) (rootAvailable index within)
    (rootClosed index within) (queryFuel index) (inputs index within) (fields index within)).2
      used rest after bounded actualPrefix

end MicroCFTA.SourceCurrentNativeNumericalSeedInvariant
