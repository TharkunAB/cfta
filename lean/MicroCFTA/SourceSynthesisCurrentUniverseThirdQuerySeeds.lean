import MicroCFTA.SourceSynthesisCurrentUniverseThirdQueryNodeSeed
import MicroCFTA.SourceSynthesisCurrentUniverseThirdQueryEdgeSeed
import MicroCFTA.SourceCurrentNativeWarmBodyFirstInitialPayloads
import MicroCFTA.SourceCurrentNativeWarmCoherentInitialPayloads
import MicroCFTA.SourceSynthesisCurrentUniverseWarmNoNewMu

namespace MicroCFTA.SourceSynthesisCurrentUniverseNativeAllocation
open Cache InternedConstructorTemplates InternedProbeProvenance
open InternedBinderProtocol (NodeKey)
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceEqualityNativeDemand
open SourceCurrentAllocatedNativeContextCache (Returned)
open SourceCurrentAllocatedNativePhysicalTraceCompletion (Trace)
open SourceCurrentAllocatedNativePhysicalExecution (Inputs InputsThrough)
open SourceEqualityNativeDemandOperations (FieldsThrough)
open SourceSynthesisTypeSyntax (Library Query)
open SourceSynthesisFirstOrderConstruction (Expression)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSynthesisGeneralizeSyntax.Guard
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Profile" => SourceCurrentAllocatedNativeClosedResetProfile.Profile
local notation "ordinarySymbols" => SourceSynthesisUniverseCallerBoundary.ordinarySymbols
set_option autoImplicit false

/- Note [One third-history seed bundle]
The two actual query prefixes retain separate controls and endpoints.
The original source determines one body identity for all four auxiliary laws.
The cold and warm inventory laws compose at their literal shared snapshot.
Each semantic component keeps the same full third history.
This theorem supplies cache seeds. It does not construct a finite model.
-/

theorem original_universe_two_prefix_cache_seeds_for_third_actual_history
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat}
    (lib : Library) (query : Query) (signed : Int) (whole : Expression)
    (accepted : SourceSynthesisCurrentConstruction.firstOrderRaw lib query signed = .ok whole)
    (rootValue : Value Symbol Guard) (sourceHeap : InternedConstructorTemplates.State Symbol Guard)
    (built : InternedFreshOrdinaryConstruction.build (ordinarySymbols whole) [] empty =
      .done rootValue sourceHeap)
    (key : NodeKey) (entry : Interned NodeKey) (body depth ordinary : Value Symbol Guard)
    (stored : sourceHeap.nodeRecords key = some (.mu entry body depth ordinary))
    (oldRoot : NodeRequest Symbol Guard) (machine : Machine Symbol Guard)
    (oldRootDomain : oldRoot.domain = IntersectionEmptyDomain.emptyDomain)
    (oldRootClosed : oldRoot.left.free = [] ∧ oldRoot.right.free = [])
    (machineValid : SourceRecursiveIntersectionKernel.Valid machine)
    (sourceGrowth : Grows sourceHeap machine.heap)
    (pastInventory : InternedShallowHeap.NoNewMu sourceHeap machine.heap)
    (operations : SourceEqualityConstraintMemoAllocation.State)
    (operationsValid : SourceEqualityConstraintMemoAllocation.Valid operations)
    (oldFuel oldCount : Nat) (oldControl : Control (Value Symbol Guard))
    (oldSnapshot : Checked width) (oldBound : oldCount ≤ oldFuel)
    (oldInputs : InputsThrough oldFuel (.code (.node oldRoot .pure))
      (⟨initial width machine, operations⟩ : Checked width))
    (oldFields : FieldsThrough oldFuel (.code (.node oldRoot .pure))
      (⟨initial width machine, operations⟩ : Checked width))
    (oldActual : Trace oldCount (.code (.node oldRoot .pure))
      (⟨initial width machine, operations⟩ : Checked width) oldControl oldSnapshot)
    (middleRoot : NodeRequest Symbol Guard) (middleFuel : Nat)
    (middleRootDomain : middleRoot.domain = IntersectionEmptyDomain.emptyDomain)
    (middleLeftAvailable : Available oldSnapshot.native.machine.heap middleRoot.left)
    (middleRightAvailable : Available oldSnapshot.native.machine.heap middleRoot.right)
    (middleLeftClosed : middleRoot.left.free = []) (middleRightClosed : middleRoot.right.free = [])
    (middleInputs : InputsThrough middleFuel (.code (.node middleRoot .pure)) oldSnapshot)
    (middleFields : FieldsThrough middleFuel (.code (.node middleRoot .pure)) oldSnapshot)
    (middleCount : Nat) (middleControl : Control (Value Symbol Guard))
    (middleSnapshot : Checked width) (middleBound : middleCount ≤ middleFuel)
    (middleActual : Trace middleCount (.code (.node middleRoot .pure))
      oldSnapshot middleControl middleSnapshot)
    (nextRoot : NodeRequest Symbol Guard) (nextFuel nextCount : Nat)
    (nextControl : Control (Value Symbol Guard)) (reader : Checked width)
    (nextRootDomain : nextRoot.domain = IntersectionEmptyDomain.emptyDomain)
    (nextRootAvailable : Available middleSnapshot.native.machine.heap nextRoot.left ∧
      Available middleSnapshot.native.machine.heap nextRoot.right)
    (nextRootClosed : nextRoot.left.free = [] ∧ nextRoot.right.free = [])
    (nextBound : nextCount ≤ nextFuel)
    (nextInputs : InputsThrough nextFuel (.code (.node nextRoot .pure)) middleSnapshot)
    (nextFields : FieldsThrough nextFuel (.code (.node nextRoot .pure)) middleSnapshot)
    (nextActual : Trace nextCount (.code (.node nextRoot .pure)) middleSnapshot
      nextControl reader) :
    let start := middleSnapshot
    let nodeLaw := SourceCurrentNativeWarmCMDefinitions.NodeResult (width := width)
      nextRoot start nextCount entry body depth ordinary
    let edgeLaw := SourceCurrentNativeWarmCMDefinitions.EdgeResult (width := width)
      nextRoot start nextCount entry body depth ordinary
    InternedShallowHeap.NoNewMu sourceHeap start.native.machine.heap ∧
      (Returned nodeLaw start.native.nodes ∧ Returned edgeLaw start.native.edges) ∧
      ∃ bodyId : Nat, SourceRecursiveIntersectionControl.identity body = some bodyId ∧
        ∀ (pattern : Value Symbol Guard) (patternId : Nat)
          (domain : Interned IntersectionFlatMemoKeyDomain.DomainKey),
          SourceCurrentAllocatedNativeSourceWarmEntry.AuthenticEntryAt (width := width)
            nextRoot start nextCount entry body depth ordinary pattern patternId domain →
          let universeValue : Value Symbol Guard := .mu entry body depth ordinary
          let bodyFirst := SourceRecursiveIntersectionDomain.extend domain.key [entry.identity]
            (SourceRecursiveIntersectionControl.pair bodyId entry.identity)
          let diagonalFirst := SourceRecursiveIntersectionDomain.extend domain.key [entry.identity]
            (SourceRecursiveIntersectionControl.pair entry.identity entry.identity)
          let diagonalTerminal := SourceRecursiveIntersectionDomain.extend diagonalFirst [entry.identity]
            (SourceRecursiveIntersectionControl.pair bodyId entry.identity)
          Returned (SourceCurrentAllocatedNativeBodyFirstKeyQueryGlobalLaws.NodeResult
              entry.identity bodyId bodyFirst body universeValue) start.native.nodes ∧
          Returned (SourceCurrentAllocatedNativeBodyFirstKeyQueryGlobalLaws.EdgeResult
              entry.identity bodyId bodyFirst universeValue) start.native.edges ∧
          Returned (SourceCurrentAllocatedNativeCoherentOpenBodyQueryGlobalLaws.NodeResult
              entry.identity entry.identity entry.identity diagonalTerminal diagonalFirst body universeValue)
            start.native.nodes ∧
          Returned SourceCurrentAllocatedNativeTopRowQueryGlobalLaws.EdgeResult start.native.edges := by
  let coldInitial : Checked width := ⟨initial width machine, operations⟩
  have oldCurrent : Inputs (.code (.node oldRoot .pure)) coldInitial := by
    cases oldFuel with
    | zero => exact oldInputs
    | succ remaining => exact oldInputs.1
  have oldLeftAvailable : Available machine.heap oldRoot.left := oldCurrent.1.2.1
  have oldRightAvailable : Available machine.heap oldRoot.right := oldCurrent.1.2.2
  have leftProfile : Profile entry.identity oldRoot.left :=
    ⟨oldRootClosed.1,
      SourceSynthesisCurrentUniverseStartupAtoms.current_stored_universe_closed_atoms_after_no_new_mu
        lib query signed whole accepted rootValue sourceHeap built key entry body depth ordinary stored
        machine.heap machineValid.1.coherent pastInventory oldRoot.left oldLeftAvailable oldRootClosed.1⟩
  have rightProfile : Profile entry.identity oldRoot.right :=
    ⟨oldRootClosed.2,
      SourceSynthesisCurrentUniverseStartupAtoms.current_stored_universe_closed_atoms_after_no_new_mu
        lib query signed whole accepted rootValue sourceHeap built key entry body depth ordinary stored
        machine.heap machineValid.1.coherent pastInventory oldRoot.right oldRightAvailable oldRootClosed.2⟩
  have coldInventory := original_universe_cold_query_no_new_mu (width := width)
    lib query signed whole accepted rootValue sourceHeap built key entry body depth ordinary stored
    oldRoot machine machineValid sourceGrowth oldRootDomain leftProfile rightProfile
    operations operationsValid oldFuel oldInputs oldFields
  have inventoryAtOld : InternedShallowHeap.NoNewMu sourceHeap oldSnapshot.native.machine.heap :=
    InternedShallowHeap.noNewMu_trans pastInventory
      (coldInventory.2 oldCount oldControl oldSnapshot oldBound oldActual)
  have warmInventory := original_universe_next_warm_query_no_new_mu (width := width)
    lib query signed whole accepted rootValue sourceHeap built key entry body depth ordinary stored
    oldRoot machine oldRootDomain oldRootClosed machineValid sourceGrowth pastInventory
    operations operationsValid oldFuel oldCount oldControl oldSnapshot oldBound oldInputs oldFields oldActual
    middleRoot middleFuel middleRootDomain middleLeftAvailable middleRightAvailable middleLeftClosed middleRightClosed
    middleInputs middleFields
  have inventoryAtMiddle : InternedShallowHeap.NoNewMu sourceHeap middleSnapshot.native.machine.heap :=
    InternedShallowHeap.noNewMu_trans inventoryAtOld
      (warmInventory.2 middleCount middleControl middleSnapshot middleBound middleActual)
  obtain ⟨bodyEntry, _marker, _arrow, _sourceRows, bodyEq, _bodyAvailable, _markerShape,
      _arrowChildren, _arrowKey, _catalog, _markerClosed, _markerAvailable, _markerAtoms,
      _rowKinds, _arrowRetained⟩ :=
    SourceSynthesisCurrentUniverseBodyChildClassification.current_stored_universe_body_physical_children_after_growth
      lib query signed whole accepted rootValue sourceHeap built key entry body depth ordinary stored
      machine.heap machineValid.1 sourceGrowth
  have bodyIdentity : SourceRecursiveIntersectionControl.identity body = some bodyEntry.identity := by
    rw [bodyEq]
    rfl
  have nodeSeed := original_universe_two_prefix_node_seed_for_third_actual_history (width := width)
    lib query signed whole accepted rootValue sourceHeap built key entry body depth ordinary stored
    oldRoot machine oldRootDomain oldRootClosed machineValid sourceGrowth pastInventory
    operations operationsValid oldFuel oldCount oldControl oldSnapshot oldBound oldInputs oldFields oldActual
    middleRoot middleFuel middleRootDomain middleLeftAvailable middleRightAvailable middleLeftClosed middleRightClosed
    middleInputs middleFields middleCount middleControl middleSnapshot middleBound middleActual
    nextRoot nextFuel nextCount nextControl reader nextRootDomain nextRootAvailable nextRootClosed
    nextBound nextInputs nextFields nextActual
  have edgeSeed := original_universe_two_prefix_edge_seed_for_third_actual_history (width := width)
    lib query signed whole accepted rootValue sourceHeap built key entry body depth ordinary stored
    oldRoot machine oldRootDomain oldRootClosed machineValid sourceGrowth pastInventory
    operations operationsValid oldFuel oldCount oldControl oldSnapshot oldBound oldInputs oldFields oldActual
    middleRoot middleFuel middleRootDomain middleLeftAvailable middleRightAvailable middleLeftClosed middleRightClosed
    middleInputs middleFields middleCount middleControl middleSnapshot middleBound middleActual
    nextRoot nextFuel nextCount nextControl reader nextRootDomain nextRootAvailable nextRootClosed
    nextBound nextInputs nextFields nextActual
  have bodyFirst :=
    SourceCurrentNativeWarmBodyFirstInitialPayloads.body_first_initial_payloads_for_third_actual_history
      (width := width)
      lib query signed whole accepted rootValue sourceHeap built key entry body depth ordinary stored
      oldRoot machine oldRootDomain oldRootClosed machineValid sourceGrowth pastInventory
      operations operationsValid oldFuel oldCount oldControl oldSnapshot oldBound oldInputs oldFields oldActual
      middleRoot middleFuel middleRootDomain middleLeftAvailable middleRightAvailable middleLeftClosed middleRightClosed
      middleInputs middleFields middleCount middleControl middleSnapshot middleBound middleActual
      nextRoot nextFuel nextCount nextControl reader nextRootDomain nextRootAvailable nextRootClosed
      nextBound nextInputs nextFields nextActual bodyEntry.identity bodyIdentity
  have coherent :=
    SourceCurrentNativeWarmCoherentInitialPayloads.coherent_initial_payloads_for_third_actual_history
      (width := width)
      lib query signed whole accepted rootValue sourceHeap built key entry body depth ordinary stored
      oldRoot machine oldRootDomain oldRootClosed machineValid sourceGrowth pastInventory
      operations operationsValid oldFuel oldCount oldControl oldSnapshot oldBound oldInputs oldFields oldActual
      middleRoot middleFuel middleRootDomain middleLeftAvailable middleRightAvailable middleLeftClosed middleRightClosed
      middleInputs middleFields middleCount middleControl middleSnapshot middleBound middleActual
      nextRoot nextFuel nextCount nextControl reader nextRootDomain nextRootAvailable nextRootClosed
      nextBound nextInputs nextFields nextActual bodyEntry.identity bodyIdentity
  dsimp only
  refine ⟨inventoryAtMiddle, ⟨nodeSeed, edgeSeed⟩, bodyEntry.identity, bodyIdentity, ?_⟩
  intro pattern patternId domain authentic
  have bodyFirstPair := bodyFirst pattern patternId domain authentic
  have coherentPair := coherent pattern patternId domain authentic
  exact ⟨bodyFirstPair.1, bodyFirstPair.2, coherentPair.1, coherentPair.2⟩

end MicroCFTA.SourceSynthesisCurrentUniverseNativeAllocation
