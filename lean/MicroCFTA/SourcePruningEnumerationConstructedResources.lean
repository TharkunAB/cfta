import MicroCFTA.SourcePruningEnumerationConstructedInitial
import MicroCFTA.SourcePruningEnumerationFiniteResources
import MicroCFTA.SourcePruningEnumerationPreparedFiniteResources
import MicroCFTA.SourceEqualityAnnotationConstruction
import MicroCFTA.InternedValueMassHeap

/-!
# Bounded recursive runs from original syntax

Original construction and literal preparation supply the initial packet.
The actual constructed heap computes its initial profile and word width.
Each fixed recursive budget has a stable run with its resource certificate.
The returned outcome can contain an exhaustion stop.
-/
namespace MicroCFTA.SourcePruningEnumerationConstructedResources
open EnumerationState InternedConstructorTemplates
open SourcePruningEnumerationNodes
open SourceCurrentAllocatedPartialInitialization (inventory caller globals)
open SourcePruningEnumerationIncomingReservation (Seed)
open SourceCurrentConstrainedCapGeneratedQueryResources (Fits)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "Metadata" => SourcePruningRecordTypes.Metadata
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Guard
local notation "Syntax" => InternedNestedConstruction.Syntax Symbol Guard
variable {Typing Key : Type}
variable [DecidableEq (EdgeKey Symbol Guard)]

private theorem initial_fits (width : Nat) (cache : Cache.State SourceEqualityPartialConstraintKey.Key)
    (expression : Syntax) (value : Node) (heap : InternedConstructorTemplates.State Symbol Guard)
    (built : InternedFreshOrdinaryConstruction.build expression [] empty = .done value heap) :
    Fits ⟨heap.nodes.next, heap.edges.next, 0, InternedValueMassHeap.initialBound heap⟩
      (caller width cache heap).checked := by
  have verified := InternedFreshOrdinaryFacts.closed_verified expression
  have facts : InternedNestedFacts.Facts heap := by
    simpa only [built, InternedNestedConstruction.Outcome.state] using verified.facts
  exact ⟨Nat.le_refl _, Nat.le_refl _, Nat.le_refl _, InternedValueMassHeap.initial heap facts⟩

variable [DecidableEq Symbol] [DecidableEq Node]

/-- Original syntax computes admission and finite resources for the actual Native bounded run. -/
theorem native_run
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (graph : Graph Symbol Guard) (templates : List (Template.Pattern Symbol))
    (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Guard))
    (stop : Option (Metadata Typing → Nat → Bool)) (order : Metadata Typing → List Nat → Option Nat)
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula)
    (cache : Cache.State SourceEqualityPartialConstraintKey.Key) (valid : Cache.Valid cache)
    (expression : Syntax)
    (cached : ∀ original ∈ SourceEqualityConstraintOrigins.guards expression,
      SourceEqualityGuardReadback.Cached original.equalities)
    (metadata : Metadata Typing) (emptyPending : metadata.pending = []) (recursiveFuel : Nat)
    (selectionMembers : ∀ entry rows depth free, ∀ edge ∈ edgesOf (.node entry rows depth free), edge ∈ rows)
    (selectionLength : ∀ entry rows depth free, (edgesOf (.node entry rows depth free)).length ≤ rows.length) :
    ∃ value heap, ∃ _built : InternedFreshOrdinaryConstruction.build expression [] empty = .done value heap,
      let seed : Seed := (SourceEqualityConstraintOrigins.guards expression,
        ⟨heap.nodes.next, heap.edges.next, 0, InternedValueMassHeap.initialBound heap⟩)
      let bits := SourceCurrentParentInitialRoom.roomBits
        (SourcePruningEnumerationFiniteReservation.final recursiveFuel seed 0).2
      let finalCache := (SourceEqualityOriginalAllocationPreparation.prepare seed.1 cache).2
      let beforeCaller := caller (bits + 2) finalCache heap
      ∃ handle, encodeNode value = some handle ∧ lookupNode heap handle = some value ∧
      let before : Cached := ⟨EnumerationState.initial handle,
        fun slot => if slot = 0 then !MergedOrdinaryHeight.recursiveBoundary value else false,
        fun _ => none⟩
      ∃ bound outcome,
        (∀ extra, SourcePruningEnumerationRecursive.run holeKey fits admits graph templates checkEmpty edgesOf
          stop order (bound + extra) recursiveFuel metadata beforeCaller globals.query before = outcome) ∧
        SourcePruningEnumerationRecursive.OutcomeResources formulas solver beforeCaller
          (SourcePruningEnumerationFiniteReservation.final recursiveFuel seed 0) outcome := by
  let annotation := fun guard => guard ∈ SourceEqualityConstraintOrigins.guards expression
  obtain ⟨value, heap, built, known, _annotated⟩ :=
    SourceEqualityAnnotationConstruction.closed annotation expression
      (SourceEqualityConstraintOrigins.allowed _ expression (fun _ member => member))
  refine ⟨value, heap, built, ?_⟩
  let seed : Seed := (SourceEqualityConstraintOrigins.guards expression,
    ⟨heap.nodes.next, heap.edges.next, 0, InternedValueMassHeap.initialBound heap⟩)
  let bits := SourceCurrentParentInitialRoom.roomBits
    (SourcePruningEnumerationFiniteReservation.final recursiveFuel seed 0).2
  let finalCache := (SourceEqualityOriginalAllocationPreparation.prepare seed.1 cache).2
  let beforeCaller := caller (bits + 2) finalCache heap
  obtain ⟨other, after, observed, _available, _closed, handle, encoded, decoded,
    packet, _canonical, _stored, suspended, _waiting, _flags⟩ :=
    SourcePruningEnumerationConstructedInitial.prepared_initial_packet (width := bits + 2)
      formulas solver cache valid expression cached metadata emptyPending
  obtain ⟨rfl, rfl⟩ := InternedNestedConstruction.Outcome.done.inj (built.symm.trans observed)
  refine ⟨handle, encoded, decoded, ?_⟩
  let before : Cached := ⟨EnumerationState.initial handle,
    fun slot => if slot = 0 then !MergedOrdinaryHeight.recursiveBoundary value else false,
    fun _ => none⟩
  exact SourcePruningEnumerationRecursive.run_finite_complete_resources holeKey fits admits graph templates
    checkEmpty edgesOf stop order formulas solver recursiveFuel (inventory expression value heap built)
    beforeCaller globals before metadata seed 0 packet
    (initial_fits (bits + 2) finalCache expression value heap built) known selectionMembers selectionLength
    (Nat.le_of_eq suspended) (SourcePruningEnumerationFiniteReservation.reserved_computed recursiveFuel seed 0)

/-- Original syntax computes admission and finite resources for the actual Prepared bounded run. -/
theorem prepared_run
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (graph : Graph Symbol Guard) (templates : List (Template.Pattern Symbol))
    (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Guard))
    (stop : Option (Metadata Typing → Nat → Bool)) (order : Metadata Typing → List Nat → Option Nat)
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula)
    (cache : Cache.State SourceEqualityPartialConstraintKey.Key) (valid : Cache.Valid cache)
    (expression : Syntax)
    (cached : ∀ original ∈ SourceEqualityConstraintOrigins.guards expression,
      SourceEqualityGuardReadback.Cached original.equalities)
    (metadata : Metadata Typing) (emptyPending : metadata.pending = []) (recursiveFuel : Nat)
    (selectionMembers : ∀ entry rows depth free, ∀ edge ∈ edgesOf (.node entry rows depth free), edge ∈ rows)
    (selectionLength : ∀ entry rows depth free, (edgesOf (.node entry rows depth free)).length ≤ rows.length) :
    ∃ value heap, ∃ _built : InternedFreshOrdinaryConstruction.build expression [] empty = .done value heap,
      let seed : Seed := (SourceEqualityConstraintOrigins.guards expression,
        ⟨heap.nodes.next, heap.edges.next, 0, InternedValueMassHeap.initialBound heap⟩)
      let bits := SourceCurrentParentInitialRoom.roomBits
        (SourcePruningEnumerationPreparedReservation.final recursiveFuel seed 0).2
      let finalCache := (SourceEqualityOriginalAllocationPreparation.prepare seed.1 cache).2
      let beforeCaller := caller (bits + 2) finalCache heap
      ∃ handle, encodeNode value = some handle ∧ lookupNode heap handle = some value ∧
      let before : Cached := ⟨EnumerationState.initial handle,
        fun slot => if slot = 0 then !MergedOrdinaryHeight.recursiveBoundary value else false,
        fun _ => none⟩
      ∃ bound outcome,
        (∀ extra, SourcePruningEnumerationPreparedRecursive.run holeKey fits admits graph templates checkEmpty edgesOf
          stop order (bound + extra) recursiveFuel metadata beforeCaller globals.query before = outcome) ∧
        SourcePruningEnumerationPreparedRecursive.OutcomeResources formulas solver beforeCaller
          (SourcePruningEnumerationPreparedReservation.final recursiveFuel seed 0) outcome := by
  let annotation := fun guard => guard ∈ SourceEqualityConstraintOrigins.guards expression
  obtain ⟨value, heap, built, known, _annotated⟩ :=
    SourceEqualityAnnotationConstruction.closed annotation expression
      (SourceEqualityConstraintOrigins.allowed _ expression (fun _ member => member))
  refine ⟨value, heap, built, ?_⟩
  let seed : Seed := (SourceEqualityConstraintOrigins.guards expression,
    ⟨heap.nodes.next, heap.edges.next, 0, InternedValueMassHeap.initialBound heap⟩)
  let bits := SourceCurrentParentInitialRoom.roomBits
    (SourcePruningEnumerationPreparedReservation.final recursiveFuel seed 0).2
  let finalCache := (SourceEqualityOriginalAllocationPreparation.prepare seed.1 cache).2
  let beforeCaller := caller (bits + 2) finalCache heap
  obtain ⟨other, after, observed, _available, _closed, handle, encoded, decoded,
    packet, _canonical, _stored, suspended, _waiting, _flags⟩ :=
    SourcePruningEnumerationConstructedInitial.prepared_initial_packet (width := bits + 2)
      formulas solver cache valid expression cached metadata emptyPending
  obtain ⟨rfl, rfl⟩ := InternedNestedConstruction.Outcome.done.inj (built.symm.trans observed)
  refine ⟨handle, encoded, decoded, ?_⟩
  let before : Cached := ⟨EnumerationState.initial handle,
    fun slot => if slot = 0 then !MergedOrdinaryHeight.recursiveBoundary value else false,
    fun _ => none⟩
  exact SourcePruningEnumerationPreparedRecursive.run_finite_complete_resources holeKey fits admits graph templates
    checkEmpty edgesOf stop order formulas solver recursiveFuel (inventory expression value heap built)
    beforeCaller globals before metadata seed 0 packet
    (initial_fits (bits + 2) finalCache expression value heap built) known selectionMembers selectionLength
    (Nat.le_of_eq suspended) (SourcePruningEnumerationPreparedReservation.reserved_computed recursiveFuel seed 0)

end MicroCFTA.SourcePruningEnumerationConstructedResources
