import MicroCFTA.SourceSizedPrefixProductInitial

/-!
# Known ordinary nodes in the enumeration cache

The predicate reads each stored known handle and its shared original height bound.
It permits unassigned slots. It does not assert global worker progress.
The callback preservation law retains the same native heap.
-/
namespace MicroCFTA.SourceSizedPrefixKnownOrdinary
open InternedConstructorTemplates InternedProbeProvenance
open SourcePruningEnumerationNodes
open SourceEqualityConstraintOrigins (guards)
open SourceCurrentAllocatedPartialInitialization (inventory caller globals)
open SourceSizedDecided (Row)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Metadata" => SourcePruningRecordTypes.Metadata
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Guard

/-- Every known pending handle has its actual ordinary node within the shared height bound. -/
def KnownOrdinary (heightBound : Nat) (heap : State Symbol Guard) (before : Cached) : Prop :=
  ∀ handle scs, EnumerationState.UVarValue.unenumerated (some handle) scs ∈ before.core.values →
    ∃ value, lookupNode heap handle = some value ∧ SourceCurrentAllocatedFiniteOrdinaryDomain.Node value ∧
      MergedOrdinaryHeight.height value ≤ heightBound

/-- The literal singleton core derives the property from its actual decoded root. -/
theorem initial_core (heightBound : Nat) (heap : State Symbol Guard) (before : Cached) (handle : Nat)
    (value : Value Symbol Guard) (core : before.core = EnumerationState.initial handle)
    (decoded : lookupNode heap handle = some value)
    (ordinary : SourceCurrentAllocatedFiniteOrdinaryDomain.Node value)
    (height : MergedOrdinaryHeight.height value ≤ heightBound) : KnownOrdinary heightBound heap before := by
  intro current scs member
  rw [core] at member
  simp [EnumerationState.initial] at member
  rcases member with ⟨same, _scs⟩
  subst current
  exact ⟨value, decoded, ordinary, height⟩

/-- Representative compression preserves known handles because it preserves values. -/
theorem compression_frame (heightBound : Nat) (heap : State Symbol Guard) (before : Cached)
    (observed : EnumerationState.State Symbol Guard) (known : KnownOrdinary heightBound heap before)
    (frame : EnumerationCompressionFrame.Frame before.core observed) :
    KnownOrdinary heightBound heap (EnumerationExpandableIndex.frame observed before) := by
  intro handle scs member
  change EnumerationState.UVarValue.unenumerated (some handle) scs ∈ observed.values at member
  rw [frame.values] at member
  exact known handle scs member

/-- Every actual successful callback row retains the property at the same heap. -/
theorem recordTypes_rows {Typing : Type} (heightBound : Nat) (heap : State Symbol Guard)
    (graph : EnumerationState.Graph Symbol Guard) (templates : List (Template.Pattern Symbol))
    (fuel : Nat) (metadata : Metadata Typing) (uv : Nat)
    (input : Sum (Fragments.Fragment Symbol) Nat) (before : Cached)
    (known : KnownOrdinary heightBound heap before) (total : UnionFind.Total before.core.representatives) :
    ∀ row ∈ ExceptT.run (SourcePruningRecordTypes.recordTypes graph templates fuel metadata uv input before.core),
      match row with
      | .error _ => True
      | .ok (_, observed) => KnownOrdinary heightBound heap (EnumerationExpandableIndex.frame observed before) := by
  intro row member
  cases row with
  | error _error => trivial
  | ok pair =>
      rcases pair with ⟨result, observed⟩
      exact compression_frame heightBound heap before observed known
        (SourcePruningRecordTypes.recordTypes_frame graph templates fuel metadata uv input
          before.core observed result total member)

/-- The cold caller retains exactly the heap used by the root construction. -/
theorem caller_heap (width : Nat) (cache : Cache.State SourceEqualityPartialConstraintKey.Key)
    (heap : State Symbol Guard) : (caller width cache heap).checked.native.machine.heap = heap := rfl

variable {Q Typing : Type} {width : Nat}
variable [DecidableEq (EdgeKey Symbol Guard)]

/-- Original initialization supplies the property with the same Packet, Fits and root. -/
theorem initial_packet_known
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (cache : Cache.State SourceEqualityPartialConstraintKey.Key) (valid : Cache.Valid cache)
    (original : Q → List (Row Q Symbol Guard)) (minimum : Q → Option Nat)
    (equalSizes : Guard → List Nat → Bool) (root : Q) (bound : Int)
    (normalized : ∀ current row, row ∈ original current → SourceEqualityGuardReadback.Cached row.constraint.equalities)
    (metadata : Metadata Typing) (emptyPending : metadata.pending = []) :
    let expression := SourceSizedPrefixProductOrdinary.expression original minimum equalSizes root bound
    let final := (SourceEqualityOriginalAllocationPreparation.prepare (guards expression) cache).2
    ∃ value heap, ∃ built : InternedFreshOrdinaryConstruction.build expression [] empty = .done value heap,
      InternedNestedFacts.Facts heap ∧ Available heap value ∧ value.free = [] ∧
      SourceCurrentAllocatedFiniteOrdinaryDomain.Node value ∧ MergedOrdinaryHeight.height value ≤ bound.toNat + 1 ∧
      SourceEqualityAnnotationHeap.Heap (fun guard => guard ∈ guards expression) heap ∧
      ∃ handle, encodeNode value = some handle ∧ lookupNode heap handle = some value ∧
      let startup : Cached := ⟨EnumerationState.initial handle,
        fun slot => if slot = 0 then !MergedOrdinaryHeight.recursiveBoundary value else false, fun _ => none⟩
      SourcePruningEnumerationRecursive.Packet formulas solver (inventory expression value heap built)
        (caller width final heap) globals metadata startup ∧
      SourceCurrentConstrainedCapGeneratedQueryResources.Fits
        ⟨heap.nodes.next, heap.edges.next, 0, InternedValueMassHeap.initialBound heap⟩ (caller width final heap).checked ∧
      EnumerationValidity.Canonical startup.core ∧
      startup.core.values[0]? = some (.unenumerated (some handle) []) ∧
      SourcePruningEnumerationPrefixAdmission.suspendedBound startup.core = 0 ∧
      KnownOrdinary (bound.toNat + 1) (caller width final heap).checked.native.machine.heap startup := by
  obtain ⟨value, heap, built, facts, available, free, ordinary, height, annotated,
    handle, encoded, decoded, packet, fits, canonical, stored, mass⟩ :=
    SourceSizedPrefixProductInitial.initial_packet (width := width)
      formulas solver cache valid original minimum equalSizes root bound normalized metadata emptyPending
  refine ⟨value, heap, built, facts, available, free, ordinary, height, annotated,
    handle, encoded, decoded, packet, fits, canonical, stored, mass, ?_⟩
  rw [caller_heap]
  exact initial_core (bound.toNat + 1) heap _ handle value rfl decoded ordinary height

end MicroCFTA.SourceSizedPrefixKnownOrdinary
