import MicroCFTA.SourcePruningEnumerationPreparedFiniteHistoryContract
import MicroCFTA.SourcePruningEnumerationSelectedPreparationPointResources
import MicroCFTA.SourcePruningEnumerationPrefixMass

/-!
# Recover original opaque resources at the actual prepared prefix

The history already retains its original reservation and prefix certificate.
The actual narrowed cache retains the original suspended-mass bound.
The actual selected preparation derives the resources for its opaque call.
No future endpoint certificate or additional history type is required.
-/
namespace MicroCFTA.SourcePruningEnumerationPreparedRecursive
open EnumerationState InternedConstructorTemplates
open SourcePruningEnumerationRecursive (Packet)
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentConstrainedCapGeneratedQueryResources (Fits)
open SourcePruningEnumerationIncomingReservation (Seed)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Metadata" => SourcePruningRecordTypes.Metadata
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Core" => EnumerationState.State Symbol Constraint
local notation "Heap" => SourceEqualityAnnotationHeap.Heap
local notation "suspendedBound" => SourcePruningEnumerationPrefixAdmission.suspendedBound
variable {Typing Key : Type} {bits : Nat}

private theorem stored_length_le (before : Core) (slot : Nat) (handle : Option Nat)
    (scs : List Suspended) (stored : before.values[slot]? = some (.unenumerated handle scs)) :
    scs.length ≤ suspendedBound before := by
  have member : (.unenumerated handle scs : UVarValue Symbol) ∈ before.values :=
    List.mem_of_getElem? stored
  unfold SourcePruningEnumerationPrefixAdmission.suspendedBound
  generalize before.values = values at member ⊢
  induction values with
  | nil => cases member
  | cons first rest ih =>
      rcases List.mem_cons.mp member with same | listed
      · subst first
        simp only [List.map_cons, List.sum_cons]
        exact Nat.le_add_right _ _
      · have bounded := ih listed
        simp only [List.map_cons, List.sum_cons]
        omega

variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]
attribute [local irreducible] SourceCurrentConstrainedCapEditForecast.headProfile
attribute [local irreducible] SourcePruningEnumerationSelectedValueCaller.normalizationProfile

/-- Original history admission pays each actual prepared opaque view of its narrowed prefix. -/
theorem HistoryAdmission.prepared_opaque_resources
    {holeKey : Typing → Nat → Key} {fits : Key → Symbol → Bool} {admits : Key → Node → Bool}
    {graph : Graph Symbol Constraint} {templates : List (Template.Pattern Symbol)}
    {checkEmpty : Bool} {edgesOf : Node → List (EdgeValue Symbol Constraint)}
    {stop : Option (Metadata Typing → Nat → Bool)} {order : Metadata Typing → List Nat → Option Nat}
    {formulas : SourceGuards.Formulas FullSyntax.Formula} {solver : SourceGuards.Entailment FullSyntax.Formula}
    {inventory : Inventory} {caller : Caller (bits + 2)} {memos : Memos} {metadata : Metadata Typing}
    {before : Cached} {recursiveFuel workFuel uv : Nat} {seed : Seed} {ceiling : Nat}
    (admission : HistoryAdmission formulas solver inventory caller memos metadata before
      (recursiveFuel + 1) seed ceiling)
    (observed : SourcePruningEnumerationSelectedStep.Result (bits + 2) Typing)
    (valid : SourcePruningEnumerationSelectedStep.PrefixValid holeKey fits admits graph templates checkEmpty edgesOf
      stop order metadata formulas solver inventory workFuel uv caller before memos observed)
    (actual : SourcePruningEnumerationSelectedStep.runPrefix holeKey fits admits graph templates stop order metadata
      workFuel workFuel workFuel workFuel workFuel workFuel uv caller before memos.query = observed) :
    match observed with
    | .narrowed _ _ reached _ _ (some narrowed) _ _ =>
        ∀ (nextInventory : Inventory) (nextMemos : Memos) (nextMetadata : Metadata Typing),
          Packet formulas solver nextInventory reached nextMemos nextMetadata narrowed →
          ∀ (handle : Nat) (scs : List Suspended) (decoded prepared : Node)
            (heap : InternedConstructorTemplates.State Symbol Constraint) (entered : Core),
            narrowed.core.values[uv]? = some (.unenumerated (some handle) scs) →
            SourcePruningEnumerationNodes.lookupNode reached.checked.native.machine.heap handle = some decoded →
            SourcePruningEnumerationSelectedPreparation.run workFuel workFuel uv reached narrowed =
              ([.ok ((uv, handle, scs, decoded), entered)], some (.done prepared heap)) →
            Fits (SourcePruningEnumerationPreparedReservation.preparedSeed seed).2
                (SourcePruningEnumerationSelectedValueCaller.advance reached heap).checked ∧
              Heap (fun guard => guard ∈ seed.1) heap ∧
              SourcePruningEnumerationIncomingReservation.Reserved bits
                (SourcePruningEnumerationPreparedReservation.preparedSeed seed) (scs.length + 1)
    | _ => True := by
  obtain ⟨packet, bounded, known, originalMass, reserved⟩ := admission
  obtain ⟨_roots, _paths, _storage, realized, _counts, _flags⟩ := packet.valid
  have resources := SourcePruningEnumerationSelectedStep.prefix_resources holeKey fits admits graph templates
    checkEmpty edgesOf stop order metadata formulas solver inventory workFuel uv caller before memos
    seed.2 (fun guard => guard ∈ seed.1) packet.context realized bounded known observed valid
  have mass := SourcePruningEnumerationPrefixMass.retained_le holeKey fits admits graph templates checkEmpty edgesOf
    stop order metadata formulas solver inventory workFuel uv caller memos before packet observed valid actual
  cases observed with
  | stopped _ _ | parked _ _ _ => trivial
  | narrowed checked prefixPrepared reached queries action candidate right ordinary =>
      cases candidate with
      | none => trivial
      | some narrowed =>
          change Fits (SourceCurrentConstrainedCapEditForecast.headProfile seed.2) reached.checked ∧
            Heap (fun guard => guard ∈ seed.1) reached.checked.native.machine.heap at resources
          change suspendedBound narrowed.core ≤ suspendedBound before.core at mass
          intro nextInventory nextMemos nextMetadata nextPacket handle scs decoded prepared heap entered
            stored decodedLookup preparing
          have numeric := SourcePruningEnumerationSelectedPreparation.run_resources_known
            nextPacket stored decodedLookup preparing
            (SourceCurrentConstrainedCapEditForecast.headProfile seed.2) resources.1
            (fun guard => guard ∈ seed.1) resources.2
          have preparedFits : Fits (SourcePruningEnumerationPreparedReservation.preparedSeed seed).2
              (SourcePruningEnumerationSelectedValueCaller.advance reached heap).checked := numeric.1
          have lengths : scs.length ≤ ceiling :=
            Nat.le_trans (stored_length_le narrowed.core uv (some handle) scs stored)
              (Nat.le_trans mass originalMass)
          have positive : 1 ≤ SourceCurrentConstrainedCapTargetForecast.scalar
              (SourcePruningEnumerationPreparedReservation.preparedSeed seed).2 :=
            Nat.le_trans preparedFits.stored.positive
              (SourceCurrentConstrainedCapTargetForecast.scalar_mass _)
          have pay := Nat.mul_le_mul_right
            (ceiling + SourcePruningEnumerationGuardWidth.width seed.1 + 1) positive
          simp only [Nat.one_mul] at pay
          have cost : scs.length + 1 ≤ SourcePruningEnumerationRecursiveReservation.edgeCount
              (SourcePruningEnumerationPreparedReservation.preparedSeed seed) ceiling := by
            unfold SourcePruningEnumerationRecursiveReservation.edgeCount
            change scs.length + 1 ≤ SourceCurrentConstrainedCapTargetForecast.scalar
              (SourcePruningEnumerationPreparedReservation.preparedSeed seed).2 *
                (ceiling + SourcePruningEnumerationGuardWidth.width seed.1 + 1)
            omega
          exact ⟨preparedFits, numeric.2.2, reserved.first.edge cost⟩

end MicroCFTA.SourcePruningEnumerationPreparedRecursive
