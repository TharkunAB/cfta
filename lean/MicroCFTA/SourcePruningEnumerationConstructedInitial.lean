import MicroCFTA.SourceCurrentAllocatedPartialInitialization
import MicroCFTA.SourcePruningEnumerationInitialPacket
import MicroCFTA.InternedFreshOrdinaryClosedCompletion
import MicroCFTA.SourceEqualityOriginalAllocationPreparation

/-!
# Native enumeration startup from original syntax

Closed construction supplies the root and its actual heap.
A covered original equality-cache history supplies the caller context.
The native startup theorem then derives the packet and both indexes.
-/
namespace MicroCFTA.SourcePruningEnumerationConstructedInitial
open EnumerationState EnumerationCorrectness EnumerationSchedule InternedConstructorTemplates
open SourcePruningEnumerationNodes SourcePruningEnumerationObservation
open InternedProbeProvenance
open SourceEqualityOriginalAllocationHistory (History)
open SourceCurrentAllocatedPartialInitialization (inventory caller globals)
open SourcePruningEnumerationRecursive (Packet)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Key" => SourceEqualityPartialConstraintKey.Key
local notation "Metadata" => SourcePruningRecordTypes.Metadata
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Guard
variable {Typing : Type} {width : Nat}
variable [DecidableEq (EdgeKey Symbol Guard)]

/-- Original construction and covered cache history derive the literal startup packet. -/
theorem original_initial_packet
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula)
    {initial final : Cache.State Key} {originals : List Guard}
    (history : History initial final originals) (valid : Cache.Valid initial)
    (expression : InternedNestedConstruction.Syntax Symbol Guard)
    (covered : ∀ original ∈ SourceEqualityConstraintOrigins.guards expression, original ∈ originals)
    (metadata : Metadata Typing) (emptyPending : metadata.pending = []) :
    ∃ value heap, ∃ built : InternedFreshOrdinaryConstruction.build expression [] empty = .done value heap,
      Available heap value ∧ value.free = [] ∧
      ∃ handle,
        encodeNode value = some handle ∧
        lookupNode heap handle = some value ∧
        let startup : Cached :=
          ⟨EnumerationState.initial handle,
            fun slot => if slot = 0 then !MergedOrdinaryHeight.recursiveBoundary value else false,
            fun _ => none⟩
        Packet formulas solver (inventory expression value heap built)
          (caller width final heap) globals metadata startup ∧
        EnumerationValidity.Canonical startup.core ∧
        startup.core.values[0]? = some (.unenumerated (some handle) []) ∧
        SourcePruningEnumerationPrefixAdmission.suspendedBound startup.core = 0 ∧
        EnumerationCanonicalWaiting.Correct (fun uv => uv) startup.core.values startup.waiting ∧
        ∀ slot, SourcePruningEnumerationNativeIndex.candidate heap
          ((startup.core.values[slot]?).getD .eliminated) = some (startup.expandable slot) := by
  classical
  obtain ⟨value, heap, built⟩ := InternedFreshOrdinaryClosedCompletion.closed_complete expression
  obtain ⟨context, identity, inherited, ready, available, closed, original⟩ :=
    SourceCurrentAllocatedPartialInitialization.constructed width history valid expression covered
      value heap built formulas solver
  obtain ⟨handle, encoded, decoded, packet, canonical, stored, suspended, waiting, flags⟩ :=
    SourcePruningEnumerationRecursive.initial_packet formulas solver
      (inventory expression value heap built) (caller width final heap) globals metadata value
      context available closed emptyPending
  exact ⟨value, heap, built, available, closed, handle, encoded, decoded,
    packet, canonical, stored, suspended, waiting, flags⟩

/-- Actual cached literal preparation derives the original history and startup packet. -/
theorem prepared_initial_packet
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula)
    (initial : Cache.State Key) (valid : Cache.Valid initial)
    (expression : InternedNestedConstruction.Syntax Symbol Guard)
    (cached : ∀ original ∈ SourceEqualityConstraintOrigins.guards expression,
      SourceEqualityGuardReadback.Cached original.equalities)
    (metadata : Metadata Typing) (emptyPending : metadata.pending = []) :
    let final := (SourceEqualityOriginalAllocationPreparation.prepare
      (SourceEqualityConstraintOrigins.guards expression) initial).2
    ∃ value heap, ∃ built : InternedFreshOrdinaryConstruction.build expression [] empty = .done value heap,
      Available heap value ∧ value.free = [] ∧
      ∃ handle,
        encodeNode value = some handle ∧
        lookupNode heap handle = some value ∧
        let startup : Cached :=
          ⟨EnumerationState.initial handle,
            fun slot => if slot = 0 then !MergedOrdinaryHeight.recursiveBoundary value else false,
            fun _ => none⟩
        Packet formulas solver (inventory expression value heap built)
          (caller width final heap) globals metadata startup ∧
        EnumerationValidity.Canonical startup.core ∧
        startup.core.values[0]? = some (.unenumerated (some handle) []) ∧
        SourcePruningEnumerationPrefixAdmission.suspendedBound startup.core = 0 ∧
        EnumerationCanonicalWaiting.Correct (fun uv => uv) startup.core.values startup.waiting ∧
        ∀ slot, SourcePruningEnumerationNativeIndex.candidate heap
          ((startup.core.values[slot]?).getD .eliminated) = some (startup.expandable slot) := by
  obtain ⟨fields, after, prepared⟩ := SourceEqualityOriginalAllocationPreparation.prepare_complete
    (SourceEqualityConstraintOrigins.guards expression) initial valid cached
  have sameCache : (SourceEqualityOriginalAllocationPreparation.prepare
      (SourceEqualityConstraintOrigins.guards expression) initial).2 = after :=
    congrArg Prod.snd prepared.done
  simpa only [sameCache] using
    (original_initial_packet (width := width) formulas solver prepared.history valid expression
      (fun _ member => member) metadata emptyPending)

end MicroCFTA.SourcePruningEnumerationConstructedInitial
