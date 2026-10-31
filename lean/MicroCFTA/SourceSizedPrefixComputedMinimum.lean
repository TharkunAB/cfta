import MicroCFTA.SourceSizedMinimumConvergence
import MicroCFTA.SourceSizedPrefixKnownOrdinary

/-!
# Bounded startup from the actual computed minimum table

The natural table comes from the computed positive signed table.
Its signed embedding is derived from the actual minimum specification.
The startup retains the original cache and row gates and the same built root.
-/
namespace MicroCFTA.SourceSizedPrefixComputedMinimum
open SourceSizedMinimumConvergence

section Minimum
variable {Q Symbol Guard : Type}

/-- Convert the actual computed signed table to natural sizes. -/
def minimumNat [DecidableEq Q] (input : SourceSizedPreprocessing.Input Q Symbol Guard) : Q → Option Nat :=
  fun current => (minimumSizes input current).map Int.toNat

/-- Positivity makes the natural table embed exactly into the computed signed table. -/
theorem minimumNat_embedded [DecidableEq Q] (input : SourceSizedPreprocessing.Input Q Symbol Guard) :
    (fun current => (minimumNat input current).map (fun size : Nat => (size : Int))) = minimumSizes input := by
  funext current
  cases observed : minimumSizes input current with
  | none => simp only [minimumNat, observed, Option.map_none]
  | some value =>
      have positive : 0 < value := ((minimum_spec input).2 current value observed).2
      have exactCast : (value.toNat : Int) = value := by omega
      simp only [minimumNat, observed, Option.map_some, exactCast]
end Minimum

open InternedConstructorTemplates InternedProbeProvenance
open SourcePruningEnumerationNodes
open SourceEqualityConstraintOrigins (guards)
open SourceCurrentAllocatedPartialInitialization (inventory caller globals)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Metadata" => SourcePruningRecordTypes.Metadata
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Guard
variable {Q Typing : Type} {width : Nat}
variable [DecidableEq Q] [DecidableEq (EdgeKey Symbol Guard)]

/-- Original input computes its minimum and supplies the actual same-root bounded startup. -/
theorem initial_packet_computed
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (cache : Cache.State SourceEqualityPartialConstraintKey.Key) (valid : Cache.Valid cache)
    (input : SourceSizedPreprocessing.Input Q Symbol Guard)
    (equalSizes : Guard → List Nat → Bool) (bound : Int)
    (normalized : ∀ current row, row ∈ input.rows current → SourceEqualityGuardReadback.Cached row.constraint.equalities)
    (metadata : Metadata Typing) (emptyPending : metadata.pending = []) :
    ((fun current => (minimumNat input current).map (fun size : Nat => (size : Int))) = minimumSizes input) ∧
    let expression := SourceSizedPrefixProductOrdinary.expression input.rows (minimumNat input) equalSizes input.root bound
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
      SourceSizedPrefixKnownOrdinary.KnownOrdinary
        (bound.toNat + 1) (caller width final heap).checked.native.machine.heap startup := by
  refine ⟨minimumNat_embedded input, ?_⟩
  exact SourceSizedPrefixKnownOrdinary.initial_packet_known (width := width)
    formulas solver cache valid input.rows (minimumNat input) equalSizes input.root bound normalized metadata emptyPending

end MicroCFTA.SourceSizedPrefixComputedMinimum
