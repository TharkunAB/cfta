import MicroCFTA.SourceSizedPrefixComputedMinimum
import MicroCFTA.SourceSizedConstraintEqualSizes

/-!
# Bounded startup with the computed minimum and full-constraint filter

Original input computes the minimum table and the current natural-path filter.
The original admission gates and the same constructed root remain explicit.
The signed Haskell and source representation adapters remain separate.
-/
namespace MicroCFTA.SourceSizedPrefixCurrentConstraintStartup
open SourceSizedMinimumConvergence SourceSizedPrefixComputedMinimum
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

/-- Original input supplies bounded startup without a free minimum table or numeric filter. -/
theorem initial_packet
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (cache : Cache.State SourceEqualityPartialConstraintKey.Key) (valid : Cache.Valid cache)
    (input : SourceSizedPreprocessing.Input Q Symbol Guard) (bound : Int)
    (normalized : ∀ current row, row ∈ input.rows current → SourceEqualityGuardReadback.Cached row.constraint.equalities)
    (metadata : Metadata Typing) (emptyPending : metadata.pending = []) :
    ((fun current => (minimumNat input current).map (fun size : Nat => (size : Int))) = minimumSizes input) ∧
    let expression := SourceSizedPrefixProductOrdinary.expression input.rows (minimumNat input)
      SourceSizedConstraintEqualSizes.equalSizes input.root bound
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
  exact SourceSizedPrefixComputedMinimum.initial_packet_computed (width := width)
    formulas solver cache valid input SourceSizedConstraintEqualSizes.equalSizes bound normalized metadata emptyPending

end MicroCFTA.SourceSizedPrefixCurrentConstraintStartup
