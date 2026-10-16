import MicroCFTA.SourceCurrentAllocatedRecursiveInitialRanges
import MicroCFTA.SourceCurrentHereditaryNativeTrace
import MicroCFTA.SourceCurrentHereditaryUnconstrained

/-!
# Hereditary laws at the same constructed cold native return

Initial source resources construct the existing exact-language receipt.
The local annotation induction follows that receipt's actual checked trace.
Unrelated constrained records remain permitted in the source heap.
-/
namespace MicroCFTA.SourceCurrentHereditaryNativeCold
open Cache Language InternedConstructorTemplates InternedProbeProvenance
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceRecursiveIntersectionInputView IntersectSchedule SourceEqualityNativeDemand
open SourceCurrentAllocatedNativePhysicalCompletion (Good)
open SourceEqualityRequiredSemanticCache (SemanticReady)
open SourceCurrentHereditaryConstruction (MuStored)
open SourceEqualityAnnotationLanguage (Annotated)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Plain" => (fun guard : Guard => SourceMemoGate.plain guard = true)
local notation "DomainKey" => IntersectionFlatMemoKeyDomain.DomainKey
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]

/-- Initial resources construct one exact closed intersection with its hereditary return laws. -/
theorem cold_complete (bits : Nat)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (machine : Machine Symbol Guard) (operations : SourceEqualityConstraintMemoAllocation.State)
    (good : Good (⟨initial (bits + 2) machine, operations⟩ : Checked (bits + 2)))
    (semantic : SemanticReady machine.heap)
    (left right : Value Symbol Guard) (leftOriginal : Original left) (rightOriginal : Original right)
    (leftAvailable : Available machine.heap left) (rightAvailable : Available machine.heap right)
    (leftClosed : left.free = []) (rightClosed : right.free = [])
    (nodes : machine.heap.nodes.next < 2 ^ bits) (edges : machine.heap.edges.next ≤ 2 ^ (bits + 2))
    (room : machine.domains.next + 2 ^ (machine.heap.nodes.next + machine.heap.nodes.next * machine.heap.nodes.next) <
      2 ^ (bits + 1))
    (stored : MuStored Plain machine.heap) (leftAnnotated : Annotated Plain left) (rightAnnotated : Annotated Plain right) :
    ∃ (inputModel : InputMeaning (view machine.heap (SourceEqualityPCSGuard.holds formulas solver)))
      (inputRanked : RankedInput (view machine.heap (SourceEqualityPCSGuard.holds formulas solver)) inputModel.valid)
      (fuel : Nat) (value : Value Symbol Guard) (after : Checked (bits + 2)),
      SourceCurrentAllocatedNativeContextualCompletion.Receipt
        (semanticView := view machine.heap (SourceEqualityPCSGuard.holds formulas solver)) (model := inputModel)
        (ranked := inputRanked) (semanticHolds := SourceEqualityPCSGuard.holds formulas solver)
        fuel (.code (requestNode IntersectionEmptyDomain.emptyDomain left right))
        ⟨initial (bits + 2) machine, operations⟩ value after
        (fun final value => Available final.heap value)
        (fun _ value => SourceCurrentAllocatedNativeContextCache.NodeLaw
          (view machine.heap (SourceEqualityPCSGuard.holds formulas solver)) inputModel inputRanked
          (SourceEqualityPCSGuard.holds formulas solver) ⟨IntersectionEmptyDomain.emptyDomain, left, right⟩ value) ∧
      SourceCurrentAllocatedNativeScopeCache.Scoped after.native ∧
      SourceRecursiveIntersectionNative.Idle after.native ∧ value.free = [] ∧
      (∀ output term, InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver) output value term ↔
        InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver) output left term ∧
        InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver) output right term) ∧
      SourceCurrentHereditaryNativeControl.Stored Plain machine.heap after ∧
      Annotated Plain value ∧ SourceMemoGate.unconstrained value = true := by
  obtain ⟨inputModel, inputRanked, fuel, value, after, receipt, scopedCache, idle, closed, meaning⟩ :=
    SourceCurrentAllocatedRecursiveInitialRanges.cold_complete bits formulas solver machine operations good semantic
      left right leftOriginal rightOriginal leftAvailable rightAvailable leftClosed rightClosed nodes edges room
  let inventory := SourceRecursiveIntersectionSourceInventory.domains machine.heap
  let before : Checked (bits + 2) := ⟨initial (bits + 2) machine, operations⟩
  let request : NodeRequest Symbol Guard := ⟨IntersectionEmptyDomain.emptyDomain, left, right⟩
  have resources : SourceCurrentAllocatedRecursivePrefixAdmission.Resources bits machine.heap inventory machine.domains :=
    ⟨good.native.machine.1, SourceCurrentAllocatedRecursiveDomainCode.source_closed machine.heap good.native.machine.1,
      good.native.machine.2, nodes, edges, by
        simpa only [inventory, SourceRecursiveIntersectionSourceInventory.domains_length] using room⟩
  have current : SourceCurrentAllocatedRecursivePrefixState.Current machine.heap inventory machine.domains before :=
    SourceCurrentAllocatedRecursivePrefixState.initial machine.heap inventory before good semantic rfl
  have scope := initial_scope machine.heap left right leftOriginal rightOriginal leftAvailable rightAvailable
  have physical : SourceCurrentAllocatedRecursivePrefixControl.Certified machine.heap inventory
      (.code (requestNode request.domain request.left request.right)) before.native.machine
      (fun final value => Available final.heap value) :=
    SourceCurrentAllocatedRecursivePrefixCode.request_node machine.heap inventory request machine
      ⟨empty_domain machine, leftAvailable, rightAvailable⟩ scope
      (SourceRecursiveIntersectionSourceInventory.empty_mem machine.heap)
  have certificate : SourceCurrentHereditaryNativeControl.Certified Plain machine.heap
      (.code (requestNode request.domain request.left request.right)) before.native.machine
      (fun final value => Available final.heap value ∧ Annotated Plain value) :=
    SourceCurrentHereditaryNativeEffects.request_node Plain machine.heap request machine
      (SourceCurrentHereditaryNativeScope.empty Plain machine.heap) leftAnnotated rightAnnotated
  have initialStored : SourceCurrentHereditaryNativeControl.Stored Plain machine.heap before :=
    ⟨stored, SourceCurrentHereditaryNativeCache.initial_stored Plain machine.heap (bits + 2) machine⟩
  have retained := SourceCurrentHereditaryNativeTrace.completed resources fuel _ before after value _ _
    current physical (fun _ => trivial) certificate initialStored receipt.trace.steps
  exact ⟨inputModel, inputRanked, fuel, value, after, receipt, scopedCache, idle, closed, meaning, retained.1,
    retained.2.2, SourceCurrentHereditaryUnconstrained.unconstrained value retained.2.2⟩

end MicroCFTA.SourceCurrentHereditaryNativeCold
