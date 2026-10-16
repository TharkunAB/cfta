import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryFinite

set_option pp.universes true
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.funBinderTypes true

#print axioms MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryFinite.original
#check @MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryFinite.original
#print axioms MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryFinite.closed
#check @MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryFinite.closed
#print axioms MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryFinite.finite
#check @MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryFinite.finite

namespace FiniteOrdinaryFiniteChecks
open MicroCFTA Cache InternedConstructorTemplates InternedProbeProvenance InternedRecordCoherence
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceRecursiveIntersectionInputView SourceCurrentAllocatedFiniteOrdinaryStored
open SourceCurrentAllocatedNativePhysicalCompletion (Good)
open SourceCurrentAllocatedNativePhysicalTraceCompletion (Receipt)
open SourceEqualityRequiredSemanticCache (SemanticReady)

/-- Actual normalization excludes spurious cached free names without assuming closedness. -/
theorem closed_metadata {Symbol Guard : Type}
    (state : InternedConstructorTemplates.State Symbol Guard) (coherent : Coherent state)
    (entry : Interned InternedBinderProtocol.NodeKey) (rows : List (EdgeValue Symbol Guard))
    (depth : Nat) (free : List InternedBinderProtocol.Reference)
    (available : Available state (.node entry rows depth free))
    (domain : SourceCurrentAllocatedFiniteOrdinaryDomain.Rows rows) : free = [] :=
  SourceCurrentAllocatedFiniteOrdinaryFinite.closed state coherent (.node entry rows depth free) available (.ordinary domain)

local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat}

/-- Nonempty equality classes do not add an originalness or closedness premise. -/
theorem full_guard_finite
    (symbol : Symbol) (guard : SourceGuards.Guard FullSyntax.Formula)
    (holds : Guard → Language.Term Symbol → Bool) (state : Checked width)
    (good : Good state) (semantic : SemanticReady state.native.machine.heap)
    (stored : Stored state.native) (idle : SourceRecursiveIntersectionNative.Idle state.native)
    (leftAvailable : Available state.native.machine.heap
      (.node ⟨2, .node [0]⟩ [.mk ⟨0, ⟨symbol, [.empty, .empty], ⟨some [[[0], [1]]], guard⟩⟩⟩ [.empty, .empty]] 0 []))
    (right : Value Symbol Guard) (rightAvailable : Available state.native.machine.heap right)
    (rightDomain : SourceCurrentAllocatedFiniteOrdinaryDomain.Node right)
    (ranges : SourceCurrentAllocatedNativeRequestBounds.WordRanges
      (.code (requestNode IntersectionEmptyDomain.emptyDomain
        (.node ⟨2, .node [0]⟩ [.mk ⟨0, ⟨symbol, [.empty, .empty], ⟨some [[[0], [1]]], guard⟩⟩⟩ [.empty, .empty]] 0 []) right)) state) :
    ∃ fuel value after,
      Receipt fuel (.code (requestNode IntersectionEmptyDomain.emptyDomain
        (.node ⟨2, .node [0]⟩ [.mk ⟨0, ⟨symbol, [.empty, .empty], ⟨some [[[0], [1]]], guard⟩⟩⟩ [.empty, .empty]] 0 []) right))
        state value after (fun final value => Available final.heap value) ∧
      Stored after.native ∧ SourceCurrentAllocatedFiniteOrdinaryDomain.Node value ∧ value.free = [] := by
  obtain ⟨fuel, value, after, receipt, _, _, retained, domain, _, _, closed⟩ :=
    SourceCurrentAllocatedFiniteOrdinaryFinite.finite holds state good semantic stored idle _ right
      leftAvailable rightAvailable (.ordinary (.cons (.cons .empty (.cons .empty .nil)) .nil)) rightDomain ranges
  exact ⟨fuel, value, after, receipt, retained, domain, closed⟩

/-- A first actual result supplies every physical invariant for the next serial call. -/
theorem serial
    (holds : Guard → Language.Term Symbol → Bool) (state : Checked width)
    (good : Good state) (semantic : SemanticReady state.native.machine.heap)
    (stored : Stored state.native) (idle : SourceRecursiveIntersectionNative.Idle state.native)
    (left right : Value Symbol Guard)
    (leftAvailable : Available state.native.machine.heap left) (rightAvailable : Available state.native.machine.heap right)
    (leftDomain : SourceCurrentAllocatedFiniteOrdinaryDomain.Node left)
    (rightDomain : SourceCurrentAllocatedFiniteOrdinaryDomain.Node right)
    (ranges : SourceCurrentAllocatedNativeRequestBounds.WordRanges
      (.code (requestNode IntersectionEmptyDomain.emptyDomain left right)) state) :
    ∃ fuel value middle,
      Receipt fuel (.code (requestNode IntersectionEmptyDomain.emptyDomain left right)) state value middle
        (fun final value => Available final.heap value) ∧
      ∀ _nextRanges : SourceCurrentAllocatedNativeRequestBounds.WordRanges
          (.code (requestNode IntersectionEmptyDomain.emptyDomain value right)) middle,
        ∃ nextFuel output after,
          Receipt nextFuel (.code (requestNode IntersectionEmptyDomain.emptyDomain value right)) middle output after
            (fun final value => Available final.heap value) ∧ Stored after.native ∧
          SourceCurrentAllocatedFiniteOrdinaryDomain.Node output ∧
          MergedOrdinaryHeight.height output ≤ MergedOrdinaryHeight.height value ∧
          MergedOrdinaryHeight.height output ≤ MergedOrdinaryHeight.height right ∧ output.free = [] := by
  obtain ⟨fuel, value, middle, receipt, middleIdle, middleSemantic, middleStored, valueDomain, _, _, _⟩ :=
    SourceCurrentAllocatedFiniteOrdinaryFinite.finite holds state good semantic stored idle left right
      leftAvailable rightAvailable leftDomain rightDomain ranges
  refine ⟨fuel, value, middle, receipt, ?_⟩
  intro nextRanges
  obtain ⟨nextFuel, output, after, nextReceipt, _, _, finalStored, outputDomain, leftBound, rightBound, closed⟩ :=
    SourceCurrentAllocatedFiniteOrdinaryFinite.finite holds middle receipt.good middleSemantic middleStored middleIdle value right
      receipt.result (receipt.extension.available right rightAvailable) valueDomain rightDomain nextRanges
  exact ⟨nextFuel, output, after, nextReceipt, finalStored, outputDomain, leftBound, rightBound, closed⟩

end FiniteOrdinaryFiniteChecks

#print axioms FiniteOrdinaryFiniteChecks.closed_metadata
#check @FiniteOrdinaryFiniteChecks.closed_metadata
#print axioms FiniteOrdinaryFiniteChecks.full_guard_finite
#check @FiniteOrdinaryFiniteChecks.full_guard_finite
#print axioms FiniteOrdinaryFiniteChecks.serial
#check @FiniteOrdinaryFiniteChecks.serial
