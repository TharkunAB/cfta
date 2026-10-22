import MicroCFTA.SourceCurrentSameSymbolEdgeReady
import MicroCFTA.SourceCurrentSameSymbolEdgeOriginalRows

namespace MicroCFTA.SourceCurrentSameSymbolEdgeComparison
open Cache Language IntersectSchedule InternedConstructorTemplates InternedEdgeResidency
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceRecursiveIntersectionInputView InternedProbeProvenance
open SourceCurrentAllocatedNativePhysicalCompletion (Good)
open SourceEqualityRequiredSemanticCache (SemanticReady)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Edge" => EdgeValue Symbol Guard
local notation "Wrapper" => SourceCurrentSameSymbolEdgeControl.State
local notation "Stable" => SourceCurrentSameSymbolEdgeStable.Stable
local notation "NativeIdle" => SourceRecursiveIntersectionNative.Idle
local notation "guardHolds" => (@SourceEqualityPCSGuard.holds FullSyntax.Formula FormulaExecutable.formulaDecidableEq)

/-- Complete an original-row comparison and retain its current native and pair invariants. -/
theorem original_rows_complete [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (bits : Nat) (source : InternedConstructorTemplates.State Symbol Guard)
    (facts : InternedNestedFacts.Facts source)
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inputModel : InputMeaning (view source (guardHolds formulas solver)))
    (inputRanked : RankedInput (view source (guardHolds formulas solver)) inputModel.valid)
    (leftParent rightParent : Value Symbol Guard)
    (leftOriginal : OriginalInput source (inputOf leftParent))
    (rightOriginal : OriginalInput source (inputOf rightParent))
    (leftAvailable : Available source leftParent) (rightAvailable : Available source rightParent)
    (leftClosed : leftParent.free = []) (rightClosed : rightParent.free = [])
    (left right : Edge)
    (leftMember : left ∈ nodeEdges leftParent) (rightMember : right ∈ nodeEdges rightParent)
    (symbols : left.entry.key.symbol = right.entry.key.symbol)
    (before : Wrapper (bits + 2))
    (stable : Stable (view source (guardHolds formulas solver)) inputModel inputRanked
      (guardHolds formulas solver) before)
    (good : Good before.checked)
    (contextual : SourceCurrentAllocatedNativeContextCache.Contextual
      (view source (guardHolds formulas solver)) inputModel inputRanked
      (guardHolds formulas solver) before.checked.native)
    (semantic : SemanticReady before.checked.native.machine.heap)
    (growth : Grows source before.checked.native.machine.heap)
    (history : Extends source.nodes.issued before.checked.native.machine.heap.nodes.issued)
    (idle : NativeIdle before.checked.native)
    (room : SourceCurrentAllocatedNativeResourceForecast.Room bits
      ⟨source.nodes.next, source.edges.next, before.checked.native.machine.domains.next, 0⟩) :
    let ordered := if right.entry.identity < left.entry.identity then (right, left) else (left, right)
    let request : EdgeRequest Symbol Guard := ⟨IntersectionEmptyDomain.emptyDomain, ordered.1, ordered.2⟩
    ∃ (fuel : Nat) (result : Edge) (after : Wrapper (bits + 2)),
      SourceCurrentSameSymbolEdgeControl.execute fuel (.call (left, right) []) before = .done result after ∧
      EdgeResident after.checked.native.machine.heap result ∧
      SourceCurrentAllocatedNativeContextCache.EdgeLaw
        (view source (guardHolds formulas solver)) inputModel inputRanked
        (guardHolds formulas solver) request result ∧
      Good after.checked ∧
      SourceCurrentAllocatedNativeContextCache.Contextual
        (view source (guardHolds formulas solver)) inputModel inputRanked
        (guardHolds formulas solver) after.checked.native ∧
      SemanticReady after.checked.native.machine.heap ∧
      Extension before.checked.native.machine after.checked.native.machine ∧
      Stable (view source (guardHolds formulas solver)) inputModel inputRanked
        (guardHolds formulas solver) after ∧
      NativeIdle after.checked.native ∧
      Extends before.memo.table after.memo.table ∧
      FlatMemoThunk.Returned before.memo after.memo := by
  dsimp only
  have leftResident : EdgeResident before.checked.native.machine.heap left :=
    edge_grows source _ growth left
      (resident_edges source facts.linked leftParent leftAvailable.resident left leftMember)
  have rightResident : EdgeResident before.checked.native.machine.heap right :=
    edge_grows source _ growth right
      (resident_edges source facts.linked rightParent rightAvailable.resident right rightMember)
  cases found : before.memo.table (left.entry.identity, right.entry.identity) with
  | some handle =>
      obtain ⟨result, after, done, same, resident, law, afterStable, tables, retained⟩ :=
        SourceCurrentSameSymbolEdgeReady.ready_complete
          (view source (guardHolds formulas solver)) inputModel inputRanked (guardHolds formulas solver)
          left right before good.native.machine.1.coherent stable leftResident rightResident
          (Or.inl ⟨handle, found⟩)
      refine ⟨7, result, after, done, resident, law, ?_, ?_, ?_, ?_, afterStable, ?_, tables, retained⟩
      · simpa only [same] using good
      · simpa only [same] using contextual
      · simpa only [same] using semantic
      · rw [same]
        exact Extension.refl _
      · simpa only [same] using idle
  | none =>
      cases reverseFound : before.memo.table (right.entry.identity, left.entry.identity) with
      | some handle =>
          obtain ⟨result, after, done, same, resident, law, afterStable, tables, retained⟩ :=
            SourceCurrentSameSymbolEdgeReady.ready_complete
              (view source (guardHolds formulas solver)) inputModel inputRanked (guardHolds formulas solver)
              left right before good.native.machine.1.coherent stable leftResident rightResident
              (Or.inr ⟨handle, reverseFound⟩)
          refine ⟨7, result, after, done, resident, law, ?_, ?_, ?_, ?_, afterStable, ?_, tables, retained⟩
          · simpa only [same] using good
          · simpa only [same] using contextual
          · simpa only [same] using semantic
          · rw [same]
            exact Extension.refl _
          · simpa only [same] using idle
      | none =>
          obtain ⟨fuel, _, _, result, after, done, receipt, afterStable, afterIdle,
              tables, retained, _, _, _⟩ :=
            SourceCurrentSameSymbolEdgeOriginalRows.both_miss_complete bits source facts formulas solver
              inputModel inputRanked leftParent rightParent leftOriginal rightOriginal
              leftAvailable rightAvailable leftClosed rightClosed left right leftMember rightMember
              symbols before stable found reverseFound good contextual semantic growth history idle room
          exact ⟨fuel, result, after, done, receipt.result, receipt.law, receipt.good,
            receipt.contextual, receipt.semantic, receipt.extension, afterStable, afterIdle, tables, retained⟩

end MicroCFTA.SourceCurrentSameSymbolEdgeComparison

set_option maxRecDepth 30000
set_option maxHeartbeats 0
set_option linter.all true
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.proofs true
set_option pp.proofs.threshold 254
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000
#check @MicroCFTA.SourceCurrentSameSymbolEdgeComparison.original_rows_complete
#print MicroCFTA.SourceCurrentSameSymbolEdgeComparison.original_rows_complete
#print axioms MicroCFTA.SourceCurrentSameSymbolEdgeComparison.original_rows_complete
