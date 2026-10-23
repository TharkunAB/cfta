import MicroCFTA.SourceCurrentSameSymbolEdgeOriginalRows
import MicroCFTA.SourceCurrentOriginalRowPhysicalMeaning
import MicroCFTA.SourceCurrentAllocatedNativeCoveredQuery
import MicroCFTA.FormulaExecutable

namespace MicroCFTA.SourceCurrentSameSymbolEdgeOriginalRowsCovered
open Cache Language IntersectSchedule InternedConstructorTemplates InternedEdgeResidency
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceRecursiveIntersectionInputView InternedProbeProvenance
open SourceCurrentAllocatedNativePhysicalCompletion (Good)
open SourceEqualityRequiredSemanticCache (SemanticReady)
open SourceCurrentAllocatedNativeAdmissionCache (Covered EdgeCovered)
open SourceCurrentAllocatedNativeAdmissionTrace (ControlCertified)
open SourceCurrentAllocatedNativeFieldClosure (Fields)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Edge" => EdgeValue Symbol Guard
local notation "Wrapper" => SourceCurrentSameSymbolEdgeControl.State
local notation "Stable" => SourceCurrentSameSymbolEdgeStable.Stable
local notation "NativeIdle" => SourceRecursiveIntersectionNative.Idle
local notation "guardHolds" => (@SourceEqualityPCSGuard.holds FullSyntax.Formula FormulaExecutable.formulaDecidableEq)

/-- Complete absent original-row pairs and retain admission of every native request. -/
theorem both_miss_complete [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (bits : Nat) (source : InternedConstructorTemplates.State Symbol Guard)
    (facts : InternedNestedFacts.Facts source)
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inputs : FiniteInput (view source (guardHolds formulas solver)))
    (leftParent rightParent : Value Symbol Guard)
    (leftOriginal : OriginalInput source (inputOf leftParent))
    (rightOriginal : OriginalInput source (inputOf rightParent))
    (leftAvailable : Available source leftParent) (rightAvailable : Available source rightParent)
    (leftClosed : leftParent.free = []) (rightClosed : rightParent.free = [])
    (leftAdmitted : inputs.valid (inputOf leftParent))
    (rightAdmitted : inputs.valid (inputOf rightParent))
    (left right : Edge)
    (leftMember : left ∈ nodeEdges leftParent) (rightMember : right ∈ nodeEdges rightParent)
    (symbols : left.entry.key.symbol = right.entry.key.symbol)
    (before : Wrapper (bits + 2))
    (stable : Stable (view source (guardHolds formulas solver))
      (finiteInputMeaning (view source (guardHolds formulas solver)) inputs)
      (finiteRankedInput (view source (guardHolds formulas solver)) inputs)
      (guardHolds formulas solver) before)
    (missing : before.memo.table (left.entry.identity, right.entry.identity) = none)
    (reverseMissing : before.memo.table (right.entry.identity, left.entry.identity) = none)
    (good : Good before.checked)
    (contextual : SourceCurrentAllocatedNativeContextCache.Contextual
      (view source (guardHolds formulas solver))
      (finiteInputMeaning (view source (guardHolds formulas solver)) inputs)
      (finiteRankedInput (view source (guardHolds formulas solver)) inputs)
      (guardHolds formulas solver) before.checked.native)
    (semantic : SemanticReady before.checked.native.machine.heap)
    (covered : Covered inputs before.checked.native)
    (growth : Grows source before.checked.native.machine.heap)
    (history : Extends source.nodes.issued before.checked.native.machine.heap.nodes.issued)
    (idle : NativeIdle before.checked.native)
    (room : SourceCurrentAllocatedNativeResourceForecast.Room bits
      ⟨source.nodes.next, source.edges.next, before.checked.native.machine.domains.next, 0⟩) :
    let ordered := if right.entry.identity < left.entry.identity then (right, left) else (left, right)
    let request : EdgeRequest Symbol Guard := ⟨IntersectionEmptyDomain.emptyDomain, ordered.1, ordered.2⟩
    ∃ (fuel nativeFuel handle : Nat) (result : Edge) (after : Wrapper (bits + 2)),
      SourceCurrentSameSymbolEdgeControl.execute fuel (.call (left, right) []) before = .done result after ∧
      SourceCurrentAllocatedNativeContextualCompletion.Receipt
        (semanticView := view source (guardHolds formulas solver))
        (model := finiteInputMeaning (view source (guardHolds formulas solver)) inputs)
        (ranked := finiteRankedInput (view source (guardHolds formulas solver)) inputs)
        (semanticHolds := guardHolds formulas solver)
        nativeFuel (.edgeBody request .pure) before.checked result after.checked
        (fun final value => EdgeResident final.heap value)
        (fun _ value => SourceCurrentAllocatedNativeContextCache.EdgeLaw
          (view source (guardHolds formulas solver))
          (finiteInputMeaning (view source (guardHolds formulas solver)) inputs)
          (finiteRankedInput (view source (guardHolds formulas solver)) inputs)
          (guardHolds formulas solver) request value) ∧
      Stable (view source (guardHolds formulas solver))
        (finiteInputMeaning (view source (guardHolds formulas solver)) inputs)
        (finiteRankedInput (view source (guardHolds formulas solver)) inputs)
        (guardHolds formulas solver) after ∧
      NativeIdle after.checked.native ∧
      Extends before.memo.table after.memo.table ∧
      FlatMemoThunk.Returned before.memo after.memo ∧
      after.memo.table (left.entry.identity, right.entry.identity) = some handle ∧
      after.memo.cells handle = some ⟨(left, right), .returned result⟩ ∧
      (right.entry.identity < left.entry.identity →
        ∃ reversedHandle, reversedHandle ≠ handle ∧
          after.memo.table (right.entry.identity, left.entry.identity) = some reversedHandle ∧
          after.memo.cells reversedHandle = some ⟨(right, left), .returned result⟩) ∧
      Covered inputs after.checked.native := by
  dsimp only
  let ordered := if right.entry.identity < left.entry.identity then (right, left) else (left, right)
  let request : EdgeRequest Symbol Guard := ⟨IntersectionEmptyDomain.emptyDomain, ordered.1, ordered.2⟩
  obtain ⟨leftInputs, _⟩ :=
    SourceCurrentOriginalRowPhysicalMeaning.row_inputs_meaning source facts
      (guardHolds formulas solver)
      (finiteInputMeaning (view source (guardHolds formulas solver)) inputs)
      leftParent left leftOriginal leftAvailable leftClosed leftAdmitted leftMember
  obtain ⟨rightInputs, _⟩ :=
    SourceCurrentOriginalRowPhysicalMeaning.row_inputs_meaning source facts
      (guardHolds formulas solver)
      (finiteInputMeaning (view source (guardHolds formulas solver)) inputs)
      rightParent right rightOriginal rightAvailable rightClosed rightAdmitted rightMember
  have rawScope : EdgeScope source ⟨IntersectionEmptyDomain.emptyDomain, left, right⟩ := by
    refine ⟨resident_edges source facts.linked leftParent leftAvailable.resident left leftMember,
      resident_edges source facts.linked rightParent rightAvailable.resident right rightMember,
      ?_, ?_, ?_⟩
    · intro child member
      exact (leftInputs child member).1
    · intro child member
      exact (rightInputs child member).1
    · intro _ member
      cases member
  have rawCovered : EdgeCovered inputs ⟨IntersectionEmptyDomain.emptyDomain, left, right⟩ := by
    exact ⟨⟨leftInputs, rightInputs⟩,
      SourceCurrentAllocatedNativePairAdmission.empty_seen inputs⟩
  have orderedInputs : EdgeScope source request ∧ EdgeCovered inputs request := by
    by_cases swap : right.entry.identity < left.entry.identity
    · simp only [request, ordered, swap, ↓reduceIte]
      exact ⟨⟨rawScope.rightResident, rawScope.leftResident,
        rawScope.right, rawScope.left, rawScope.bindings⟩,
        ⟨⟨rightInputs, leftInputs⟩,
          SourceCurrentAllocatedNativePairAdmission.empty_seen inputs⟩⟩
    · simpa only [request, ordered, swap, ↓reduceIte] using And.intro rawScope rawCovered
  have ready : EdgeReady before.checked.native.machine request := by
    exact ⟨empty_domain _, edge_grows source _ growth _ orderedInputs.1.leftResident,
      edge_grows source _ growth _ orderedInputs.1.rightResident⟩
  have fields : Fields (.edgeBody request .pure) before.checked := by
    exact ⟨ready, fun _ => True.intro⟩
  have certificate : ControlCertified source (guardHolds formulas solver) inputs
      (.edgeBody request .pure) before.checked.native.machine
      (fun final value => EdgeResident final.heap value) := by
    refine ⟨orderedInputs.1, orderedInputs.2, ?_⟩
    intro _ _ _ _ _ resident
    exact resident
  obtain ⟨fuel, nativeFuel, handle, result, after, done, receipt, afterStable, afterIdle,
      tables, retained, stored, cell, reversed⟩ :=
    SourceCurrentSameSymbolEdgeOriginalRows.both_miss_complete bits source facts formulas solver
      (finiteInputMeaning (view source (guardHolds formulas solver)) inputs)
      (finiteRankedInput (view source (guardHolds formulas solver)) inputs)
      leftParent rightParent leftOriginal rightOriginal leftAvailable rightAvailable
      leftClosed rightClosed left right leftMember rightMember symbols before stable
      missing reverseMissing good contextual semantic growth history idle room
  have finalCovered : Covered inputs after.checked.native := by
    exact (SourceCurrentAllocatedNativeAdmissionTrace.Trace.covered source
      (guardHolds formulas solver) inputs
      (SourceCurrentAllocatedNativeCoveredQuery.branches source facts (guardHolds formulas solver) inputs)
      receipt.trace (fun final value => EdgeResident final.heap value)
      good semantic growth history fields covered certificate).1
  exact ⟨fuel, nativeFuel, handle, result, after, done, receipt, afterStable, afterIdle,
    tables, retained, stored, cell, reversed, finalCovered⟩

end MicroCFTA.SourceCurrentSameSymbolEdgeOriginalRowsCovered
