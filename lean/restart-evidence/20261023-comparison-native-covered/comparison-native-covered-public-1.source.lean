import MicroCFTA.SourceCurrentSameSymbolEdgeComparisonDomains
import MicroCFTA.SourceCurrentSameSymbolEdgeHitReadback
import MicroCFTA.SourceCurrentOriginalRowPhysicalMeaning
import MicroCFTA.SourceCurrentAllocatedNativeCoveredQuery
import MicroCFTA.FormulaExecutable

namespace MicroCFTA.SourceCurrentSameSymbolEdgeComparisonCovered
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

/-- Complete an original-row comparison and retain native request admission. -/
theorem original_rows_complete [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
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
    (initialDomains : Cache.State IntersectionFlatMemoKeyDomain.DomainKey)
    (initialValid : Cache.Valid initialDomains)
    (before : Wrapper (bits + 2))
    (stable : Stable (view source (guardHolds formulas solver))
      (finiteInputMeaning (view source (guardHolds formulas solver)) inputs)
      (finiteRankedInput (view source (guardHolds formulas solver)) inputs)
      (guardHolds formulas solver) before)
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
    (allocations : SourceRecursiveIntersectionDomainAllocation.Trace
      (SourceRecursiveIntersectionSourceInventory.domains source)
      initialDomains before.checked.native.machine.domains)
    (idle : NativeIdle before.checked.native)
    (room : SourceCurrentAllocatedNativeResourceForecast.Room bits
      ⟨source.nodes.next, source.edges.next,
        initialDomains.next + (SourceRecursiveIntersectionSourceInventory.domains source).length, 0⟩) :
    let ordered := if right.entry.identity < left.entry.identity then (right, left) else (left, right)
    let request : EdgeRequest Symbol Guard := ⟨IntersectionEmptyDomain.emptyDomain, ordered.1, ordered.2⟩
    ∃ (fuel : Nat) (result : Edge) (after : Wrapper (bits + 2)),
      SourceCurrentSameSymbolEdgeControl.execute fuel (.call (left, right) []) before = .done result after ∧
      EdgeResident after.checked.native.machine.heap result ∧
      SourceCurrentAllocatedNativeContextCache.EdgeLaw
        (view source (guardHolds formulas solver))
        (finiteInputMeaning (view source (guardHolds formulas solver)) inputs)
        (finiteRankedInput (view source (guardHolds formulas solver)) inputs)
        (guardHolds formulas solver) request result ∧
      Good after.checked ∧
      SourceCurrentAllocatedNativeContextCache.Contextual
        (view source (guardHolds formulas solver))
        (finiteInputMeaning (view source (guardHolds formulas solver)) inputs)
        (finiteRankedInput (view source (guardHolds formulas solver)) inputs)
        (guardHolds formulas solver) after.checked.native ∧
      SemanticReady after.checked.native.machine.heap ∧
      Extension before.checked.native.machine after.checked.native.machine ∧
      Stable (view source (guardHolds formulas solver))
        (finiteInputMeaning (view source (guardHolds formulas solver)) inputs)
        (finiteRankedInput (view source (guardHolds formulas solver)) inputs)
        (guardHolds formulas solver) after ∧
      NativeIdle after.checked.native ∧
      Extends before.memo.table after.memo.table ∧
      FlatMemoThunk.Returned before.memo after.memo ∧
      SourceRecursiveIntersectionDomainAllocation.Trace
        (SourceRecursiveIntersectionSourceInventory.domains source)
        initialDomains after.checked.native.machine.domains ∧
      Covered inputs after.checked.native := by
  classical
  dsimp only
  let inventory : List IntersectionFlatMemoKeyDomain.DomainKey :=
    SourceRecursiveIntersectionSourceInventory.domains source
  let ordered : Edge × Edge := if right.entry.identity < left.entry.identity then (right, left) else (left, right)
  let request : EdgeRequest Symbol Guard := ⟨IntersectionEmptyDomain.emptyDomain, ordered.1, ordered.2⟩
  obtain ⟨fuel, result, after, done, resident, law, afterGood, afterContextual,
    afterSemantic, extension, afterStable, afterIdle, tables, retained, afterAllocations⟩ :=
    SourceCurrentSameSymbolEdgeComparisonDomains.original_rows_complete bits source facts formulas solver
      (finiteInputMeaning (view source (guardHolds formulas solver)) inputs)
      (finiteRankedInput (view source (guardHolds formulas solver)) inputs)
      leftParent rightParent leftOriginal rightOriginal leftAvailable rightAvailable
      leftClosed rightClosed left right leftMember rightMember symbols initialDomains initialValid
      before stable good contextual semantic growth history allocations idle room
  have finalCovered : Covered inputs after.checked.native := by
    by_cases present :
      (∃ handle, before.memo.table (left.entry.identity, right.entry.identity) = some handle) ∨
      (∃ handle, before.memo.table (right.entry.identity, left.entry.identity) = some handle)
    ·
      have hitChecked : after.checked = before.checked := by
        exact SourceCurrentSameSymbolEdgeHitReadback.completed_hit_checked
          (view source (guardHolds formulas solver))
          (finiteInputMeaning (view source (guardHolds formulas solver)) inputs)
          (finiteRankedInput (view source (guardHolds formulas solver)) inputs)
          (guardHolds formulas solver) fuel left right result before after stable present done
      simpa only [hitChecked] using covered
    ·
      have missing : before.memo.table (left.entry.identity, right.entry.identity) = none := by
        cases found : before.memo.table (left.entry.identity, right.entry.identity) with
        | none => rfl
        | some handle => exact False.elim (present (Or.inl ⟨handle, found⟩))
      have reverseMissing : before.memo.table (right.entry.identity, left.entry.identity) = none := by
        cases reverseFound : before.memo.table (right.entry.identity, left.entry.identity) with
        | none => rfl
        | some handle => exact False.elim (present (Or.inr ⟨handle, reverseFound⟩))
      have leftInputs : ∀ child ∈ left.children,
          Original child ∧ inputs.valid (inputOf child) := by
        exact (SourceCurrentOriginalRowPhysicalMeaning.row_inputs_meaning source facts
          (guardHolds formulas solver)
          (finiteInputMeaning (view source (guardHolds formulas solver)) inputs)
          leftParent left leftOriginal leftAvailable leftClosed leftAdmitted leftMember).1
      have rightInputs : ∀ child ∈ right.children,
          Original child ∧ inputs.valid (inputOf child) := by
        exact (SourceCurrentOriginalRowPhysicalMeaning.row_inputs_meaning source facts
          (guardHolds formulas solver)
          (finiteInputMeaning (view source (guardHolds formulas solver)) inputs)
          rightParent right rightOriginal rightAvailable rightClosed rightAdmitted rightMember).1
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
      have resources : SourceCurrentAllocatedRecursivePrefixAdmission.Resources
          bits source inventory initialDomains := by
        exact ⟨facts, SourceCurrentAllocatedRecursiveDomainCode.source_closed source facts,
          initialValid, room.1, room.2.1, Nat.lt_of_le_of_lt (Nat.le_add_right _ _) room.2.2⟩
      have current : SourceCurrentAllocatedRecursivePrefixState.Current
          source inventory initialDomains before.checked := by
        exact ⟨good, semantic, growth, history, allocations⟩
      have physicalCertificate : SourceCurrentAllocatedRecursivePrefixControl.Certified
          source inventory (.edgeBody request .pure) before.checked.native.machine
          (fun final value => EdgeResident final.heap value) := by
        exact SourceCurrentAllocatedRecursivePrefixControl.edge_body source inventory request
          before.checked.native.machine orderedInputs.1
          (SourceRecursiveIntersectionSourceInventory.empty_mem source) ready
      have admissionCertificate : ControlCertified source (guardHolds formulas solver) inputs
          (.edgeBody request .pure) before.checked.native.machine
          (fun final value => EdgeResident final.heap value) := by
        refine ⟨orderedInputs.1, orderedInputs.2, ?_⟩
        intro _ _ _ _ _ resident
        exact resident
      obtain ⟨nativeFuel, _, steps, _, _, _, _⟩ :=
        SourceCurrentSameSymbolEdgeControl.miss_readback fuel left right result before after
          (FlatMemoThunk.Valid.map before.memo _ _ _ stable.valid (fun _ _ => True.intro))
          missing reverseMissing done
      have physicalRun : SourceCurrentAllocatedRecursivePrefixReceipt.Receipt
          source inventory initialDomains nativeFuel (.edgeBody request .pure) before.checked
          (.code (.pure result)) after.checked (fun final value => EdgeResident final.heap value) := by
        exact SourceCurrentAllocatedRecursivePrefixAdmission.prefixes resources nativeFuel
          (.edgeBody request .pure) before.checked (.code (.pure result)) after.checked
          (fun final value => EdgeResident final.heap value) current physicalCertificate fields steps
      exact (SourceCurrentAllocatedNativeAdmissionTrace.Trace.covered source
        (guardHolds formulas solver) inputs
        (SourceCurrentAllocatedNativeCoveredQuery.branches source facts (guardHolds formulas solver) inputs)
        physicalRun.trace (fun final value => EdgeResident final.heap value)
        good semantic growth history fields covered admissionCertificate).1
  exact ⟨fuel, result, after, done, resident, law, afterGood, afterContextual,
    afterSemantic, extension, afterStable, afterIdle, tables, retained, afterAllocations, finalCovered⟩

end MicroCFTA.SourceCurrentSameSymbolEdgeComparisonCovered

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
#check @MicroCFTA.SourceCurrentSameSymbolEdgeComparisonCovered.original_rows_complete
#print MicroCFTA.SourceCurrentSameSymbolEdgeComparisonCovered.original_rows_complete
#print axioms MicroCFTA.SourceCurrentSameSymbolEdgeComparisonCovered.original_rows_complete
