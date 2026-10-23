import MicroCFTA.SourceCurrentOriginalRowClusterExecution
import MicroCFTA.SourceCurrentSameSymbolEdgeComparisonCovered
import MicroCFTA.SourceCurrentSameSymbolEdgeRequestAdmission
import MicroCFTA.SourceCurrentAllocatedNativeInventoryState
import MicroCFTA.FormulaExecutable

namespace MicroCFTA.SourceCurrentOriginalRowClusterAdmissionBoundary
open Cache Language IntersectSchedule InternedConstructorTemplates InternedEdgeResidency
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionInputView InternedProbeProvenance
open SourceCurrentAllocatedNativePhysicalCompletion (Good)
open SourceEqualityRequiredSemanticCache (SemanticReady)
open SourceCurrentAllocatedNativeInventoryState (Inventory At)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Edge" => EdgeValue Symbol Guard
local notation "Wrapper" => SourceCurrentSameSymbolEdgeControl.State
local notation "ScanControl" => SourceCurrentOriginalRowClusterScan.Control
local notation "NativeIdle" => SourceRecursiveIntersectionNative.Idle
local notation "guardHolds" => (@SourceEqualityPCSGuard.holds FullSyntax.Formula FormulaExecutable.formulaDecidableEq)
variable (inventory : Inventory)
variable (formulas : SourceGuards.Formulas FullSyntax.Formula)
variable (solver : SourceGuards.Entailment FullSyntax.Formula)
local notation "holds" => guardHolds formulas solver
local notation "inputs" => inventory.inputs holds
local notation "inputView" => view inventory.source holds
local notation "inputModel" => finiteInputMeaning inputView inputs
local notation "inputRanked" => finiteRankedInput inputView inputs
local notation "Stable" => SourceCurrentSameSymbolEdgeStable.Stable inputView inputModel inputRanked holds
local notation "Current" => At formulas solver inventory
local notation "PairInputs" => (fun pair : Edge × Edge =>
  SourceCurrentAllocatedNativeContextCache.EdgeInputs inputView inputModel
    (SourceRecursiveIntersectionThunks.EdgeRequest.mk IntersectionEmptyDomain.emptyDomain (Prod.fst pair) (Prod.snd pair)))

/-- Complete one scan boundary with the same inventory and captured request admission. -/
theorem boundary_complete
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (bits : Nat) (parent : Value Symbol Guard) (member : parent ∈ inventory.roots)
    (symbol : Symbol)
    (initialDomains : Cache.State IntersectionFlatMemoKeyDomain.DomainKey)
    (initialValid : Cache.Valid initialDomains)
    (pivot : Edge) (remaining incomparableReversed keptReversed : List Edge)
    (before : Wrapper (bits + 2))
    (stable : Stable before) (good : Good before.checked)
    (current : Current before.checked)
    (semantic : SemanticReady before.checked.native.machine.heap)
    (allocations : SourceRecursiveIntersectionDomainAllocation.Trace
      (SourceRecursiveIntersectionSourceInventory.domains inventory.source)
      initialDomains before.checked.native.machine.domains)
    (idle : NativeIdle before.checked.native)
    (admitted : ∀ (handle : Nat) (pair : Edge × Edge) (value : Edge),
      before.memo.cells handle = some ⟨pair, .returned value⟩ →
      PairInputs (if pair.2.entry.identity < pair.1.entry.identity then (pair.2, pair.1) else pair))
    (room : SourceCurrentAllocatedNativeResourceForecast.Room bits
      ⟨inventory.source.nodes.next, inventory.source.edges.next,
        initialDomains.next + (SourceRecursiveIntersectionSourceInventory.domains inventory.source).length, 0⟩) :
    let rows := (nodeEdges parent).filter (fun edge => decide (edge.entry.key.symbol = symbol))
    pivot ∈ rows → (∀ edge ∈ remaining, edge ∈ rows) →
    (∀ edge ∈ incomparableReversed, edge ∈ rows) →
    ∃ (used : Nat) (next newKept : List Edge) (after : Wrapper (bits + 2)),
      0 < used ∧
      SourceCurrentOriginalRowClusterScan.execute used
        (.scan pivot remaining incomparableReversed keptReversed) before =
          .yielded (.cluster next newKept) after ∧
      next.length < 1 + remaining.length + incomparableReversed.length ∧
      (∀ edge ∈ next, edge ∈ rows) ∧
      Good after.checked ∧ Current after.checked ∧
      SemanticReady after.checked.native.machine.heap ∧ Stable after ∧
      NativeIdle after.checked.native ∧
      SourceRecursiveIntersectionDomainAllocation.Trace
        (SourceRecursiveIntersectionSourceInventory.domains inventory.source)
        initialDomains after.checked.native.machine.domains ∧
      ∀ (handle : Nat) (pair : Edge × Edge) (value : Edge),
        after.memo.cells handle = some ⟨pair, .returned value⟩ →
        PairInputs (if pair.2.entry.identity < pair.1.entry.identity then (pair.2, pair.1) else pair) := by
  dsimp only
  have parentOriginal : OriginalInput inventory.source (inputOf parent) := by
    exact ⟨parent, inventory.originals parent member, inventory.available parent member,
      (inventory.originals parent member).codec parent⟩
  have parentAdmitted : (inputs).valid (inputOf parent) := by
    exact SourceCurrentAllocatedNativeInputInventoryModels.root_valid inventory.source inventory.facts
      holds inventory.roots inventory.originals inventory.available inventory.closed parent member
  revert stable good current semantic allocations idle admitted
  induction remaining generalizing incomparableReversed keptReversed before with
  | nil =>
      intro stable good current semantic allocations idle admitted
        _pivotMember _remainingMembers incomparableMembers
      refine ⟨1, incomparableReversed.reverse, pivot :: keptReversed, before, by omega,
        rfl, ?_, ?_, good, current, semantic, stable, idle, allocations, admitted⟩
      · simp only [List.length_reverse, List.length_nil]
        omega
      · simpa only [List.mem_reverse] using incomparableMembers
  | cons candidate tail ih =>
      intro stable good current semantic allocations idle admitted
        pivotMember remainingMembers incomparableMembers
      have candidateMember : candidate ∈
          (nodeEdges parent).filter (fun edge => decide (edge.entry.key.symbol = symbol)) := by
        exact remainingMembers candidate List.mem_cons_self
      have tailMembers : ∀ edge ∈ tail, edge ∈
          (nodeEdges parent).filter (fun row => decide (row.entry.key.symbol = symbol)) := by
        intro edge present
        exact remainingMembers edge (List.mem_cons_of_mem candidate present)
      have symbols : pivot.entry.key.symbol = candidate.entry.key.symbol := by
        exact (of_decide_eq_true (List.mem_filter.mp pivotMember).2).trans
          (of_decide_eq_true (List.mem_filter.mp candidateMember).2).symm
      obtain ⟨fuel, common, middle, done, _resident, _law, midGood, midContextual,
          midSemantic, extension, midStable, midIdle, _tables, _retained, midTrace, midCovered⟩ :=
        SourceCurrentSameSymbolEdgeComparisonCovered.original_rows_complete bits inventory.source
          inventory.facts formulas solver inputs parent parent parentOriginal parentOriginal
          (inventory.available parent member) (inventory.available parent member)
          (inventory.closed parent member) (inventory.closed parent member)
          parentAdmitted parentAdmitted pivot candidate (List.mem_filter.mp pivotMember).1
          (List.mem_filter.mp candidateMember).1 symbols initialDomains initialValid before stable
          good current.contextual semantic current.covered current.growth current.history allocations idle room
      have known : PairInputs (pivot, candidate) := by
        exact ⟨(SourceCurrentOriginalRowPhysicalMeaning.row_inputs_meaning inventory.source
          inventory.facts holds inputModel parent pivot parentOriginal
          (inventory.available parent member) (inventory.closed parent member) parentAdmitted
          (List.mem_filter.mp pivotMember).1).1,
          (SourceCurrentOriginalRowPhysicalMeaning.row_inputs_meaning inventory.source
            inventory.facts holds inputModel parent candidate parentOriginal
            (inventory.available parent member) (inventory.closed parent member) parentAdmitted
            (List.mem_filter.mp candidateMember).1).1⟩
      have middleAt : Current middle.checked := by
        exact ⟨midContextual, midCovered, grows_trans current.growth extension.heap,
          extends_trans current.history extension.history⟩
      have middleAdmission : ∀ (handle : Nat) (pair : Edge × Edge) (value : Edge),
          middle.memo.cells handle = some ⟨pair, .returned value⟩ →
          PairInputs (if pair.2.entry.identity < pair.1.entry.identity then (pair.2, pair.1) else pair) := by
        exact (SourceCurrentSameSymbolEdgeRequestAdmission.completed_admitted inputView inputModel
          inputRanked holds pivot candidate common before middle fuel stable admitted known done).2
      obtain ⟨used, _positive, _bound, resumed⟩ :=
        SourceCurrentOriginalRowClusterScan.comparison_lift fuel pivot candidate common tail
          incomparableReversed keptReversed (.call (pivot, candidate) []) before middle done
      have prefixRun : SourceCurrentOriginalRowClusterScan.execute (used + 1)
          (.scan pivot (candidate :: tail) incomparableReversed keptReversed) before =
          .yielded
            (if common.entry.identity = candidate.entry.identity then
               .scan pivot tail incomparableReversed keptReversed
             else if common.entry.identity = pivot.entry.identity then
               .cluster (candidate :: (incomparableReversed.reverse ++ tail)) keptReversed
             else .scan pivot tail (candidate :: incomparableReversed) keptReversed) middle := by
        simpa only [SourceCurrentOriginalRowClusterScan.execute,
          SourceCurrentOriginalRowClusterScan.step] using resumed
      by_cases promoted : common.entry.identity ≠ candidate.entry.identity ∧
          common.entry.identity = pivot.entry.identity
      · rcases promoted with ⟨notDropped, promoted⟩
        refine ⟨used + 1, candidate :: (incomparableReversed.reverse ++ tail), keptReversed,
          middle, by omega, ?_, ?_, ?_, midGood, middleAt, midSemantic, midStable,
          midIdle, midTrace, middleAdmission⟩
        · simpa only [ite_eq_right notDropped, ite_eq_left promoted] using prefixRun
        · simp only [List.length_cons, List.length_append, List.length_reverse]
          omega
        · intro edge present
          rcases List.mem_cons.mp present with rfl | present
          · exact candidateMember
          · rcases List.mem_append.mp present with present | present
            · exact incomparableMembers edge (List.mem_reverse.mp present)
            · exact tailMembers edge present
      · let nextIncomparable : List Edge :=
          if common.entry.identity = candidate.entry.identity then
            incomparableReversed else candidate :: incomparableReversed
        have nextMembers : ∀ edge ∈ nextIncomparable, edge ∈
            (nodeEdges parent).filter (fun row => decide (row.entry.key.symbol = symbol)) := by
          dsimp only [nextIncomparable]
          split
          · exact incomparableMembers
          · intro edge present
            rcases List.mem_cons.mp present with rfl | present
            · exact candidateMember
            · exact incomparableMembers edge present
        have nextLength : nextIncomparable.length ≤ incomparableReversed.length + 1 := by
          dsimp only [nextIncomparable]
          split
          · omega
          · simp only [List.length_cons]
            omega
        have resumedScan : SourceCurrentOriginalRowClusterScan.execute (used + 1)
            (.scan pivot (candidate :: tail) incomparableReversed keptReversed) before =
            .yielded (.scan pivot tail nextIncomparable keptReversed) middle := by
          by_cases dropped : common.entry.identity = candidate.entry.identity
          · simpa only [dropped, ↓reduceIte, nextIncomparable] using prefixRun
          · have notPromoted : common.entry.identity ≠ pivot.entry.identity := by
              exact fun equal => promoted ⟨dropped, equal⟩
            simpa only [dropped, notPromoted, ↓reduceIte, nextIncomparable] using prefixRun
        obtain ⟨more, next, newKept, after, _positive, scanned, shorter,
            nextMembers, afterGood, afterAt, afterSemantic, afterStable,
            afterIdle, afterTrace, afterAdmission⟩ :=
          ih (incomparableReversed := nextIncomparable) (keptReversed := keptReversed)
            (before := middle) midStable midGood middleAt midSemantic midTrace midIdle
            middleAdmission pivotMember tailMembers nextMembers
        refine ⟨used + 1 + more, next, newKept, after, by omega, ?_, ?_, nextMembers,
          afterGood, afterAt, afterSemantic, afterStable, afterIdle, afterTrace, afterAdmission⟩
        · rw [SourceCurrentOriginalRowClusterExecution.yielded_add (used + 1) more
            _ _ _ _ resumedScan]
          exact scanned
        · simp only [List.length_cons]
          omega

end MicroCFTA.SourceCurrentOriginalRowClusterAdmissionBoundary

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
#check @MicroCFTA.SourceCurrentOriginalRowClusterAdmissionBoundary.boundary_complete
#print MicroCFTA.SourceCurrentOriginalRowClusterAdmissionBoundary.boundary_complete
#print axioms MicroCFTA.SourceCurrentOriginalRowClusterAdmissionBoundary.boundary_complete
