import MicroCFTA.SourceCurrentOriginalRowClusterAdmissionBoundary

namespace MicroCFTA.SourceCurrentOriginalRowClusterAdmission
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

/-- Complete a generalized original-row cluster with the same admission certificates. -/
theorem cluster_complete
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (bits : Nat) (parent : Value Symbol Guard) (member : parent ∈ inventory.roots)
    (symbol : Symbol)
    (initialDomains : Cache.State IntersectionFlatMemoKeyDomain.DomainKey)
    (initialValid : Cache.Valid initialDomains)
    (candidates keptReversed : List Edge)
    (members : ∀ edge ∈ candidates,
      edge ∈ (nodeEdges parent).filter (fun row => decide (row.entry.key.symbol = symbol)))
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
    ∃ (fuel : Nat) (kept : List Edge) (after : Wrapper (bits + 2)),
      SourceCurrentOriginalRowClusterScan.execute fuel
        (.cluster candidates keptReversed) before = .done kept after ∧
      Current after.checked ∧
      ∀ (handle : Nat) (pair : Edge × Edge) (value : Edge),
        after.memo.cells handle = some ⟨pair, .returned value⟩ →
        PairInputs (if pair.2.entry.identity < pair.1.entry.identity then (pair.2, pair.1) else pair) := by
  induction sized : candidates.length using Nat.strongRecOn generalizing candidates keptReversed before with
  | ind size ih =>
      cases candidates with
      | nil =>
          exact ⟨1, keptReversed.reverse, before, rfl, current, admitted⟩
      | cons pivot tail =>
        have pivotMember : pivot ∈
            (nodeEdges parent).filter (fun edge => decide (edge.entry.key.symbol = symbol)) := by
          exact members pivot List.mem_cons_self
        have tailMembers : ∀ edge ∈ tail, edge ∈
            (nodeEdges parent).filter (fun row => decide (row.entry.key.symbol = symbol)) := by
          intro edge present
          exact members edge (List.mem_cons_of_mem pivot present)
        obtain ⟨used, next, newKept, middle, _positive, scanned, shorter,
            nextMembers, midGood, midAt, midSemantic, midStable,
            midIdle, midTrace, midAdmission⟩ :=
          SourceCurrentOriginalRowClusterAdmissionBoundary.boundary_complete inventory formulas solver
            bits parent member symbol initialDomains initialValid pivot tail [] keptReversed before
            stable good current semantic allocations idle admitted room pivotMember tailMembers
            (by simp only [List.not_mem_nil, false_implies, implies_true])
        have smaller : next.length < size := by
          simp only [List.length_cons, List.length_nil] at shorter sized
          omega
        obtain ⟨fuel, kept, after, done, finalAt, finalAdmission⟩ :=
          ih next.length smaller next newKept nextMembers middle midStable midGood midAt
            midSemantic midTrace midIdle midAdmission rfl
        have prefixRun : SourceCurrentOriginalRowClusterScan.execute (used + 1)
            (.cluster (pivot :: tail) keptReversed) before =
            .yielded (.cluster next newKept) middle := by
          simpa only [SourceCurrentOriginalRowClusterScan.execute,
            SourceCurrentOriginalRowClusterScan.step] using scanned
        refine ⟨used + 1 + fuel, kept, after, ?_, finalAt, finalAdmission⟩
        rw [SourceCurrentOriginalRowClusterExecution.yielded_add (used + 1) fuel _ _ _ _ prefixRun]
        exact done

/-- Retain both admission certificates at the exact supplied completed cluster state. -/
theorem completed_admitted
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (bits : Nat) (parent : Value Symbol Guard) (member : parent ∈ inventory.roots)
    (symbol : Symbol)
    (initialDomains : Cache.State IntersectionFlatMemoKeyDomain.DomainKey)
    (initialValid : Cache.Valid initialDomains)
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
        initialDomains.next + (SourceRecursiveIntersectionSourceInventory.domains inventory.source).length, 0⟩)
    (fuel : Nat) (kept : List Edge) (after : Wrapper (bits + 2))
    (observed : SourceCurrentOriginalRowClusterScan.execute fuel
      (.cluster ((nodeEdges parent).filter (fun edge => decide (edge.entry.key.symbol = symbol))) [])
      before = .done kept after) :
    Current after.checked ∧
    ∀ (handle : Nat) (pair : Edge × Edge) (value : Edge),
      after.memo.cells handle = some ⟨pair, .returned value⟩ →
      PairInputs (if pair.2.entry.identity < pair.1.entry.identity then (pair.2, pair.1) else pair) := by
  obtain ⟨otherFuel, otherKept, otherAfter, otherDone, otherAt, otherAdmission⟩ :=
    cluster_complete inventory formulas solver bits parent member symbol initialDomains initialValid
      ((nodeEdges parent).filter (fun edge => decide (edge.entry.key.symbol = symbol))) []
      (fun _ present => present) before stable good current semantic allocations idle admitted room
  obtain ⟨_sameKept, sameState⟩ :=
    SourceCurrentOriginalRowClusterExecution.completed_unique otherFuel fuel
      (.cluster ((nodeEdges parent).filter (fun edge => decide (edge.entry.key.symbol = symbol))) [])
      before otherAfter after otherKept kept otherDone observed
  cases sameState
  exact ⟨otherAt, otherAdmission⟩

end MicroCFTA.SourceCurrentOriginalRowClusterAdmission

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
#check @MicroCFTA.SourceCurrentOriginalRowClusterAdmission.cluster_complete
#print MicroCFTA.SourceCurrentOriginalRowClusterAdmission.cluster_complete
#print axioms MicroCFTA.SourceCurrentOriginalRowClusterAdmission.cluster_complete
#check @MicroCFTA.SourceCurrentOriginalRowClusterAdmission.completed_admitted
#print MicroCFTA.SourceCurrentOriginalRowClusterAdmission.completed_admitted
#print axioms MicroCFTA.SourceCurrentOriginalRowClusterAdmission.completed_admitted
