import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryParentResources
import MicroCFTA.SourceCurrentAllocatedParentWorkerStability
set_option linter.all true
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
set_option pp.proofs true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000
namespace MicroCFTA.ParentResourceIndependentChecks
open Cache Language InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open SourceCurrentAllocatedNativeInventoryState (Inventory At)
open SourceCurrentConjunctionClassScan (Ready)
open SourceCurrentAllocatedParentEdge (Edge Receipt)
open SourceCurrentAllocatedParentEdgeActual (Reads)
open SourceCurrentAllocatedFiniteOrdinaryNativeProfile (ChildrenShape EdgeShape)
open SourceCurrentAllocatedFiniteOrdinaryRequired (EdgeNarrow)
open SourceCurrentAllocatedFiniteOrdinaryConstructorWorkTrace (Trace nodeRequests_append edgeRequests_append)
open SourceCurrentAllocatedFiniteOrdinaryReservations (nodeRequests edgeRequests)
open MergedOrdinaryHeight (childrenHeight)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Allocated" => SourceEqualityConjoinAllocation.Constraint FullSyntax.Formula
local notation "EqValue" => SourceEqualityConstraintAllocation.Value
local notation "Operations" => SourceEqualityConstraintMemoAllocation.State
local notation "Memo" => SourceCurrentMemoMergeGraph.Memo Symbol Guard
local notation "Fourth" => SourceCurrentEmptinessMemo.Memo
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Valid" => EndpointMemoGateTrace.Valid
local notation "PhysicalStored" => SourceCurrentMemoMergeEffects.Stored
local notation "Profiles" => SourceCurrentAllocatedFiniteOrdinaryMergeProfileCache.Stored
local notation "NativeStored" => SourceCurrentAllocatedFiniteOrdinaryStored.Stored
local notation "OutputStored" => SourceCurrentAllocatedFiniteOrdinaryOutputStored.Stored
local notation "Capacity" => SourceCurrentAllocatedFiniteOrdinaryCapacity.Capacity
local notation "contradictory" => SourceEqualityMkEdgeAllocation.contradictory
local notation "raw" => SourceEqualityConjoinAllocation.readback
local notation "prefixState" => SourceCurrentAllocatedPrecheck.state
local notation "runPrefix" => SourceEqualityPartialPrecheckAllocation.run

open SourceCurrentAllocatedFiniteOrdinaryParentResources (nodeBudget edgeBudget outputRows outputArity)
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq (Value Symbol Guard)]
theorem constructed_raw_rejection (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (inventory : Inventory)
    (bits budget : Nat) (original : EdgeValue Symbol Guard) (loaded : Allocated) (inherited : EqValue)
    (before : Checked (bits + 2)) (fourth : Fourth) (memo : Memo)
    (ready : Ready before) (admitted : At formulas solver inventory before)
    (test : contradictory original.entry.key.constraint = true)
    (correct : SourceCurrentEmptinessMemo.Correct formulas solver before.native.machine.heap fourth)
    (physical : PhysicalStored before.native.machine.heap memo) (profiles : Profiles memo)
    (native : NativeStored before.native) (output : OutputStored before.native)
    (covered : ∀ ambient, SourceCurrentMemoMergeLanguage.CacheCovers (SourceEqualityPCSGuard.holds formulas solver) ambient memo)
    (memos : Memos) (valid : Valid before.native.machine.heap memos) (rows arity : Nat)
    (nodes : before.native.machine.heap.nodes.next ≤ 2 ^ bits)
    (edges : before.native.machine.heap.edges.next + 1 ≤ 2 ^ (bits + 2)) :
    let result := (SourceCurrentAllocatedMkEdge.reject original.entry.key.symbol before).1
    let after := (SourceCurrentAllocatedMkEdge.reject original.entry.key.symbol before).2
    ∃ requests, ∃ actual : Edge budget original.entry.key.symbol original.entry.key.constraint loaded inherited
        original.children before fourth memo result after fourth memo,
      Reads formulas solver actual memos memos ∧
      Receipt formulas solver inventory original.entry.key.symbol original.entry.key.constraint loaded inherited
        original.children before result after fourth fourth memo memo memos ∧
      SourceCurrentAllocatedParentWorkerCompletion.StableRun
        (fun g s r e p h m c n => SourceCurrentAllocatedParentWorker.edge g s r e p h m c n budget
          original.entry.key.symbol original.entry.key.constraint inherited original.children before fourth memo) result after fourth memo ∧
      NativeStored after.native ∧ OutputStored after.native ∧ Profiles memo ∧ EdgeShape rows (max arity 1) result ∧
      EdgeNarrow original result ∧ Trace before.native.machine.heap after.native.machine.heap requests ∧
      nodeRequests requests = 0 ∧ edgeRequests requests = 1 ∧ Capacity bits after ∧
      after.native.machine.heap.nodes.next = before.native.machine.heap.nodes.next ∧
      after.native.machine.heap.edges.next ≤ before.native.machine.heap.edges.next + 1 ∧
      SourceCurrentAllocatedParentWorker.edge 0 0 0 0 0 0 0 0 0 budget original.entry.key.symbol
        original.entry.key.constraint inherited original.children before fourth memo = .done result after fourth memo ∧
      ∀ ambient term, ¬ InternedGuardedLanguage.edgeMeaning (SourceEqualityPCSGuard.holds formulas solver) ambient result term := by
  obtain ⟨requests, actual, reads, receipt, stable, finalNative, finalOutput, finalProfiles, produced,
    narrowed, trace, nodeCount, edgeCount, capacity, nodeSupply, edgeSupply⟩ :=
    SourceCurrentAllocatedFiniteOrdinaryParentResources.rejected formulas solver inventory bits budget original loaded inherited before fourth memo ready admitted test correct physical profiles native output covered memos valid rows arity nodes edges
  refine ⟨requests, actual, reads, receipt, stable, finalNative, finalOutput, finalProfiles, produced,
    narrowed, trace, nodeCount, edgeCount, capacity, nodeSupply, edgeSupply, ?_, ?_⟩
  · simp only [SourceCurrentAllocatedParentWorker.edge, test, ↓reduceIte]
  · exact (SourceCurrentAllocatedMkEdge.reject_correct formulas solver inventory original.entry.key.symbol before ready admitted).empty
      (SourceEqualityPCSGuard.holds formulas solver)

theorem supplied_success_accounted (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (inventory : Inventory)
    (bits budget : Nat) (original : EdgeValue Symbol Guard) (loaded : Allocated) (inherited : EqValue)
    (before : Checked (bits + 2)) (fourth : Fourth) (memo : Memo)
    (ready : Ready before) (admitted : At formulas solver inventory before)
    (cached : SourceEqualityGuardReadback.Cached original.entry.key.constraint.equalities)
    (found : SourceEqualityConstraintFieldLookup.load original.entry.key.constraint before.operations.constraints = .ok (some loaded))
    (inheritedReady : SourceEqualityConstraintAllocation.Ready before.operations.constraints inherited)
    (available : Values before.native.machine.heap original.children)
    (correct : SourceCurrentEmptinessMemo.Correct formulas solver before.native.machine.heap fourth)
    (physical : PhysicalStored before.native.machine.heap memo) (profiles : Profiles memo)
    (native : NativeStored before.native) (output : OutputStored before.native)
    (covered : ∀ ambient, SourceCurrentMemoMergeLanguage.CacheCovers (SourceEqualityPCSGuard.holds formulas solver) ambient memo)
    (memos : Memos) (valid : Valid before.native.machine.heap memos)
    (rows arity count depth bound : Nat) (profile : ChildrenShape rows arity original.children)
    (lengthBound : original.children.length ≤ count)
    (pathsBound : ∀ records, (runPrefix loaded.stored loaded.guard inherited before.operations).1 = .ok (.classes records) →
      ∀ record ∈ records, ∀ path ∈ record.paths, path.length ≤ depth)
    (heightBound : childrenHeight original.children ≤ bound)
    (nodes : before.native.machine.heap.nodes.next + nodeBudget original.entry.key.constraint loaded inherited before.operations rows arity count depth bound ≤ 2 ^ bits)
    (edges : before.native.machine.heap.edges.next + edgeBudget original.entry.key.constraint loaded inherited before.operations rows arity count depth bound ≤ 2 ^ (bits + 2))
    (g s r e p h m c n : Nat) (result : EdgeValue Symbol Guard) (after : Checked (bits + 2))
    (savedFourth : Fourth) (saved : Memo)
    (done : SourceCurrentAllocatedParentWorker.edge g s r e p h m c n budget original.entry.key.symbol
      original.entry.key.constraint inherited original.children before fourth memo = .done result after savedFourth saved) :
    savedFourth = fourth ∧ ∃ next final requests,
    ∃ actual : Edge budget original.entry.key.symbol original.entry.key.constraint loaded inherited original.children before fourth memo result after fourth saved,
      Reads formulas solver actual memos final ∧
      Receipt formulas solver next original.entry.key.symbol original.entry.key.constraint loaded inherited original.children
        before result after fourth fourth memo saved final ∧
      SourceCurrentAllocatedParentWorkerCompletion.StableRun
        (fun g s r e p h m c n => SourceCurrentAllocatedParentWorker.edge g s r e p h m c n budget
          original.entry.key.symbol original.entry.key.constraint inherited original.children before fourth memo) result after fourth saved ∧
      NativeStored after.native ∧ OutputStored after.native ∧ Profiles saved ∧
      EdgeShape (outputRows original.entry.key.constraint loaded inherited before.operations rows count depth bound)
        (outputArity original.entry.key.constraint loaded inherited before.operations arity count) result ∧
      EdgeNarrow original result ∧ Trace before.native.machine.heap after.native.machine.heap requests ∧
      nodeRequests requests ≤ nodeBudget original.entry.key.constraint loaded inherited before.operations rows arity count depth bound ∧
      edgeRequests requests ≤ edgeBudget original.entry.key.constraint loaded inherited before.operations rows arity count depth bound ∧ Capacity bits after ∧
      after.native.machine.heap.nodes.next ≤ before.native.machine.heap.nodes.next + nodeBudget original.entry.key.constraint loaded inherited before.operations rows arity count depth bound ∧
      after.native.machine.heap.edges.next ≤ before.native.machine.heap.edges.next + edgeBudget original.entry.key.constraint loaded inherited before.operations rows arity count depth bound := by
  obtain ⟨chosen, returned, savedMemo, next, final, requests, actual, reads, receipt, stable, rest⟩ :=
    SourceCurrentAllocatedFiniteOrdinaryParentResources.complete formulas solver inventory bits budget original loaded inherited before fourth memo ready admitted cached found inheritedReady available correct physical profiles native output covered memos valid rows arity count depth bound profile lengthBound pathsBound heightBound nodes edges
  obtain ⟨G, S, R, E, P, H, M, C, N, exactReturn⟩ := stable
  have constructed := exactReturn G S R E P H M C N
    (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _)
    (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _)
  obtain ⟨rfl, rfl, rfl, rfl⟩ := SourceCurrentAllocatedParentWorkerStability.edge_done_unique done constructed
  exact ⟨rfl, next, final, requests, actual, reads, receipt,
    ⟨G, S, R, E, P, H, M, C, N, exactReturn⟩, rest⟩

#print axioms constructed_raw_rejection
#check @constructed_raw_rejection
#print axioms supplied_success_accounted
#check @supplied_success_accounted
end MicroCFTA.ParentResourceIndependentChecks
