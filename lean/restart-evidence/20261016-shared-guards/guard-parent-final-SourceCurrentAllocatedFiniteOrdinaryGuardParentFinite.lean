import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryGuardParent
import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryParentResources

/-!
# Constructed parent resources with hereditary guard bounds

Initial raw guard limits bound the actual own precheck paths.
The existing resource construction supplies its own graph and strict reads.
Those same reads derive both guard stores and the final edge profile.
All physical receipts, Work requests, and final supplies refer to one return.
This result does not derive a complete outer resource plan.
-/
namespace MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryGuardParentFinite
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

local notation "Limits" => SourceCurrentAllocatedFiniteOrdinaryGuardEnvelope.Limits
local notation "NativeGuards" => SourceCurrentAllocatedFiniteOrdinaryGuardStored.Stored
local notation "MergeGuards" => SourceCurrentAllocatedFiniteOrdinaryMergeGuardCache.Stored
local notation "GuardEdge" => SourceCurrentAllocatedFiniteOrdinaryGuardProfiles.Edge
open SourceCurrentAllocatedFiniteOrdinaryParentResources (nodeBudget edgeBudget outputRows outputArity)
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq (Value Symbol Guard)]

/-- Initial hereditary guards supply own path bounds for the same constructed resource receipt. -/
theorem complete (formulas : SourceGuards.Formulas FullSyntax.Formula)
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
    (limits : Limits) (guardProfile : GuardEdge limits original)
    (guards : NativeGuards before.native) (mergeGuards : MergeGuards memo)
    (rows arity count bound : Nat) (profile : ChildrenShape rows arity original.children)
    (lengthBound : original.children.length ≤ count)
    (heightBound : childrenHeight original.children ≤ bound)
    (nodes : before.native.machine.heap.nodes.next + nodeBudget original.entry.key.constraint loaded inherited before.operations rows arity count (SourceCurrentAllocatedFiniteOrdinaryGuardOwn.pathDepth limits) bound ≤ 2 ^ bits)
    (edges : before.native.machine.heap.edges.next + edgeBudget original.entry.key.constraint loaded inherited before.operations rows arity count (SourceCurrentAllocatedFiniteOrdinaryGuardOwn.pathDepth limits) bound ≤ 2 ^ (bits + 2)) :
    ∃ result after saved next final requests,
    ∃ actual : Edge budget original.entry.key.symbol original.entry.key.constraint loaded inherited original.children before fourth memo result after fourth saved,
      Reads formulas solver actual memos final ∧
      Receipt formulas solver next original.entry.key.symbol original.entry.key.constraint loaded inherited original.children
        before result after fourth fourth memo saved final ∧
      SourceCurrentAllocatedParentWorkerCompletion.StableRun
        (fun g s r e p h m c n => SourceCurrentAllocatedParentWorker.edge g s r e p h m c n budget
          original.entry.key.symbol original.entry.key.constraint inherited original.children before fourth memo) result after fourth saved ∧
      NativeStored after.native ∧ OutputStored after.native ∧ Profiles saved ∧
      EdgeShape (outputRows original.entry.key.constraint loaded inherited before.operations rows count (SourceCurrentAllocatedFiniteOrdinaryGuardOwn.pathDepth limits) bound)
        (outputArity original.entry.key.constraint loaded inherited before.operations arity count) result ∧
      EdgeNarrow original result ∧ Trace before.native.machine.heap after.native.machine.heap requests ∧
      nodeRequests requests ≤ nodeBudget original.entry.key.constraint loaded inherited before.operations rows arity count (SourceCurrentAllocatedFiniteOrdinaryGuardOwn.pathDepth limits) bound ∧
      edgeRequests requests ≤ edgeBudget original.entry.key.constraint loaded inherited before.operations rows arity count (SourceCurrentAllocatedFiniteOrdinaryGuardOwn.pathDepth limits) bound ∧ Capacity bits after ∧
      after.native.machine.heap.nodes.next ≤ before.native.machine.heap.nodes.next + nodeBudget original.entry.key.constraint loaded inherited before.operations rows arity count (SourceCurrentAllocatedFiniteOrdinaryGuardOwn.pathDepth limits) bound ∧
      after.native.machine.heap.edges.next ≤ before.native.machine.heap.edges.next + edgeBudget original.entry.key.constraint loaded inherited before.operations rows arity count (SourceCurrentAllocatedFiniteOrdinaryGuardOwn.pathDepth limits) bound ∧
      NativeGuards after.native ∧ MergeGuards saved ∧
      GuardEdge (SourceCurrentAllocatedFiniteOrdinaryGuardParent.outputLimit limits) result := by
  have pathsBound : ∀ records,
      (runPrefix loaded.stored loaded.guard inherited before.operations).1 = .ok (.classes records) →
      ∀ record ∈ records, ∀ path ∈ record.paths,
        path.length ≤ SourceCurrentAllocatedFiniteOrdinaryGuardOwn.pathDepth limits := by
    intro records actual
    obtain ⟨own, receipt⟩ := SourceCurrentAllocatedLocalReductionActual.prefix_verified formulas solver inventory
      before original.entry.key.constraint loaded inherited ready admitted cached found inheritedReady actual
    exact (SourceCurrentAllocatedFiniteOrdinaryGuardOwn.receipt receipt limits
      (SourceCurrentAllocatedFiniteOrdinaryGuardProfiles.Edge.guard original guardProfile)).2.2.2
  obtain ⟨result, after, saved, next, final, requests, actual, reads, receipt, stable, finalNative,
    finalOutput, finalProfiles, produced, narrowed, trace, nodeCount, edgeCount, capacity, nodeSupply, edgeSupply⟩ :=
    SourceCurrentAllocatedFiniteOrdinaryParentResources.complete formulas solver inventory bits budget original
      loaded inherited before fourth memo ready admitted cached found inheritedReady available correct physical
      profiles native output covered memos valid rows arity count
      (SourceCurrentAllocatedFiniteOrdinaryGuardOwn.pathDepth limits) bound profile lengthBound pathsBound heightBound nodes edges
  have finalGuards := SourceCurrentAllocatedFiniteOrdinaryGuardParent.structure_from_reads formulas solver inventory original
    reads ready admitted (fun _ => ⟨cached, found, inheritedReady, available⟩) limits guardProfile correct physical covered
    native profiles.domain valid guards mergeGuards
  exact ⟨result, after, saved, next, final, requests, actual, reads, receipt, stable, finalNative,
    finalOutput, finalProfiles, produced, narrowed, trace, nodeCount, edgeCount, capacity, nodeSupply, edgeSupply,
    finalGuards.2.1, finalGuards.2.2.1, finalGuards.2.2.2.1⟩

end MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryGuardParentFinite
