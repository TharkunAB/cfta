import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryLocalResources
import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryMkEdgeResources
import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryParent

/-!
# Initial resources for checked parent reduction

Raw contradiction makes one sentinel edge request before any local work.
A live field uses the actual local return and then the checked constructor.
The constructor can replace rejected children with one Empty child.
All bounds retain the same full receipt, strict Reads, and actual Work.
-/
namespace MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryParentResources
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

/-- A raw rejected parent skips every local node request. -/
noncomputable def nodeBudget (original : Guard) (loaded : Allocated) (inherited : EqValue) (operations : Operations)
    (rows arity count depth bound : Nat) : Nat :=
  if contradictory original then 0 else
    SourceCurrentAllocatedFiniteOrdinaryLocalResources.nodeBudget loaded inherited operations rows arity count depth bound

/-- Every parent adds one actual checked edge request after any live local work. -/
noncomputable def edgeBudget (original : Guard) (loaded : Allocated) (inherited : EqValue) (operations : Operations)
    (rows arity count depth bound : Nat) : Nat :=
  if contradictory original then 1 else
    SourceCurrentAllocatedFiniteOrdinaryLocalResources.edgeBudget loaded inherited operations rows arity count depth bound + 1

/-- Rejected sentinels need no larger row bound than the original input. -/
noncomputable def outputRows (original : Guard) (loaded : Allocated) (inherited : EqValue) (operations : Operations)
    (rows count depth bound : Nat) : Nat :=
  if contradictory original then rows else
    SourceCurrentAllocatedFiniteOrdinaryLocalResources.outputRows loaded inherited operations rows count depth bound

/-- The profile includes both descendant arities and the source sentinel arity. -/
noncomputable def outputArity (original : Guard) (loaded : Allocated) (inherited : EqValue) (operations : Operations)
    (arity count : Nat) : Nat :=
  if contradictory original then max arity 1 else
    max (max (SourceCurrentAllocatedFiniteOrdinaryLocalResources.outputArity loaded inherited operations arity) count) 1

variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq (Value Symbol Guard)]

/-- Raw rejection constructs the full parent receipt without child, field, or inherited readiness. -/
theorem rejected (formulas : SourceGuards.Formulas FullSyntax.Formula)
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
      after.native.machine.heap.edges.next ≤ before.native.machine.heap.edges.next + 1 := by
  obtain ⟨requests, constructor, finalNative, finalOutput, produced, trace, nodeCount, edgeCount, capacity, nodeSupply, edgeSupply⟩ :=
    SourceCurrentAllocatedFiniteOrdinaryMkEdgeResources.rejected formulas solver inventory bits original.entry.key.symbol before
      ready admitted native output rows arity nodes edges
  obtain ⟨_broad, _reads, receipt⟩ := SourceCurrentAllocatedParentEdge.rejected formulas solver inventory budget
    original.entry.key.symbol original.entry.key.constraint loaded inherited original.children before fourth memo
      ready admitted test correct physical covered memos valid
  let actual : Edge budget original.entry.key.symbol original.entry.key.constraint loaded inherited original.children
      before fourth memo (SourceCurrentAllocatedMkEdge.reject original.entry.key.symbol before).1
        (SourceCurrentAllocatedMkEdge.reject original.entry.key.symbol before).2 fourth memo := .rejected test
  have reads : Reads formulas solver actual memos memos := .rejected (test := test)
  have stable := SourceCurrentAllocatedParentWorkerCompletion.edge_complete actual (by intro impossible; rw [test] at impossible; cases impossible)
  exact ⟨requests, actual, reads, receipt, stable, finalNative, finalOutput, profiles, produced,
    SourceCurrentAllocatedFiniteOrdinaryMkEdge.rejected constructor original, trace, nodeCount, edgeCount, capacity, nodeSupply, edgeSupply⟩

/-- Initial local facts and total headroom construct the exact parent and constructor return. -/
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
    (rows arity count depth bound : Nat) (profile : ChildrenShape rows arity original.children)
    (lengthBound : original.children.length ≤ count)
    (pathsBound : ∀ records, (runPrefix loaded.stored loaded.guard inherited before.operations).1 = .ok (.classes records) →
      ∀ record ∈ records, ∀ path ∈ record.paths, path.length ≤ depth)
    (heightBound : childrenHeight original.children ≤ bound)
    (nodes : before.native.machine.heap.nodes.next + nodeBudget original.entry.key.constraint loaded inherited before.operations rows arity count depth bound ≤ 2 ^ bits)
    (edges : before.native.machine.heap.edges.next + edgeBudget original.entry.key.constraint loaded inherited before.operations rows arity count depth bound ≤ 2 ^ (bits + 2)) :
    ∃ result after saved next final requests,
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
  cases test : contradictory original.entry.key.constraint with
  | true =>
      obtain ⟨requests, actual, reads, receipt, stable, finalNative, finalOutput, finalProfiles, produced, narrowed,
        trace, nodeCount, edgeCount, capacity, nodeSupply, edgeSupply⟩ := rejected formulas solver inventory bits budget
          original loaded inherited before fourth memo ready admitted test correct physical profiles native output covered memos valid rows arity
          (by simpa only [nodeBudget, test, ↓reduceIte, Nat.add_zero] using nodes)
          (by simpa only [edgeBudget, test, ↓reduceIte] using edges)
      refine ⟨_, _, memo, inventory, memos, requests, actual, reads, receipt, stable, finalNative, finalOutput, finalProfiles,
        ?_, narrowed, trace, ?_, ?_, capacity, ?_, ?_⟩
      · simpa only [outputRows, outputArity, test, ↓reduceIte] using produced
      · simp only [nodeBudget, test, ↓reduceIte]; omega
      · simp only [edgeBudget, test, ↓reduceIte]; omega
      · simp only [nodeBudget, test, ↓reduceIte]; omega
      · simp only [edgeBudget, test, ↓reduceIte]; exact edgeSupply
  | false =>
      obtain ⟨children, middle, saved, _localInventory, final, earlier, reduction, localReads, localReceipt, _localStable,
        middleNative, middleOutput, middleProfiles, middleProfile, related, sameLength, _height, earlierTrace, earlierNodes,
        earlierEdges, _middleCapacity, middleNodeSupply, middleEdgeSupply⟩ := SourceCurrentAllocatedFiniteOrdinaryLocalResources.complete
          formulas solver inventory bits budget original.entry.key.constraint loaded inherited original.children before fourth memo
            ready admitted cached found inheritedReady available correct physical profiles native output covered memos valid
            rows arity count depth bound profile lengthBound pathsBound heightBound
            (by simpa only [nodeBudget, test, Bool.false_eq_true, ↓reduceIte] using nodes)
            (by simp only [edgeBudget, test, Bool.false_eq_true, ↓reduceIte] at edges; omega)
      have loadedReady := SourceEqualityConstraintFieldLookup.load_ready original.entry.key.constraint before.operations.constraints
        ready.good.operations.constraints cached loaded found
      have storedReady := loadedReady.1.grows localReceipt.effects.grows.constraint_growth
      have field : SourceCurrentConjunctionEquality.FieldAvailable middle.operations (raw loaded) := by
        rw [loadedReady.2]
        exact (show SourceCurrentConjunctionEquality.FieldAvailable before.operations original.entry.key.constraint from
          ⟨cached, loaded, found⟩).grows localReceipt.effects.grows
      let currentRows := SourceCurrentAllocatedFiniteOrdinaryLocalResources.outputRows loaded inherited before.operations rows count depth bound
      let currentArity := max (SourceCurrentAllocatedFiniteOrdinaryLocalResources.outputArity loaded inherited before.operations arity) count
      have constructorNodes : middle.native.machine.heap.nodes.next ≤ 2 ^ bits := by
        simp only [nodeBudget, test, Bool.false_eq_true, ↓reduceIte] at nodes
        omega
      have constructorEdges : middle.native.machine.heap.edges.next + 1 ≤ 2 ^ (bits + 2) := by
        simp only [edgeBudget, test, Bool.false_eq_true, ↓reduceIte] at edges
        omega
      obtain ⟨result, after, later, constructor, finalNative, finalOutput, produced, laterTrace, laterNodes, laterEdges,
        capacity, finalNodeSupply, finalEdgeSupply⟩ := SourceCurrentAllocatedFiniteOrdinaryMkEdgeResources.complete
          formulas solver _ bits original.entry.key.symbol loaded children middle localReceipt.ready localReceipt.admitted
          storedReady field localReceipt.available middleNative middleOutput currentRows currentArity
          (ChildrenShape.mono children middleProfile (Nat.le_refl _) (Nat.le_max_left _ _))
          (Nat.le_trans (by omega : children.length ≤ count) (Nat.le_max_right _ _)) constructorNodes constructorEdges
      have actual : Edge budget original.entry.key.symbol original.entry.key.constraint loaded inherited original.children
          before fourth memo result after fourth saved := .live test reduction constructor.actual
      have reads : Reads formulas solver actual memos final := .live (test := test) (built := constructor.actual) localReads
      have ranges : SourceCurrentAllocatedLocalReductionActual.Ranges budget loaded inherited original.children before fourth := by
        intro records _
        exact SourceCurrentAllocatedFiniteOrdinaryScanRanges.scan_ranges budget SourceMemoGate.unconstrained
          (SourceEndpointReachability.reaches SourceMemoGate.unconstrained) original.children
          (records.map SourceEqualityClassOrder.Record.paths) (prefixState before loaded inherited) fourth
          ready.good.native.machine.1.coherent available (ChildrenShape.domain original.children profile)
      obtain ⟨next, receipt, _native, _merged, narrowed⟩ := SourceCurrentAllocatedFiniteOrdinaryParent.verified
        formulas solver inventory original reads ready admitted (fun _ => ⟨cached, found, inheritedReady, available, ranges⟩)
        (ChildrenShape.domain original.children profile) correct physical covered native profiles.domain valid
      refine ⟨result, after, saved, next, final, earlier ++ later, actual, reads, receipt,
        SourceCurrentAllocatedParentWorkerCompletion.edge_complete actual (fun _ => found), finalNative, finalOutput,
        middleProfiles, ?_, narrowed, earlierTrace.trans laterTrace, ?_, ?_, capacity, ?_, ?_⟩
      · simpa only [outputRows, outputArity, test, Bool.false_eq_true, ↓reduceIte, currentRows, currentArity] using produced
      · rw [nodeRequests_append]
        simp only [nodeBudget, test, Bool.false_eq_true, ↓reduceIte]
        omega
      · rw [edgeRequests_append]
        simp only [edgeBudget, test, Bool.false_eq_true, ↓reduceIte]
        omega
      · simp only [nodeBudget, test, Bool.false_eq_true, ↓reduceIte]
        omega
      · simp only [edgeBudget, test, Bool.false_eq_true, ↓reduceIte]
        omega

end MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryParentResources
