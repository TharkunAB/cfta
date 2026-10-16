import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryClassResources
import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryClassPass

/-!
# Initial resources for the current class right fold

Each class captures the exact forest returned by its tail.
The tail profile determines the next class profile and constructor budget.
Initial cumulative headroom pays for every actual prefix.
Final empty propagation changes no heap or memo table.
-/
namespace MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryPassResources
open Cache Language InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open SourceCurrentAllocatedNativeInventoryState (Inventory At)
open SourceCurrentAllocatedClassPass (Fold FoldReads Pass PassReads Receipt)
open SourceCurrentAllocatedFiniteOrdinaryNativeProfile (ChildrenShape)
open SourceCurrentAllocatedFiniteOrdinaryRequired (NodeNarrow)
open SourceCurrentAllocatedFiniteOrdinaryNarrow (forest_refl forest_trans forest_height)
open SourceCurrentAllocatedFiniteOrdinaryConstructorWorkTrace (Trace nodeRequests_append edgeRequests_append)
open SourceCurrentAllocatedFiniteOrdinaryReservations (nodeRequests edgeRequests)
open MergedOrdinaryHeight (childrenHeight)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Record" => SourceEqualityClassOrder.Record
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Memo" => SourceCurrentMemoMergeGraph.Memo Symbol Guard
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Valid" => EndpointMemoGateTrace.Valid
local notation "Ready" => SourceCurrentConjunctionClassScan.Ready
local notation "PhysicalStored" => SourceCurrentMemoMergeEffects.Stored
local notation "Profiles" => SourceCurrentAllocatedFiniteOrdinaryMergeProfileCache.Stored
local notation "NativeStored" => SourceCurrentAllocatedFiniteOrdinaryStored.Stored
local notation "OutputStored" => SourceCurrentAllocatedFiniteOrdinaryOutputStored.Stored
local notation "Capacity" => SourceCurrentAllocatedFiniteOrdinaryCapacity.Capacity

/-- Each head class uses the row limit produced by its tail. -/
def outputRows (records : List Record) (rows count depth bound : Nat) : Nat :=
  match records with
  | [] => rows
  | record :: rest => SourceCurrentAllocatedFiniteOrdinaryClassResources.outputRows
      record (outputRows rest rows count depth bound) count depth bound

/-- Each head class uses the arity limit produced by its tail. -/
def outputArity (records : List Record) (arity : Nat) : Nat :=
  match records with
  | [] => arity
  | _ :: rest => SourceCurrentAllocatedFiniteOrdinaryClassResources.outputArity (outputArity rest arity)

/-- The tail cost precedes the head cost at the tail's computed profile. -/
def nodeBudget (records : List Record) (rows arity count depth bound : Nat) : Nat :=
  match records with
  | [] => 0
  | record :: rest => nodeBudget rest rows arity count depth bound +
      SourceCurrentAllocatedFiniteOrdinaryClassResources.nodeBudget record
        (outputRows rest rows count depth bound) (outputArity rest arity) count depth bound

/-- Edge headroom follows the same literal class order and returned profiles. -/
def edgeBudget (records : List Record) (rows arity count depth bound : Nat) : Nat :=
  match records with
  | [] => 0
  | record :: rest => edgeBudget rest rows arity count depth bound +
      SourceCurrentAllocatedFiniteOrdinaryClassResources.edgeBudget record
        (outputRows rest rows count depth bound) (outputArity rest arity) count depth bound

variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]

/-- Initial profiles and total headroom construct the full right fold at its actual returned state. -/
theorem fold_complete (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (inventory : Inventory)
    (bits : Nat) (records : List Record)
    (coherent : ∀ record ∈ records, SourceEqualityClassOrder.Coherent record)
    (active : ∀ record ∈ records, EqualityNormalize.Nontrivial record.paths)
    (values : List (Value Symbol Guard)) (before : Checked (bits + 2)) (memo : Memo)
    (ready : Ready before) (admitted : At formulas solver inventory before)
    (available : Values before.native.machine.heap values)
    (physical : PhysicalStored before.native.machine.heap memo) (profiles : Profiles memo)
    (native : NativeStored before.native) (output : OutputStored before.native)
    (covered : ∀ ambient, SourceCurrentMemoMergeLanguage.CacheCovers (SourceEqualityPCSGuard.holds formulas solver) ambient memo)
    (memos : Memos) (valid : Valid before.native.machine.heap memos)
    (rows arity count depth bound : Nat) (profile : ChildrenShape rows arity values)
    (lengthBound : values.length ≤ count)
    (pathsBound : ∀ record ∈ records, ∀ path ∈ record.paths, path.length ≤ depth)
    (heightBound : childrenHeight values ≤ bound)
    (nodes : before.native.machine.heap.nodes.next + nodeBudget records rows arity count depth bound ≤ 2 ^ bits)
    (edges : before.native.machine.heap.edges.next + edgeBudget records rows arity count depth bound ≤ 2 ^ (bits + 2)) :
    ∃ results after saved next final requests, ∃ actual : Fold records values before memo results after saved,
      FoldReads formulas solver actual memos final ∧
      Receipt formulas solver next records values before memo results after saved memos final ∧
      SourceCurrentAllocatedClassWorkerCompletion.StableRun
        (fun e p h m s n => SourceCurrentAllocatedClassWorker.fold e p h m s n records values before memo) results after saved ∧
      NativeStored after.native ∧ OutputStored after.native ∧ Profiles saved ∧
      ChildrenShape (outputRows records rows count depth bound) (outputArity records arity) results ∧
      All₂ NodeNarrow values results ∧ results.length = values.length ∧ childrenHeight results ≤ bound ∧
      Trace before.native.machine.heap after.native.machine.heap requests ∧
      nodeRequests requests ≤ nodeBudget records rows arity count depth bound ∧
      edgeRequests requests ≤ edgeBudget records rows arity count depth bound ∧ Capacity bits after ∧
      after.native.machine.heap.nodes.next ≤ before.native.machine.heap.nodes.next + nodeBudget records rows arity count depth bound ∧
      after.native.machine.heap.edges.next ≤ before.native.machine.heap.edges.next + edgeBudget records rows arity count depth bound := by
  induction records generalizing inventory values before memo memos with
  | nil =>
      have actual : Fold [] values before memo values before memo := .nil
      have reads : FoldReads formulas solver actual memos memos := .nil
      obtain ⟨next, receipt⟩ := SourceCurrentAllocatedClassPass.Fold.verified formulas solver inventory reads coherent active
        ready admitted available
        (fun _ _ path _ => SourceCurrentAllocatedFiniteOrdinaryTarget.forest_closed _ ready.semantic values available
          (ChildrenShape.domain values profile) (path.map Int.ofNat)) physical covered valid
      simp only [nodeBudget] at nodes
      simp only [edgeBudget] at edges
      exact ⟨values, before, memo, next, memos, [], actual, reads, receipt,
        SourceCurrentAllocatedClassWorkerCompletion.fold_complete actual, native, output, profiles, profile,
        forest_refl (ChildrenShape.domain values profile), rfl, heightBound, .refl _, Nat.le_refl _, Nat.le_refl _,
        ⟨by omega, by omega⟩, Nat.le_refl _, Nat.le_refl _⟩
  | cons record records ih =>
      have tailCoherent := fun own member => coherent own (List.mem_cons_of_mem record member)
      have tailActive := fun own member => active own (List.mem_cons_of_mem record member)
      have tailPaths := fun own member => pathsBound own (List.mem_cons_of_mem record member)
      change before.native.machine.heap.nodes.next + (nodeBudget records rows arity count depth bound +
        SourceCurrentAllocatedFiniteOrdinaryClassResources.nodeBudget record
          (outputRows records rows count depth bound) (outputArity records arity) count depth bound) ≤ 2 ^ bits at nodes
      change before.native.machine.heap.edges.next + (edgeBudget records rows arity count depth bound +
        SourceCurrentAllocatedFiniteOrdinaryClassResources.edgeBudget record
          (outputRows records rows count depth bound) (outputArity records arity) count depth bound) ≤ 2 ^ (bits + 2) at edges
      obtain ⟨middle, step, current, tailInventory, stepMemos, tailRequests, tailActual, tailReads, first,
        _tailStable, tailNative, tailOutput, tailProfiles, tailProfile, tailNarrow, tailLength, tailHeight,
        tailTrace, tailNodes, tailEdges, _tailCapacity, tailNodeSupply, tailEdgeSupply⟩ :=
        ih (inventory := inventory) (coherent := tailCoherent) (active := tailActive) (values := values)
          (before := before) (memo := memo) (ready := ready) (admitted := admitted) (available := available)
          (physical := physical) (profiles := profiles) (native := native) (output := output) (covered := covered)
          (memos := memos) (valid := valid) (profile := profile) (lengthBound := lengthBound) (pathsBound := tailPaths)
          (heightBound := heightBound) (nodes := by omega) (edges := by omega)
      obtain ⟨results, after, saved, _headInventory, final, headRequests, headActual, headReads, _last,
        _headStable, finalNative, finalOutput, finalProfiles, finalProfile, headNarrow, headLength, finalHeight,
        headTrace, headNodes, headEdges, capacity, headNodeSupply, headEdgeSupply⟩ :=
        SourceCurrentAllocatedFiniteOrdinaryClassResources.complete formulas solver tailInventory bits record
          (coherent _ List.mem_cons_self) (active _ List.mem_cons_self) middle step current first.ready first.admitted first.available
          first.stored tailProfiles tailNative tailOutput first.covered stepMemos first.globals.valid
          (outputRows records rows count depth bound) (outputArity records arity) count depth bound tailProfile
          (by omega) (pathsBound _ List.mem_cons_self) tailHeight (by omega) (by omega)
      have actual : Fold (record :: records) values before memo results after saved := .cons tailActual headActual
      have reads : FoldReads formulas solver actual memos final := .cons tailReads headReads
      obtain ⟨next, receipt⟩ := SourceCurrentAllocatedClassPass.Fold.verified formulas solver inventory reads coherent active
        ready admitted available
        (fun _ _ path _ => SourceCurrentAllocatedFiniteOrdinaryTarget.forest_closed _ ready.semantic values available
          (ChildrenShape.domain values profile) (path.map Int.ofNat)) physical covered valid
      refine ⟨results, after, saved, next, final, tailRequests ++ headRequests, actual, reads, receipt,
        SourceCurrentAllocatedClassWorkerCompletion.fold_complete actual, finalNative, finalOutput, finalProfiles,
        finalProfile, forest_trans tailNarrow headNarrow, headLength.trans tailLength, finalHeight,
        tailTrace.trans headTrace, ?_, ?_, capacity, ?_, ?_⟩
      · rw [nodeRequests_append]
        change nodeRequests tailRequests + nodeRequests headRequests ≤ nodeBudget records rows arity count depth bound + _
        omega
      · rw [edgeRequests_append]
        change edgeRequests tailRequests + edgeRequests headRequests ≤ edgeBudget records rows arity count depth bound + _
        omega
      · change after.native.machine.heap.nodes.next ≤ before.native.machine.heap.nodes.next +
          (nodeBudget records rows arity count depth bound + _)
        omega
      · change after.native.machine.heap.edges.next ≤ before.native.machine.heap.edges.next +
          (edgeBudget records rows arity count depth bound + _)
        omega

private theorem erase_profile {rows arity : Nat} (values : List (Value Symbol Guard)) :
    ChildrenShape rows arity (EqualityLeafProjectionRuntimeEmpty.erase values) := by
  induction values with
  | nil => trivial
  | cons value values ih => exact ⟨trivial, ih⟩

private theorem propagate_profile {rows arity : Nat} {values : List (Value Symbol Guard)}
    (profile : ChildrenShape rows arity values) :
    ChildrenShape rows arity (EqualityLeafProjectionRuntimeEmpty.propagate values) := by
  unfold EqualityLeafProjectionRuntimeEmpty.propagate
  split
  · exact erase_profile values
  · exact profile

omit [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] in
private theorem propagate_length (values : List (Value Symbol Guard)) :
    (EqualityLeafProjectionRuntimeEmpty.propagate values).length = values.length := by
  unfold EqualityLeafProjectionRuntimeEmpty.propagate
  split <;> simp [EqualityLeafProjectionRuntimeEmpty.erase]

/-- Initial total headroom constructs the complete class pass and allocation-free propagation. -/
theorem complete (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (inventory : Inventory)
    (bits : Nat) (records : List Record)
    (coherent : ∀ record ∈ records, SourceEqualityClassOrder.Coherent record)
    (active : ∀ record ∈ records, EqualityNormalize.Nontrivial record.paths)
    (values : List (Value Symbol Guard)) (before : Checked (bits + 2)) (memo : Memo)
    (ready : Ready before) (admitted : At formulas solver inventory before)
    (available : Values before.native.machine.heap values)
    (physical : PhysicalStored before.native.machine.heap memo) (profiles : Profiles memo)
    (native : NativeStored before.native) (output : OutputStored before.native)
    (covered : ∀ ambient, SourceCurrentMemoMergeLanguage.CacheCovers (SourceEqualityPCSGuard.holds formulas solver) ambient memo)
    (memos : Memos) (valid : Valid before.native.machine.heap memos)
    (rows arity count depth bound : Nat) (profile : ChildrenShape rows arity values)
    (lengthBound : values.length ≤ count)
    (pathsBound : ∀ record ∈ records, ∀ path ∈ record.paths, path.length ≤ depth)
    (heightBound : childrenHeight values ≤ bound)
    (nodes : before.native.machine.heap.nodes.next + nodeBudget records rows arity count depth bound ≤ 2 ^ bits)
    (edges : before.native.machine.heap.edges.next + edgeBudget records rows arity count depth bound ≤ 2 ^ (bits + 2)) :
    ∃ results after saved next final requests, ∃ actual : Pass records values before memo results after saved,
      PassReads formulas solver actual memos final ∧
      Receipt formulas solver next records values before memo results after saved memos final ∧
      SourceCurrentAllocatedClassWorkerCompletion.StableRun
        (fun e p h m s n => SourceCurrentAllocatedClassWorker.pass e p h m s n records values before memo) results after saved ∧
      NativeStored after.native ∧ OutputStored after.native ∧ Profiles saved ∧
      ChildrenShape (outputRows records rows count depth bound) (outputArity records arity) results ∧
      All₂ NodeNarrow values results ∧ results.length = values.length ∧ childrenHeight results ≤ bound ∧
      Trace before.native.machine.heap after.native.machine.heap requests ∧
      nodeRequests requests ≤ nodeBudget records rows arity count depth bound ∧
      edgeRequests requests ≤ edgeBudget records rows arity count depth bound ∧ Capacity bits after ∧
      after.native.machine.heap.nodes.next ≤ before.native.machine.heap.nodes.next + nodeBudget records rows arity count depth bound ∧
      after.native.machine.heap.edges.next ≤ before.native.machine.heap.edges.next + edgeBudget records rows arity count depth bound := by
  obtain ⟨middle, after, saved, _foldInventory, final, requests, fold, foldReads, _first,
    _foldStable, nativeAfter, outputAfter, profilesAfter, produced, _foldNarrow, sameLength, _foldHeight,
    trace, nodeCount, edgeCount, capacity, nodeSupply, edgeSupply⟩ :=
    fold_complete formulas solver inventory bits records coherent active values before memo ready admitted available
      physical profiles native output covered memos valid rows arity count depth bound profile lengthBound pathsBound heightBound nodes edges
  have actual : Pass records values before memo (EqualityLeafProjectionRuntimeEmpty.propagate middle) after saved := .done fold
  have reads : PassReads formulas solver actual memos final := .done foldReads
  obtain ⟨next, receipt, _native, _merged, related⟩ := SourceCurrentAllocatedFiniteOrdinaryClassPass.pass
    formulas solver inventory reads coherent active ready admitted available (ChildrenShape.domain values profile)
      physical covered native profiles.domain valid
  exact ⟨_, after, saved, next, final, requests, actual, reads, receipt,
    SourceCurrentAllocatedClassWorkerCompletion.pass_complete actual, nativeAfter, outputAfter, profilesAfter,
    propagate_profile produced, related, (propagate_length middle).trans sameLength,
    Nat.le_trans (forest_height related) heightBound, trace, nodeCount, edgeCount, capacity, nodeSupply, edgeSupply⟩

end MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryPassResources
