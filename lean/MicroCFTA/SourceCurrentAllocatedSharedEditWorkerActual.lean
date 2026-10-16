import MicroCFTA.SourceCurrentAllocatedSharedEditWorkerCompletion
import MicroCFTA.SourceCurrentAllocatedSharedEditWorkerStability
import MicroCFTA.SourceCurrentAllocatedSharedEditComplete
import MicroCFTA.SourceCurrentAllocatedSharedEditLanguage
import MicroCFTA.SourceCurrentAllocatedProbeEdits

/-!
# Actual receipts for current checked edit workers

Initial selected domains construct a finite current edit graph. That graph
supplies literal stable worker bounds, its reads, and its physical receipt.
Successful worker uniqueness aligns a supplied return with that same graph.
The equality covers the full checked state, equality operations, target
slots, and merge table. No future edit or output language is assumed.
-/
namespace MicroCFTA.SourceCurrentAllocatedSharedEditWorkerActual
open Cache Language InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open SourceEqualityEdits SourceEqualityEditLeafPaths SourceCurrentEditDomains
open SourceEqualityProjectionPathDomain (ForestClosed)
open SourceEqualitySharedEditEffects (Allowed)
open SourceCurrentAllocatedSharedEditGraph SourceCurrentAllocatedSharedEditWorker
open SourceCurrentAllocatedSharedEditRanges SourceCurrentAllocatedSharedEditEffects
open SourceCurrentAllocatedSharedEditWorkerCompletion (StableRun)
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open InternedGuardedLanguage (meaning)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Heap" => InternedConstructorTemplates.State Symbol Guard
local notation "Ready" => SourceCurrentAllocatedSharedTargetState.Ready
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "MemoValid" => EndpointMemoGateTrace.Valid
local notation "ProbeHeap" => InternedFreshOrdinaryProbeHeap.Heap
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat}
variable (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
variable (record : SourceEqualityClassOrder.Record) (originals : List (Value Symbol Guard)) (base : Heap)
variable (known : Values base originals)
variable (domains : ∀ path ∈ record.paths, ForestClosed (path.map Int.ofNat) originals)
variable (coherent : SourceEqualityClassOrder.Coherent record) (active : EqualityNormalize.Nontrivial record.paths)
include known domains coherent active

/-- Initial node support derives its finite graph, stable worker, and exact returned receipt. -/
theorem node_finite (inventory : Inventory) {edits value} {before : SharedState width}
    (ranges : NodeRanges record originals edits value before)
    (populated : Populated edits) (nonempty : HasLeaf edits) (allowed : Allowed record edits)
    (ready : Ready formulas solver inventory record originals base before)
    (available : Available before.checked.native.machine.heap value) (safe : Safe edits value)
    (memos : Memos) (valid : MemoValid before.checked.native.machine.heap memos)
    (probes : ProbeHeap before.checked.native.machine.heap) :
    ∃ result after next final, ∃ actual : EditNode record originals edits value before result after,
      NodeReads formulas solver base actual memos final ∧
      NodeReceipt formulas solver next record originals base value before result after memos final ∧
      ProbeHeap after.checked.native.machine.heap ∧
      StableRun (fun e p h m s n => edit record originals e p h m s n edits value before) result after := by
  obtain ⟨result, after, next, final, actual, reads, receipt⟩ :=
    SourceCurrentAllocatedSharedEditComplete.node_complete formulas solver record originals base known domains coherent active
      inventory ranges populated nonempty allowed ready available safe memos valid
  exact ⟨result, after, next, final, actual, reads, receipt,
    SourceCurrentAllocatedProbeEdits.node_heap reads populated nonempty allowed ready available safe valid known probes,
    SourceCurrentAllocatedSharedEditWorkerCompletion.node_complete actual⟩

/-- Initial selected child support derives its ordered graph without closing other children. -/
theorem children_finite (inventory : Inventory) {entries offset values} {before : SharedState width}
    (ranges : ChildrenRanges record originals entries offset values before)
    (populated : Populated (.editBelow entries)) (allowed : Allowed record (.editBelow entries))
    (ready : Ready formulas solver inventory record originals base before)
    (available : Values before.checked.native.machine.heap values) (safe : ChildrenSafe entries offset values)
    (memos : Memos) (valid : MemoValid before.checked.native.machine.heap memos)
    (probes : ProbeHeap before.checked.native.machine.heap) :
    ∃ results after next final, ∃ actual : EditChildren record originals entries offset values before results after,
      ChildrenReads formulas solver base actual memos final ∧
      ChildrenReceipt formulas solver next record originals base values before results after memos final ∧
      ProbeHeap after.checked.native.machine.heap ∧
      StableRun (fun e p h m s n => children (edit record originals e p h m s n) entries offset values before) results after := by
  obtain ⟨results, after, next, final, actual, reads, receipt⟩ :=
    SourceCurrentAllocatedSharedEditComplete.children_complete formulas solver record originals base known domains coherent active
      inventory ranges populated allowed ready available safe memos valid
  exact ⟨results, after, next, final, actual, reads, receipt,
    SourceCurrentAllocatedProbeEdits.children_heap reads populated allowed ready available safe valid known probes,
    SourceCurrentAllocatedSharedEditWorkerCompletion.children_complete actual⟩

/-- Initial list support constructs the literal worker and its same full physical receipt. -/
theorem list_finite (inventory : Inventory) {edits values} {before : SharedState width}
    (ranges : ListRanges record originals edits values before)
    (populated : Populated edits) (allowed : Allowed record edits)
    (ready : Ready formulas solver inventory record originals base before)
    (available : Values before.checked.native.machine.heap values) (safe : ListSafe edits values)
    (memos : Memos) (valid : MemoValid before.checked.native.machine.heap memos)
    (probes : ProbeHeap before.checked.native.machine.heap) :
    ∃ results after next final, ∃ actual : EditList record originals edits values before results after,
      ListReads formulas solver base actual memos final ∧
      ChildrenReceipt formulas solver next record originals base values before results after memos final ∧
      ProbeHeap after.checked.native.machine.heap ∧
      StableRun (fun e p h m s n => editList (edit record originals e p h m s n) edits values before) results after := by
  obtain ⟨results, after, next, final, actual, reads, receipt⟩ :=
    SourceCurrentAllocatedSharedEditComplete.list_complete formulas solver record originals base known domains coherent active
      inventory ranges populated allowed ready available safe memos valid
  exact ⟨results, after, next, final, actual, reads, receipt,
    SourceCurrentAllocatedProbeEdits.list_heap reads populated allowed ready available safe valid known probes,
    SourceCurrentAllocatedSharedEditWorkerCompletion.list_complete actual⟩

/-- A supplied successful node return receives the graph and receipt constructed from initial support. -/
theorem node_verified (inventory : Inventory) {e p h m s n : Nat} {edits value result}
    {before after : SharedState width} (ranges : NodeRanges record originals edits value before)
    (populated : Populated edits) (nonempty : HasLeaf edits) (allowed : Allowed record edits)
    (ready : Ready formulas solver inventory record originals base before)
    (available : Available before.checked.native.machine.heap value) (safe : Safe edits value)
    (memos : Memos) (valid : MemoValid before.checked.native.machine.heap memos)
    (probes : ProbeHeap before.checked.native.machine.heap)
    (done : edit record originals e p h m s n edits value before = .done result after) :
    ∃ next final, ∃ actual : EditNode record originals edits value before result after,
      NodeReads formulas solver base actual memos final ∧
      NodeReceipt formulas solver next record originals base value before result after memos final ∧
      ProbeHeap after.checked.native.machine.heap ∧
      StableRun (fun e p h m s n => edit record originals e p h m s n edits value before) result after := by
  obtain ⟨candidate, reached, next, final, actual, reads, receipt, afterProbes, stable⟩ :=
    node_finite formulas solver record originals base known domains coherent active inventory ranges
      populated nonempty allowed ready available safe memos valid probes
  obtain ⟨a, b, c, d, f, g, returns⟩ := stable
  obtain ⟨rfl, rfl⟩ := SourceCurrentAllocatedSharedEditWorkerStability.edit_done_unique done
    (returns a b c d f g (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _))
  exact ⟨next, final, actual, reads, receipt, afterProbes,
    SourceCurrentAllocatedSharedEditWorkerCompletion.node_complete actual⟩

/-- A supplied successful child scan receives its exact ordered graph and returned inventory. -/
theorem children_verified (inventory : Inventory) {e p h m s n : Nat} {entries offset values results}
    {before after : SharedState width} (ranges : ChildrenRanges record originals entries offset values before)
    (populated : Populated (.editBelow entries)) (allowed : Allowed record (.editBelow entries))
    (ready : Ready formulas solver inventory record originals base before)
    (available : Values before.checked.native.machine.heap values) (safe : ChildrenSafe entries offset values)
    (memos : Memos) (valid : MemoValid before.checked.native.machine.heap memos)
    (probes : ProbeHeap before.checked.native.machine.heap)
    (done : children (edit record originals e p h m s n) entries offset values before = .done results after) :
    ∃ next final, ∃ actual : EditChildren record originals entries offset values before results after,
      ChildrenReads formulas solver base actual memos final ∧
      ChildrenReceipt formulas solver next record originals base values before results after memos final ∧
      ProbeHeap after.checked.native.machine.heap ∧
      StableRun (fun e p h m s n => children (edit record originals e p h m s n) entries offset values before) results after := by
  obtain ⟨candidate, reached, next, final, actual, reads, receipt, afterProbes, stable⟩ :=
    children_finite formulas solver record originals base known domains coherent active inventory ranges
      populated allowed ready available safe memos valid probes
  obtain ⟨a, b, c, d, f, g, returns⟩ := stable
  obtain ⟨rfl, rfl⟩ := SourceCurrentAllocatedSharedEditWorkerStability.children_edit_done_unique done
    (returns a b c d f g (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _))
  exact ⟨next, final, actual, reads, receipt, afterProbes,
    SourceCurrentAllocatedSharedEditWorkerCompletion.children_complete actual⟩

/-- A supplied successful list worker receives the same graph, global reads, and full physical state. -/
theorem list_verified (inventory : Inventory) {e p h m s n : Nat} {edits values results}
    {before after : SharedState width} (ranges : ListRanges record originals edits values before)
    (populated : Populated edits) (allowed : Allowed record edits)
    (ready : Ready formulas solver inventory record originals base before)
    (available : Values before.checked.native.machine.heap values) (safe : ListSafe edits values)
    (memos : Memos) (valid : MemoValid before.checked.native.machine.heap memos)
    (probes : ProbeHeap before.checked.native.machine.heap)
    (done : editList (edit record originals e p h m s n) edits values before = .done results after) :
    ∃ next final, ∃ actual : EditList record originals edits values before results after,
      ListReads formulas solver base actual memos final ∧
      ChildrenReceipt formulas solver next record originals base values before results after memos final ∧
      ProbeHeap after.checked.native.machine.heap ∧
      StableRun (fun e p h m s n => editList (edit record originals e p h m s n) edits values before) results after := by
  obtain ⟨candidate, reached, next, final, actual, reads, receipt, afterProbes, stable⟩ :=
    list_finite formulas solver record originals base known domains coherent active inventory ranges
      populated allowed ready available safe memos valid probes
  obtain ⟨a, b, c, d, f, g, returns⟩ := stable
  obtain ⟨rfl, rfl⟩ := SourceCurrentAllocatedSharedEditWorkerStability.editList_done_unique done
    (returns a b c d f g (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _))
  exact ⟨next, final, actual, reads, receipt, afterProbes,
    SourceCurrentAllocatedSharedEditWorkerCompletion.list_complete actual⟩

/-- The actual executable list return narrows and retains each original class-satisfying forest. -/
theorem list_language (inventory : Inventory) {e p h m s n : Nat} {edits values results}
    {before after : SharedState width} (ranges : ListRanges record originals edits values before)
    (editsValid : SourceEqualityEdits.Valid edits) (populated : Populated edits) (allowed : Allowed record edits)
    (ready : Ready formulas solver inventory record originals base before)
    (available : Values before.checked.native.machine.heap values) (safe : ListSafe edits values)
    (memos : Memos) (valid : MemoValid before.checked.native.machine.heap memos)
    (probes : ProbeHeap before.checked.native.machine.heap)
    (done : editList (edit record originals e p h m s n) edits values before = .done results after)
    (ambient : InternedGuardedLanguage.Env Symbol) (rootSymbol : Symbol) (rootTerms terms : List (Term Symbol)) :
    (All₂ (meaning (SourceEqualityPCSGuard.holds formulas solver) ambient) results terms →
      All₂ (meaning (SourceEqualityPCSGuard.holds formulas solver) ambient) values terms) ∧
    (All₂ (meaning (SourceEqualityPCSGuard.holds formulas solver) ambient) originals rootTerms →
      EqualityNormalize.ClassSat (.node rootSymbol rootTerms) record.paths →
      SourceEqualityEditAPI.ListCondition
        (fun path part => Term.atPath (.node rootSymbol rootTerms) path = some part) edits terms →
      All₂ (meaning (SourceEqualityPCSGuard.holds formulas solver) ambient) values terms →
      All₂ (meaning (SourceEqualityPCSGuard.holds formulas solver) ambient) results terms) := by
  obtain ⟨_, _, actual, reads, _⟩ := list_verified formulas solver record originals base known domains coherent active
    inventory ranges populated allowed ready available safe memos valid probes done
  exact SourceCurrentAllocatedSharedEditLanguage.list formulas solver base record originals ambient rootSymbol rootTerms
    reads editsValid populated allowed ready available safe valid terms

end MicroCFTA.SourceCurrentAllocatedSharedEditWorkerActual
