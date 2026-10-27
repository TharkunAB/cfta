import MicroCFTA.SourcePruningEnumerationClassEditArity

/-!
# Arity through the actual class right fold

Each class uses the checked state and full memos returned by its tail.
Final Empty propagation changes no heap.
All original class-domain and memo admissions remain explicit.
-/
namespace MicroCFTA.SourcePruningEnumerationClassEditArity
open Cache Language InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open SourceEqualityProjectionPathDomain
open SourceCurrentAllocatedNativeInventoryState (Inventory At)
open SourceCurrentAllocatedClassEditPlan
open SourcePruningEnumerationArityOrigins (Heap)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Memo" => SourceCurrentMemoMergeGraph.Memo Symbol Guard
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Ready" => SourceCurrentConjunctionClassScan.Ready
local notation "Valid" => EndpointMemoGateTrace.Valid
local notation "Stored" => SourceCurrentMemoMergeEffects.Stored
local notation "CacheCovers" => SourceCurrentMemoMergeLanguage.CacheCovers
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat}

/-- The actual compiled class derives arity without a new class-domain gate. -/
theorem class_heap
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (record : SourceEqualityClassOrder.Record)
    (coherent : SourceEqualityClassOrder.Coherent record) (active : EqualityNormalize.Nontrivial record.paths)
    {values results : List (Value Symbol Guard)} {before after : Checked width} {memo saved : Memo}
    {memos final : Memos}
    {actual : SourceCurrentAllocatedClassEdits.Class record values before memo results after saved}
    (reads : SourceCurrentAllocatedClassEdits.ClassReads formulas solver actual memos final)
    (ready : Ready before) (admitted : At formulas solver inventory before)
    (available : Values before.native.machine.heap values)
    (domains : ∀ path ∈ record.paths, ForestClosed (path.map Int.ofNat) values)
    (stored : Stored before.native.machine.heap memo)
    (covered : ∀ ambient, CacheCovers (SourceEqualityPCSGuard.holds formulas solver) ambient memo)
    (valid : Valid before.native.machine.heap memos) (heap : Heap before.native.machine.heap) :
    Heap after.native.machine.heap := by
  cases reads with
  | edit lower =>
      have initialReady := SourceCurrentAllocatedSharedTargetState.initial_ready
        formulas solver inventory record values before.native.machine.heap before memo ready admitted
        (SourceEqualityRequiredCache.pure_keeps _ ready.semantic.ready) stored covered
      have safe : SourceCurrentAllocatedSharedEditEffects.ListSafe (compiled record) values := by
        obtain ⟨entries, built⟩ := compiled_children record coherent active
        rw [built]
        exact compiled_safe record coherent values domains entries built
      exact list_heap lower available (compiled_populated record) (compiled_allowed record)
        initialReady available safe valid heap

/-- The actual right fold preserves arity at each complete tail and head endpoint. -/
theorem fold_heap
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) {records values results} {before after : Checked width} {memo saved : Memo}
    {memos final : Memos}
    {actual : SourceCurrentAllocatedClassPass.Fold records values before memo results after saved}
    (reads : SourceCurrentAllocatedClassPass.FoldReads formulas solver actual memos final)
    (coherent : ∀ record ∈ records, SourceEqualityClassOrder.Coherent record)
    (active : ∀ record ∈ records, EqualityNormalize.Nontrivial record.paths)
    (ready : Ready before) (admitted : At formulas solver inventory before)
    (available : Values before.native.machine.heap values)
    (domains : ∀ record ∈ records, ∀ path ∈ record.paths, ForestClosed (path.map Int.ofNat) values)
    (stored : Stored before.native.machine.heap memo)
    (covered : ∀ ambient, CacheCovers (SourceEqualityPCSGuard.holds formulas solver) ambient memo)
    (valid : Valid before.native.machine.heap memos) (heap : Heap before.native.machine.heap) :
    Heap after.native.machine.heap := by
  induction reads generalizing inventory with
  | nil => exact heap
  | @cons records values before memo middle step current record results after saved memos stepMemos final tail head first last ih =>
      have tailCoherent := fun own member => coherent own (List.mem_cons_of_mem _ member)
      have tailActive := fun own member => active own (List.mem_cons_of_mem _ member)
      have tailDomains := fun own member => domains own (List.mem_cons_of_mem _ member)
      obtain ⟨next, firstReceipt⟩ := SourceCurrentAllocatedClassPass.Fold.verified formulas solver inventory first
        tailCoherent tailActive ready admitted available tailDomains stored covered valid
      have tailHeap := ih inventory tailCoherent tailActive ready admitted available tailDomains stored covered valid heap
      exact class_heap formulas solver next record (coherent _ List.mem_cons_self) (active _ List.mem_cons_self)
        last firstReceipt.ready firstReceipt.admitted firstReceipt.available
        (fun path member => firstReceipt.domains _ (domains _ List.mem_cons_self path member))
        firstReceipt.stored firstReceipt.covered firstReceipt.globals.valid tailHeap

/-- Final propagation retains the same actual heap returned by the complete fold. -/
theorem pass_heap
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) {records values results} {before after : Checked width} {memo saved : Memo}
    {memos final : Memos}
    {actual : SourceCurrentAllocatedClassPass.Pass records values before memo results after saved}
    (reads : SourceCurrentAllocatedClassPass.PassReads formulas solver actual memos final)
    (coherent : ∀ record ∈ records, SourceEqualityClassOrder.Coherent record)
    (active : ∀ record ∈ records, EqualityNormalize.Nontrivial record.paths)
    (ready : Ready before) (admitted : At formulas solver inventory before)
    (available : Values before.native.machine.heap values)
    (domains : ∀ record ∈ records, ∀ path ∈ record.paths, ForestClosed (path.map Int.ofNat) values)
    (stored : Stored before.native.machine.heap memo)
    (covered : ∀ ambient, CacheCovers (SourceEqualityPCSGuard.holds formulas solver) ambient memo)
    (valid : Valid before.native.machine.heap memos) (heap : Heap before.native.machine.heap) :
    Heap after.native.machine.heap := by
  cases reads with
  | done read => exact fold_heap formulas solver inventory read coherent active ready admitted available domains stored covered valid heap

end MicroCFTA.SourcePruningEnumerationClassEditArity
