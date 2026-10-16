import MicroCFTA.SourceCurrentConjunctionRequiredGlobalMemos
import MicroCFTA.SourceCurrentConjunctionAllocatedRequired
namespace MicroCFTA.RequiredGlobalIndependentKernels
open Cache Language EqualityNormalize SourceEqualityClassOrder
open InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
open InternedNestedProvenance (Values)
open SourceEqualityOriginalAllocationHistory
open SourceCurrentConjunctionClassScan
open SourceCurrentAllocatedNativeInventoryState (Inventory At)
open SourceCurrentConjunctionAllocatedClassEntry (prefixState)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Memo" => SourceCurrentEmptinessMemo.Memo
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Valid" => EndpointMemoGateTrace.Valid
local notation "Key" => SourceEqualityPartialConstraintKey.Key
local notation "Allocated" => SourceEqualityConjoinAllocation.Constraint FullSyntax.Formula
local notation "Stored" => SourceEqualityConstraintAllocation.Value
local notation "u" => SourceMemoGate.unconstrained
local notation "reaches" => SourceEndpointReachability.reaches SourceMemoGate.unconstrained
variable {width : Nat} [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
  [DecidableEq (Value Symbol Guard)]
section Scan
variable (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
 (inventory : Inventory) {budget : Nat} {values : List (Value Symbol Guard)} {classes selected : Constraints}
 {before after : Checked width} {memo saved : Memo}
 (actual : Scan budget u reaches values classes before memo none selected after saved)
 (ready : Ready before) (admitted : At formulas solver inventory before)
 (available : Values before.native.machine.heap values)
 (proper : ∀ paths ∈ classes, ∀ path ∈ paths, path ≠ []) (active : ∀ paths ∈ classes, Nontrivial paths)
 (correct : SourceCurrentEmptinessMemo.Correct formulas solver before.native.machine.heap memo)
 (ranges : SourceCurrentConjunctionClassScanCompletion.Ranges budget u reaches values classes before memo)
 (memos : Memos) (valid : Valid before.native.machine.heap memos)

-- The derived worker retains both native families, the domain cache, and the exact operation state.
example : ∃ scanMemos finalMemos next results heap,
 SourceCurrentConjunctionClassScanGlobalMemos.ScanReads actual memos scanMemos ∧
 SourceCurrentConjunctionRequired.Receipt formulas solver next selected values results after (advanceHeap after heap) ∧
 (advanceHeap after heap).native.nodes = after.native.nodes ∧
 (advanceHeap after heap).native.edges = after.native.edges ∧
 (advanceHeap after heap).native.machine.domains = after.native.machine.domains ∧
 (advanceHeap after heap).operations = after.operations ∧
 Valid heap finalMemos ∧ finalMemos.query = scanMemos.query := by
 obtain ⟨scanMemos, finalMemos, next, results, heap, read, receipt, _, finalValid, _, query, _⟩ :=
  SourceCurrentConjunctionRequiredGlobalMemos.scan_required_memos formulas solver inventory actual ready admitted
   available proper active correct ranges memos valid
 exact ⟨scanMemos, finalMemos, next, results, heap, read, receipt,
  receipt.nodes, receipt.edges, receipt.domains, receipt.operations, finalValid, query⟩

-- The same receipt gives literal completion and the independent exact filter language.
example : ∃ results heap fuel readFuel,
 SourceEqualityRequiredExecution.requireAll fuel readFuel (SourceEqualitySelectedRequired.paths selected)
   values after.native.machine.heap = .done results heap ∧
 (∀ holds ambient terms, All₂ (InternedGuardedLanguage.meaning holds ambient) results terms ↔
  All₂ (InternedGuardedLanguage.meaning holds ambient) values terms ∧
  SourceEqualityRequiredAPI.ForestRequired (SourceEqualitySelectedRequired.paths selected) terms) := by
 obtain ⟨_, _, _, results, heap, _, receipt, _⟩ :=
  SourceCurrentConjunctionRequiredGlobalMemos.scan_required_memos formulas solver inventory actual ready admitted
   available proper active correct ranges memos valid
 obtain ⟨fuel, readFuel, enough⟩ := receipt.stable
 exact ⟨results, heap, fuel, readFuel, enough fuel readFuel (Nat.le_refl _) (Nat.le_refl _), receipt.language⟩
end Scan

-- Original positional records supply every selected path domain at the final required heap.
example (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
 (inventory : Inventory) (records : List Record) {budget : Nat} {values : List (Value Symbol Guard)}
 {selected : Constraints} {before after : Checked width} {memo saved : Memo}
 (actual : Scan budget u reaches values (records.map Record.paths) before memo none selected after saved)
 (ready : Ready before) (admitted : At formulas solver inventory before)
 (available : Values before.native.machine.heap values)
 (proper : ∀ record ∈ records, ∀ path ∈ record.paths, path ≠ [])
 (fields : ∀ record ∈ records, Coherent record ∧ EqualityTrie.Ascending record.trie ∧ Nontrivial record.paths)
 (correct : SourceCurrentEmptinessMemo.Correct formulas solver before.native.machine.heap memo)
 (ranges : SourceCurrentConjunctionClassScanCompletion.Ranges budget u reaches values (records.map Record.paths) before memo)
 (memos : Memos) (valid : Valid before.native.machine.heap memos) :
 ∃ (kept : List Record) (results : List (Value Symbol Guard)), kept.Sublist records ∧ kept.map Record.paths = selected ∧
  ∀ record ∈ kept, ∀ path ∈ record.paths,
   SourceEqualityProjectionPathDomain.ForestClosed (path.map Int.ofNat) results := by
 obtain ⟨kept, _, _, _, results, _, _, sub, same, _, _, receipt, _⟩ :=
  SourceCurrentConjunctionRequiredGlobalMemos.records_required_memos formulas solver inventory records actual ready admitted
   available proper fields correct ranges memos valid
 refine ⟨kept, results, sub, same, ?_⟩
 intro record member path present
 exact receipt.paths path (List.mem_flatten.mpr
  ⟨record.paths, same ▸ List.mem_map.mpr ⟨record, member, rfl⟩, present⟩)

-- Repeated path fields retain both literal source occurrences in source order.
example {budget : Nat} {values : List (Value Symbol Guard)} {before : Checked width}
 {firstHeap secondHeap : State Symbol Guard} {memo : Memo} (first second : Record)
 (samePaths : second.paths = first.paths)
 (firstFalse : EndpointStatefulGateTrace.ClassTrace u reaches values first.paths before.native.machine.heap false firstHeap)
 (secondFalse : EndpointStatefulGateTrace.ClassTrace u reaches values first.paths firstHeap false secondHeap) :
 SourceCurrentConjunctionSelectedRecords.Retained
  (Scan.selected firstFalse (Scan.selected secondFalse (Scan.nil :
    Scan budget u reaches values [] (advanceHeap (advanceHeap before firstHeap) secondHeap) memo none []
     (advanceHeap (advanceHeap before firstHeap) secondHeap) memo))) [first, second] [first, second] := by
 exact .selected (primary := firstFalse) rfl (.selected (primary := secondFalse) samePaths .nil)

-- The constructed entry derives a current scan and a successful required continuation with an empty fourth table.
example {initialCache finalCache : Cache.State Key} {originals : List Guard}
 (width : Nat) (history : History initialCache finalCache originals) (valid : Cache.Valid initialCache)
 (expression : InternedNestedConstruction.Syntax Symbol Guard)
 (covered : ∀ original ∈ SourceEqualityConstraintOrigins.guards expression, original ∈ originals)
 (value : Value Symbol Guard) (heap : State Symbol Guard)
 (built : InternedFreshOrdinaryConstruction.build expression [] empty = .done value heap)
 (edge : EdgeValue Symbol Guard) (resident : EdgeResident heap edge)
 (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
 (budget : Nat) (memos : Memos) (globals : Valid heap memos) :
 ∃ loaded : Allocated,
  SourceEqualityConstraintFieldLookup.load edge.entry.key.constraint finalCache = .ok (some loaded) ∧
  ∀ inherited : Stored, SourceEqualityConstraintAllocation.Ready finalCache inherited →
   ∀ output : List Record,
    (SourceEqualityPartialPrecheckAllocation.run loaded.stored loaded.guard inherited
      (SourceEqualityConstraintMemoAllocation.initial finalCache)).1 = .ok (.classes output) →
    SourceCurrentConjunctionClassScanCompletion.Ranges budget u reaches edge.children (output.map Record.paths)
      (prefixState width heap loaded inherited finalCache) SourceCurrentEmptinessMemo.empty →
    ∃ outcome selected after saved,
     ∃ _actual : Scan budget u reaches edge.children (output.map Record.paths)
       (prefixState width heap loaded inherited finalCache) SourceCurrentEmptinessMemo.empty outcome selected after saved,
     Ready after ∧ (outcome = none → ∃ results requiredHeap fuel readFuel,
      SourceEqualityRequiredExecution.requireAll fuel readFuel (SourceEqualitySelectedRequired.paths selected)
       edge.children after.native.machine.heap = .done results requiredHeap ∧
      SourceCurrentEmptinessMemo.Correct formulas solver requiredHeap saved) := by
 obtain ⟨loaded, lookup, _, _, live⟩ := SourceCurrentConjunctionAllocatedRequired.finite width history valid
   expression covered value heap built edge resident formulas solver budget SourceCurrentEmptinessMemo.empty
   (SourceCurrentEmptinessMemo.empty_correct formulas solver heap) memos globals
 refine ⟨loaded, lookup, ?_⟩
 intro inherited inheritedReady output done ranges
 obtain ⟨outcome, selected, after, saved, _, actual, ready, _, _, successful⟩ :=
  live inherited inheritedReady output done ranges
 refine ⟨outcome, selected, after, saved, actual, ready, ?_⟩
 intro none
 obtain ⟨_, _, _, _, results, requiredHeap, _, _, _, _, _, receipt, _, _, correct⟩ := successful none
 obtain ⟨fuel, readFuel, enough⟩ := receipt.stable
 exact ⟨results, requiredHeap, fuel, readFuel, enough fuel readFuel (Nat.le_refl _) (Nat.le_refl _), correct⟩
end MicroCFTA.RequiredGlobalIndependentKernels
