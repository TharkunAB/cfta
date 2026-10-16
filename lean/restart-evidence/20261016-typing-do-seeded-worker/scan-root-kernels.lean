import MicroCFTA.SourceCurrentAllocatedScanWorkerActual

namespace MicroCFTA.ScanWorkerRootKernels
open Language EqualityNormalize InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open SourceRecursiveIntersectionCode
open SourceCurrentAllocatedNativeInventoryState (Inventory At)
open SourceCurrentAllocatedPartialInvariant (Context Post)
open SourceCurrentAllocatedScanWorker (scan)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Memo" => SourceCurrentEmptinessMemo.Memo
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "source" => SourceMemoGate.unconstrained
local notation "reaches" => SourceEndpointReachability.reaches source
local notation "Ranges" => SourceCurrentConjunctionClassScanCompletion.Ranges
local notation "WordRanges" => SourceCurrentAllocatedNativeRequestBounds.WordRanges
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq (Value Symbol Guard)] {width : Nat}

theorem literal_stop_refutes_original_class
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    {inventory : Inventory} {g s p h n budget : Nat} {values : List (Value Symbol Guard)}
    {classes selected : Constraints} {paths : Class} {before : Caller width} {after : Checked width}
    {saved : Memo} {memos : Memos} (initial : Context formulas solver inventory before memos)
    (available : Values before.checked.native.machine.heap values)
    (proper : ∀ paths ∈ classes, ∀ path ∈ paths, path ≠ []) (active : ∀ paths ∈ classes, Nontrivial paths)
    (ranges : Ranges budget source reaches values classes before.checked before.fourth)
    (done : scan g s p h n budget values classes before.checked before.fourth = .done (some paths, selected) after saved) :
    ∃ next final, Post formulas solver next before
        (SourceCurrentAllocatedPartialState.advance before after saved before.merge) final ∧
      paths ∈ classes ∧ ∀ ambient symbol terms,
        All₂ (InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver) ambient) values terms →
          ¬ClassSat (.node symbol terms) paths := by
  obtain ⟨next, final, _, _, post, _, _, sound⟩ := SourceCurrentAllocatedScanWorkerActual.verified
    formulas solver initial available proper active ranges done
  obtain ⟨member, refutes⟩ := sound paths rfl
  exact ⟨next, final, post, member, refutes⟩

theorem literal_scan_then_generated_query
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    {inventory : Inventory} {g s p h n budget : Nat} {values : List (Value Symbol Guard)}
    {classes selected : Constraints} {outcome : Option Class} {before : Caller width} {after : Checked width}
    {saved : Memo} {memos : Memos} (initial : Context formulas solver inventory before memos)
    (available : Values before.checked.native.machine.heap values)
    (proper : ∀ paths ∈ classes, ∀ path ∈ paths, path ≠ []) (active : ∀ paths ∈ classes, Nontrivial paths)
    (ranges : Ranges budget source reaches values classes before.checked before.fourth)
    (done : scan g s p h n budget values classes before.checked before.fourth = .done (outcome, selected) after saved)
    (left right : Value Symbol Guard)
    (leftAvailable : Available before.checked.native.machine.heap left)
    (rightAvailable : Available before.checked.native.machine.heap right)
    (leftClosed : left.free = []) (rightClosed : right.free = [])
    (nextRanges : WordRanges (.code (requestNode IntersectionEmptyDomain.emptyDomain left right)) after) :
    ∃ next fuel result final,
      SourceCurrentAllocatedNativeCoveredQuery.Receipt next.source formulas solver
        (Inventory.inputs next (SourceEqualityPCSGuard.holds formulas solver)) fuel left right after result final ∧
      At formulas solver next final ∧ result.free = [] ∧
      ∀ ambient term,
        InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver) ambient result term ↔
          InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver) ambient left term ∧
          InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver) ambient right term := by
  obtain ⟨next, _, _, _, post, _, _, _⟩ := SourceCurrentAllocatedScanWorkerActual.verified
    formulas solver initial available proper active ranges done
  obtain ⟨finalInventory, fuel, result, final, _, _, query, finalAt⟩ :=
    SourceCurrentAllocatedNativeInventoryState.query_complete next formulas solver after post.context.ready.good
      post.context.admitted post.context.ready.scopedCache post.context.ready.semantic post.context.ready.idle
      left right (post.effects.keeps.available left leftAvailable) (post.effects.keeps.available right rightAvailable)
      leftClosed rightClosed nextRanges
  exact ⟨finalInventory, fuel, result, final, query, finalAt, query.closed, query.meaning⟩

end MicroCFTA.ScanWorkerRootKernels

#print axioms MicroCFTA.ScanWorkerRootKernels.literal_stop_refutes_original_class
#check @MicroCFTA.ScanWorkerRootKernels.literal_stop_refutes_original_class
#print axioms MicroCFTA.ScanWorkerRootKernels.literal_scan_then_generated_query
#check @MicroCFTA.ScanWorkerRootKernels.literal_scan_then_generated_query
