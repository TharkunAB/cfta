import MicroCFTA.SourceCurrentAllocatedClassEditPlan
import MicroCFTA.SourceCurrentAllocatedSharedEditGraph
import MicroCFTA.SourceCurrentAllocatedSharedEditComplete
import MicroCFTA.SourceCurrentAllocatedSharedEditLanguage

/-!
# Single-class edits in the current checked state

Each class captures its actual entry forest. Its target slots start empty.
Native tables, equality operations, and the completed merge table remain
warm. The literal signed compiler determines the ordered traversal.
-/
namespace MicroCFTA.SourceCurrentAllocatedClassEdits
open Cache Language InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open InternedGuardedLanguage (meaning)
open SourceCurrentAllocatedNativeEffects (physical)
open SourceCurrentAllocatedNativeInventoryState (Inventory At)
open SourceCurrentAllocatedClassEditPlan
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Shared" => SourceCurrentAllocatedSharedTargetState.State
local notation "Memo" => SourceCurrentMemoMergeGraph.Memo Symbol Guard
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Ready" => SourceCurrentConjunctionClassScan.Ready
local notation "Valid" => EndpointMemoGateTrace.Valid
variable {width : Nat}

/-- A class captures its entry values and clears only its local target slots. -/
inductive Class [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (record : SourceEqualityClassOrder.Record) (values : List (Value Symbol Guard))
    (before : Checked width) (memo : Memo) :
    List (Value Symbol Guard) → Checked width → Memo → Prop where
  | edit (actual : SourceCurrentAllocatedSharedEditGraph.EditList record values (compiled record) values
      (SourceCurrentAllocatedSharedTargetState.initial before memo) results shared) :
      Class record values before memo results shared.checked shared.memo

/-- The actual compiled class retains its exact ordered lower read graph. -/
inductive ClassReads [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula) :
    {record : SourceEqualityClassOrder.Record} → {values : List (Value Symbol Guard)} →
    {before after : Checked width} → {memo saved : Memo} → {results : List (Value Symbol Guard)} →
    Class record values before memo results after saved → Memos → Memos → Prop where
  | edit {record : SourceEqualityClassOrder.Record} {values results : List (Value Symbol Guard)}
      {before : Checked width} {memo : Memo} {shared : Shared width}
      {actual : SourceCurrentAllocatedSharedEditGraph.EditList record values (compiled record) values
        (SourceCurrentAllocatedSharedTargetState.initial before memo) results shared}
      (reads : SourceCurrentAllocatedSharedEditGraph.ListReads formulas solver before.native.machine.heap actual memos final) :
      ClassReads formulas solver (Class.edit actual) memos final

/-- A class requires only the checks reached by its compiled edits from the actual entry. -/
def ClassRanges [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (record : SourceEqualityClassOrder.Record) (values : List (Value Symbol Guard)) (before : Checked width) (memo : Memo) : Prop :=
  SourceCurrentAllocatedSharedEditRanges.ListRanges record values (compiled record) values
    (SourceCurrentAllocatedSharedTargetState.initial before memo)

/-- A class return retains physical state, the current inventory, and independent language bounds. -/
structure Receipt [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (record : SourceEqualityClassOrder.Record) (values : List (Value Symbol Guard))
    (before : Checked width) (memo : Memo) (results : List (Value Symbol Guard)) (after : Checked width)
    (saved : Memo) (memos final : Memos) : Prop where
  ready : Ready after
  admitted : At formulas solver inventory after
  effects : SourceCurrentConjunctionRowsAllocation.Effects (physical before) (physical after)
  extension : SourceRecursiveIntersectionKernel.Extension before.native.machine after.native.machine
  stored : SourceCurrentMemoMergeEffects.Stored after.native.machine.heap saved
  covered : ∀ ambient, SourceCurrentMemoMergeLanguage.CacheCovers (SourceEqualityPCSGuard.holds formulas solver) ambient saved
  available : Values after.native.machine.heap results
  transport : All₂ SourceCurrentEditDomains.Transport values results
  domains : ∀ path, SourceEqualityProjectionPathDomain.ForestClosed path values →
    SourceEqualityProjectionPathDomain.ForestClosed path results
  retained : Extends memo saved
  globals : SourceCurrentSubsumesQueryMemos.Effect before.native.machine.heap after.native.machine.heap memos final
  language : ∀ ambient symbol terms,
    (All₂ (meaning (SourceEqualityPCSGuard.holds formulas solver) ambient) results terms →
      All₂ (meaning (SourceEqualityPCSGuard.holds formulas solver) ambient) values terms) ∧
    (EqualityNormalize.ClassSat (.node symbol terms) record.paths →
      (All₂ (meaning (SourceEqualityPCSGuard.holds formulas solver) ambient) results terms ↔
        All₂ (meaning (SourceEqualityPCSGuard.holds formulas solver) ambient) values terms))

/-- Annotated actual class execution derives physical effects, arbitrary path domains, and language. -/
theorem verified [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (record : SourceEqualityClassOrder.Record)
    (coherent : SourceEqualityClassOrder.Coherent record) (active : EqualityNormalize.Nontrivial record.paths)
    {values results : List (Value Symbol Guard)} {before after : Checked width} {memo saved : Memo}
    {memos final : Memos} {actual : Class record values before memo results after saved}
    (reads : ClassReads formulas solver actual memos final)
    (ready : Ready before) (admitted : At formulas solver inventory before)
    (available : Values before.native.machine.heap values)
    (domains : ∀ path ∈ record.paths, SourceEqualityProjectionPathDomain.ForestClosed (path.map Int.ofNat) values)
    (stored : SourceCurrentMemoMergeEffects.Stored before.native.machine.heap memo)
    (covered : ∀ ambient, SourceCurrentMemoMergeLanguage.CacheCovers (SourceEqualityPCSGuard.holds formulas solver) ambient memo)
    (valid : Valid before.native.machine.heap memos) :
    ∃ next, Receipt formulas solver next record values before memo results after saved memos final := by
  cases reads with
  | edit lower =>
      have initialReady := SourceCurrentAllocatedSharedTargetState.initial_ready
        formulas solver inventory record values before.native.machine.heap before memo ready admitted
        (SourceEqualityRequiredCache.pure_keeps _ ready.semantic.ready) stored covered
      have safe : SourceCurrentAllocatedSharedEditEffects.ListSafe (compiled record) values := by
        obtain ⟨entries, built⟩ := compiled_children record coherent active
        rw [built]
        exact compiled_safe record coherent values domains entries built
      obtain ⟨next, checked⟩ := SourceCurrentAllocatedSharedEditEffects.list_effects lower
        (compiled_populated record) (compiled_allowed record) initialReady available safe valid
      refine ⟨next, checked.ready.checked, checked.ready.admitted, checked.effects, checked.extension,
        checked.ready.stored, checked.ready.covered, checked.available, checked.transport,
        (fun path domain => SourceCurrentEditDomains.transport_forest checked.transport path domain),
        checked.retained, checked.globals, ?_⟩
      intro ambient symbol terms
      have bounds := SourceCurrentAllocatedSharedEditLanguage.list formulas solver before.native.machine.heap
        record values ambient symbol terms lower (compiled_valid record) (compiled_populated record)
        (compiled_allowed record) initialReady available safe valid terms
      exact ⟨bounds.1, fun satisfied => ⟨bounds.1, fun accepted =>
        bounds.2 accepted satisfied (compiled_condition record coherent active symbol terms) accepted⟩⟩

/-- Initial checked facts and actual-prefix ranges construct one compiled class and all returned receipts. -/
theorem finite [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (record : SourceEqualityClassOrder.Record)
    (coherent : SourceEqualityClassOrder.Coherent record) (active : EqualityNormalize.Nontrivial record.paths)
    (values : List (Value Symbol Guard)) (before : Checked width) (memo : Memo)
    (ready : Ready before) (admitted : At formulas solver inventory before)
    (available : Values before.native.machine.heap values)
    (domains : ∀ path ∈ record.paths, SourceEqualityProjectionPathDomain.ForestClosed (path.map Int.ofNat) values)
    (stored : SourceCurrentMemoMergeEffects.Stored before.native.machine.heap memo)
    (covered : ∀ ambient, SourceCurrentMemoMergeLanguage.CacheCovers (SourceEqualityPCSGuard.holds formulas solver) ambient memo)
    (ranges : ClassRanges record values before memo) (memos : Memos) (valid : Valid before.native.machine.heap memos) :
    ∃ results after saved next final, ∃ actual : Class record values before memo results after saved,
      ClassReads formulas solver actual memos final ∧
      Receipt formulas solver next record values before memo results after saved memos final := by
  have initialReady := SourceCurrentAllocatedSharedTargetState.initial_ready
    formulas solver inventory record values before.native.machine.heap before memo ready admitted
    (SourceEqualityRequiredCache.pure_keeps _ ready.semantic.ready) stored covered
  have safe : SourceCurrentAllocatedSharedEditEffects.ListSafe (compiled record) values := by
    obtain ⟨entries, built⟩ := compiled_children record coherent active
    rw [built]
    exact compiled_safe record coherent values domains entries built
  obtain ⟨results, shared, _, final, lower, lowerReads, _⟩ := SourceCurrentAllocatedSharedEditComplete.list_complete
    formulas solver record values before.native.machine.heap available domains coherent active inventory
    ranges (compiled_populated record) (compiled_allowed record) initialReady available safe memos valid
  have actual : Class record values before memo results shared.checked shared.memo := .edit lower
  have reads : ClassReads formulas solver actual memos final := .edit lowerReads
  obtain ⟨next, receipt⟩ := verified formulas solver inventory record coherent active reads
    ready admitted available domains stored covered valid
  exact ⟨results, shared.checked, shared.memo, next, final, actual, reads, receipt⟩

/-- A class leaves the fourth memo unchanged and retains its earlier correctness through heap growth. -/
theorem Receipt.fourth_correct [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {formulas : SourceGuards.Formulas FullSyntax.Formula} {solver : SourceGuards.Entailment FullSyntax.Formula}
    {inventory : Inventory} {record : SourceEqualityClassOrder.Record} {values results : List (Value Symbol Guard)}
    {before after : Checked width} {memo saved : Memo} {memos final : Memos}
    (receipt : Receipt formulas solver inventory record values before memo results after saved memos final)
    (fourth : SourceCurrentEmptinessMemo.Memo)
    (correct : SourceCurrentEmptinessMemo.Correct formulas solver before.native.machine.heap fourth) :
    SourceCurrentEmptinessMemo.Correct formulas solver after.native.machine.heap fourth :=
  SourceCurrentEmptinessMemo.grows formulas solver receipt.effects.keeps fourth correct

end MicroCFTA.SourceCurrentAllocatedClassEdits
