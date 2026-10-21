import MicroCFTA.SourceCurrentAllocatedClassEdits
import MicroCFTA.SourceCurrentClassFoldDomains

/-!
# Current checked class right fold and final empty propagation

Each class captures the actual tail return. Only its local slots start empty.
The complete checked state, merge table, and global bundle pass between classes.
Final propagation changes no cache and preserves exact forest language.
-/
namespace MicroCFTA.SourceCurrentAllocatedClassPass
open Cache Language InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open InternedGuardedLanguage (meaning)
open SourceEqualityProjectionPathDomain
open SourceCurrentAllocatedNativeEffects (physical)
open SourceCurrentAllocatedNativeInventoryState (Inventory At)
open SourceCurrentAllocatedClassEdits (Class ClassReads ClassRanges)
open SourceCurrentEditDomains (Transport)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Memo" => SourceCurrentMemoMergeGraph.Memo Symbol Guard
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Valid" => EndpointMemoGateTrace.Valid
local notation "Ready" => SourceCurrentConjunctionClassScan.Ready
local notation "Stored" => SourceCurrentMemoMergeEffects.Stored
local notation "CacheCovers" => SourceCurrentMemoMergeLanguage.CacheCovers
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat}

/-- The head class receives the literal forest and warm tables returned by its tail. -/
inductive Fold :
    List SourceEqualityClassOrder.Record → List (Value Symbol Guard) → Checked width → Memo →
      List (Value Symbol Guard) → Checked width → Memo → Prop where
  | nil : Fold [] values before memo values before memo
  | cons (tail : Fold records values before memo middle next current)
      (head : Class record middle next current results after saved) :
      Fold (record :: records) values before memo results after saved

/-- Source empty propagation runs after the complete right fold. -/
inductive Pass :
    List SourceEqualityClassOrder.Record → List (Value Symbol Guard) → Checked width → Memo →
      List (Value Symbol Guard) → Checked width → Memo → Prop where
  | done (fold : Fold records values before memo results after saved) :
      Pass records values before memo (EqualityLeafProjectionRuntimeEmpty.propagate results) after saved

/-- Each head range plan inspects only an actual completed tail. -/
inductive Ranges :
    List SourceEqualityClassOrder.Record → List (Value Symbol Guard) → Checked width → Memo → Prop where
  | nil : Ranges [] values before memo
  | cons (tail : Ranges records values before memo)
      (head : ∀ middle next current, Fold records values before memo middle next current →
        ClassRanges record middle next current) :
      Ranges (record :: records) values before memo

/-- Actual read receipts retain the same tail and head executions. -/
inductive FoldReads (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) :
    {records : List SourceEqualityClassOrder.Record} → {values results : List (Value Symbol Guard)} →
    {before after : Checked width} → {memo saved : Memo} →
    Fold records values before memo results after saved → Memos → Memos → Prop where
  | nil : FoldReads formulas solver .nil memos memos
  | cons {tail : Fold records values before memo middle next current}
      {head : Class record middle next current results after saved}
      (first : FoldReads formulas solver tail memos stepMemos)
      (last : ClassReads formulas solver head stepMemos final) :
      FoldReads formulas solver (.cons tail head) memos final

/-- Final propagation makes no additional global or native call. -/
inductive PassReads (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) :
    {records : List SourceEqualityClassOrder.Record} → {values results : List (Value Symbol Guard)} →
    {before after : Checked width} → {memo saved : Memo} →
    Pass records values before memo results after saved → Memos → Memos → Prop where
  | done (reads : FoldReads formulas solver actual memos final) :
      PassReads formulas solver (.done actual) memos final

/-- A full pass narrows its forest and retains every class-satisfying original term. -/
structure Receipt (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (inventory : Inventory)
    (records : List SourceEqualityClassOrder.Record) (values : List (Value Symbol Guard))
    (before : Checked width) (memo : Memo) (results : List (Value Symbol Guard))
    (after : Checked width) (saved : Memo) (memos final : Memos) : Prop where
  ready : Ready after
  admitted : At formulas solver inventory after
  effects : SourceCurrentConjunctionRowsAllocation.Effects (physical before) (physical after)
  extension : SourceRecursiveIntersectionKernel.Extension before.native.machine after.native.machine
  stored : Stored after.native.machine.heap saved
  covered : ∀ ambient, CacheCovers (SourceEqualityPCSGuard.holds formulas solver) ambient saved
  available : Values after.native.machine.heap results
  transport : All₂ Transport values results
  domains : ∀ path, ForestClosed path values → ForestClosed path results
  retained : Extends memo saved
  globals : SourceCurrentSubsumesQueryMemos.Effect before.native.machine.heap after.native.machine.heap memos final
  language : ∀ ambient symbol terms,
    (All₂ (meaning (SourceEqualityPCSGuard.holds formulas solver) ambient) results terms →
      All₂ (meaning (SourceEqualityPCSGuard.holds formulas solver) ambient) values terms) ∧
    ((∀ record ∈ records, EqualityNormalize.ClassSat (.node symbol terms) record.paths) →
      (All₂ (meaning (SourceEqualityPCSGuard.holds formulas solver) ambient) results terms ↔
        All₂ (meaning (SourceEqualityPCSGuard.holds formulas solver) ambient) values terms))

omit [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] in
private theorem transport_refl (values : List (Value Symbol Guard)) : All₂ Transport values values := by
  induction values with
  | nil => exact .nil
  | cons value values ih => exact .cons (fun _ domain => domain) ih

omit [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] in
private theorem transport_trans {values middle results : List (Value Symbol Guard)}
    (first : All₂ Transport values middle) (last : All₂ Transport middle results) : All₂ Transport values results := by
  induction first generalizing results with
  | nil => cases last; exact .nil
  | cons first rest ih =>
      cases last with
      | cons second tail => exact .cons (fun path domain => second path (first path domain)) (ih tail)

variable (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)

omit [DecidableEq Symbol] in
private theorem nil_receipt (inventory : Inventory) (values : List (Value Symbol Guard)) (before : Checked width) (memo : Memo)
    (ready : Ready before) (admitted : At formulas solver inventory before)
    (available : Values before.native.machine.heap values) (stored : Stored before.native.machine.heap memo)
    (covered : ∀ ambient, CacheCovers (SourceEqualityPCSGuard.holds formulas solver) ambient memo)
    (memos : Memos) (valid : Valid before.native.machine.heap memos) :
    Receipt formulas solver inventory [] values before memo values before memo memos memos := by
  have physicalReady := SourceCurrentAllocatedConjunctionMemo.ready before ready.good ready.semantic ready.costs
  refine ⟨ready, admitted, .refl _ physicalReady, .refl _, stored, covered, available,
    transport_refl values, (fun _ domain => domain), extends_refl _,
    ⟨SourceEqualityRequiredCache.pure_keeps _ ready.semantic.ready, ready.semantic, ready.costs, valid, extends_refl _, rfl⟩, ?_⟩
  exact fun _ _ _ => ⟨id, fun _ => Iff.rfl⟩

private theorem cons_receipt {inventory next : Inventory} {record records values middle results}
    {before step after : Checked width} {memo current saved : Memo} {memos stepMemos final : Memos}
    (first : Receipt formulas solver inventory records values before memo middle step current memos stepMemos)
    (last : SourceCurrentAllocatedClassEdits.Receipt formulas solver next record middle step current results after saved stepMemos final) :
    Receipt formulas solver next (record :: records) values before memo results after saved memos final := by
  refine ⟨last.ready, last.admitted, first.effects.trans last.effects, first.extension.trans last.extension,
    last.stored, last.covered, last.available, transport_trans first.transport last.transport,
    (fun path domain => last.domains path (first.domains path domain)), extends_trans first.retained last.retained,
    SourceCurrentMemoMergeQueryMemos.effect_trans first.globals last.globals, ?_⟩
  intro ambient symbol terms
  have tail := first.language ambient symbol terms
  have head := last.language ambient symbol terms
  refine ⟨fun accepted => tail.1 (head.1 accepted), ?_⟩
  intro satisfied
  exact (head.2 (satisfied _ List.mem_cons_self)).trans
    (tail.2 (fun own member => satisfied own (List.mem_cons_of_mem _ member)))

/-- Annotated actual folds derive their final inventory and independent language bounds. -/
theorem Fold.verified (inventory : Inventory) {records values results} {before after : Checked width} {memo saved : Memo}
    {memos final : Memos} {actual : Fold records values before memo results after saved}
    (reads : FoldReads formulas solver actual memos final)
    (coherent : ∀ record ∈ records, SourceEqualityClassOrder.Coherent record)
    (active : ∀ record ∈ records, EqualityNormalize.Nontrivial record.paths)
    (ready : Ready before) (admitted : At formulas solver inventory before)
    (available : Values before.native.machine.heap values)
    (domains : ∀ record ∈ records, ∀ path ∈ record.paths, ForestClosed (path.map Int.ofNat) values)
    (stored : Stored before.native.machine.heap memo)
    (covered : ∀ ambient, CacheCovers (SourceEqualityPCSGuard.holds formulas solver) ambient memo)
    (valid : Valid before.native.machine.heap memos) :
    ∃ next, Receipt formulas solver next records values before memo results after saved memos final := by
  induction reads generalizing inventory with
  | nil => exact ⟨inventory, nil_receipt formulas solver inventory _ _ _ ready admitted available stored covered _ valid⟩
  | @cons records values before memo middle step current record results after saved memos stepMemos final tail head first last ih =>
      obtain ⟨next, firstReceipt⟩ := ih inventory
        (fun own member => coherent own (List.mem_cons_of_mem _ member))
        (fun own member => active own (List.mem_cons_of_mem _ member)) ready admitted available
        (fun own member => domains own (List.mem_cons_of_mem _ member)) stored covered valid
      obtain ⟨finalInventory, lastReceipt⟩ := SourceCurrentAllocatedClassEdits.verified formulas solver next record
        (coherent _ List.mem_cons_self) (active _ List.mem_cons_self) last firstReceipt.ready firstReceipt.admitted
        firstReceipt.available (fun path member => firstReceipt.domains _ (domains _ List.mem_cons_self path member))
        firstReceipt.stored firstReceipt.covered firstReceipt.globals.valid
      exact ⟨finalInventory, cons_receipt formulas solver firstReceipt lastReceipt⟩

/-- Initial invariants and actual-tail range checks construct the full checked class fold. -/
theorem fold_complete (inventory : Inventory) {records values} {before : Checked width} {memo : Memo}
    (ranges : Ranges records values before memo)
    (coherent : ∀ record ∈ records, SourceEqualityClassOrder.Coherent record)
    (active : ∀ record ∈ records, EqualityNormalize.Nontrivial record.paths)
    (ready : Ready before) (admitted : At formulas solver inventory before)
    (available : Values before.native.machine.heap values)
    (domains : ∀ record ∈ records, ∀ path ∈ record.paths, ForestClosed (path.map Int.ofNat) values)
    (stored : Stored before.native.machine.heap memo)
    (covered : ∀ ambient, CacheCovers (SourceEqualityPCSGuard.holds formulas solver) ambient memo)
    (memos : Memos) (valid : Valid before.native.machine.heap memos) :
    ∃ results after saved next final, ∃ actual : Fold records values before memo results after saved,
      FoldReads formulas solver actual memos final ∧
      Receipt formulas solver next records values before memo results after saved memos final := by
  induction ranges generalizing inventory memos with
  | nil =>
      exact ⟨_, _, _, inventory, memos, .nil, .nil,
        nil_receipt formulas solver inventory _ _ _ ready admitted available stored covered memos valid⟩
  | @cons records values before memo record tail head ih =>
      obtain ⟨middle, step, current, next, stepMemos, tailActual, tailRead, first⟩ := ih inventory
        (fun own member => coherent own (List.mem_cons_of_mem _ member))
        (fun own member => active own (List.mem_cons_of_mem _ member)) ready admitted available
        (fun own member => domains own (List.mem_cons_of_mem _ member)) stored covered memos valid
      obtain ⟨results, after, saved, finalInventory, final, classActual, classRead, last⟩ :=
        SourceCurrentAllocatedClassEdits.finite formulas solver next record (coherent _ List.mem_cons_self)
          (active _ List.mem_cons_self) middle step current first.ready first.admitted first.available
          (fun path member => first.domains _ (domains _ List.mem_cons_self path member)) first.stored first.covered
          (head middle step current tailActual) stepMemos first.globals.valid
      exact ⟨results, after, saved, finalInventory, final, .cons tailActual classActual,
        .cons (tail := tailActual) (head := classActual) tailRead classRead,
        cons_receipt formulas solver first last⟩

omit [DecidableEq Symbol] in
private theorem propagate_receipt {inventory : Inventory} {records values results} {before after : Checked width}
    {memo saved : Memo} {memos final : Memos}
    (receipt : Receipt formulas solver inventory records values before memo results after saved memos final) :
    Receipt formulas solver inventory records values before memo (EqualityLeafProjectionRuntimeEmpty.propagate results)
      after saved memos final := by
  refine ⟨receipt.ready, receipt.admitted, receipt.effects, receipt.extension, receipt.stored, receipt.covered,
    SourceCurrentClassFoldDomains.propagate_available _ _ receipt.available,
    transport_trans receipt.transport (SourceCurrentClassFoldDomains.propagate_transport results),
    (fun path domain => SourceCurrentClassFoldDomains.propagate_domains _ path (receipt.domains path domain)),
    receipt.retained, receipt.globals, ?_⟩
  intro ambient symbol terms
  rw [SourceEqualityEmptyPropagation.exact]
  exact receipt.language ambient symbol terms

/-- Final empty propagation retains the exact returned state and class-fold language bounds. -/
theorem Pass.verified (inventory : Inventory) {records values results} {before after : Checked width} {memo saved : Memo}
    {memos final : Memos} {actual : Pass records values before memo results after saved}
    (reads : PassReads formulas solver actual memos final)
    (coherent : ∀ record ∈ records, SourceEqualityClassOrder.Coherent record)
    (active : ∀ record ∈ records, EqualityNormalize.Nontrivial record.paths)
    (ready : Ready before) (admitted : At formulas solver inventory before)
    (available : Values before.native.machine.heap values)
    (domains : ∀ record ∈ records, ∀ path ∈ record.paths, ForestClosed (path.map Int.ofNat) values)
    (stored : Stored before.native.machine.heap memo)
    (covered : ∀ ambient, CacheCovers (SourceEqualityPCSGuard.holds formulas solver) ambient memo)
    (valid : Valid before.native.machine.heap memos) :
    ∃ next, Receipt formulas solver next records values before memo results after saved memos final := by
  cases reads with
  | done read =>
      obtain ⟨next, receipt⟩ := Fold.verified formulas solver inventory read coherent active ready admitted available domains stored covered valid
      exact ⟨next, propagate_receipt formulas solver receipt⟩

/-- Reached ranges derive finite full class-pass execution without completed callback premises. -/
theorem pass_complete (inventory : Inventory) {records values} {before : Checked width} {memo : Memo}
    (ranges : Ranges records values before memo)
    (coherent : ∀ record ∈ records, SourceEqualityClassOrder.Coherent record)
    (active : ∀ record ∈ records, EqualityNormalize.Nontrivial record.paths)
    (ready : Ready before) (admitted : At formulas solver inventory before)
    (available : Values before.native.machine.heap values)
    (domains : ∀ record ∈ records, ∀ path ∈ record.paths, ForestClosed (path.map Int.ofNat) values)
    (stored : Stored before.native.machine.heap memo)
    (covered : ∀ ambient, CacheCovers (SourceEqualityPCSGuard.holds formulas solver) ambient memo)
    (memos : Memos) (valid : Valid before.native.machine.heap memos) :
    ∃ results after saved next final, ∃ actual : Pass records values before memo results after saved,
      PassReads formulas solver actual memos final ∧
      Receipt formulas solver next records values before memo results after saved memos final := by
  obtain ⟨results, after, saved, next, final, actual, reads, receipt⟩ :=
    fold_complete formulas solver inventory ranges coherent active ready admitted available domains stored covered memos valid
  exact ⟨_, after, saved, next, final, .done actual, .done reads, propagate_receipt formulas solver receipt⟩

omit [DecidableEq Symbol] in
/-- The same fourth memo remains correct through actual complete-pass heap growth. -/
theorem Receipt.fourth_correct {inventory : Inventory} {records values results} {before after : Checked width}
    {memo saved : Memo} {memos final : Memos}
    (receipt : Receipt formulas solver inventory records values before memo results after saved memos final)
    (fourth : SourceCurrentEmptinessMemo.Memo)
    (correct : SourceCurrentEmptinessMemo.Correct formulas solver before.native.machine.heap fourth) :
    SourceCurrentEmptinessMemo.Correct formulas solver after.native.machine.heap fourth :=
  SourceCurrentEmptinessMemo.grows formulas solver receipt.effects.keeps fourth correct

end MicroCFTA.SourceCurrentAllocatedClassPass
