import MicroCFTA.SourceCurrentAllocatedTargetComplete

/-!
# Target receipts from actual component receipts

The helpers compose only the supplied actual Operand and checked query
receipts. They retain exact states, inventories, global memos, and language
inclusion. They require no future range or callback-completion premise.
-/
namespace MicroCFTA.SourceCurrentConstrainedCapTargetReceiptComposition
open Cache Language InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open InternedGuardedLanguage (meaning)
open SourceCurrentAllocatedNativeEffects (physical)
open SourceCurrentAllocatedNativeInventoryState (Inventory At)
open SourceCurrentAllocatedTargetGraph
open SourceCurrentAllocatedTargetComplete (Receipt Includes FoldReads TargetReads)
open SourceCurrentMemoMergeEffects (Stored)
open SourceCurrentMemoMergeLanguage (CacheCovers)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Memo" => SourceCurrentMemoMergeGraph.Memo Symbol Guard
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Valid" => EndpointMemoGateTrace.Valid
local notation "Ready" => SourceCurrentConjunctionClassScan.Ready
variable {width : Nat}

private theorem tail_all {A : Type} {seed first : A} {rest : List A} {property : A → Prop}
    (all : ∀ value ∈ seed :: first :: rest, property value) : ∀ value ∈ seed :: rest, property value := by
  intro value member
  rcases List.mem_cons.mp member with rfl | member
  · exact all _ List.mem_cons_self
  · exact all value (by simp only [List.mem_cons]; exact Or.inr (Or.inr member))

/-- One actual Operand supplies the complete singleton Target receipt. -/
theorem of_operand [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {formulas : SourceGuards.Formulas FullSyntax.Formula} {solver : SourceGuards.Entailment FullSyntax.Formula}
    {inventory : Inventory} {values : List (Value Symbol Guard)} {path : List Int}
    {before after : Checked width} {memo saved : Memo} {result : Value Symbol Guard} {memos final : Memos}
    (own : SourceCurrentAllocatedMergeOperand.Receipt formulas solver inventory path values
      before memo result after saved memos final) :
    Receipt formulas solver inventory values [path] before memo result after saved memos final := by
  have exactExtension : SourceRecursiveIntersectionKernel.Extension before.native.machine after.native.machine :=
    ⟨own.effects.keeps.growth, own.effects.keeps.history, by
      simpa only [own.domains] using Cache.extends_refl before.native.machine.domains.table⟩
  refine ⟨own.ready, own.admitted, own.effects, exactExtension, own.stored, own.covered,
    own.available, own.closed, own.originals, own.retained,
    ⟨own.effects.keeps, own.effects.ready.semantic, own.effects.ready.costs, own.globals, own.unfolding, own.query⟩, ?_⟩
  intro _ proper ambient symbol terms part accepted selected
  exact own.included (proper path List.mem_cons_self) ambient symbol terms part accepted (selected path List.mem_cons_self)

/-- The head Operand executes before the recursive tail and its exact checked intersection. -/
theorem cons [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {formulas : SourceGuards.Formulas FullSyntax.Formula} {solver : SourceGuards.Entailment FullSyntax.Formula}
    {inventory nextInventory finalInventory : Inventory} {values : List (Value Symbol Guard)}
    {seed path : List Int} {paths : List (List Int)} {before middle later after : Checked width}
    {memo current saved : Memo} {head tail result : Value Symbol Guard} {memos nextMemos lastMemos : Memos}
    (first : SourceCurrentAllocatedMergeOperand.Receipt formulas solver inventory path values
      before memo head middle current memos nextMemos)
    (rest : Receipt formulas solver nextInventory values (seed :: paths) middle current tail later saved nextMemos lastMemos)
    (query : SourceCurrentAllocatedTargetQuery.Receipt formulas solver finalInventory head tail later result after lastMemos) :
    Receipt formulas solver finalInventory values (seed :: path :: paths) before memo result after saved memos lastMemos := by
  have effects := first.effects.trans (rest.effects.trans query.effects)
  have firstExtension : SourceRecursiveIntersectionKernel.Extension before.native.machine middle.native.machine :=
    ⟨first.effects.keeps.growth, first.effects.keeps.history, by simpa only [first.domains] using Cache.extends_refl before.native.machine.domains.table⟩
  have queryGlobal : SourceCurrentSubsumesQueryMemos.Effect later.native.machine.heap after.native.machine.heap lastMemos lastMemos :=
    ⟨query.effects.keeps, query.ready.semantic, query.ready.costs, query.globals, extends_refl _, rfl⟩
  have firstGlobal : SourceCurrentSubsumesQueryMemos.Effect before.native.machine.heap middle.native.machine.heap memos nextMemos :=
    ⟨first.effects.keeps, first.effects.ready.semantic, first.effects.ready.costs,
      first.globals, first.unfolding, first.query⟩
  refine ⟨query.ready, query.admitted, effects,
    firstExtension.trans (rest.extension.trans query.extension), rest.stored.grows query.effects.keeps,
    rest.covered, query.available, query.closed, ?_, extends_trans first.retained rest.retained,
    SourceCurrentMemoMergeQueryMemos.effect_trans firstGlobal
      (SourceCurrentMemoMergeQueryMemos.effect_trans rest.globals queryGlobal), ?_⟩
  · intro value member
    exact query.effects.keeps.available value (rest.originals value member)
  · intro _ proper ambient symbol terms part accepted selected
    exact (query.meaning ambient part).mpr
      ⟨first.included (proper path (by simp)) ambient symbol terms part accepted (selected path (by simp)),
        rest.included (by simp) (tail_all proper) ambient symbol terms part accepted (tail_all selected)⟩

/-- An empty Target retains the full initial state and every initial table. -/
theorem empty [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {formulas : SourceGuards.Formulas FullSyntax.Formula} {solver : SourceGuards.Entailment FullSyntax.Formula}
    {inventory : Inventory} {values : List (Value Symbol Guard)} {before : Checked width} {memo : Memo} {memos : Memos}
    (ready : Ready before) (admitted : At formulas solver inventory before)
    (available : Values before.native.machine.heap values) (stored : Stored before.native.machine.heap memo)
    (covered : ∀ ambient, CacheCovers (SourceEqualityPCSGuard.holds formulas solver) ambient memo)
    (valid : Valid before.native.machine.heap memos) :
    Receipt formulas solver inventory values [] before memo .empty before memo memos memos := by
  have initial : SourceCurrentConjunctionRowsAllocation.Ready (physical before) :=
    ⟨ready.semantic, ready.costs, ready.good.operations, ready.good.fields⟩
  exact ⟨ready, admitted, .refl _ initial, .refl _, stored, covered, empty_available _, rfl, available,
    extends_refl _, ⟨SourceEqualityRequiredCache.pure_keeps _ ready.semantic.ready,
      ready.semantic, ready.costs, valid, extends_refl _, rfl⟩,
    fun nonempty => False.elim (nonempty rfl)⟩

/-- Actual retained fold reads determine a full Target receipt without range assumptions. -/
theorem of_fold_reads [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {formulas : SourceGuards.Formulas FullSyntax.Formula} {solver : SourceGuards.Entailment FullSyntax.Formula}
    {values : List (Value Symbol Guard)} {seed : List Int} {paths : List (List Int)}
    {before after : Checked width} {memo saved : Memo} {result : Value Symbol Guard} {memos final : Memos}
    {actual : Fold values seed paths before memo result after saved}
    (reads : FoldReads formulas solver actual memos final) :
    ∃ inventory, Receipt formulas solver inventory values (seed :: paths) before memo result after saved memos final := by
  induction reads with
  | nil receipt => exact ⟨_, of_operand receipt⟩
  | cons first remaining query ih =>
      obtain ⟨_, rest⟩ := ih
      exact ⟨_, cons first rest query⟩

/-- Actual retained Target reads determine a full receipt from the same initial empty-case facts. -/
theorem of_target_reads [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {formulas : SourceGuards.Formulas FullSyntax.Formula} {solver : SourceGuards.Entailment FullSyntax.Formula}
    {inventory : Inventory} {values : List (Value Symbol Guard)} {paths : List (List Int)}
    {before after : Checked width} {memo saved : Memo} {result : Value Symbol Guard} {memos final : Memos}
    {actual : Target values paths before memo result after saved}
    (reads : TargetReads formulas solver actual memos final) (ready : Ready before)
    (admitted : At formulas solver inventory before) (available : Values before.native.machine.heap values)
    (stored : Stored before.native.machine.heap memo)
    (covered : ∀ ambient, CacheCovers (SourceEqualityPCSGuard.holds formulas solver) ambient memo)
    (valid : Valid before.native.machine.heap memos) :
    ∃ next, Receipt formulas solver next values paths before memo result after saved memos final := by
  cases reads with
  | nil => exact ⟨inventory, empty ready admitted available stored covered valid⟩
  | cons retained => exact of_fold_reads retained

end MicroCFTA.SourceCurrentConstrainedCapTargetReceiptComposition
