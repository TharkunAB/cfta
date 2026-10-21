import MicroCFTA.SourceCurrentAllocatedTargetGraph
import MicroCFTA.SourceCurrentAllocatedTargetQuery

/-!
# Checked first-seeded targets with retained warm tables

Each actual operand precedes its recursive tail and checked intersection.
The input inventory changes only through a reached generated query.
Selected domains suffice. Other captured siblings can remain open.
Completed graphs do not establish GHC demand or pending publication.
-/
namespace MicroCFTA.SourceCurrentAllocatedTargetComplete
open Cache Language InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open InternedGuardedLanguage (meaning)
open SourceCurrentAllocatedNativeEffects (physical)
open SourceCurrentAllocatedNativeInventoryState (Inventory At)
open SourceCurrentAllocatedTargetGraph
open SourceCurrentMemoMergeEffects (Stored)
open SourceCurrentMemoMergeLanguage (CacheCovers)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Memo" => SourceCurrentMemoMergeGraph.Memo Symbol Guard
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Valid" => EndpointMemoGateTrace.Valid
local notation "Ready" => SourceCurrentConjunctionClassScan.Ready
local notation "Domain" => SourceEqualityProjectionPathDomain.ForestClosed
variable {width : Nat}

/-- Every common selected subtree remains in the returned target language. -/
def Includes (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (values : List (Value Symbol Guard))
    (paths : List (List Int)) (result : Value Symbol Guard) : Prop :=
  ∀ ambient symbol terms part,
    All₂ (meaning (SourceEqualityPCSGuard.holds formulas solver) ambient) values terms →
    (∀ path ∈ paths, SymbolicSignedPaths.lookup (.node symbol terms) path = some part) →
    meaning (SourceEqualityPCSGuard.holds formulas solver) ambient result part

/-- Returned target facts retain the actual current state and concrete inventory. -/
structure Receipt [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (values : List (Value Symbol Guard)) (paths : List (List Int))
    (before : Checked width) (memo : Memo) (result : Value Symbol Guard) (after : Checked width)
    (saved : Memo) (memos final : Memos) : Prop where
  ready : Ready after
  admitted : At formulas solver inventory after
  effects : SourceCurrentConjunctionRowsAllocation.Effects (physical before) (physical after)
  extension : SourceRecursiveIntersectionKernel.Extension before.native.machine after.native.machine
  stored : Stored after.native.machine.heap saved
  covered : ∀ ambient, CacheCovers (SourceEqualityPCSGuard.holds formulas solver) ambient saved
  available : Available after.native.machine.heap result
  closed : result.free = []
  originals : Values after.native.machine.heap values
  retained : Extends memo saved
  globals : SourceCurrentSubsumesQueryMemos.Effect before.native.machine.heap after.native.machine.heap memos final
  included : paths ≠ [] → (∀ path ∈ paths, path ≠ []) → Includes formulas solver values paths result

/-- Literal operands and checked requests supply the reached global receipts. -/
inductive FoldReads [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula) :
    {values : List (Value Symbol Guard)} → {seed : List Int} → {paths : List (List Int)} →
    {before after : Checked width} → {memo saved : Memo} → {result : Value Symbol Guard} →
    Fold values seed paths before memo result after saved → Memos → Memos → Prop where
  | nil {operand : Operand seed values before memo result after saved}
      (receipt : SourceCurrentAllocatedMergeOperand.Receipt formulas solver inventory seed values
        before memo result after saved memos final) : FoldReads formulas solver (.nil operand) memos final
  | cons {operand : Operand path values before memo value middle current}
      {rest : Fold values seed paths middle current tail later saved}
      {step : SourceCurrentAllocatedTargetQuery.Step value tail later result after}
      (receipt : SourceCurrentAllocatedMergeOperand.Receipt formulas solver inventory path values
        before memo value middle current memos nextMemos)
      (remaining : FoldReads formulas solver rest nextMemos lastMemos)
      (query : SourceCurrentAllocatedTargetQuery.Receipt formulas solver nextInventory value tail later result after lastMemos) :
      FoldReads formulas solver (.cons operand rest step) memos lastMemos

/-- Empty targets make no calls; nonempty targets retain the actual first-seeded reads. -/
inductive TargetReads [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula) :
    {values : List (Value Symbol Guard)} → {paths : List (List Int)} → {before after : Checked width} →
    {memo saved : Memo} → {result : Value Symbol Guard} →
    Target values paths before memo result after saved → Memos → Memos → Prop where
  | nil : TargetReads formulas solver (.nil (values := values) (before := state) (memo := memo)) memos memos
  | cons {actual : Fold values seed paths before memo result after saved}
      (reads : FoldReads formulas solver actual memos final) :
      TargetReads formulas solver (.nonempty actual) memos final

private theorem tail_all {A : Type} {seed first : A} {rest : List A} {property : A → Prop}
    (all : ∀ value ∈ seed :: first :: rest, property value) : ∀ value ∈ seed :: rest, property value := by
  intro value member
  rcases List.mem_cons.mp member with rfl | member
  · exact all _ List.mem_cons_self
  · exact all value (by simp only [List.mem_cons]; exact Or.inr (Or.inr member))

private theorem operand_receipt [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
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

private theorem cons_receipt [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
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

/-- Every actual fold derives its next inventory and all reached global receipts. -/
theorem Fold.verified [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) {values : List (Value Symbol Guard)} {seed : List Int} {paths : List (List Int)}
    {before after : Checked width} {memo saved : Memo} {result : Value Symbol Guard}
    (actual : Fold values seed paths before memo result after saved)
    (ready : Ready before) (admitted : At formulas solver inventory before)
    (available : Values before.native.machine.heap values) (domains : ∀ path ∈ seed :: paths, Domain path values)
    (stored : Stored before.native.machine.heap memo)
    (covered : ∀ ambient, CacheCovers (SourceEqualityPCSGuard.holds formulas solver) ambient memo)
    (ranges : FoldRanges values seed paths before memo) (memos : Memos) (valid : Valid before.native.machine.heap memos) :
    ∃ next final, FoldReads formulas solver actual memos final ∧
      Receipt formulas solver next values (seed :: paths) before memo result after saved memos final := by
  induction actual generalizing inventory memos with
  | nil operand =>
      obtain ⟨final, receipt⟩ := Operand.verified formulas solver inventory operand ready admitted available
        (domains _ List.mem_cons_self) stored covered memos valid
      exact ⟨inventory, final, .nil (operand := operand) receipt, operand_receipt receipt⟩
  | cons operand rest step ih =>
      obtain ⟨currentMemos, first⟩ := Operand.verified formulas solver inventory operand ready admitted available
        (domains _ (by simp)) stored covered memos valid
      obtain ⟨tailInventory, laterMemos, tailReads, remaining⟩ := ih _ first.ready first.admitted first.originals
        (tail_all domains) first.stored first.covered (ranges.1 _ _ _ operand) currentMemos first.globals
      obtain ⟨next, _, _, query⟩ := SourceCurrentAllocatedTargetQuery.Step.verified
        formulas solver tailInventory step remaining.ready remaining.admitted
        (remaining.effects.keeps.available _ first.available) remaining.available first.closed remaining.closed
        (ranges.2 _ _ _ _ _ _ operand rest) laterMemos remaining.globals.valid
      exact ⟨next, laterMemos, .cons (operand := operand) (rest := rest) (step := step)
        first tailReads query, cons_receipt first remaining query⟩

/-- Initial selected support and actual-prefix ranges construct the source right fold. -/
theorem fold_complete [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (values : List (Value Symbol Guard)) (seed : List Int) (paths : List (List Int))
    (before : Checked width) (memo : Memo) (ready : Ready before)
    (admitted : At formulas solver inventory before) (available : Values before.native.machine.heap values)
    (domains : ∀ path ∈ seed :: paths, Domain path values) (stored : Stored before.native.machine.heap memo)
    (covered : ∀ ambient, CacheCovers (SourceEqualityPCSGuard.holds formulas solver) ambient memo)
    (ranges : FoldRanges values seed paths before memo) (memos : Memos) (valid : Valid before.native.machine.heap memos) :
    ∃ result after saved next final, ∃ actual : Fold values seed paths before memo result after saved,
      FoldReads formulas solver actual memos final ∧
      Receipt formulas solver next values (seed :: paths) before memo result after saved memos final := by
  induction paths generalizing inventory before memo memos with
  | nil =>
      obtain ⟨result, after, saved, final, operand, receipt⟩ := Operand.complete formulas solver inventory seed values
        before memo ready admitted available (domains _ List.mem_cons_self) stored covered memos valid
      exact ⟨result, after, saved, inventory, final, .nil operand, .nil (operand := operand) receipt, operand_receipt receipt⟩
  | cons path paths ih =>
      obtain ⟨head, middle, current, currentMemos, operand, first⟩ := Operand.complete formulas solver inventory path values
        before memo ready admitted available (domains _ (by simp)) stored covered memos valid
      obtain ⟨tail, later, saved, tailInventory, laterMemos, rest, tailReads, remaining⟩ := ih inventory middle current
        first.ready first.admitted first.originals (tail_all domains) first.stored first.covered
        (ranges.1 _ _ _ operand) currentMemos first.globals
      obtain ⟨next, result, after, _, _, query⟩ := SourceCurrentAllocatedTargetQuery.finite
        formulas solver tailInventory head tail later remaining.ready remaining.admitted
        (remaining.effects.keeps.available head first.available) remaining.available first.closed remaining.closed
        (ranges.2 _ _ _ _ _ _ operand rest) laterMemos remaining.globals.valid
      exact ⟨result, after, saved, next, laterMemos, .cons operand rest query.actual,
        .cons (operand := operand) (rest := rest) (step := query.actual)
          first tailReads query, cons_receipt first remaining query⟩

/-- Initial warm tables construct an actual first-seeded target and its full receipt. -/
theorem target_complete [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (values : List (Value Symbol Guard)) (paths : List (List Int))
    (before : Checked width) (memo : Memo) (ready : Ready before)
    (admitted : At formulas solver inventory before) (available : Values before.native.machine.heap values)
    (domains : ∀ path ∈ paths, Domain path values) (stored : Stored before.native.machine.heap memo)
    (covered : ∀ ambient, CacheCovers (SourceEqualityPCSGuard.holds formulas solver) ambient memo)
    (ranges : TargetRanges values paths before memo) (memos : Memos) (valid : Valid before.native.machine.heap memos) :
    ∃ result after saved next final, ∃ actual : Target values paths before memo result after saved,
      TargetReads formulas solver actual memos final ∧
      Receipt formulas solver next values paths before memo result after saved memos final := by
  cases paths with
  | nil =>
      have initial : SourceCurrentConjunctionRowsAllocation.Ready (physical before) :=
        ⟨ready.semantic, ready.costs, ready.good.operations, ready.good.fields⟩
      exact ⟨.empty, before, memo, inventory, memos, .nil, .nil,
        ⟨ready, admitted, .refl _ initial, .refl _, stored, covered, empty_available _, rfl, available,
          extends_refl _, ⟨SourceEqualityRequiredCache.pure_keeps _ ready.semantic.ready,
            ready.semantic, ready.costs, valid, extends_refl _, rfl⟩,
          fun nonempty => False.elim (nonempty rfl)⟩⟩
  | cons seed paths =>
      obtain ⟨result, after, saved, next, final, actual, reads, receipt⟩ := fold_complete formulas solver inventory
        values seed paths before memo ready admitted available domains stored covered ranges memos valid
      exact ⟨result, after, saved, next, final, .nonempty actual, .cons reads, receipt⟩

/-- An existing actual target derives its receipt without a completed callback premise. -/
theorem Target.verified [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) {values : List (Value Symbol Guard)} {paths : List (List Int)}
    {before after : Checked width} {memo saved : Memo} {result : Value Symbol Guard}
    (actual : Target values paths before memo result after saved) (ready : Ready before)
    (admitted : At formulas solver inventory before) (available : Values before.native.machine.heap values)
    (domains : ∀ path ∈ paths, Domain path values) (stored : Stored before.native.machine.heap memo)
    (covered : ∀ ambient, CacheCovers (SourceEqualityPCSGuard.holds formulas solver) ambient memo)
    (ranges : TargetRanges values paths before memo) (memos : Memos) (valid : Valid before.native.machine.heap memos) :
    ∃ next final, TargetReads formulas solver actual memos final ∧
      Receipt formulas solver next values paths before memo result after saved memos final := by
  cases actual with
  | nil =>
      have initial : SourceCurrentConjunctionRowsAllocation.Ready (physical before) :=
        ⟨ready.semantic, ready.costs, ready.good.operations, ready.good.fields⟩
      exact ⟨inventory, memos, .nil,
        ⟨ready, admitted, .refl _ initial, .refl _, stored, covered, empty_available _, rfl, available,
          extends_refl _, ⟨SourceEqualityRequiredCache.pure_keeps _ ready.semantic.ready,
            ready.semantic, ready.costs, valid, extends_refl _, rfl⟩,
          fun nonempty => False.elim (nonempty rfl)⟩⟩
  | nonempty fold =>
      obtain ⟨next, final, reads, receipt⟩ := Fold.verified formulas solver inventory fold ready admitted available
        domains stored covered ranges memos valid
      exact ⟨next, final, .cons reads, receipt⟩

/-- Actual target heap growth retains a previously correct fourth table unchanged. -/
theorem Receipt.fourth_correct [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {formulas : SourceGuards.Formulas FullSyntax.Formula} {solver : SourceGuards.Entailment FullSyntax.Formula}
    {inventory : Inventory} {values : List (Value Symbol Guard)} {paths : List (List Int)}
    {before after : Checked width} {memo saved : Memo} {result : Value Symbol Guard} {memos final : Memos}
    (receipt : Receipt formulas solver inventory values paths before memo result after saved memos final)
    (fourth : SourceCurrentEmptinessMemo.Memo)
    (correct : SourceCurrentEmptinessMemo.Correct formulas solver before.native.machine.heap fourth) :
    SourceCurrentEmptinessMemo.Correct formulas solver after.native.machine.heap fourth :=
  SourceCurrentEmptinessMemo.grows formulas solver receipt.effects.keeps fourth correct

end MicroCFTA.SourceCurrentAllocatedTargetComplete
