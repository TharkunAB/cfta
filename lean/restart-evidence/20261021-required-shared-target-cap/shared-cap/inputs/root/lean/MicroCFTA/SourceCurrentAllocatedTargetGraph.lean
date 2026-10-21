import MicroCFTA.SourceCurrentAllocatedMergeOperand
import MicroCFTA.SourceCurrentAllocatedTargetQuery

/-!
# Literal allocated target operands and right folds

An operand projects the captured forest and merges the actual projection.
A fold evaluates its head operand, its recursive tail, and their checked
intersection in that order. The merge memo passes through each returned
prefix. Range plans inspect only these actual operand and tail prefixes.
No semantic result or completed native request is supplied by the plans.
The completed serial graph retains its separate runtime demand boundary.
-/
namespace MicroCFTA.SourceCurrentAllocatedTargetGraph
open Cache Language InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open SourceCurrentAllocatedNativeEffects (physical)
open SourceCurrentAllocatedQueryMemo (advancePhysical)
open SourceCurrentAllocatedNativeInventoryState (Inventory At)
open SourceCurrentMemoMergeEffects (Stored)
open SourceCurrentMemoMergeLanguage (CacheCovers)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Memo" => SourceCurrentMemoMergeGraph.Memo Symbol Guard
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Valid" => EndpointMemoGateTrace.Valid
local notation "Ready" => SourceCurrentConjunctionClassScan.Ready
local notation "Step" => SourceCurrentAllocatedTargetQuery.Step
local notation "WordRanges" => SourceCurrentAllocatedNativeRequestBounds.WordRanges
local notation "requestNode" => SourceRecursiveIntersectionCode.requestNode
local notation "emptyDomain" => IntersectionEmptyDomain.emptyDomain
variable {width : Nat}

/-- The actual forest projection precedes merging at its literal advanced checked state. -/
inductive Operand [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (path : List Int) (values : List (Value Symbol Guard)) :
    Checked width → Memo → Value Symbol Guard → Checked width → Memo → Prop where
  | force (projection : SourceEqualityProjectionGraph.Forest path values before.native.machine.heap projected heap)
      (merged : SourceCurrentAllocatedMerge.Merge SourceCurrentAllocatedMerge.literalClear projected
        (advancePhysical before ⟨heap, before.operations⟩) memo result after saved) :
      Operand path values before memo result after saved

/-- One raw operand derives its full existing checked receipt from initial invariants. -/
theorem Operand.verified [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) {path : List Int} {values : List (Value Symbol Guard)}
    {before after : Checked width} {memo saved : Memo} {result : Value Symbol Guard}
    (actual : Operand path values before memo result after saved)
    (ready : Ready before) (admitted : At formulas solver inventory before)
    (available : Values before.native.machine.heap values)
    (domain : SourceEqualityProjectionPathDomain.ForestClosed path values)
    (stored : Stored before.native.machine.heap memo)
    (covered : ∀ ambient, CacheCovers (SourceEqualityPCSGuard.holds formulas solver) ambient memo)
    (memos : Memos) (valid : Valid before.native.machine.heap memos) :
    ∃ final, SourceCurrentAllocatedMergeOperand.Receipt formulas solver inventory path values
      before memo result after saved memos final := by
  cases actual with
  | force projection merged =>
      obtain ⟨current, projected⟩ := SourceCurrentConjunctionTargetProjection.verified
        formulas solver inventory projection ready admitted available domain memos valid
      obtain ⟨final, merged⟩ := SourceCurrentAllocatedMerge.verified formulas solver inventory
        SourceCurrentAllocatedMerge.literalClear (SourceCurrentAllocatedMerge.literalClear_true formulas solver)
        merged projected.ready projected.admitted (stored.grows projected.effects.keeps)
        covered projected.available current projected.globals.valid
      have effects := projected.effects.trans merged.effects
      refine ⟨final, ⟨⟨_, _, current, projected, merged⟩,
        merged.ready, merged.admitted, effects, merged.stored, merged.covered, merged.available,
        merged.closed projected.closed, ?_, merged.nodes.trans projected.nodes,
        merged.edges.trans projected.edges, merged.domains.trans projected.domains,
        merged.retained, merged.globals.valid,
        extends_trans projected.globals.retained merged.globals.retained,
        merged.globals.query.trans projected.globals.query, ?_, ?_⟩⟩
      · intro value member
        exact effects.keeps.available value (available value member)
      · intro nonroot ambient symbol terms part accepted found
        exact merged.included ambient part (projected.included nonroot _ ambient symbol terms part accepted found)
      · intro root ambient term accepted
        exact merged.included ambient term ((projected.root_exact root _ ambient term).mpr accepted)

/-- The existing operand receipt determines this raw graph at the same exact endpoints. -/
theorem of_receipt [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {formulas : SourceGuards.Formulas FullSyntax.Formula} {solver : SourceGuards.Entailment FullSyntax.Formula}
    {inventory : Inventory} {path : List Int} {values : List (Value Symbol Guard)}
    {before after : Checked width} {memo saved : Memo} {result : Value Symbol Guard} {memos final : Memos}
    (receipt : SourceCurrentAllocatedMergeOperand.Receipt formulas solver inventory path values
      before memo result after saved memos final) : Operand path values before memo result after saved := by
  obtain ⟨projected, middle, current, projection, merged⟩ := receipt.actual
  apply Operand.force projection.graph
  rw [← projection.advanced]
  exact merged.actual

/-- Initial selected domains construct the raw operand and its full checked receipt. -/
theorem Operand.complete [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (path : List Int) (values : List (Value Symbol Guard))
    (before : Checked width) (memo : Memo) (ready : Ready before)
    (admitted : At formulas solver inventory before) (available : Values before.native.machine.heap values)
    (domain : SourceEqualityProjectionPathDomain.ForestClosed path values)
    (stored : Stored before.native.machine.heap memo)
    (covered : ∀ ambient, CacheCovers (SourceEqualityPCSGuard.holds formulas solver) ambient memo)
    (memos : Memos) (valid : Valid before.native.machine.heap memos) :
    ∃ result after saved final, Operand path values before memo result after saved ∧
      SourceCurrentAllocatedMergeOperand.Receipt formulas solver inventory path values
        before memo result after saved memos final := by
  obtain ⟨result, after, saved, final, receipt⟩ := SourceCurrentAllocatedMergeOperand.complete
    formulas solver inventory path values before memo ready admitted available domain stored covered memos valid
  exact ⟨result, after, saved, final, of_receipt receipt, receipt⟩

/-- Each head operand runs before its tail and the checked request at that tail's return. -/
inductive Fold [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (values : List (Value Symbol Guard)) (seed : List Int) :
    List (List Int) → Checked width → Memo → Value Symbol Guard → Checked width → Memo → Prop where
  | nil (operand : Operand seed values before memo result after saved) :
      Fold values seed [] before memo result after saved
  | cons (operand : Operand path values before memo head middle current)
      (rest : Fold values seed paths middle current tail later saved)
      (checked : Step head tail later result after) :
      Fold values seed (path :: paths) before memo result after saved

/-- Empty targets return EmptyNode. Nonempty targets use their literal first operand as seed. -/
inductive Target [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (values : List (Value Symbol Guard)) :
    List (List Int) → Checked width → Memo → Value Symbol Guard → Checked width → Memo → Prop where
  | nil : Target values [] before memo .empty before memo
  | nonempty (fold : Fold values seed paths before memo result after saved) :
      Target values (seed :: paths) before memo result after saved

/-- Only actual raw operand and tail returns select a native word-range obligation. -/
def FoldRanges [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (values : List (Value Symbol Guard)) (seed : List Int) :
    List (List Int) → Checked width → Memo → Prop
  | [], _, _ => True
  | path :: paths, before, memo =>
      (∀ head middle current, Operand path values before memo head middle current →
        FoldRanges values seed paths middle current) ∧
      (∀ head middle current tail later saved,
        Operand path values before memo head middle current → Fold values seed paths middle current tail later saved →
        WordRanges (.code (requestNode emptyDomain head tail)) later)

/-- Range plans retain the actual target seed and captured forest. -/
def TargetRanges [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (values : List (Value Symbol Guard)) (paths : List (List Int)) (before : Checked width) (memo : Memo) : Prop :=
  match paths with
  | [] => True
  | seed :: paths => FoldRanges values seed paths before memo

/-- Every actual operand retains the earlier completed merge entries. -/
theorem Operand.extends [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {path : List Int} {values : List (Value Symbol Guard)} {before after : Checked width}
    {memo saved : Memo} {result : Value Symbol Guard}
    (actual : Operand path values before memo result after saved) : Extends memo saved := by
  cases actual with
  | force _ merged => cases merged with
    | done call => exact call.graph.extends

/-- The right fold passes all completed merge entries through its actual prefixes. -/
theorem Fold.extends [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {values : List (Value Symbol Guard)} {seed : List Int} {paths : List (List Int)}
    {before after : Checked width} {memo saved : Memo} {result : Value Symbol Guard}
    (actual : Fold values seed paths before memo result after saved) : Extends memo saved := by
  induction actual with
  | nil operand => exact operand.extends
  | cons operand _ _ tail => exact extends_trans operand.extends tail

/-- Empty and nonempty targets retain the same earlier completed merge records. -/
theorem Target.extends [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {values : List (Value Symbol Guard)} {paths : List (List Int)} {before after : Checked width}
    {memo saved : Memo} {result : Value Symbol Guard}
    (actual : Target values paths before memo result after saved) : Extends memo saved := by
  cases actual with
  | nil => exact extends_refl _
  | nonempty fold => exact fold.extends

end MicroCFTA.SourceCurrentAllocatedTargetGraph
