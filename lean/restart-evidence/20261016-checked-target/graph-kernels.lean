import MicroCFTA.SourceCurrentAllocatedTargetGraph
namespace MicroCFTA.AllocatedTargetGraphKernels
open Cache Language InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open SourceCurrentAllocatedTargetGraph
open SourceCurrentAllocatedNativeInventoryState (Inventory At)
open SourceCurrentAllocatedQueryMemo (advancePhysical)
open SourceCurrentMemoMergeEffects (Stored)
open SourceCurrentMemoMergeLanguage (CacheCovers)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Memo" => SourceCurrentMemoMergeGraph.Memo Symbol Guard
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Valid" => EndpointMemoGateTrace.Valid
local notation "Ready" => SourceCurrentConjunctionClassScan.Ready
variable {width : Nat} [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]

-- The raw operand starts merging at the exact checked projection return.
example {path : List Int} {values : List (Value Symbol Guard)} {before after : Checked width}
 {memo saved : Memo} {projected result : Value Symbol Guard} {heap : State Symbol Guard}
 (projection : SourceEqualityProjectionGraph.Forest path values before.native.machine.heap projected heap)
 (merged : SourceCurrentAllocatedMerge.Merge SourceCurrentAllocatedMerge.literalClear projected
   (advancePhysical before ⟨heap, before.operations⟩) memo result after saved) :
 Operand path values before memo result after saved := .force projection merged

-- Initial selected support constructs an actual raw operand with closed result and retained native tables.
example (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
 (inventory : Inventory) (path : List Int) (values : List (Value Symbol Guard)) (before : Checked width) (memo : Memo)
 (ready : Ready before) (admitted : At formulas solver inventory before)
 (available : Values before.native.machine.heap values) (domain : SourceEqualityProjectionPathDomain.ForestClosed path values)
 (stored : Stored before.native.machine.heap memo)
 (covered : ∀ ambient, CacheCovers (SourceEqualityPCSGuard.holds formulas solver) ambient memo)
 (memos : Memos) (valid : Valid before.native.machine.heap memos) :
 ∃ result after saved final, Operand path values before memo result after saved ∧ result.free = [] ∧
  Valid after.native.machine.heap final ∧ after.native.nodes = before.native.nodes ∧
  after.native.edges = before.native.edges ∧ after.native.machine.domains = before.native.machine.domains := by
 obtain ⟨result, after, saved, final, actual, receipt⟩ := Operand.complete formulas solver inventory path values before memo
  ready admitted available domain stored covered memos valid
 exact ⟨result, after, saved, final, actual, receipt.closed, receipt.globals, receipt.nodes, receipt.edges, receipt.domains⟩

-- Verification uses the supplied actual raw operand, with selected-subterm inclusion at its exact output.
example (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
 (inventory : Inventory) {path : List Int} {values : List (Value Symbol Guard)} {before after : Checked width}
 {memo saved : Memo} {result : Value Symbol Guard} (actual : Operand path values before memo result after saved)
 (ready : Ready before) (admitted : At formulas solver inventory before)
 (available : Values before.native.machine.heap values) (domain : SourceEqualityProjectionPathDomain.ForestClosed path values)
 (stored : Stored before.native.machine.heap memo)
 (covered : ∀ ambient, CacheCovers (SourceEqualityPCSGuard.holds formulas solver) ambient memo)
 (memos : Memos) (valid : Valid before.native.machine.heap memos)
 (nonroot : path ≠ []) (ambient : InternedGuardedLanguage.Env Symbol) (symbol : Symbol)
 (terms : List (Term Symbol)) (part : Term Symbol)
 (accepted : All₂ (InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver) ambient) values terms)
 (selected : SymbolicSignedPaths.lookup (.node symbol terms) path = some part) :
 InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver) ambient result part := by
 obtain ⟨_, receipt⟩ := actual.verified formulas solver inventory ready admitted available domain stored covered memos valid
 exact receipt.included nonroot ambient symbol terms part accepted selected

-- A reached head and tail select exactly their returned-state range check.
example {values : List (Value Symbol Guard)} {seed path : List Int} {paths : List (List Int)}
 {before middle later : Checked width} {memo current saved : Memo} {head tail : Value Symbol Guard}
 (ranges : FoldRanges values seed (path :: paths) before memo)
 (operand : Operand path values before memo head middle current)
 (rest : Fold values seed paths middle current tail later saved) :
 FoldRanges values seed paths middle current ∧
 SourceCurrentAllocatedNativeRequestBounds.WordRanges
  (.code (SourceRecursiveIntersectionCode.requestNode IntersectionEmptyDomain.emptyDomain head tail)) later :=
 ⟨ranges.1 head middle current operand, ranges.2 head middle current tail later saved operand rest⟩

-- The literal two-path fold intersects the head with its actual first-seed result and retains that tail memo.
example {values : List (Value Symbol Guard)} {seed path : List Int}
 {before middle later after : Checked width} {memo current saved : Memo} {head tail result : Value Symbol Guard}
 (operand : Operand path values before memo head middle current)
 (seeded : Operand seed values middle current tail later saved)
 (checked : SourceCurrentAllocatedTargetQuery.Step head tail later result after) :
 Target values [seed, path] before memo result after saved := .nonempty (.cons operand (.nil seeded) checked)

-- Empty targets need no projection, merge, native query, or changed state.
example (values : List (Value Symbol Guard)) (before : Checked width) (memo : Memo) :
 Target values [] before memo .empty before memo ∧ TargetRanges values [] before memo := ⟨.nil, trivial⟩

-- The raw actual fold retains all earlier completed merge records across checked requests.
example {values : List (Value Symbol Guard)} {seed : List Int} {paths : List (List Int)}
 {before after : Checked width} {memo saved : Memo} {result : Value Symbol Guard}
 (actual : Fold values seed paths before memo result after saved) (key : InternedBinderProtocol.NodeRef)
 (entry : SourceCurrentMemoMergeGraph.Entry Symbol Guard) (found : memo key = some entry) : saved key = some entry :=
 actual.extends key entry found
end MicroCFTA.AllocatedTargetGraphKernels
