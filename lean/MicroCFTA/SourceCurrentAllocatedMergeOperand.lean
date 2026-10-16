import MicroCFTA.SourceCurrentAllocatedMerge
import MicroCFTA.SourceCurrentConjunctionTargetProjection

/-!
# Checked projection and allocated target merging

One operand projects the captured forest, then merges that actual result.
The returned state retains native tables, loaded fields, and the input inventory.
Only the selected projection domain must be closed.
Merging retains accepted selected terms and can add terms.
-/
namespace MicroCFTA.SourceCurrentAllocatedMergeOperand
open Cache Language EqualityNormalize InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open InternedGuardedLanguage (meaning)
open SourceCurrentAllocatedNativeEffects (physical)
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
variable {width : Nat}

/-- Both actual operations retain the same captured input forest and intermediate state. -/
structure Receipt [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (path : List Int) (values : List (Value Symbol Guard))
    (before : Checked width) (memo : Memo) (output : Value Symbol Guard) (after : Checked width)
    (saved : Memo) (memos final : Memos) : Prop where
  actual : ∃ projected middle current,
    SourceCurrentConjunctionTargetProjection.Receipt formulas solver inventory path values before projected middle memos current ∧
    SourceCurrentAllocatedMerge.Receipt formulas solver inventory SourceCurrentAllocatedMerge.literalClear
      projected middle memo output after saved current final
  ready : Ready after
  admitted : At formulas solver inventory after
  effects : SourceCurrentConjunctionRowsAllocation.Effects (physical before) (physical after)
  stored : Stored after.native.machine.heap saved
  covered : ∀ ambient, CacheCovers (SourceEqualityPCSGuard.holds formulas solver) ambient saved
  available : Available after.native.machine.heap output
  closed : output.free = []
  originals : Values after.native.machine.heap values
  nodes : after.native.nodes = before.native.nodes
  edges : after.native.edges = before.native.edges
  domains : after.native.machine.domains = before.native.machine.domains
  retained : Extends memo saved
  globals : Valid after.native.machine.heap final
  unfolding : Extends memos.unfolding final.unfolding
  query : final.query = memos.query
  included : path ≠ [] → ∀ ambient symbol terms part,
    All₂ (meaning (SourceEqualityPCSGuard.holds formulas solver) ambient) values terms →
    SymbolicSignedPaths.lookup (.node symbol terms) path = some part →
    meaning (SourceEqualityPCSGuard.holds formulas solver) ambient output part
  root_covered : path = [] → ∀ ambient term,
    (∃ value ∈ values, meaning (SourceEqualityPCSGuard.holds formulas solver) ambient value term) →
    meaning (SourceEqualityPCSGuard.holds formulas solver) ambient output term

/-- Initial selected support constructs projection, merge, and all returned invariants. -/
theorem complete [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (path : List Int) (values : List (Value Symbol Guard))
    (before : Checked width) (memo : Memo) (ready : Ready before)
    (admitted : At formulas solver inventory before) (available : Values before.native.machine.heap values)
    (domain : SourceEqualityProjectionPathDomain.ForestClosed path values)
    (stored : Stored before.native.machine.heap memo)
    (covered : ∀ ambient, CacheCovers (SourceEqualityPCSGuard.holds formulas solver) ambient memo)
    (memos : Memos) (valid : Valid before.native.machine.heap memos) :
    ∃ output after saved final, Receipt formulas solver inventory path values before memo output after saved memos final := by
  obtain ⟨projected, middle, current, projection⟩ := SourceCurrentConjunctionTargetProjection.complete
    formulas solver inventory path values before ready admitted available domain memos valid
  obtain ⟨output, after, saved, final, merged⟩ := SourceCurrentAllocatedMerge.source_finite
    formulas solver inventory projected middle memo projection.ready projection.admitted
    (stored.grows projection.effects.keeps) covered projection.available current projection.globals.valid
  have effects := projection.effects.trans merged.effects
  refine ⟨output, after, saved, final, ⟨⟨projected, middle, current, projection, merged⟩,
    merged.ready, merged.admitted, effects, merged.stored, merged.covered, merged.available,
    merged.closed projection.closed, ?_, merged.nodes.trans projection.nodes,
    merged.edges.trans projection.edges, merged.domains.trans projection.domains,
    merged.retained, merged.globals.valid,
    extends_trans projection.globals.retained merged.globals.retained,
    merged.globals.query.trans projection.globals.query, ?_, ?_⟩⟩
  · intro value member
    exact effects.keeps.available value (available value member)
  · intro nonroot ambient symbol terms part accepted found
    exact merged.included ambient part (projection.included nonroot _ ambient symbol terms part accepted found)
  · intro root ambient term accepted
    exact merged.included ambient term ((projection.root_exact root _ ambient term).mpr accepted)

/-- Current required preparation supplies the exact selected operand domain. -/
theorem of_required [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) {selected : Constraints} {originals values : List (Value Symbol Guard)}
    {before after : Checked width}
    (required : SourceCurrentConjunctionRequired.Receipt formulas solver inventory selected originals values before after)
    (path : Path) (member : path ∈ selected.flatten) (memo : Memo)
    (stored : Stored after.native.machine.heap memo)
    (covered : ∀ ambient, CacheCovers (SourceEqualityPCSGuard.holds formulas solver) ambient memo)
    (memos : Memos) (valid : Valid after.native.machine.heap memos) :
    ∃ output reached saved final,
      Receipt formulas solver inventory (path.map Int.ofNat) values after memo output reached saved memos final :=
  complete formulas solver inventory (path.map Int.ofNat) values after memo required.ready required.admitted
    required.resident (required.paths path member) stored covered memos valid

end MicroCFTA.SourceCurrentAllocatedMergeOperand
