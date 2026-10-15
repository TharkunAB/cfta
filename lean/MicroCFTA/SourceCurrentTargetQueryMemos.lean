import MicroCFTA.SourceCurrentTargetPathComplete
import MicroCFTA.SourceCurrentMergedQueryMemos
import MicroCFTA.SourceCurrentRequiredQueryMemos
import MicroCFTA.SourceNativeGlobalMemos
import MicroCFTA.SourceEqualityNativeScopedCosts

/-!
# Actual global memo receipts through shared class targets

Captured operands use their selected path domains. Projection, merge body,
recursive target fold, and native calls retain their literal returned states.
A stored target hit adds no call. A first force records its actual target.
These receipts concern the resident source graphs, not GHC publication.
-/
namespace MicroCFTA.SourceCurrentTargetQueryMemos
open Cache InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open SourceEqualityRequiredCache SourceEqualityRequiredSemanticCache SourceEqualityNativeScoped
open SourceEqualityTargetOperand SourceEqualityDemandTarget SourceEqualityProjectionPathDomain
open SourceCurrentSubsumesQueryMemos (Effect)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Native" => SourceRecursiveIntersectionThunks.State
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Valid" => EndpointMemoGateTrace.Valid
local notation "CostHeap" => InternedFreshOrdinaryCostHeap.Heap

/-- Adjacent actual memo effects retain all earlier entries and final invariants. -/
theorem effect_trans [DecidableEq (EdgeKey Symbol Guard)]
    {before middle after : State Symbol Guard} {memos saved final : Memos}
    (first : Effect before middle memos saved) (second : Effect middle after saved final) :
    Effect before after memos final :=
  ⟨first.keeps.trans second.keeps, second.semantic, second.costs, second.valid,
    extends_trans first.retained second.retained, second.query.trans first.query⟩

/-- A completed scoped native request retains its actual silent primitive trace. -/
def NativeReads [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {emptyGuard : Guard} {conjoin : Guard → Guard → Guard}
    {target input result : Value Symbol Guard} {before after : Native width Symbol Guard}
    (_trace : Step emptyGuard conjoin target input before result after) (memos saved : Memos) : Prop :=
  saved = memos ∧ ∃ events, SourceGlobalUnfold.Runs ⟨before.machine.heap, memos.unfolding⟩
    ⟨after.machine.heap, memos.unfolding⟩ events ∧ SourceGlobalUnfold.NoGlobal events

/-- The captured operand records actual projection followed by its actual merge body. -/
inductive OperandReads [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] :
    {clear : Guard → Bool} → {top : Guard} → {path : List Int} → {values : List (Value Symbol Guard)} →
    {result : Value Symbol Guard} → {before after : Native width Symbol Guard} →
    Operand clear top path values before result after → Memos → Memos → Prop where
  | force (projected : SourceEqualityQueryGlobalMemos.ProjectionReads projection memos saved)
      (combined : SourceCurrentMergedQueryMemos.MergeReads merged saved final) :
      OperandReads (.force projection merged) memos final

/-- Source target folds retain the left operand, tail, and native step in actual demand order. -/
inductive FoldReads [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] :
    {emptyGuard : Guard} → {conjoin : Guard → Guard → Guard} → {clear : Guard → Bool} → {top : Guard} →
    {values : List (Value Symbol Guard)} → {seed : List Int} → {paths : List (List Int)} →
    {result : Value Symbol Guard} → {before after : Native width Symbol Guard} →
    SourceEqualityDemandTarget.Fold emptyGuard conjoin clear top values seed paths before result after → Memos → Memos → Prop where
  | nil (own : OperandReads seedDemand memos saved) : FoldReads (.nil seedDemand) memos saved
  | cons (own : OperandReads operand memos saved) (tail : FoldReads rest saved next)
      (native : NativeReads step next final) : FoldReads (.cons operand rest step) memos final

/-- Empty targets add no calls; nonempty targets retain their exact demanded fold. -/
inductive TargetReads [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] :
    {emptyGuard : Guard} → {conjoin : Guard → Guard → Guard} → {clear : Guard → Bool} → {top : Guard} →
    {values : List (Value Symbol Guard)} → {paths : List (List Int)} →
    {result : Value Symbol Guard} → {before after : Native width Symbol Guard} →
    Target emptyGuard conjoin clear top values paths before result after → Memos → Memos → Prop where
  | nil : TargetReads .nil memos memos
  | cons (own : FoldReads fold memos saved) : TargetReads (.cons fold) memos saved

/-- Concrete native steps derive coherent unchanged global tables and the actual stored cost invariant. -/
theorem native_memos [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {emptyGuard : Guard} {conjoin : Guard → Guard → Guard}
    {target input result : Value Symbol Guard} {before after : Native width Symbol Guard}
    (trace : Step emptyGuard conjoin target input before result after) (ready : IdleReady emptyGuard conjoin before)
    (costs : CostHeap before.machine.heap) (targetAvailable : Available before.machine.heap target)
    (inputAvailable : Available before.machine.heap input) (targetClosed : target.free = []) (inputClosed : input.free = [])
    (memos : Memos) (valid : Valid before.machine.heap memos) :
    NativeReads trace memos memos ∧ Effect before.machine.heap after.machine.heap memos memos := by
  obtain ⟨events, actual, silent, coherent⟩ := SourceNativeGlobalMemos.scoped_memos trace ready
    targetAvailable inputAvailable targetClosed inputClosed (fun _ _ => true) (fun _ _ _ => rfl) memos valid
  have checked := trace.verified ready targetAvailable inputAvailable targetClosed inputClosed
    (fun _ _ => true) (fun _ _ _ => rfl)
  exact ⟨⟨rfl, events, actual, silent⟩, checked.2.1, checked.1.semantic,
    trace.cost_heap ready costs targetAvailable inputAvailable, coherent, extends_refl _, rfl⟩

/-- An actual operand derives projection and merge receipts without closing its captured forest. -/
theorem operand_memos [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {emptyGuard : Guard} {conjoin : Guard → Guard → Guard} {clear : Guard → Bool} {top : Guard}
    {path : List Int} {values : List (Value Symbol Guard)} {result : Value Symbol Guard}
    {before after : Native width Symbol Guard}
    (trace : Operand clear top path values before result after) (ready : IdleReady emptyGuard conjoin before)
    (costs : CostHeap before.machine.heap) (available : Values before.machine.heap values) (domain : ForestClosed path values)
    (memos : Memos) (valid : Valid before.machine.heap memos) :
    ∃ saved, OperandReads trace memos saved ∧ Effect before.machine.heap after.machine.heap memos saved := by
  cases trace with
  | force projection merged =>
      have projected := SourceEqualityProjectionPathDomain.forest_effects projection ready.semantic available domain
      have physical := SourceEqualityProjectionCosts.forest_effects projection ready.semantic costs available
      obtain ⟨middle, read, coherent, retained⟩ :=
        SourceEqualityQueryGlobalMemos.forest_memos projection ready.semantic costs available memos valid
      have first : Effect before.machine.heap _ memos middle :=
        ⟨physical.1, physical.2.1, physical.2.2.1, coherent, retained, read.2⟩
      obtain ⟨saved, mergeReads, effects, _⟩ := SourceCurrentMergedQueryMemos.merge_memos merged
        (ready.advance _ projected.1 projected.2.1) first.costs projected.2.2.1 middle first.valid
      exact ⟨saved, .force read mergeReads, effect_trans first effects⟩

/-- Every actual target fold derives its ordered reads and all three coherent returned tables. -/
theorem fold_memos [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {emptyGuard : Guard} {conjoin : Guard → Guard → Guard} {clear : Guard → Bool} {top : Guard}
    {values : List (Value Symbol Guard)} {seed : List Int} {paths : List (List Int)} {result : Value Symbol Guard}
    {before after : Native width Symbol Guard}
    (trace : SourceEqualityDemandTarget.Fold emptyGuard conjoin clear top values seed paths before result after)
    (ready : IdleReady emptyGuard conjoin before) (costs : CostHeap before.machine.heap)
    (available : Values before.machine.heap values) (domains : ∀ path ∈ seed :: paths, ForestClosed path values)
    (memos : Memos) (valid : Valid before.machine.heap memos) :
    ∃ saved, FoldReads trace memos saved ∧ Effect before.machine.heap after.machine.heap memos saved := by
  induction trace generalizing memos with
  | nil seedDemand =>
      obtain ⟨saved, read, effects⟩ := operand_memos seedDemand ready costs available (domains _ List.mem_cons_self) memos valid
      exact ⟨saved, .nil read, effects⟩
  | @cons path before value middle paths tail later result after operand rest step ih =>
      have first := operand.path_effects ready available (domains path (by simp))
      obtain ⟨saved, own, effects⟩ := operand_memos operand ready costs available (domains path (by simp)) memos valid
      have tailDomains : ∀ own ∈ seed :: paths, ForestClosed own values := by
        intro own member
        rcases List.mem_cons.mp member with rfl | member
        · exact domains _ List.mem_cons_self
        · exact domains own (by simp only [List.mem_cons]; exact Or.inr (Or.inr member))
      have nextAvailable : Values middle.machine.heap values := fun value member => effects.keeps.available value (available value member)
      have remaining := rest.path_effects first.1 nextAvailable tailDomains
      obtain ⟨next, tailReads, tailEffects⟩ := ih first.1 effects.costs nextAvailable tailDomains saved effects.valid
      have native := native_memos step remaining.1 tailEffects.costs
        (tailEffects.keeps.available value first.2.2.1) remaining.2.2.1 first.2.2.2.1 remaining.2.2.2 next tailEffects.valid
      exact ⟨next, .cons own tailReads native.1, effect_trans effects (effect_trans tailEffects native.2)⟩

/-- Actual targets derive their exact read sequence, final coherence, and retained unfolding entries. -/
theorem target_memos [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {emptyGuard : Guard} {conjoin : Guard → Guard → Guard} {clear : Guard → Bool} {top : Guard}
    {values : List (Value Symbol Guard)} {paths : List (List Int)} {result : Value Symbol Guard}
    {before after : Native width Symbol Guard}
    (trace : Target emptyGuard conjoin clear top values paths before result after)
    (ready : IdleReady emptyGuard conjoin before) (costs : CostHeap before.machine.heap)
    (available : Values before.machine.heap values) (domains : ∀ path ∈ paths, ForestClosed path values)
    (memos : Memos) (valid : Valid before.machine.heap memos) :
    ∃ saved, TargetReads trace memos saved ∧ Effect before.machine.heap after.machine.heap memos saved := by
  cases trace with
  | nil => exact ⟨memos, .nil, pure_keeps _ ready.semantic.ready, ready.semantic, costs, valid, extends_refl _, rfl⟩
  | cons fold =>
      obtain ⟨saved, read, effects⟩ := fold_memos fold ready costs available domains memos valid
      exact ⟨saved, .cons read, effects⟩

open SourceEqualitySharedTargetState SourceEqualitySharedTargetForce SourceEqualitySharedTargetLeaf

/-- Stored target hits add no calls; first forces retain their actual constructed target. -/
inductive ForceReads [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] :
    {emptyGuard : Guard} → {conjoin : Guard → Guard → Guard} → {clear : Guard → Bool} → {top : Guard} →
    {record : SourceEqualityClassOrder.Record} → {values : List (Value Symbol Guard)} → {path : EqualityNormalize.Path} →
    {value : Value Symbol Guard} → {before after : SourceEqualitySharedTargetState.State width Symbol Guard} →
    Force emptyGuard conjoin clear top record values path before value after → Memos → Memos → Prop where
  | hit {before : SourceEqualitySharedTargetState.State width Symbol Guard} (present : before.targets path = some value) : ForceReads (.hit present) memos memos
  | miss {emptyGuard : Guard} {conjoin : Guard → Guard → Guard} {clear : Guard → Bool} {top : Guard}
      {record : SourceEqualityClassOrder.Record} {values : List (Value Symbol Guard)} {path : EqualityNormalize.Path}
      {before : SourceEqualitySharedTargetState.State width Symbol Guard} {native : Native width Symbol Guard}
      {value : Value Symbol Guard} {memos saved : Memos}
      (absent : before.targets path = none)
      {actual : Target emptyGuard conjoin clear top values
        (SourceEqualityClassTarget.operandPaths record.paths path) before.native value native}
      (read : TargetReads actual memos saved) : ForceReads (.miss absent actual) memos saved

/-- Actual edit leaves retain first-force or reuse receipts before their scoped native request. -/
inductive LeafReads [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] :
    {emptyGuard : Guard} → {conjoin : Guard → Guard → Guard} → {clear : Guard → Bool} → {top : Guard} →
    {record : SourceEqualityClassOrder.Record} → {values : List (Value Symbol Guard)} → {path : EqualityNormalize.Path} →
    {input result : Value Symbol Guard} → {before after : SourceEqualitySharedTargetState.State width Symbol Guard} →
    Leaf emptyGuard conjoin clear top record values path input before result after → Memos → Memos → Prop where
  | apply (forced : ForceReads force memos saved) (native : NativeReads step saved final) : LeafReads (.apply force step) memos final

/-- A target closure derives actual reads and coherent global tables in either force branch. -/
theorem force_memos [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {emptyGuard : Guard} {conjoin : Guard → Guard → Guard} {clear : Guard → Bool} {top : Guard}
    {record : SourceEqualityClassOrder.Record} {values : List (Value Symbol Guard)}
    {base : InternedConstructorTemplates.State Symbol Guard} {path : EqualityNormalize.Path} {value : Value Symbol Guard}
    {before after : SourceEqualitySharedTargetState.State width Symbol Guard}
    (trace : Force emptyGuard conjoin clear top record values path before value after)
    (ready : Ready emptyGuard conjoin clear top record values base before) (known : Values base values)
    (domains : ∀ path ∈ record.paths, ForestClosed (path.map Int.ofNat) values)
    (costs : CostHeap before.native.machine.heap) (memos : Memos) (valid : Valid before.native.machine.heap memos) :
    ∃ saved, ForceReads trace memos saved ∧ Effect before.native.machine.heap after.native.machine.heap memos saved := by
  cases trace with
  | hit present => exact ⟨memos, .hit present, pure_keeps _ ready.native.semantic.ready,
      ready.native.semantic, costs, valid, extends_refl _, rfl⟩
  | miss absent actual =>
      obtain ⟨saved, read, effects⟩ := target_memos actual ready.native costs
        (fun value member => ready.captured.available value (known value member))
        (SourceCurrentTargetPathComplete.operand_domains record values domains path) memos valid
      exact ⟨saved, .miss absent read, effects⟩

/-- A concrete shared edit leaf derives all global reads and final heap invariants. -/
theorem leaf_memos [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {emptyGuard : Guard} {conjoin : Guard → Guard → Guard} {clear : Guard → Bool} {top : Guard}
    {record : SourceEqualityClassOrder.Record} {values : List (Value Symbol Guard)}
    {base : InternedConstructorTemplates.State Symbol Guard} {path : EqualityNormalize.Path}
    {input result : Value Symbol Guard} {before after : SourceEqualitySharedTargetState.State width Symbol Guard}
    (trace : Leaf emptyGuard conjoin clear top record values path input before result after)
    (ready : Ready emptyGuard conjoin clear top record values base before) (known : Values base values)
    (domains : ∀ path ∈ record.paths, ForestClosed (path.map Int.ofNat) values) (member : path ∈ record.paths)
    (available : Available before.native.machine.heap input) (closed : input.free = [])
    (costs : CostHeap before.native.machine.heap) (memos : Memos) (valid : Valid before.native.machine.heap memos) :
    ∃ saved, LeafReads trace memos saved ∧ Effect before.native.machine.heap after.native.machine.heap memos saved := by
  cases trace with
  | apply force step =>
      have first := force.path_effects ready known domains member
      obtain ⟨saved, forceReads, forceEffects⟩ := force_memos force ready known domains costs memos valid
      have native := native_memos step first.1.native forceEffects.costs first.2.2.1
        (forceEffects.keeps.available input available) first.2.2.2.1 closed saved forceEffects.valid
      exact ⟨saved, .apply forceReads native.1, effect_trans forceEffects native.2⟩

end MicroCFTA.SourceCurrentTargetQueryMemos
