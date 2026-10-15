import MicroCFTA.SourceCurrentMemoMergeNative
import MicroCFTA.SourceEqualityProjectionPathComplete
import MicroCFTA.SourceEqualityProjectionCosts
import MicroCFTA.SourceEqualityQueryGlobalMemos

/-!
# Selected target operands with actual memo-aware merging

Each operand projects its captured original forest. It then merges the
projected record through the completed result table at the returned heap.
Only the selected path domain must be closed. Unrelated ordinary siblings
can remain open. The graph retains the same full native state throughout.
-/
namespace MicroCFTA.SourceCurrentMemoTargetOperand
open Cache Language InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open InternedGuardedLanguage (meaning)
open SourceEqualityRequiredCache SourceEqualityRequiredSemanticCache SourceEqualityNativeScoped
open SourceEqualityProjectionGraph SourceEqualityProjectionPathDomain SourceCurrentMemoMergeGraph
open SourceCurrentMemoMergeEffects (Stored)
open SourceCurrentMemoMergeLanguage (CacheCovers)
open SourceCurrentMemoMergeOrigins (Produced)
local notation "Native" => SourceRecursiveIntersectionThunks.State
local notation "CostHeap" => InternedFreshOrdinaryCostHeap.Heap

/-- One literal captured projection precedes the actual completed memo-aware merge. -/
inductive Operand [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (clear : Guard → Bool) (top : Guard) (path : List Int) (values : List (Value Symbol Guard)) :
    Native width Symbol Guard → Memo Symbol Guard → Value Symbol Guard → Native width Symbol Guard → Memo Symbol Guard → Prop where
  | force (projection : Forest path values before.machine.heap projected heap)
      (merged : SourceCurrentMemoMergeNative.Merge clear top projected (advanceHeap before heap) memo result after saved) :
      Operand clear top path values before memo result after saved

/-- Actual operands retain native state and return a closed available result. -/
structure Effects [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (emptyGuard : Guard) (conjoin : Guard → Guard → Guard)
    (before : Native width Symbol Guard) (memo : Memo Symbol Guard) (result : Value Symbol Guard)
    (after : Native width Symbol Guard) (saved : Memo Symbol Guard) : Prop where
  ready : IdleReady emptyGuard conjoin after
  keeps : Keeps before.machine.heap after.machine.heap
  costs : CostHeap after.machine.heap
  stored : Stored after.machine.heap saved
  available : Available after.machine.heap result
  closed : result.free = []
  nodes : after.nodes = before.nodes
  edges : after.edges = before.edges
  domains : after.machine.domains = before.machine.domains
  retained : Extends memo saved

/-- Every accepted original term supplies each subterm selected by the proper forest path. -/
def SelectedCovers (holds : Guard → Term Symbol → Bool) (ambient : InternedGuardedLanguage.Env Symbol)
    (path : List Int) (values : List (Value Symbol Guard)) (result : Value Symbol Guard) : Prop :=
  ∀ symbol terms part, All₂ (meaning holds ambient) values terms →
    SymbolicSignedPaths.lookup (.node symbol terms) path = some part → meaning holds ambient result part

/-- The selected projection domain derives all physical and native operand effects. -/
theorem Operand.effects [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {emptyGuard : Guard} {conjoin : Guard → Guard → Guard} {clear : Guard → Bool} {top : Guard}
    {path : List Int} {values : List (Value Symbol Guard)} {result : Value Symbol Guard}
    {before after : Native width Symbol Guard} {memo saved : Memo Symbol Guard}
    (trace : Operand clear top path values before memo result after saved) (ready : IdleReady emptyGuard conjoin before)
    (costs : CostHeap before.machine.heap) (stored : Stored before.machine.heap memo)
    (available : Values before.machine.heap values) (domain : ForestClosed path values) :
    Effects emptyGuard conjoin before memo result after saved := by
  cases trace with
  | force projection merged =>
      have projected := SourceEqualityProjectionPathDomain.forest_effects projection ready.semantic available domain
      have physical := SourceEqualityProjectionCosts.forest_effects projection ready.semantic costs available
      have checked := merged.effects (ready.advance _ projected.1 projected.2.1) physical.2.2.1
        (stored.grows projected.1) projected.2.2.1
      exact ⟨checked.ready, projected.1.trans checked.keeps, checked.costs, checked.stored, checked.available,
        checked.closed projected.2.2.2, checked.nodes, checked.edges, checked.domains, checked.retained⟩

/-- Actual memo-aware merging retains accepted selected subterms of the original forest. -/
theorem Operand.included [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {emptyGuard : Guard} {conjoin : Guard → Guard → Guard} {clear : Guard → Bool} {top : Guard}
    {path : List Int} {values : List (Value Symbol Guard)} {result : Value Symbol Guard}
    {before after : Native width Symbol Guard} {memo saved : Memo Symbol Guard}
    (trace : Operand clear top path values before memo result after saved) (ready : IdleReady emptyGuard conjoin before)
    (costs : CostHeap before.machine.heap) (stored : Stored before.machine.heap memo)
    (holds : Guard → Term Symbol → Bool) (ambient : InternedGuardedLanguage.Env Symbol)
    (covered : CacheCovers holds ambient memo) (available : Values before.machine.heap values) (domain : ForestClosed path values)
    (clearTrue : ∀ guard, clear guard = true → ∀ term, holds guard term = true)
    (topTrue : ∀ term, holds top term = true) :
    CacheCovers holds ambient saved ∧ (path ≠ [] → SelectedCovers holds ambient path values result) := by
  cases trace with
  | force projection merged =>
      have projected := SourceEqualityProjectionPathDomain.forest_effects projection ready.semantic available domain
      have physical := SourceEqualityProjectionCosts.forest_effects projection ready.semantic costs available
      obtain ⟨retained, inclusion⟩ := merged.included (ready.advance _ projected.1 projected.2.1) physical.2.2.1
        (stored.grows projected.1) holds ambient covered projected.2.2.1 clearTrue topTrue
      refine ⟨retained, ?_⟩
      intro nonroot symbol terms part accepted selected
      cases path with
      | nil => exact False.elim (nonroot rfl)
      | cons index path =>
          exact inclusion part (SourceEqualityProjectionPathDomain.forest_included projection ready.semantic available domain
            holds ambient symbol terms part accepted selected)

/-- One operand trace supplies physical effects, retained cache coverage, and selected-term coverage. -/
theorem Operand.verified [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {emptyGuard : Guard} {conjoin : Guard → Guard → Guard} {clear : Guard → Bool} {top : Guard}
    {path : List Int} {values : List (Value Symbol Guard)} {result : Value Symbol Guard}
    {before after : Native width Symbol Guard} {memo saved : Memo Symbol Guard}
    (trace : Operand clear top path values before memo result after saved) (ready : IdleReady emptyGuard conjoin before)
    (costs : CostHeap before.machine.heap) (stored : Stored before.machine.heap memo)
    (holds : Guard → Term Symbol → Bool) (ambient : InternedGuardedLanguage.Env Symbol)
    (covered : CacheCovers holds ambient memo) (available : Values before.machine.heap values) (domain : ForestClosed path values)
    (clearTrue : ∀ guard, clear guard = true → ∀ term, holds guard term = true)
    (topTrue : ∀ term, holds top term = true) :
    Effects emptyGuard conjoin before memo result after saved ∧ CacheCovers holds ambient saved ∧
      (path ≠ [] → SelectedCovers holds ambient path values result) :=
  ⟨trace.effects ready costs stored available domain,
    trace.included ready costs stored holds ambient covered available domain clearTrue topTrue⟩

/-- Projection adds no result-table entries; the actual merge retains all earlier producers. -/
theorem Operand.produced [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {clear : Guard → Bool} {top : Guard} {path : List Int} {values : List (Value Symbol Guard)} {result : Value Symbol Guard}
    {before after : Native width Symbol Guard} {memo saved : Memo Symbol Guard}
    (trace : Operand clear top path values before memo result after saved) : Produced clear top memo → Produced clear top saved := by
  cases trace with
  | force _ merged => exact merged.produced

/-- Selected path domains derive a finite operand at the existing warm native and result tables. -/
theorem finite [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (emptyGuard : Guard) (conjoin : Guard → Guard → Guard) (clear : Guard → Bool) (top : Guard)
    (holds : Guard → Term Symbol → Bool) (ambient : InternedGuardedLanguage.Env Symbol)
    (clearTrue : ∀ guard, clear guard = true → ∀ term, holds guard term = true)
    (topTrue : ∀ term, holds top term = true)
    (path : List Int) (values : List (Value Symbol Guard)) (before : Native width Symbol Guard) (memo : Memo Symbol Guard)
    (ready : IdleReady emptyGuard conjoin before) (costs : CostHeap before.machine.heap) (stored : Stored before.machine.heap memo)
    (covered : CacheCovers holds ambient memo) (available : Values before.machine.heap values) (domain : ForestClosed path values) :
    ∃ result after saved, Operand clear top path values before memo result after saved ∧
      Effects emptyGuard conjoin before memo result after saved ∧ CacheCovers holds ambient saved ∧
      (path ≠ [] → SelectedCovers holds ambient path values result) := by
  obtain ⟨projected, heap, projection, checked⟩ :=
    SourceEqualityProjectionPathComplete.forest_complete path values before.machine.heap ready.semantic available domain
  have physical := SourceEqualityProjectionCosts.forest_effects projection ready.semantic costs available
  obtain ⟨result, after, saved, merged, _⟩ := SourceCurrentMemoMergeNative.finite
    emptyGuard conjoin clear top holds ambient clearTrue topTrue projected (advanceHeap before heap) memo
      (ready.advance _ checked.1 checked.2.1) physical.2.2.1 (stored.grows checked.1) covered checked.2.2.1
  have trace : Operand clear top path values before memo result after saved := .force projection merged
  exact ⟨result, after, saved, trace, trace.verified ready costs stored holds ambient covered available domain clearTrue topTrue⟩

/-- Empty result tables derive physical, semantic, and historical entry obligations. -/
theorem finite_cold [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (emptyGuard : Guard) (conjoin : Guard → Guard → Guard) (clear : Guard → Bool) (top : Guard)
    (holds : Guard → Term Symbol → Bool) (ambient : InternedGuardedLanguage.Env Symbol)
    (clearTrue : ∀ guard, clear guard = true → ∀ term, holds guard term = true)
    (topTrue : ∀ term, holds top term = true)
    (path : List Int) (values : List (Value Symbol Guard)) (before : Native width Symbol Guard)
    (ready : IdleReady emptyGuard conjoin before) (costs : CostHeap before.machine.heap)
    (available : Values before.machine.heap values) (domain : ForestClosed path values) :
    ∃ result after saved, Operand clear top path values before empty result after saved ∧
      Effects emptyGuard conjoin before empty result after saved ∧ CacheCovers holds ambient saved ∧
      Produced clear top saved ∧ (path ≠ [] → SelectedCovers holds ambient path values result) := by
  obtain ⟨result, after, saved, trace, effect, covered, inclusion⟩ := finite emptyGuard conjoin clear top holds ambient clearTrue topTrue
    path values before empty ready costs (SourceCurrentMemoMergeEffects.stored_empty _) (SourceCurrentMemoMergeLanguage.cache_covers_empty _ _) available domain
  exact ⟨result, after, saved, trace, effect, covered, trace.produced (SourceCurrentMemoMergeOrigins.produced_empty _ _), inclusion⟩

end MicroCFTA.SourceCurrentMemoTargetOperand

namespace MicroCFTA.SourceCurrentMemoTargetOperand
open Cache Language InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open SourceEqualityRequiredCache SourceEqualityNativeScoped SourceEqualityProjectionGraph SourceEqualityProjectionPathDomain SourceCurrentMemoMergeGraph
open SourceCurrentMemoMergeEffects (Stored)
open SourceCurrentMemoMergeLanguage (CacheCovers)
open SourceCurrentMemoMergeOrigins (Produced)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Native" => SourceRecursiveIntersectionThunks.State
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Valid" => EndpointMemoGateTrace.Valid
local notation "CostHeap" => InternedFreshOrdinaryCostHeap.Heap

/-- Operand receipts retain exact projection reads before the actual memo-aware merge reads. -/
inductive Reads [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (clear : Guard → Bool) (top : Guard) (path : List Int) (values : List (Value Symbol Guard)) :
    Native width Symbol Guard → Memo Symbol Guard → Value Symbol Guard → Native width Symbol Guard →
      Memo Symbol Guard → Memos → Memos → Prop where
  | force {projection : Forest path values before.machine.heap projected heap}
      (projectedReads : SourceEqualityQueryGlobalMemos.ProjectionReads projection memos middle)
      (mergedReads : SourceCurrentMemoMergeNative.Reads clear top projected (advanceHeap before heap) memo result after saved middle final) :
      Reads clear top path values before memo result after saved memos final

theorem Reads.graph [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {clear : Guard → Bool} {top : Guard} {path : List Int} {values : List (Value Symbol Guard)} {result : Value Symbol Guard}
    {before after : Native width Symbol Guard} {memo saved : Memo Symbol Guard} {memos final : Memos}
    (receipt : Reads clear top path values before memo result after saved memos final) :
    Operand clear top path values before memo result after saved := by
  cases receipt with
  | force _ merged => exact .force (by assumption) merged.graph

theorem Reads.query [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {clear : Guard → Bool} {top : Guard} {path : List Int} {values : List (Value Symbol Guard)} {result : Value Symbol Guard}
    {before after : Native width Symbol Guard} {memo saved : Memo Symbol Guard} {memos final : Memos}
    (receipt : Reads clear top path values before memo result after saved memos final) : final.query = memos.query := by
  cases receipt with
  | force projected merged => exact merged.query.trans projected.2

/-- Actual operands derive the coherent three global tables in projection-then-merge order. -/
theorem Operand.memos [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {emptyGuard : Guard} {conjoin : Guard → Guard → Guard} {clear : Guard → Bool} {top : Guard}
    {path : List Int} {values : List (Value Symbol Guard)} {result : Value Symbol Guard}
    {before after : Native width Symbol Guard} {memo saved : Memo Symbol Guard}
    (trace : Operand clear top path values before memo result after saved) (ready : IdleReady emptyGuard conjoin before)
    (costs : CostHeap before.machine.heap) (stored : Stored before.machine.heap memo)
    (available : Values before.machine.heap values) (domain : ForestClosed path values)
    (memos : Memos) (valid : Valid before.machine.heap memos) :
    ∃ final, Reads clear top path values before memo result after saved memos final ∧
      SourceCurrentSubsumesQueryMemos.Effect before.machine.heap after.machine.heap memos final := by
  cases trace with
  | force projection merged =>
      have projected := SourceEqualityProjectionPathDomain.forest_effects projection ready.semantic available domain
      have physical := SourceEqualityProjectionCosts.forest_effects projection ready.semantic costs available
      obtain ⟨middle, read, coherent, retained⟩ := SourceEqualityQueryGlobalMemos.forest_memos projection ready.semantic costs available memos valid
      have first : SourceCurrentSubsumesQueryMemos.Effect before.machine.heap _ memos middle :=
        ⟨physical.1, physical.2.1, physical.2.2.1, coherent, retained, read.2⟩
      obtain ⟨final, mergeReads, effect⟩ := merged.memos (ready.advance _ projected.1 projected.2.1) first.costs
        (stored.grows projected.1) projected.2.2.1 middle first.valid
      exact ⟨final, .force read mergeReads, SourceCurrentMemoMergeQueryMemos.effect_trans first effect⟩

local notation "clear" => SourceMemoGate.plain
local notation "top" => SourceEqualityConstraintConstructors.top (Formula := FullSyntax.Formula)

/-- The source operand completes with retained warm tables and exact projection and merge reads. -/
theorem source_finite [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (emptyGuard : Guard) (conjoin : Guard → Guard → Guard)
    (holds : Guard → Term Symbol → Bool) (ambient : InternedGuardedLanguage.Env Symbol)
    (clearTrue : ∀ guard, clear guard = true → ∀ term, holds guard term = true) (topTrue : ∀ term, holds top term = true)
    (path : List Int) (values : List (Value Symbol Guard)) (before : Native width Symbol Guard) (memo : Memo Symbol Guard)
    (ready : IdleReady emptyGuard conjoin before) (costs : CostHeap before.machine.heap) (stored : Stored before.machine.heap memo)
    (covered : CacheCovers holds ambient memo) (available : Values before.machine.heap values) (domain : ForestClosed path values)
    (memos : Memos) (valid : Valid before.machine.heap memos) :
    ∃ result after saved final, Operand clear top path values before memo result after saved ∧
      Reads clear top path values before memo result after saved memos final ∧ Effects emptyGuard conjoin before memo result after saved ∧
      CacheCovers holds ambient saved ∧ (path ≠ [] → SelectedCovers holds ambient path values result) ∧
      SourceCurrentSubsumesQueryMemos.Effect before.machine.heap after.machine.heap memos final := by
  obtain ⟨result, after, saved, trace, effect, covered, inclusion⟩ := finite emptyGuard conjoin clear top holds ambient clearTrue topTrue
    path values before memo ready costs stored covered available domain
  obtain ⟨final, receipt, global⟩ := trace.memos ready costs stored available domain memos valid
  exact ⟨result, after, saved, final, trace, receipt, effect, covered, inclusion, global⟩

/-- An empty source result table derives a finite closed operand and its literal global receipts. -/
theorem source_cold [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (emptyGuard : Guard) (conjoin : Guard → Guard → Guard)
    (holds : Guard → Term Symbol → Bool) (ambient : InternedGuardedLanguage.Env Symbol)
    (clearTrue : ∀ guard, clear guard = true → ∀ term, holds guard term = true) (topTrue : ∀ term, holds top term = true)
    (path : List Int) (values : List (Value Symbol Guard)) (before : Native width Symbol Guard)
    (ready : IdleReady emptyGuard conjoin before) (costs : CostHeap before.machine.heap)
    (available : Values before.machine.heap values) (domain : ForestClosed path values)
    (memos : Memos) (valid : Valid before.machine.heap memos) :
    ∃ result after saved final, Operand clear top path values before empty result after saved ∧
      Reads clear top path values before empty result after saved memos final ∧ Effects emptyGuard conjoin before empty result after saved ∧
      CacheCovers holds ambient saved ∧ Produced clear top saved ∧ (path ≠ [] → SelectedCovers holds ambient path values result) ∧
      SourceCurrentSubsumesQueryMemos.Effect before.machine.heap after.machine.heap memos final := by
  obtain ⟨result, after, saved, trace, effect, covered, produced, inclusion⟩ := finite_cold emptyGuard conjoin clear top holds ambient clearTrue topTrue
    path values before ready costs available domain
  obtain ⟨final, receipt, global⟩ := trace.memos ready costs (SourceCurrentMemoMergeEffects.stored_empty _) available domain memos valid
  exact ⟨result, after, saved, final, trace, receipt, effect, covered, produced, inclusion, global⟩

end MicroCFTA.SourceCurrentMemoTargetOperand
