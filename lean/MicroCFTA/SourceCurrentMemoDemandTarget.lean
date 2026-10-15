import MicroCFTA.SourceCurrentMemoTargetOperand
import MicroCFTA.SourceEqualityNativeScopedCosts
import MicroCFTA.SourceNativeGlobalMemos

/-!
# First-seeded target folds with a completed merge table

Each recursive fold demands its left operand, completes its tail, and then
intersects the two returned values. Operand calls thread the completed merge
table. Native intersection retains that table and advances its physical heap.
Only the original selected path domains must be closed.
-/
namespace MicroCFTA.SourceCurrentMemoDemandTarget
open Cache Language InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open InternedGuardedLanguage (meaning)
open SourceEqualityRequiredCache SourceEqualityNativeScoped SourceEqualityProjectionPathDomain SourceCurrentMemoMergeGraph
open SourceCurrentMemoMergeEffects (Stored)
open SourceCurrentMemoMergeLanguage (CacheCovers)
open SourceCurrentMemoMergeOrigins (Produced)
open SourceCurrentMemoTargetOperand (Operand)
local notation "Native" => SourceRecursiveIntersectionThunks.State
local notation "CostHeap" => InternedFreshOrdinaryCostHeap.Heap

/-- Source order demands the left operand before the tail and its native intersection. -/
inductive Fold [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (emptyGuard : Guard) (conjoin : Guard → Guard → Guard) (clear : Guard → Bool) (top : Guard)
    (values : List (Value Symbol Guard)) (seed : List Int) :
    List (List Int) → Native width Symbol Guard → Memo Symbol Guard → Value Symbol Guard →
      Native width Symbol Guard → Memo Symbol Guard → Prop where
  | nil (operand : Operand clear top seed values before memo result after saved) :
      Fold emptyGuard conjoin clear top values seed [] before memo result after saved
  | cons (operand : Operand clear top path values before memo value middle current)
      (rest : Fold emptyGuard conjoin clear top values seed paths middle current tail later saved)
      (step : Step emptyGuard conjoin value tail later result after) :
      Fold emptyGuard conjoin clear top values seed (path :: paths) before memo result after saved

/-- The first path is the deferred seed; the empty list returns EmptyNode directly. -/
inductive Target [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (emptyGuard : Guard) (conjoin : Guard → Guard → Guard) (clear : Guard → Bool) (top : Guard)
    (values : List (Value Symbol Guard)) : List (List Int) → Native width Symbol Guard → Memo Symbol Guard →
      Value Symbol Guard → Native width Symbol Guard → Memo Symbol Guard → Prop where
  | nil : Target emptyGuard conjoin clear top values [] state memo .empty state memo
  | cons (fold : Fold emptyGuard conjoin clear top values seed paths before memo result after saved) :
      Target emptyGuard conjoin clear top values (seed :: paths) before memo result after saved

/-- Returned native state remains ready and retains the actual completed merge entries. -/
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
  retained : Extends memo saved

/-- A target retains every original subterm selected at all its operand paths. -/
def CommonCovers (holds : Guard → Term Symbol → Bool) (ambient : InternedGuardedLanguage.Env Symbol)
    (paths : List (List Int)) (values : List (Value Symbol Guard)) (result : Value Symbol Guard) : Prop :=
  ∀ symbol terms part, All₂ (meaning holds ambient) values terms →
    (∀ path ∈ paths, SymbolicSignedPaths.lookup (.node symbol terms) path = some part) → meaning holds ambient result part

private theorem tail_all {A : Type} {seed first : A} {rest : List A} {property : A → Prop}
    (all : ∀ value ∈ seed :: first :: rest, property value) : ∀ value ∈ seed :: rest, property value := by
  intro value member
  rcases List.mem_cons.mp member with rfl | member
  · exact all _ List.mem_cons_self
  · exact all value (by simp only [List.mem_cons]; exact Or.inr (Or.inr member))

/-- Each actual fold derives Stored at every native intersection's returned heap. -/
theorem Fold.effects [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {emptyGuard : Guard} {conjoin : Guard → Guard → Guard} {clear : Guard → Bool} {top : Guard}
    {values : List (Value Symbol Guard)} {seed : List Int} {paths : List (List Int)} {result : Value Symbol Guard}
    {before after : Native width Symbol Guard} {memo saved : Memo Symbol Guard}
    (trace : Fold emptyGuard conjoin clear top values seed paths before memo result after saved)
    (ready : IdleReady emptyGuard conjoin before) (costs : CostHeap before.machine.heap) (stored : Stored before.machine.heap memo)
    (available : Values before.machine.heap values) (domains : ∀ path ∈ seed :: paths, ForestClosed path values) :
    Effects emptyGuard conjoin before memo result after saved := by
  induction trace with
  | nil operand =>
      have checked := operand.effects ready costs stored available (domains _ List.mem_cons_self)
      exact ⟨checked.ready, checked.keeps, checked.costs, checked.stored, checked.available, checked.closed, checked.retained⟩
  | cons operand rest step ih =>
      have first := operand.effects ready costs stored available (domains _ (by simp))
      have remaining := ih first.ready first.costs first.stored
        (fun value member => first.keeps.available value (available value member)) (tail_all domains)
      have own := remaining.keeps.available _ first.available
      have checked := step.verified remaining.ready own remaining.available first.closed remaining.closed
        (fun _ _ => true) (fun _ _ _ => rfl)
      exact ⟨checked.1, first.keeps.trans (remaining.keeps.trans checked.2.1),
        step.cost_heap remaining.ready remaining.costs own remaining.available,
        remaining.stored.grows checked.2.1, checked.2.2.1, checked.2.2.2.1,
        extends_trans first.retained remaining.retained⟩

theorem Target.effects [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {emptyGuard : Guard} {conjoin : Guard → Guard → Guard} {clear : Guard → Bool} {top : Guard}
    {values : List (Value Symbol Guard)} {paths : List (List Int)} {result : Value Symbol Guard}
    {before after : Native width Symbol Guard} {memo saved : Memo Symbol Guard}
    (trace : Target emptyGuard conjoin clear top values paths before memo result after saved)
    (ready : IdleReady emptyGuard conjoin before) (costs : CostHeap before.machine.heap) (stored : Stored before.machine.heap memo)
    (available : Values before.machine.heap values) (domains : ∀ path ∈ paths, ForestClosed path values) :
    Effects emptyGuard conjoin before memo result after saved := by
  cases trace with
  | nil => exact ⟨ready, pure_keeps _ ready.semantic.ready, costs, stored, empty_available _, rfl, extends_refl _⟩
  | cons fold => exact fold.effects ready costs stored available domains

/-- Every actual source intersection retains the common selected original term. -/
theorem Fold.included [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {emptyGuard : Guard} {conjoin : Guard → Guard → Guard} {clear : Guard → Bool} {top : Guard}
    {values : List (Value Symbol Guard)} {seed : List Int} {paths : List (List Int)} {result : Value Symbol Guard}
    {before after : Native width Symbol Guard} {memo saved : Memo Symbol Guard}
    (trace : Fold emptyGuard conjoin clear top values seed paths before memo result after saved)
    (ready : IdleReady emptyGuard conjoin before) (costs : CostHeap before.machine.heap) (stored : Stored before.machine.heap memo)
    (holds : Guard → Term Symbol → Bool) (ambient : InternedGuardedLanguage.Env Symbol) (covered : CacheCovers holds ambient memo)
    (available : Values before.machine.heap values) (domains : ∀ path ∈ seed :: paths, ForestClosed path values)
    (clearTrue : ∀ guard, clear guard = true → ∀ term, holds guard term = true) (topTrue : ∀ term, holds top term = true)
    (conjoined : ∀ first second term, holds (conjoin first second) term = (holds first term && holds second term)) :
    CacheCovers holds ambient saved ∧ ((∀ path ∈ seed :: paths, path ≠ []) → CommonCovers holds ambient (seed :: paths) values result) := by
  induction trace with
  | nil operand =>
      obtain ⟨retained, inclusion⟩ := operand.included ready costs stored holds ambient covered available (domains _ List.mem_cons_self) clearTrue topTrue
      refine ⟨retained, ?_⟩
      intro proper symbol terms part accepted selected
      exact inclusion (proper _ List.mem_cons_self) symbol terms part accepted (selected _ List.mem_cons_self)
  | cons operand rest step ih =>
      have first := operand.effects ready costs stored available (domains _ (by simp))
      obtain ⟨firstCovered, firstIncluded⟩ := operand.included ready costs stored holds ambient covered available (domains _ (by simp)) clearTrue topTrue
      have inputs : Values _ values := fun value member => first.keeps.available value (available value member)
      obtain ⟨finalCovered, tailIncluded⟩ := ih first.ready first.costs first.stored firstCovered inputs (tail_all domains)
      have remaining := rest.effects first.ready first.costs first.stored inputs (tail_all domains)
      have checked := step.verified remaining.ready (remaining.keeps.available _ first.available) remaining.available
        first.closed remaining.closed holds conjoined
      refine ⟨finalCovered, ?_⟩
      intro proper symbol terms part accepted selected
      have tailAccepted := tailIncluded (tail_all proper) symbol terms part accepted (tail_all selected)
      have ownAccepted := firstIncluded (proper _ (by simp)) symbol terms part accepted (selected _ (by simp))
      exact (checked.2.2.2.2 ambient part).mpr ⟨tailAccepted, ownAccepted⟩

theorem Target.included [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {emptyGuard : Guard} {conjoin : Guard → Guard → Guard} {clear : Guard → Bool} {top : Guard}
    {values : List (Value Symbol Guard)} {paths : List (List Int)} {result : Value Symbol Guard}
    {before after : Native width Symbol Guard} {memo saved : Memo Symbol Guard}
    (trace : Target emptyGuard conjoin clear top values paths before memo result after saved)
    (ready : IdleReady emptyGuard conjoin before) (costs : CostHeap before.machine.heap) (stored : Stored before.machine.heap memo)
    (holds : Guard → Term Symbol → Bool) (ambient : InternedGuardedLanguage.Env Symbol) (covered : CacheCovers holds ambient memo)
    (available : Values before.machine.heap values) (domains : ∀ path ∈ paths, ForestClosed path values)
    (clearTrue : ∀ guard, clear guard = true → ∀ term, holds guard term = true) (topTrue : ∀ term, holds top term = true)
    (conjoined : ∀ first second term, holds (conjoin first second) term = (holds first term && holds second term)) :
    CacheCovers holds ambient saved ∧ (paths ≠ [] → (∀ path ∈ paths, path ≠ []) → CommonCovers holds ambient paths values result) := by
  cases trace with
  | nil => exact ⟨covered, fun nonempty => False.elim (nonempty rfl)⟩
  | cons fold =>
      obtain ⟨retained, inclusion⟩ := fold.included ready costs stored holds ambient covered available domains clearTrue topTrue conjoined
      exact ⟨retained, fun _ => inclusion⟩

/-- Native intersection retains the merge-result contents and their historical producers. -/
theorem Fold.produced [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {emptyGuard : Guard} {conjoin : Guard → Guard → Guard} {clear : Guard → Bool} {top : Guard}
    {values : List (Value Symbol Guard)} {seed : List Int} {paths : List (List Int)} {result : Value Symbol Guard}
    {before after : Native width Symbol Guard} {memo saved : Memo Symbol Guard}
    (trace : Fold emptyGuard conjoin clear top values seed paths before memo result after saved) :
    Produced clear top memo → Produced clear top saved := by
  induction trace with
  | nil operand => exact operand.produced
  | cons operand _ _ ih => exact fun produced => ih (operand.produced produced)

theorem Target.produced [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {emptyGuard : Guard} {conjoin : Guard → Guard → Guard} {clear : Guard → Bool} {top : Guard}
    {values : List (Value Symbol Guard)} {paths : List (List Int)} {result : Value Symbol Guard}
    {before after : Native width Symbol Guard} {memo saved : Memo Symbol Guard}
    (trace : Target emptyGuard conjoin clear top values paths before memo result after saved) :
    Produced clear top memo → Produced clear top saved := by
  cases trace with
  | nil => exact id
  | cons fold => exact fold.produced

/-- Word checks follow only actual operand and fold prefixes, with their reached result tables. -/
inductive FoldRanges [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (emptyGuard : Guard) (conjoin : Guard → Guard → Guard) (clear : Guard → Bool) (top : Guard)
    (values : List (Value Symbol Guard)) (seed : List Int) : List (List Int) → Native width Symbol Guard → Memo Symbol Guard → Prop where
  | nil : FoldRanges emptyGuard conjoin clear top values seed [] before memo
  | cons
      (rest : ∀ value middle current, Operand clear top path values before memo value middle current →
        FoldRanges emptyGuard conjoin clear top values seed paths middle current)
      (step : ∀ value middle current, Operand clear top path values before memo value middle current → ∀ tail later saved,
        Fold emptyGuard conjoin clear top values seed paths middle current tail later saved →
        SourceRecursiveIntersectionNative.WordRanges emptyGuard conjoin (.node ⟨IntersectionEmptyDomain.emptyDomain, value, tail⟩ .pure) later) :
      FoldRanges emptyGuard conjoin clear top values seed (path :: paths) before memo

def TargetRanges [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (emptyGuard : Guard) (conjoin : Guard → Guard → Guard) (clear : Guard → Bool) (top : Guard)
    (values : List (Value Symbol Guard)) (paths : List (List Int)) (before : Native width Symbol Guard) (memo : Memo Symbol Guard) : Prop :=
  match paths with
  | [] => True
  | seed :: rest => FoldRanges emptyGuard conjoin clear top values seed rest before memo

/-- Local operand progress and checked native requests derive the finite source right fold. -/
theorem fold_finite [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (emptyGuard : Guard) (conjoin : Guard → Guard → Guard) (clear : Guard → Bool) (top : Guard)
    (holds : Guard → Term Symbol → Bool) (ambient : InternedGuardedLanguage.Env Symbol)
    (clearTrue : ∀ guard, clear guard = true → ∀ term, holds guard term = true) (topTrue : ∀ term, holds top term = true)
    (values : List (Value Symbol Guard)) (seed : List Int) (paths : List (List Int)) (before : Native width Symbol Guard) (memo : Memo Symbol Guard)
    (ready : IdleReady emptyGuard conjoin before) (costs : CostHeap before.machine.heap) (stored : Stored before.machine.heap memo)
    (covered : CacheCovers holds ambient memo) (ranges : FoldRanges emptyGuard conjoin clear top values seed paths before memo)
    (available : Values before.machine.heap values) (domains : ∀ path ∈ seed :: paths, ForestClosed path values) :
    ∃ result after saved, Fold emptyGuard conjoin clear top values seed paths before memo result after saved ∧
      Effects emptyGuard conjoin before memo result after saved ∧ CacheCovers holds ambient saved := by
  induction paths generalizing before memo with
  | nil =>
      obtain ⟨result, after, saved, operand, checked, retained, _⟩ := SourceCurrentMemoTargetOperand.finite
        emptyGuard conjoin clear top holds ambient clearTrue topTrue seed values before memo ready costs stored covered available (domains _ List.mem_cons_self)
      exact ⟨result, after, saved, .nil operand,
        ⟨checked.ready, checked.keeps, checked.costs, checked.stored, checked.available, checked.closed, checked.retained⟩, retained⟩
  | cons path paths ih =>
      cases ranges with
      | cons restPlan stepPlan =>
          obtain ⟨value, middle, current, operand, first, firstCovered, _⟩ := SourceCurrentMemoTargetOperand.finite
            emptyGuard conjoin clear top holds ambient clearTrue topTrue path values before memo ready costs stored covered available (domains _ (by simp))
          obtain ⟨tail, later, saved, rest, remaining, retained⟩ := ih middle current first.ready first.costs first.stored firstCovered
            (restPlan value middle current operand) (fun value member => first.keeps.available value (available value member)) (tail_all domains)
          obtain ⟨result, after, step, _⟩ := SourceEqualityNativeScoped.complete emptyGuard conjoin later remaining.ready value tail
            (remaining.keeps.available value first.available) remaining.available first.closed remaining.closed
            (stepPlan value middle current operand tail later saved rest) (fun _ _ => true) (fun _ _ _ => rfl)
          have trace : Fold emptyGuard conjoin clear top values seed (path :: paths) before memo result after saved := .cons operand rest step
          exact ⟨result, after, saved, trace, trace.effects ready costs stored available domains, retained⟩

/-- Finite targets derive complete state effects and independent common-subterm coverage. -/
theorem finite [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (emptyGuard : Guard) (conjoin : Guard → Guard → Guard) (clear : Guard → Bool) (top : Guard)
    (holds : Guard → Term Symbol → Bool) (ambient : InternedGuardedLanguage.Env Symbol)
    (clearTrue : ∀ guard, clear guard = true → ∀ term, holds guard term = true) (topTrue : ∀ term, holds top term = true)
    (conjoined : ∀ first second term, holds (conjoin first second) term = (holds first term && holds second term))
    (values : List (Value Symbol Guard)) (paths : List (List Int)) (before : Native width Symbol Guard) (memo : Memo Symbol Guard)
    (ready : IdleReady emptyGuard conjoin before) (costs : CostHeap before.machine.heap) (stored : Stored before.machine.heap memo)
    (covered : CacheCovers holds ambient memo) (ranges : TargetRanges emptyGuard conjoin clear top values paths before memo)
    (available : Values before.machine.heap values) (domains : ∀ path ∈ paths, ForestClosed path values) :
    ∃ result after saved, Target emptyGuard conjoin clear top values paths before memo result after saved ∧
      Effects emptyGuard conjoin before memo result after saved ∧ CacheCovers holds ambient saved ∧
      (paths ≠ [] → (∀ path ∈ paths, path ≠ []) → CommonCovers holds ambient paths values result) := by
  have completed : ∃ result after saved, Target emptyGuard conjoin clear top values paths before memo result after saved := by
    cases paths with
    | nil => exact ⟨.empty, before, memo, .nil⟩
    | cons seed paths =>
        obtain ⟨result, after, saved, fold, _⟩ := fold_finite emptyGuard conjoin clear top holds ambient clearTrue topTrue values seed paths
          before memo ready costs stored covered ranges available domains
        exact ⟨result, after, saved, .cons fold⟩
  obtain ⟨result, after, saved, trace⟩ := completed
  exact ⟨result, after, saved, trace, trace.effects ready costs stored available domains,
    trace.included ready costs stored holds ambient covered available domains clearTrue topTrue conjoined⟩

private theorem operand_tables [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {clear : Guard → Bool} {top : Guard} {path : List Int} {values : List (Value Symbol Guard)} {result : Value Symbol Guard}
    {before after : Native width Symbol Guard} {memo saved : Memo Symbol Guard}
    (trace : Operand clear top path values before memo result after saved) :
    after.nodes = before.nodes ∧ after.edges = before.edges ∧ after.machine.domains = before.machine.domains := by
  cases trace with
  | force _ merged => cases merged; exact ⟨rfl, rfl, rfl⟩

/-- A singleton target issues no native intersection and retains both native tables and domains exactly. -/
theorem Target.singleton_tables [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {emptyGuard : Guard} {conjoin : Guard → Guard → Guard} {clear : Guard → Bool} {top : Guard}
    {values : List (Value Symbol Guard)} {path : List Int} {result : Value Symbol Guard}
    {before after : Native width Symbol Guard} {memo saved : Memo Symbol Guard}
    (trace : Target emptyGuard conjoin clear top values [path] before memo result after saved) :
    after.nodes = before.nodes ∧ after.edges = before.edges ∧ after.machine.domains = before.machine.domains := by
  cases trace with
  | cons fold => cases fold with | nil operand => exact operand_tables operand

/-- An empty target retains the full native state and result table without operand work. -/
theorem Target.empty_unchanged [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {emptyGuard : Guard} {conjoin : Guard → Guard → Guard} {clear : Guard → Bool} {top : Guard}
    {values : List (Value Symbol Guard)} {result : Value Symbol Guard}
    {before after : Native width Symbol Guard} {memo saved : Memo Symbol Guard}
    (trace : Target emptyGuard conjoin clear top values [] before memo result after saved) :
    after = before ∧ saved = memo ∧ result = .empty := by cases trace; exact ⟨rfl, rfl, rfl⟩

/-- Empty completed merge tables derive all entry obligations through the finite target. -/
theorem finite_cold [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (emptyGuard : Guard) (conjoin : Guard → Guard → Guard) (clear : Guard → Bool) (top : Guard)
    (holds : Guard → Term Symbol → Bool) (ambient : InternedGuardedLanguage.Env Symbol)
    (clearTrue : ∀ guard, clear guard = true → ∀ term, holds guard term = true) (topTrue : ∀ term, holds top term = true)
    (conjoined : ∀ first second term, holds (conjoin first second) term = (holds first term && holds second term))
    (values : List (Value Symbol Guard)) (paths : List (List Int)) (before : Native width Symbol Guard)
    (ready : IdleReady emptyGuard conjoin before) (costs : CostHeap before.machine.heap)
    (ranges : TargetRanges emptyGuard conjoin clear top values paths before empty)
    (available : Values before.machine.heap values) (domains : ∀ path ∈ paths, ForestClosed path values) :
    ∃ result after saved, Target emptyGuard conjoin clear top values paths before empty result after saved ∧
      Effects emptyGuard conjoin before empty result after saved ∧ CacheCovers holds ambient saved ∧ Produced clear top saved ∧
      (paths ≠ [] → (∀ path ∈ paths, path ≠ []) → CommonCovers holds ambient paths values result) := by
  obtain ⟨result, after, saved, trace, effect, covered, inclusion⟩ := finite emptyGuard conjoin clear top holds ambient clearTrue topTrue conjoined
    values paths before empty ready costs (SourceCurrentMemoMergeEffects.stored_empty _) (SourceCurrentMemoMergeLanguage.cache_covers_empty _ _)
      ranges available domains
  exact ⟨result, after, saved, trace, effect, covered, trace.produced (SourceCurrentMemoMergeOrigins.produced_empty _ _), inclusion⟩

end MicroCFTA.SourceCurrentMemoDemandTarget

namespace MicroCFTA.SourceCurrentMemoDemandTarget
open Cache Language InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open SourceEqualityRequiredCache SourceEqualityNativeScoped SourceEqualityProjectionPathDomain SourceCurrentMemoMergeGraph
open SourceCurrentMemoMergeEffects (Stored)
open SourceCurrentMemoMergeLanguage (CacheCovers)
open SourceCurrentMemoMergeOrigins (Produced)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Native" => SourceRecursiveIntersectionThunks.State
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Valid" => EndpointMemoGateTrace.Valid
local notation "CostHeap" => InternedFreshOrdinaryCostHeap.Heap
local notation "GlobalEffect" => SourceCurrentSubsumesQueryMemos.Effect

/-- A native intersection has its actual silent primitive trace and leaves the global tables unchanged. -/
def StepReads [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {emptyGuard : Guard} {conjoin : Guard → Guard → Guard}
    {target input result : Value Symbol Guard} {before after : Native width Symbol Guard}
    (_trace : Step emptyGuard conjoin target input before result after) (memos final : Memos) : Prop :=
  final = memos ∧ ∃ events, SourceGlobalUnfold.Runs ⟨before.machine.heap, memos.unfolding⟩
    ⟨after.machine.heap, memos.unfolding⟩ events ∧ SourceGlobalUnfold.NoGlobal events

/-- Actual fold receipts follow the left operand, recursive tail, and reached native request. -/
inductive FoldReads [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] :
    {emptyGuard : Guard} → {conjoin : Guard → Guard → Guard} → {clear : Guard → Bool} → {top : Guard} →
    {values : List (Value Symbol Guard)} → {seed : List Int} → {paths : List (List Int)} →
    {before : Native width Symbol Guard} → {memo : Memo Symbol Guard} → {result : Value Symbol Guard} →
    {after : Native width Symbol Guard} → {saved : Memo Symbol Guard} →
    Fold emptyGuard conjoin clear top values seed paths before memo result after saved → Memos → Memos → Prop where
  | nil (own : SourceCurrentMemoTargetOperand.Reads clear top seed values before memo result after saved memos final) :
      FoldReads (.nil operand) memos final
  | cons (own : SourceCurrentMemoTargetOperand.Reads clear top path values before memo value middle current memos first)
      (tail : FoldReads rest first later) (native : StepReads step later final) :
      FoldReads (.cons operand rest step) memos final

inductive TargetReads [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] :
    {emptyGuard : Guard} → {conjoin : Guard → Guard → Guard} → {clear : Guard → Bool} → {top : Guard} →
    {values : List (Value Symbol Guard)} → {paths : List (List Int)} → {before : Native width Symbol Guard} →
    {memo : Memo Symbol Guard} → {result : Value Symbol Guard} → {after : Native width Symbol Guard} → {saved : Memo Symbol Guard} →
    Target emptyGuard conjoin clear top values paths before memo result after saved → Memos → Memos → Prop where
  | nil : TargetReads .nil memos memos
  | cons (own : FoldReads fold memos final) : TargetReads (.cons fold) memos final

theorem FoldReads.query [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {emptyGuard : Guard} {conjoin : Guard → Guard → Guard} {clear : Guard → Bool} {top : Guard}
    {values : List (Value Symbol Guard)} {seed : List Int} {paths : List (List Int)} {result : Value Symbol Guard}
    {before after : Native width Symbol Guard} {memo saved : Memo Symbol Guard} {memos final : Memos}
    {trace : Fold emptyGuard conjoin clear top values seed paths before memo result after saved}
    (receipt : FoldReads trace memos final) : final.query = memos.query := by
  induction receipt with
  | nil own => exact own.query
  | cons own _ native ih => rw [native.1]; exact ih.trans own.query

theorem TargetReads.query [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {emptyGuard : Guard} {conjoin : Guard → Guard → Guard} {clear : Guard → Bool} {top : Guard}
    {values : List (Value Symbol Guard)} {paths : List (List Int)} {result : Value Symbol Guard}
    {before after : Native width Symbol Guard} {memo saved : Memo Symbol Guard} {memos final : Memos}
    {trace : Target emptyGuard conjoin clear top values paths before memo result after saved}
    (receipt : TargetReads trace memos final) : final.query = memos.query := by
  cases receipt with
  | nil => rfl
  | cons own => exact own.query

private theorem step_memos [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {emptyGuard : Guard} {conjoin : Guard → Guard → Guard}
    {target input result : Value Symbol Guard} {before after : Native width Symbol Guard}
    (trace : Step emptyGuard conjoin target input before result after) (ready : IdleReady emptyGuard conjoin before)
    (costs : CostHeap before.machine.heap) (targetAvailable : Available before.machine.heap target)
    (inputAvailable : Available before.machine.heap input) (targetClosed : target.free = []) (inputClosed : input.free = [])
    (memos : Memos) (valid : Valid before.machine.heap memos) :
    StepReads trace memos memos ∧ GlobalEffect before.machine.heap after.machine.heap memos memos := by
  obtain ⟨events, actual, silent, coherent⟩ := SourceNativeGlobalMemos.scoped_memos trace ready
    targetAvailable inputAvailable targetClosed inputClosed (fun _ _ => true) (fun _ _ _ => rfl) memos valid
  have checked := trace.verified ready targetAvailable inputAvailable targetClosed inputClosed (fun _ _ => true) (fun _ _ _ => rfl)
  exact ⟨⟨rfl, events, actual, silent⟩, checked.2.1, checked.1.semantic,
    trace.cost_heap ready costs targetAvailable inputAvailable, coherent, extends_refl _, rfl⟩

/-- The actual fold derives all three global receipts without future validity assumptions. -/
theorem Fold.memos [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {emptyGuard : Guard} {conjoin : Guard → Guard → Guard} {clear : Guard → Bool} {top : Guard}
    {values : List (Value Symbol Guard)} {seed : List Int} {paths : List (List Int)} {result : Value Symbol Guard}
    {before after : Native width Symbol Guard} {memo saved : Memo Symbol Guard}
    (trace : Fold emptyGuard conjoin clear top values seed paths before memo result after saved)
    (ready : IdleReady emptyGuard conjoin before) (costs : CostHeap before.machine.heap) (stored : Stored before.machine.heap memo)
    (available : Values before.machine.heap values) (domains : ∀ path ∈ seed :: paths, ForestClosed path values)
    (memos : Memos) (valid : Valid before.machine.heap memos) :
    ∃ final, FoldReads trace memos final ∧ GlobalEffect before.machine.heap after.machine.heap memos final := by
  induction trace generalizing memos with
  | nil operand =>
      obtain ⟨final, read, effect⟩ := operand.memos ready costs stored available (domains _ List.mem_cons_self) memos valid
      exact ⟨final, .nil (operand := operand) read, effect⟩
  | cons operand rest step ih =>
      have first := operand.effects ready costs stored available (domains _ (by simp))
      obtain ⟨middle, ownRead, ownEffect⟩ := operand.memos ready costs stored available (domains _ (by simp)) memos valid
      have inputs : Values _ values := fun value member => first.keeps.available value (available value member)
      have remaining := rest.effects first.ready first.costs first.stored inputs (tail_all domains)
      obtain ⟨later, tailRead, tailEffect⟩ := ih first.ready first.costs first.stored inputs (tail_all domains) middle ownEffect.valid
      have native := step_memos step remaining.ready tailEffect.costs (remaining.keeps.available _ first.available) remaining.available
        first.closed remaining.closed later tailEffect.valid
      exact ⟨later, .cons (operand := operand) ownRead tailRead native.1,
        SourceCurrentMemoMergeQueryMemos.effect_trans ownEffect (SourceCurrentMemoMergeQueryMemos.effect_trans tailEffect native.2)⟩

theorem Target.memos [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {emptyGuard : Guard} {conjoin : Guard → Guard → Guard} {clear : Guard → Bool} {top : Guard}
    {values : List (Value Symbol Guard)} {paths : List (List Int)} {result : Value Symbol Guard}
    {before after : Native width Symbol Guard} {memo saved : Memo Symbol Guard}
    (trace : Target emptyGuard conjoin clear top values paths before memo result after saved)
    (ready : IdleReady emptyGuard conjoin before) (costs : CostHeap before.machine.heap) (stored : Stored before.machine.heap memo)
    (available : Values before.machine.heap values) (domains : ∀ path ∈ paths, ForestClosed path values)
    (memos : Memos) (valid : Valid before.machine.heap memos) :
    ∃ final, TargetReads trace memos final ∧ GlobalEffect before.machine.heap after.machine.heap memos final := by
  cases trace with
  | nil => exact ⟨memos, .nil, pure_keeps _ ready.semantic.ready, ready.semantic, costs, valid, extends_refl _, rfl⟩
  | cons fold =>
      obtain ⟨final, read, effect⟩ := fold.memos ready costs stored available domains memos valid
      exact ⟨final, .cons read, effect⟩

local notation "clear" => SourceMemoGate.plain
local notation "top" => SourceEqualityConstraintConstructors.top (Formula := FullSyntax.Formula)

/-- Source targets complete at warm native and result tables with the same exact global receipts. -/
theorem source_finite [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (emptyGuard : Guard) (conjoin : Guard → Guard → Guard)
    (holds : Guard → Term Symbol → Bool) (ambient : InternedGuardedLanguage.Env Symbol)
    (clearTrue : ∀ guard, clear guard = true → ∀ term, holds guard term = true) (topTrue : ∀ term, holds top term = true)
    (conjoined : ∀ first second term, holds (conjoin first second) term = (holds first term && holds second term))
    (values : List (Value Symbol Guard)) (paths : List (List Int)) (before : Native width Symbol Guard) (memo : Memo Symbol Guard)
    (ready : IdleReady emptyGuard conjoin before) (costs : CostHeap before.machine.heap) (stored : Stored before.machine.heap memo)
    (covered : CacheCovers holds ambient memo) (ranges : TargetRanges emptyGuard conjoin clear top values paths before memo)
    (available : Values before.machine.heap values) (domains : ∀ path ∈ paths, ForestClosed path values)
    (memos : Memos) (valid : Valid before.machine.heap memos) :
    ∃ result after saved final, ∃ trace : Target emptyGuard conjoin clear top values paths before memo result after saved,
      TargetReads trace memos final ∧ Effects emptyGuard conjoin before memo result after saved ∧ CacheCovers holds ambient saved ∧
      (paths ≠ [] → (∀ path ∈ paths, path ≠ []) → CommonCovers holds ambient paths values result) ∧
      GlobalEffect before.machine.heap after.machine.heap memos final := by
  obtain ⟨result, after, saved, trace, effect, covered, inclusion⟩ := finite emptyGuard conjoin clear top holds ambient clearTrue topTrue conjoined
    values paths before memo ready costs stored covered ranges available domains
  obtain ⟨final, receipt, global⟩ := trace.memos ready costs stored available domains memos valid
  exact ⟨result, after, saved, final, trace, receipt, effect, covered, inclusion, global⟩

/-- Empty merge tables derive finite source targets, producer histories, and all global receipts. -/
theorem source_cold [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (emptyGuard : Guard) (conjoin : Guard → Guard → Guard)
    (holds : Guard → Term Symbol → Bool) (ambient : InternedGuardedLanguage.Env Symbol)
    (clearTrue : ∀ guard, clear guard = true → ∀ term, holds guard term = true) (topTrue : ∀ term, holds top term = true)
    (conjoined : ∀ first second term, holds (conjoin first second) term = (holds first term && holds second term))
    (values : List (Value Symbol Guard)) (paths : List (List Int)) (before : Native width Symbol Guard)
    (ready : IdleReady emptyGuard conjoin before) (costs : CostHeap before.machine.heap)
    (ranges : TargetRanges emptyGuard conjoin clear top values paths before empty)
    (available : Values before.machine.heap values) (domains : ∀ path ∈ paths, ForestClosed path values)
    (memos : Memos) (valid : Valid before.machine.heap memos) :
    ∃ result after saved final, ∃ trace : Target emptyGuard conjoin clear top values paths before empty result after saved,
      TargetReads trace memos final ∧ Effects emptyGuard conjoin before empty result after saved ∧ CacheCovers holds ambient saved ∧
      Produced clear top saved ∧ (paths ≠ [] → (∀ path ∈ paths, path ≠ []) → CommonCovers holds ambient paths values result) ∧
      GlobalEffect before.machine.heap after.machine.heap memos final := by
  obtain ⟨result, after, saved, trace, effect, covered, produced, inclusion⟩ := finite_cold emptyGuard conjoin clear top holds ambient clearTrue topTrue conjoined
    values paths before ready costs ranges available domains
  obtain ⟨final, receipt, global⟩ := trace.memos ready costs (SourceCurrentMemoMergeEffects.stored_empty _) available domains memos valid
  exact ⟨result, after, saved, final, trace, receipt, effect, covered, produced, inclusion, global⟩

end MicroCFTA.SourceCurrentMemoDemandTarget
