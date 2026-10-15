import MicroCFTA.SourceCurrentMemoSharedTargetState

/-!
# First force and reuse of memo-aware shared targets

A hit returns its stored physical value without a request. A miss runs the
actual new target graph and stores its native state and completed merge
table. Every older target slot and completed merge entry remains retained.
-/
namespace MicroCFTA.SourceCurrentMemoSharedTargetForce
open Cache Language InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open SourceEqualityRequiredCache SourceEqualityNativeScoped SourceEqualityProjectionPathDomain SourceEqualityClassTarget
open SourceCurrentMemoMergeGraph (Memo)
open SourceCurrentMemoMergeEffects (Stored)
open SourceCurrentMemoMergeLanguage (CacheCovers)
open SourceCurrentMemoMergeOrigins (Produced)
open SourceCurrentMemoDemandTarget SourceCurrentMemoSharedTargetState
local notation "Native" => SourceRecursiveIntersectionThunks.State
local notation "Heap" => InternedConstructorTemplates.State
local notation "CostHeap" => InternedFreshOrdinaryCostHeap.Heap

def Retains (before after : State width Symbol Guard) : Prop :=
  ∀ path value, before.targets path = some value → after.targets path = some value

theorem Retains.trans {before middle after : State width Symbol Guard}
    (first : Retains before middle) (later : Retains middle after) : Retains before after :=
  fun path value found => later path value (first path value found)

inductive Force [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (emptyGuard : Guard) (conjoin : Guard → Guard → Guard) (clear : Guard → Bool) (top : Guard)
    (record : SourceEqualityClassOrder.Record) (values : List (Value Symbol Guard)) (path : EqualityNormalize.Path) :
    State width Symbol Guard → Value Symbol Guard → State width Symbol Guard → Prop where
  | hit (present : before.targets path = some value) :
      Force emptyGuard conjoin clear top record values path before value before
  | miss (absent : before.targets path = none)
      (actual : Target emptyGuard conjoin clear top values (operandPaths record.paths path) before.native before.memo value native saved) :
      Force emptyGuard conjoin clear top record values path before value (store before path value native saved)

theorem Force.effects [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {emptyGuard : Guard} {conjoin : Guard → Guard → Guard} {clear : Guard → Bool} {top : Guard}
    {record : SourceEqualityClassOrder.Record} {values : List (Value Symbol Guard)} {base : Heap Symbol Guard}
    {path : EqualityNormalize.Path} {value : Value Symbol Guard} {before after : State width Symbol Guard}
    (trace : Force emptyGuard conjoin clear top record values path before value after)
    (ready : Ready emptyGuard conjoin clear top record values base before) (known : Values base values)
    (domains : ∀ path ∈ record.paths, ForestClosed (path.map Int.ofNat) values) (member : path ∈ record.paths) :
    Ready emptyGuard conjoin clear top record values base after ∧ Keeps before.native.machine.heap after.native.machine.heap ∧
      Available after.native.machine.heap value ∧ value.free = [] ∧ after.targets path = some value ∧ Retains before after := by
  cases trace with
  | hit present =>
      have checked := (ready.receipts path value present).available
      exact ⟨ready, pure_keeps _ ready.native.semantic.ready, checked.1, checked.2, present, fun _ _ stored => stored⟩
  | miss absent actual =>
      have available : Values before.native.machine.heap values := fun value member => ready.captured.available value (known value member)
      have checked := actual.effects ready.native ready.costs ready.stored available
        (SourceCurrentTargetPathComplete.operand_domains record values domains path)
      refine ⟨ready.store known domains path member value _ _ actual, checked.keeps, checked.available, checked.closed, ?_, ?_⟩
      · simp only [store, put, ite_true]
      · intro other target present
        by_cases same : other = path
        · subst other; rw [absent] at present; cases present
        · simpa only [store, put, same, ite_false] using present

private theorem operand_extends [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {clear : Guard → Bool} {top : Guard} {path : List Int} {values : List (Value Symbol Guard)} {value : Value Symbol Guard}
    {before after : Native width Symbol Guard} {memo saved : Memo Symbol Guard}
    (actual : SourceCurrentMemoTargetOperand.Operand clear top path values before memo value after saved) : Extends memo saved := by
  cases actual with
  | force _ merged => cases merged with | done call => exact call.extends

private theorem fold_extends [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {emptyGuard : Guard} {conjoin : Guard → Guard → Guard} {clear : Guard → Bool} {top : Guard}
    {values : List (Value Symbol Guard)} {seed : List Int} {paths : List (List Int)} {value : Value Symbol Guard}
    {before after : Native width Symbol Guard} {memo saved : Memo Symbol Guard}
    (actual : Fold emptyGuard conjoin clear top values seed paths before memo value after saved) : Extends memo saved := by
  induction actual with
  | nil operand => exact operand_extends operand
  | cons operand _ _ ih => exact extends_trans (operand_extends operand) ih

private theorem target_extends [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {emptyGuard : Guard} {conjoin : Guard → Guard → Guard} {clear : Guard → Bool} {top : Guard}
    {values : List (Value Symbol Guard)} {paths : List (List Int)} {value : Value Symbol Guard}
    {before after : Native width Symbol Guard} {memo saved : Memo Symbol Guard}
    (actual : Target emptyGuard conjoin clear top values paths before memo value after saved) : Extends memo saved := by
  cases actual with
  | nil => exact extends_refl _
  | cons fold => exact fold_extends fold

theorem Force.extends [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {emptyGuard : Guard} {conjoin : Guard → Guard → Guard} {clear : Guard → Bool} {top : Guard}
    {record : SourceEqualityClassOrder.Record} {values : List (Value Symbol Guard)}
    {path : EqualityNormalize.Path} {value : Value Symbol Guard} {before after : State width Symbol Guard}
    (trace : Force emptyGuard conjoin clear top record values path before value after) : Extends before.memo after.memo := by
  cases trace with
  | hit => exact extends_refl _
  | miss _ actual => exact target_extends actual

theorem Force.covered [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {emptyGuard : Guard} {conjoin : Guard → Guard → Guard} {clear : Guard → Bool} {top : Guard}
    {record : SourceEqualityClassOrder.Record} {values : List (Value Symbol Guard)} {base : Heap Symbol Guard}
    {path : EqualityNormalize.Path} {value : Value Symbol Guard} {before after : State width Symbol Guard}
    (trace : Force emptyGuard conjoin clear top record values path before value after)
    (ready : Ready emptyGuard conjoin clear top record values base before) (known : Values base values)
    (domains : ∀ path ∈ record.paths, ForestClosed (path.map Int.ofNat) values) (_member : path ∈ record.paths)
    (holds : Guard → Term Symbol → Bool) (ambient : InternedGuardedLanguage.Env Symbol) (covered : CacheCovers holds ambient before.memo)
    (clearTrue : ∀ guard, clear guard = true → ∀ term, holds guard term = true) (topTrue : ∀ term, holds top term = true)
    (conjoined : ∀ first second term, holds (conjoin first second) term = (holds first term && holds second term)) :
    CacheCovers holds ambient after.memo := by
  cases trace with
  | hit => exact covered
  | miss _ actual =>
      exact (actual.included ready.native ready.costs ready.stored holds ambient covered
        (fun value member => ready.captured.available value (known value member))
        (SourceCurrentTargetPathComplete.operand_domains record values domains path) clearTrue topTrue conjoined).1

theorem Force.produced [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {emptyGuard : Guard} {conjoin : Guard → Guard → Guard} {clear : Guard → Bool} {top : Guard}
    {record : SourceEqualityClassOrder.Record} {values : List (Value Symbol Guard)}
    {path : EqualityNormalize.Path} {value : Value Symbol Guard} {before after : State width Symbol Guard}
    (trace : Force emptyGuard conjoin clear top record values path before value after) :
    Produced clear top before.memo → Produced clear top after.memo := by
  cases trace with
  | hit => exact id
  | miss _ actual => exact actual.produced

theorem advance_retains (before : State width Symbol Guard) (native : Native width Symbol Guard) :
    Retains before (advance before native) := fun _ _ present => present

def ForceRanges [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (emptyGuard : Guard) (conjoin : Guard → Guard → Guard) (clear : Guard → Bool) (top : Guard)
    (record : SourceEqualityClassOrder.Record) (values : List (Value Symbol Guard)) (path : EqualityNormalize.Path)
    (before : State width Symbol Guard) : Prop :=
  match before.targets path with
  | some _ => True
  | none => TargetRanges emptyGuard conjoin clear top values (operandPaths record.paths path) before.native before.memo

private theorem operand_complete [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (emptyGuard : Guard) (conjoin : Guard → Guard → Guard) (clear : Guard → Bool) (top : Guard)
    (path : List Int) (values : List (Value Symbol Guard)) (before : Native width Symbol Guard) (memo : Memo Symbol Guard)
    (ready : IdleReady emptyGuard conjoin before) (costs : CostHeap before.machine.heap) (stored : Stored before.machine.heap memo)
    (available : Values before.machine.heap values) (domain : ForestClosed path values) :
    ∃ value after saved, SourceCurrentMemoTargetOperand.Operand clear top path values before memo value after saved ∧
      SourceCurrentMemoTargetOperand.Effects emptyGuard conjoin before memo value after saved := by
  obtain ⟨projected, heap, projection, checked⟩ := SourceEqualityProjectionPathComplete.forest_complete
    path values before.machine.heap ready.semantic available domain
  have physical := SourceEqualityProjectionCosts.forest_effects projection ready.semantic costs available
  obtain ⟨value, final, saved, call, _⟩ := SourceCurrentMemoMergeCompletion.call_complete clear top projected heap memo
    checked.2.1 physical.2.2.1 (stored.grows checked.1) checked.2.2.1
  have merged : SourceCurrentMemoMergeNative.Merge clear top projected (SourceEqualityNativeScoped.advanceHeap before heap) memo
      value (SourceEqualityNativeScoped.advanceHeap (SourceEqualityNativeScoped.advanceHeap before heap) final) saved := .done call
  have trace : SourceCurrentMemoTargetOperand.Operand clear top path values before memo value _ saved := .force projection merged
  exact ⟨value, _, saved, trace, trace.effects ready costs stored available domain⟩

private theorem fold_complete [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (emptyGuard : Guard) (conjoin : Guard → Guard → Guard) (clear : Guard → Bool) (top : Guard)
    (values : List (Value Symbol Guard)) (seed : List Int) (paths : List (List Int)) (before : Native width Symbol Guard) (memo : Memo Symbol Guard)
    (ready : IdleReady emptyGuard conjoin before) (costs : CostHeap before.machine.heap) (stored : Stored before.machine.heap memo)
    (ranges : FoldRanges emptyGuard conjoin clear top values seed paths before memo)
    (available : Values before.machine.heap values) (domains : ∀ path ∈ seed :: paths, ForestClosed path values) :
    ∃ value after saved, Fold emptyGuard conjoin clear top values seed paths before memo value after saved ∧
      SourceCurrentMemoDemandTarget.Effects emptyGuard conjoin before memo value after saved := by
  induction paths generalizing before memo with
  | nil =>
      obtain ⟨value, after, saved, operand, _⟩ := operand_complete emptyGuard conjoin clear top seed values before memo ready costs stored available
        (domains _ List.mem_cons_self)
      exact ⟨value, after, saved, .nil operand, (Fold.nil operand).effects ready costs stored available domains⟩
  | cons path paths ih =>
      cases ranges with
      | cons restPlan stepPlan =>
          obtain ⟨value, middle, current, operand, first⟩ := operand_complete emptyGuard conjoin clear top path values before memo ready costs stored
            available (domains _ (by simp))
          have tailDomains : ∀ own ∈ seed :: paths, ForestClosed own values := by
            intro own member
            rcases List.mem_cons.mp member with rfl | member
            · exact domains _ List.mem_cons_self
            · exact domains own (by simp only [List.mem_cons]; exact Or.inr (Or.inr member))
          obtain ⟨tail, later, saved, rest, remaining⟩ := ih middle current first.ready first.costs first.stored
            (restPlan value middle current operand) (fun value member => first.keeps.available value (available value member)) tailDomains
          obtain ⟨result, after, step, _⟩ := SourceEqualityNativeScoped.complete emptyGuard conjoin later remaining.ready value tail
            (remaining.keeps.available value first.available) remaining.available first.closed remaining.closed
            (stepPlan value middle current operand tail later saved rest) (fun _ _ => true) (fun _ _ _ => rfl)
          have trace : Fold emptyGuard conjoin clear top values seed (path :: paths) before memo result after saved := .cons operand rest step
          exact ⟨result, after, saved, trace, trace.effects ready costs stored available domains⟩

/-- Physical first-force completion needs no supplied language property of warm cache entries. -/
theorem complete [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (emptyGuard : Guard) (conjoin : Guard → Guard → Guard) (clear : Guard → Bool) (top : Guard)
    (record : SourceEqualityClassOrder.Record) (values : List (Value Symbol Guard)) (base : Heap Symbol Guard) (known : Values base values)
    (domains : ∀ path ∈ record.paths, ForestClosed (path.map Int.ofNat) values) (path : EqualityNormalize.Path) (member : path ∈ record.paths)
    (before : State width Symbol Guard) (ready : Ready emptyGuard conjoin clear top record values base before)
    (ranges : ForceRanges emptyGuard conjoin clear top record values path before) :
    ∃ value after, Force emptyGuard conjoin clear top record values path before value after ∧
      Ready emptyGuard conjoin clear top record values base after ∧ Keeps before.native.machine.heap after.native.machine.heap ∧
      Available after.native.machine.heap value ∧ value.free = [] ∧ after.targets path = some value ∧ Retains before after := by
  cases present : before.targets path with
  | some value =>
      have trace : Force emptyGuard conjoin clear top record values path before value before := .hit present
      exact ⟨value, before, trace, trace.effects ready known domains member⟩
  | none =>
      have actualRanges := ranges
      simp only [ForceRanges, present] at actualRanges
      have available : Values before.native.machine.heap values := fun value member => ready.captured.available value (known value member)
      have selectedDomains := SourceCurrentTargetPathComplete.operand_domains record values domains path
      have completed : ∃ value native saved, Target emptyGuard conjoin clear top values (operandPaths record.paths path)
          before.native before.memo value native saved := by
        cases paths : operandPaths record.paths path with
        | nil => exact ⟨.empty, before.native, before.memo, by simpa only [paths] using
            (Target.nil : Target emptyGuard conjoin clear top values [] before.native before.memo .empty before.native before.memo)⟩
        | cons seed rest =>
            obtain ⟨value, native, saved, fold, _⟩ := fold_complete emptyGuard conjoin clear top values seed rest before.native before.memo
              ready.native ready.costs ready.stored (by simpa only [TargetRanges, paths] using actualRanges) available
              (by simpa only [paths] using selectedDomains)
            exact ⟨value, native, saved, by simpa only [paths] using Target.cons fold⟩
      obtain ⟨value, native, saved, actual⟩ := completed
      have trace : Force emptyGuard conjoin clear top record values path before value (store before path value native saved) := .miss present actual
      exact ⟨value, _, trace, trace.effects ready known domains member⟩

end MicroCFTA.SourceCurrentMemoSharedTargetForce

namespace MicroCFTA.SourceCurrentMemoSharedTargetForce
open Cache Language InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open SourceEqualityRequiredCache SourceEqualityNativeScoped SourceEqualityProjectionPathDomain SourceEqualityClassTarget
open SourceCurrentMemoDemandTarget SourceCurrentMemoSharedTargetState
open SourceCurrentMemoMergeLanguage (CacheCovers)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Heap" => InternedConstructorTemplates.State
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Valid" => EndpointMemoGateTrace.Valid
local notation "GlobalEffect" => SourceCurrentSubsumesQueryMemos.Effect

/-- Hits add no reads; misses retain the exact new target's ordered receipts. -/
inductive Reads [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] :
    {emptyGuard : Guard} → {conjoin : Guard → Guard → Guard} → {clear : Guard → Bool} → {top : Guard} →
    {record : SourceEqualityClassOrder.Record} → {values : List (Value Symbol Guard)} → {path : EqualityNormalize.Path} →
    {value : Value Symbol Guard} → {before after : State width Symbol Guard} →
    Force emptyGuard conjoin clear top record values path before value after → Memos → Memos → Prop where
  | hit {before : State width Symbol Guard} (present : before.targets path = some value) : Reads (.hit present) memos memos
  | miss {emptyGuard : Guard} {conjoin : Guard → Guard → Guard} {clear : Guard → Bool} {top : Guard}
      {record : SourceEqualityClassOrder.Record} {values : List (Value Symbol Guard)} {path : EqualityNormalize.Path}
      {before : State width Symbol Guard} {value : Value Symbol Guard} {native : SourceRecursiveIntersectionThunks.State width Symbol Guard}
      {saved : SourceCurrentMemoMergeGraph.Memo Symbol Guard} {memos final : Memos}
      (absent : before.targets path = none)
      {actual : Target emptyGuard conjoin clear top values (operandPaths record.paths path) before.native before.memo value native saved}
      (receipt : TargetReads actual memos final) : Reads (.miss absent actual) memos final

theorem Reads.query [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {emptyGuard : Guard} {conjoin : Guard → Guard → Guard} {clear : Guard → Bool} {top : Guard}
    {record : SourceEqualityClassOrder.Record} {values : List (Value Symbol Guard)} {path : EqualityNormalize.Path} {value : Value Symbol Guard}
    {before after : State width Symbol Guard} {memos final : Memos}
    {trace : Force emptyGuard conjoin clear top record values path before value after} (receipt : Reads trace memos final) :
    final.query = memos.query := by
  cases receipt with
  | hit => rfl
  | miss _ actual => exact actual.query

/-- Both force branches derive coherent global tables at their actual returned state. -/
theorem Force.memos [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {emptyGuard : Guard} {conjoin : Guard → Guard → Guard} {clear : Guard → Bool} {top : Guard}
    {record : SourceEqualityClassOrder.Record} {values : List (Value Symbol Guard)} {base : Heap Symbol Guard}
    {path : EqualityNormalize.Path} {value : Value Symbol Guard} {before after : State width Symbol Guard}
    (trace : Force emptyGuard conjoin clear top record values path before value after)
    (ready : Ready emptyGuard conjoin clear top record values base before) (known : Values base values)
    (domains : ∀ path ∈ record.paths, ForestClosed (path.map Int.ofNat) values) (_member : path ∈ record.paths)
    (memos : Memos) (valid : Valid before.native.machine.heap memos) :
    ∃ final, Reads trace memos final ∧ GlobalEffect before.native.machine.heap after.native.machine.heap memos final := by
  cases trace with
  | hit present =>
      exact ⟨memos, .hit present, pure_keeps _ ready.native.semantic.ready, ready.native.semantic, ready.costs, valid, extends_refl _, rfl⟩
  | miss absent actual =>
      obtain ⟨final, receipt, effect⟩ := actual.memos ready.native ready.costs ready.stored
        (fun value member => ready.captured.available value (known value member))
        (SourceCurrentTargetPathComplete.operand_domains record values domains path) memos valid
      exact ⟨final, .miss absent receipt, effect⟩

local notation "clear" => SourceMemoGate.plain
local notation "top" => SourceEqualityConstraintConstructors.top (Formula := FullSyntax.Formula)

/-- Finite source forcing derives the same physical state, warm cache coverage, and actual global reads. -/
theorem source_complete [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (emptyGuard : Guard) (conjoin : Guard → Guard → Guard) (record : SourceEqualityClassOrder.Record)
    (values : List (Value Symbol Guard)) (base : Heap Symbol Guard) (known : Values base values)
    (domains : ∀ path ∈ record.paths, ForestClosed (path.map Int.ofNat) values) (path : EqualityNormalize.Path) (member : path ∈ record.paths)
    (before : State width Symbol Guard) (ready : Ready emptyGuard conjoin clear top record values base before)
    (ranges : ForceRanges emptyGuard conjoin clear top record values path before)
    (holds : Guard → Term Symbol → Bool) (ambient : InternedGuardedLanguage.Env Symbol) (covered : CacheCovers holds ambient before.memo)
    (clearTrue : ∀ guard, clear guard = true → ∀ term, holds guard term = true) (topTrue : ∀ term, holds top term = true)
    (conjoined : ∀ first second term, holds (conjoin first second) term = (holds first term && holds second term))
    (memos : Memos) (valid : Valid before.native.machine.heap memos) :
    ∃ value after final, ∃ trace : Force emptyGuard conjoin clear top record values path before value after,
      Reads trace memos final ∧ Ready emptyGuard conjoin clear top record values base after ∧
      Keeps before.native.machine.heap after.native.machine.heap ∧ Available after.native.machine.heap value ∧ value.free = [] ∧
      after.targets path = some value ∧ Retains before after ∧ CacheCovers holds ambient after.memo ∧
      GlobalEffect before.native.machine.heap after.native.machine.heap memos final := by
  obtain ⟨value, after, trace, afterReady, keeps, available, closed, present, retained⟩ := complete
    emptyGuard conjoin clear top record values base known domains path member before ready ranges
  obtain ⟨final, receipt, effect⟩ := trace.memos ready known domains member memos valid
  exact ⟨value, after, final, trace, receipt, afterReady, keeps, available, closed, present, retained,
    trace.covered ready known domains member holds ambient covered clearTrue topTrue conjoined, effect⟩

end MicroCFTA.SourceCurrentMemoSharedTargetForce
