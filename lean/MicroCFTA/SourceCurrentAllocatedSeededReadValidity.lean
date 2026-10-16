import MicroCFTA.SourceCurrentAllocatedProjectionReadValidity
import MicroCFTA.SourceCurrentAllocatedSeededMemos

/-!
# Validity of supplied checked seeded-query reads

Projection, tail recursion, and native execution use their actual returned
states and tables. The native phase retains those same global memos.
Reached word checks and initial physical invariants remain explicit.
-/
namespace MicroCFTA.SourceCurrentAllocatedSeededReadValidity
open Cache InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open SourceEqualityRequiredCache SourceEqualityRequiredSemanticCache
open SourceCurrentAllocatedNativeEffects (physical)
open SourceCurrentAllocatedNativePhysicalCompletion (Good)
open SourceEqualityNativeDemand
open SourceCurrentConjunctionRowsAllocation (Ready Effects)
open SourceCurrentSecondaryProjectionScoped (PathSupport)
open SourceCurrentAllocatedSeededQuery (Operand Fold Seeded FoldRanges SeededRanges)
open SourceCurrentAllocatedSeededMemos (OperandReads FoldReads SeededReads)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Valid" => EndpointMemoGateTrace.Valid
local notation "GateReady" => InternedFreshOrdinaryMemoGateTrace.Ready
local notation "Scoped" => SourceCurrentAllocatedNativeScopeCache.Scoped
local notation "Idle" => SourceRecursiveIntersectionNative.Idle
variable [DecidableEq (EdgeKey Symbol Guard)] {width : Nat}

/-- A supplied operand projection derives validity of its own actual final tables. -/
theorem operand {path : List Int} {values : List (Value Symbol Guard)} {before after : Checked width}
    {result : Value Symbol Guard} {actual : Operand path values before result after} {memos final : Memos}
    (reads : OperandReads actual memos final) (ready : Ready (physical before))
    (available : Values before.native.machine.heap values) (valid : Valid before.native.machine.heap memos) :
    Valid after.native.machine.heap final ∧ Extends memos.unfolding final.unfolding ∧ final.query = memos.query := by
  cases reads with
  | force read => exact SourceCurrentAllocatedProjectionReadValidity.forest read ready.semantic ready.costs available valid

variable [DecidableEq Symbol]

private theorem fold_effects
    (unconstrained : Value Symbol Guard → Bool) (anchor : State Symbol Guard)
    (anchorSemantic : SemanticReady anchor) (anchorReady : GateReady anchor)
    {values : List (Value Symbol Guard)} {paths : List (List Int)} {before after : Checked width}
    {result : Value Symbol Guard} (actual : Fold values paths before result after)
    (ranges : FoldRanges values paths before) (good : Good before) (ready : Ready (physical before))
    (scopes : Scoped before.native) (idle : Idle before.native)
    (available : Values before.native.machine.heap values) (growth : Grows anchor before.native.machine.heap)
    (supported : ∀ path ∈ paths, PathSupport unconstrained anchor path values) :
    Good after ∧ Effects (physical before) (physical after) ∧
      SourceRecursiveIntersectionKernel.Extension before.native.machine after.native.machine ∧
      Scoped after.native ∧ Idle after.native ∧ Available after.native.machine.heap result ∧ result.free = [] := by
  obtain ⟨chosen, reached, complete, effects⟩ := SourceCurrentAllocatedSeededQuery.fold_complete
    unconstrained anchor anchorSemantic anchorReady values paths before ranges good ready scopes idle available growth supported
  obtain ⟨rfl, rfl⟩ := actual.unique complete
  exact effects

/-- Supplied fold reads retain their literal tables across the actual recursive native suffix. -/
theorem fold
    (unconstrained : Value Symbol Guard → Bool) (anchor : State Symbol Guard)
    (anchorSemantic : SemanticReady anchor) (anchorReady : GateReady anchor)
    {values : List (Value Symbol Guard)} {paths : List (List Int)} {before after : Checked width}
    {result : Value Symbol Guard} {actual : Fold values paths before result after} {memos final : Memos}
    (reads : FoldReads actual memos final)
    (ranges : FoldRanges values paths before) (good : Good before) (ready : Ready (physical before))
    (scopes : Scoped before.native) (idle : Idle before.native)
    (available : Values before.native.machine.heap values) (growth : Grows anchor before.native.machine.heap)
    (supported : ∀ path ∈ paths, PathSupport unconstrained anchor path values)
    (valid : Valid before.native.machine.heap memos) :
    Valid after.native.machine.heap final ∧ Extends memos.unfolding final.unfolding ∧ final.query = memos.query := by
  revert ranges good ready scopes idle available growth supported valid
  induction reads with
  | one read =>
      intro ranges good ready scopes idle available growth supported valid
      exact operand read ready available valid
  | @cons values path next paths before middle later after value tail result fuel actual remaining native
      memos middleMemos laterMemos saved first rest checked ih =>
      intro ranges good ready scopes idle available growth supported valid
      cases ranges with
      | cons restRanges nativeRanges =>
          have firstEffects := SourceCurrentAllocatedSeededOperandLanguage.Operand.effects
            unconstrained anchor anchorSemantic anchorReady actual good ready scopes idle available growth
              (supported path List.mem_cons_self)
          have firstValid := operand first ready available valid
          have middleValues : Values middle.native.machine.heap values :=
            fun value member => firstEffects.2.1.keeps.available value (available value member)
          have middleGrowth := grows_trans growth firstEffects.2.1.keeps.growth
          have tailSupport := fun path member => supported path (List.mem_cons_of_mem _ member)
          have tailValid := ih (restRanges value middle actual) firstEffects.1 firstEffects.2.1.ready
            firstEffects.2.2.2.1 firstEffects.2.2.2.2.1 middleValues middleGrowth tailSupport firstValid.1
          have tailEffects := fold_effects unconstrained anchor anchorSemantic anchorReady remaining
            (restRanges value middle actual) firstEffects.1 firstEffects.2.1.ready
            firstEffects.2.2.2.1 firstEffects.2.2.2.2.1 middleValues middleGrowth tailSupport
          cases checked with
          | silent events runs quiet =>
              obtain ⟨_, _, _, finalValid⟩ := SourceCurrentAllocatedNativeGlobalMemos.trace_memos native
                tailEffects.1 tailEffects.2.1.ready.semantic tailEffects.2.1.ready.costs
                (fun _ => trivial) laterMemos tailValid.1
              exact ⟨finalValid, extends_trans firstValid.2.1 tailValid.2.1,
                tailValid.2.2.trans firstValid.2.2⟩

/-- The supplied seeded read preserves its exact rotation and returned global bundle. -/
theorem seeded
    (unconstrained : Value Symbol Guard → Bool) (anchor : State Symbol Guard)
    (anchorSemantic : SemanticReady anchor) (anchorReady : GateReady anchor)
    {values : List (Value Symbol Guard)} {paths : List (List Int)} {before after : Checked width}
    {result : Value Symbol Guard} {actual : Seeded values paths before result after} {memos final : Memos}
    (reads : SeededReads actual memos final)
    (ranges : SeededRanges values paths before) (good : Good before) (ready : Ready (physical before))
    (scopes : Scoped before.native) (idle : Idle before.native)
    (available : Values before.native.machine.heap values) (growth : Grows anchor before.native.machine.heap)
    (supported : ∀ path ∈ paths, PathSupport unconstrained anchor path values)
    (valid : Valid before.native.machine.heap memos) :
    Valid after.native.machine.heap final ∧ Extends memos.unfolding final.unfolding ∧ final.query = memos.query := by
  cases reads with
  | nil => exact ⟨valid, extends_refl _, rfl⟩
  | nonempty read =>
      exact fold unconstrained anchor anchorSemantic anchorReady read ranges good ready scopes idle available growth
        (by
          intro path member
          exact supported path (by simpa [List.mem_append, List.mem_cons, or_comm] using member)) valid

end MicroCFTA.SourceCurrentAllocatedSeededReadValidity
