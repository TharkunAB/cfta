import MicroCFTA.SourceCurrentAllocatedSeededOperandLanguage
import MicroCFTA.SourceCurrentAllocatedNativeGlobalMemos
import MicroCFTA.SourceEqualityQueryGlobalMemos

/-!
# Global memo receipts through actual checked seeded folds

Projection records its literal global unfolding calls. The fold then visits
its tail and executes its actual checked native request. That native trace
derives real constructor effects with no global unfolding call. The first
source operand remains the final fold seed. All three global tables remain
coherent. These receipts do not describe GHC thunk publication or forcing.
-/
namespace MicroCFTA.SourceCurrentAllocatedSeededMemos
open Cache Language InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open SourceEqualityRequiredCache SourceEqualityRequiredSemanticCache
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceEqualityNativeDemand
open SourceCurrentAllocatedNativePhysicalCompletion (Good)
open SourceCurrentAllocatedNativePhysicalTraceCompletion (Trace)
open SourceCurrentAllocatedNativeEffects (physical)
open SourceCurrentConjunctionRowsAllocation (Ready Effects)
open SourceCurrentSecondaryProjectionScoped (PathSupport)
open SourceCurrentAllocatedSeededQuery (Operand Fold Seeded FoldRanges SeededRanges)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Valid" => EndpointMemoGateTrace.Valid
local notation "GateReady" => InternedFreshOrdinaryMemoGateTrace.Ready
local notation "Scoped" => SourceCurrentAllocatedNativeScopeCache.Scoped
local notation "Idle" => SourceRecursiveIntersectionNative.Idle
variable {width : Nat}

/-- An operand records the literal forest projection in its actual returned checked state. -/
inductive OperandReads [DecidableEq (EdgeKey Symbol Guard)] :
    {path : List Int} → {values : List (Value Symbol Guard)} → {before after : Checked width} →
    {result : Value Symbol Guard} → Operand path values before result after → Memos → Memos → Prop where
  | force {path : List Int} {values : List (Value Symbol Guard)} {before : Checked width}
      {result : Value Symbol Guard} {heap : State Symbol Guard}
      {projection : SourceEqualityProjectionGraph.Forest path values before.native.machine.heap result heap}
      {memos saved : Memos} (read : SourceEqualityQueryGlobalMemos.ProjectionReads projection memos saved) :
      OperandReads (.force result heap projection) memos saved

/-- A native phase records real primitive execution at the exact checked trace heaps. -/
inductive NativeReads [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] :
    {A : Type} → {fuel : Nat} → {control next : Control A} → {before after : Checked width} →
    Trace fuel control before next after → Memos → Memos → Prop where
  | silent {A : Type} {fuel : Nat} {control next : Control A} {before after : Checked width}
      {trace : Trace fuel control before next after} {memos : Memos}
      (events : List (SourceGlobalUnfold.Event Symbol Guard))
      (runs : SourceGlobalUnfold.Runs ⟨before.native.machine.heap, memos.unfolding⟩
        ⟨after.native.machine.heap, memos.unfolding⟩ events)
      (quiet : SourceGlobalUnfold.NoGlobal events) : NativeReads trace memos memos

/-- Fold receipts retain head projection, tail traversal, and native execution in order. -/
inductive FoldReads [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] :
    {values : List (Value Symbol Guard)} → {paths : List (List Int)} → {before after : Checked width} →
    {result : Value Symbol Guard} → Fold values paths before result after → Memos → Memos → Prop where
  | one {path : List Int} {values : List (Value Symbol Guard)} {before after : Checked width}
      {result : Value Symbol Guard} {operand : Operand path values before result after} {memos saved : Memos}
      (read : OperandReads operand memos saved) : FoldReads (.one operand) memos saved
  | cons {values : List (Value Symbol Guard)} {path next : List Int} {paths : List (List Int)}
      {before middle later after : Checked width} {value tail result : Value Symbol Guard} {fuel : Nat}
      {operand : Operand path values before value middle}
      {remaining : Fold values (next :: paths) middle tail later}
      {native : Trace fuel (.code (requestNode IntersectionEmptyDomain.emptyDomain value tail)) later
        (.code (.pure result)) after} {memos middleMemos laterMemos saved : Memos}
      (first : OperandReads operand memos middleMemos)
      (rest : FoldReads remaining middleMemos laterMemos) (checked : NativeReads native laterMemos saved) :
      FoldReads (.cons operand remaining native) memos saved

/-- Seeded receipts use the same literal rotation as the checked source graph. -/
inductive SeededReads [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] :
    {values : List (Value Symbol Guard)} → {paths : List (List Int)} → {before after : Checked width} →
    {result : Value Symbol Guard} → Seeded values paths before result after → Memos → Memos → Prop where
  | nil {values : List (Value Symbol Guard)} {before : Checked width} {memos : Memos} :
      SeededReads (values := values) (.nil before) memos memos
  | nonempty {values : List (Value Symbol Guard)} {seed : List Int} {rest : List (List Int)}
      {before after : Checked width} {result : Value Symbol Guard}
      {actual : Fold values (rest ++ [seed]) before result after} {memos saved : Memos}
      (read : FoldReads actual memos saved) : SeededReads (.nonempty actual) memos saved

/-- Actual checked operands derive all global memo receipts without closing unrelated siblings. -/
theorem operand_memos [DecidableEq (EdgeKey Symbol Guard)]
    {path : List Int} {values : List (Value Symbol Guard)} {before after : Checked width} {result : Value Symbol Guard}
    (actual : Operand path values before result after) (ready : Ready (physical before))
    (available : Values before.native.machine.heap values) (memos : Memos) (valid : Valid before.native.machine.heap memos) :
    ∃ saved, OperandReads actual memos saved ∧ Valid after.native.machine.heap saved ∧
      Extends memos.unfolding saved.unfolding ∧ saved.query = memos.query := by
  cases actual with
  | force heap projection =>
      obtain ⟨saved, read, coherent, retained⟩ := SourceEqualityQueryGlobalMemos.forest_memos
        projection ready.semantic ready.costs available memos valid
      exact ⟨saved, .force read, coherent, retained, read.2⟩

private theorem fold_effects [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (unconstrained : Value Symbol Guard → Bool) (anchor : State Symbol Guard)
    (anchorSemantic : SemanticReady anchor) (anchorReady : GateReady anchor)
    {values : List (Value Symbol Guard)} {paths : List (List Int)} {before after : Checked width}
    {result : Value Symbol Guard} (actual : Fold values paths before result after)
    (ranges : FoldRanges values paths before) (good : Good before) (ready : Ready (physical before))
    (scopes : Scoped before.native) (idle : Idle before.native)
    (available : Values before.native.machine.heap values) (growth : Grows anchor before.native.machine.heap)
    (supported : ∀ path ∈ paths, PathSupport unconstrained anchor path values) :
    Good after ∧ Effects (physical before) (physical after) ∧ Extension before.native.machine after.native.machine ∧
      Scoped after.native ∧ Idle after.native ∧ Available after.native.machine.heap result ∧ result.free = [] := by
  obtain ⟨chosen, reached, complete, effects⟩ := SourceCurrentAllocatedSeededQuery.fold_complete
    unconstrained anchor anchorSemantic anchorReady values paths before ranges good ready scopes idle available growth supported
  obtain ⟨rfl, rfl⟩ := actual.unique complete
  exact effects

/-- Every actual checked fold derives coherent final global tables from initial invariants. -/
theorem fold_memos [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (unconstrained : Value Symbol Guard → Bool) (anchor : State Symbol Guard)
    (anchorSemantic : SemanticReady anchor) (anchorReady : GateReady anchor)
    {values : List (Value Symbol Guard)} {paths : List (List Int)} {before after : Checked width}
    {result : Value Symbol Guard} (actual : Fold values paths before result after)
    (ranges : FoldRanges values paths before) (good : Good before) (ready : Ready (physical before))
    (scopes : Scoped before.native) (idle : Idle before.native)
    (available : Values before.native.machine.heap values) (growth : Grows anchor before.native.machine.heap)
    (supported : ∀ path ∈ paths, PathSupport unconstrained anchor path values)
    (memos : Memos) (valid : Valid before.native.machine.heap memos) :
    ∃ saved, FoldReads actual memos saved ∧ Valid after.native.machine.heap saved ∧
      Extends memos.unfolding saved.unfolding ∧ saved.query = memos.query := by
  induction actual generalizing memos with
  | one operand =>
      obtain ⟨saved, read, coherent, retained, same⟩ := operand_memos operand ready available memos valid
      exact ⟨saved, .one read, coherent, retained, same⟩
  | @cons path before value middle next paths tail later fuel result after operand remaining native ih =>
      cases ranges with
      | cons rest nativeRanges =>
          have first := SourceCurrentAllocatedSeededOperandLanguage.Operand.effects
            unconstrained anchor anchorSemantic anchorReady operand good ready scopes idle available growth
              (supported path List.mem_cons_self)
          obtain ⟨middleMemos, firstRead, middleValid, firstRetained, firstSame⟩ :=
            operand_memos operand ready available memos valid
          have middleValues : Values middle.native.machine.heap values :=
            fun value member => first.2.1.keeps.available value (available value member)
          have middleGrowth := grows_trans growth first.2.1.keeps.growth
          have tailSupport := fun path member => supported path (List.mem_cons_of_mem _ member)
          obtain ⟨laterMemos, tailRead, laterValid, tailRetained, tailSame⟩ :=
            ih (rest value middle operand) first.1 first.2.1.ready first.2.2.2.1 first.2.2.2.2.1
              middleValues middleGrowth tailSupport middleMemos middleValid
          have tailEffects := fold_effects unconstrained anchor anchorSemantic anchorReady remaining
            (rest value middle operand) first.1 first.2.1.ready first.2.2.2.1 first.2.2.2.2.1
            middleValues middleGrowth tailSupport
          obtain ⟨events, checked, quiet, finalValid⟩ := SourceCurrentAllocatedNativeGlobalMemos.trace_memos native
            tailEffects.1 tailEffects.2.1.ready.semantic tailEffects.2.1.ready.costs (fun _ => trivial) laterMemos laterValid
          exact ⟨laterMemos, .cons (native := native) firstRead tailRead (.silent (trace := native) events checked quiet), finalValid,
            extends_trans firstRetained tailRetained, tailSame.trans firstSame⟩

/-- The actual first-seeded query derives all three global memo receipts and retains both query tables. -/
theorem seeded_memos [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (unconstrained : Value Symbol Guard → Bool) (anchor : State Symbol Guard)
    (anchorSemantic : SemanticReady anchor) (anchorReady : GateReady anchor)
    {values : List (Value Symbol Guard)} {paths : List (List Int)} {before after : Checked width}
    {result : Value Symbol Guard} (actual : Seeded values paths before result after)
    (ranges : SeededRanges values paths before) (good : Good before) (ready : Ready (physical before))
    (scopes : Scoped before.native) (idle : Idle before.native)
    (available : Values before.native.machine.heap values) (growth : Grows anchor before.native.machine.heap)
    (supported : ∀ path ∈ paths, PathSupport unconstrained anchor path values)
    (memos : Memos) (valid : Valid before.native.machine.heap memos) :
    ∃ saved, SeededReads actual memos saved ∧ Valid after.native.machine.heap saved ∧
      Extends memos.unfolding saved.unfolding ∧ saved.query = memos.query := by
  cases actual with
  | nil => exact ⟨memos, .nil, valid, extends_refl _, rfl⟩
  | @nonempty rest seed before result after actual =>
      obtain ⟨saved, read, coherent, retained, same⟩ := fold_memos unconstrained anchor anchorSemantic anchorReady actual
        ranges good ready scopes idle available growth (by
          intro path member
          exact supported path (by simpa [List.mem_append, List.mem_cons, or_comm] using member)) memos valid
      exact ⟨saved, .nonempty read, coherent, retained, same⟩

end MicroCFTA.SourceCurrentAllocatedSeededMemos
