import MicroCFTA.SourceEqualityQueryGlobalMemos
import MicroCFTA.SourceNativeGlobalMemos
import MicroCFTA.SourceCurrentSecondaryQueryCosts

/-!
# Three global tables through actual class folds

The receipt records projection, tail evaluation, and native construction in
that order. Each native request executes its primitive event trace and has
no global unfolding call. Projection can extend the unfolding table. Both
query tables retain their exact contents. The seeded fold uses its actual
rotation and its effect-free empty fallback.

The proofs use completed scoped requests and projection receipts. They do
not describe GHC delayed demand, pending memo entries, or native containers.
-/
namespace MicroCFTA.SourceClassQueryGlobalMemos
open Cache Language InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open MergedColdReaderClosedInputs (ClosedValues)
open SourceEqualityRequiredCache SourceEqualityRequiredSemanticCache SourceEqualityNativeScoped
open SourceEmptinessClassFold SourceEqualityQueryGlobalMemos
open SourceCurrentSecondaryProjectionScoped (PathSupport operand_effects)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Valid" => EndpointMemoGateTrace.Valid
local notation "CostHeap" => InternedFreshOrdinaryCostHeap.Heap
local notation "GateReady" => InternedFreshOrdinaryMemoGateTrace.Ready

/-- Actual fold receipts pass each returned table to the next operation. -/
inductive FoldReads [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {emptyGuard : Guard} {conjoin : Guard → Guard → Guard} :
    {values : List (Value Symbol Guard)} → {paths : List (List Int)} →
    {before : SourceRecursiveIntersectionThunks.State width Symbol Guard} → {result : Value Symbol Guard} →
    {after : SourceRecursiveIntersectionThunks.State width Symbol Guard} →
    Fold emptyGuard conjoin values paths before result after → Memos → Memos → Prop where
  | one (read : OperandReads operand memos saved) : FoldReads (.one operand) memos saved
  | cons {values : List (Value Symbol Guard)} {path next : List Int} {paths : List (List Int)}
      {before middle later after : SourceRecursiveIntersectionThunks.State width Symbol Guard}
      {value tail result : Value Symbol Guard}
      {operand : SourceEmptinessProjection.Operand path values before value middle}
      {rest : Fold emptyGuard conjoin values (next :: paths) middle tail later}
      {native : Step emptyGuard conjoin value tail later result after}
      {memos first saved : Memos} {events : List (SourceGlobalUnfold.Event Symbol Guard)}
      (read : OperandReads operand memos first) (tailRead : FoldReads rest first saved)
      (nativeRead : SourceGlobalUnfold.Runs ⟨later.machine.heap, saved.unfolding⟩
        ⟨after.machine.heap, saved.unfolding⟩ events)
      (silent : SourceGlobalUnfold.NoGlobal events) : FoldReads (.cons operand rest native) memos saved

/-- Seeded receipts retain the actual rotated fold or all tables in the empty case. -/
def SeededReads [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {emptyGuard : Guard} {conjoin : Guard → Guard → Guard}
    {values : List (Value Symbol Guard)} {paths : List (List Int)}
    {before after : SourceRecursiveIntersectionThunks.State width Symbol Guard} {result : Value Symbol Guard}
    (trace : Seeded emptyGuard conjoin values paths before result after) (memos saved : Memos) : Prop :=
  match paths with
  | [] => saved = memos
  | _ :: _ => FoldReads trace memos saved

private theorem operand_query [DecidableEq (EdgeKey Symbol Guard)]
    {path : List Int} {values : List (Value Symbol Guard)} {result : Value Symbol Guard}
    {before after : SourceRecursiveIntersectionThunks.State width Symbol Guard}
    {operand : SourceEmptinessProjection.Operand path values before result after} {memos saved : Memos}
    (read : OperandReads operand memos saved) : saved.query = memos.query := by
  cases read with
  | force projection => exact projection.2

/-- Every actual fold receipt retains both query tables exactly. -/
theorem FoldReads.query_unchanged [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {emptyGuard : Guard} {conjoin : Guard → Guard → Guard}
    {values : List (Value Symbol Guard)} {paths : List (List Int)} {result : Value Symbol Guard}
    {before after : SourceRecursiveIntersectionThunks.State width Symbol Guard}
    {trace : Fold emptyGuard conjoin values paths before result after} {memos saved : Memos}
    (read : FoldReads trace memos saved) : saved.query = memos.query := by
  induction read with
  | one read => exact operand_query read
  | cons read _ _ _ ih => exact ih.trans (operand_query read)

/-- The empty fallback and actual seeded rotation retain both query tables. -/
theorem SeededReads.query_unchanged [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {emptyGuard : Guard} {conjoin : Guard → Guard → Guard}
    {values : List (Value Symbol Guard)} {paths : List (List Int)} {result : Value Symbol Guard}
    {before after : SourceRecursiveIntersectionThunks.State width Symbol Guard}
    {trace : Seeded emptyGuard conjoin values paths before result after} {memos saved : Memos}
    (read : SeededReads trace memos saved) : saved.query = memos.query := by
  cases paths with
  | nil => exact congrArg EndpointMemoGateTrace.Memos.query read
  | cons => exact FoldReads.query_unchanged read

/-- Current anchored path support derives coherent tables through the exact fold schedule. -/
theorem fold_memos [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (unconstrained : Value Symbol Guard → Bool) (anchor : State Symbol Guard)
    (anchorSemantic : SemanticReady anchor) (anchorReady : GateReady anchor)
    {emptyGuard : Guard} {conjoin : Guard → Guard → Guard}
    {values : List (Value Symbol Guard)} {paths : List (List Int)} {result : Value Symbol Guard}
    {before after : SourceRecursiveIntersectionThunks.State width Symbol Guard}
    (trace : Fold emptyGuard conjoin values paths before result after)
    (ready : IdleReady emptyGuard conjoin before) (available : Values before.machine.heap values)
    (growth : Grows anchor before.machine.heap)
    (supported : ∀ path ∈ paths, PathSupport unconstrained anchor path values)
    (costs : CostHeap before.machine.heap) (memos : Memos) (valid : Valid before.machine.heap memos) :
    ∃ saved, FoldReads trace memos saved ∧ Valid after.machine.heap saved ∧
      Extends memos.unfolding saved.unfolding ∧ saved.query = memos.query := by
  induction trace generalizing memos with
  | one operand =>
      obtain ⟨saved, read, coherent, retained⟩ := operand_memos operand ready.semantic costs available memos valid
      exact ⟨saved, .one read, coherent, retained, operand_query read⟩
  | cons operand rest native ih =>
      have first := operand_effects unconstrained anchor anchorSemantic anchorReady operand ready available growth
        (supported _ (by simp))
      have firstCosts := SourceEmptinessClassFoldCosts.operand_costs operand ready available costs
      have tailInputs : Values _ values := fun value member => first.2.1.available value (available value member)
      have tailGrowth := grows_trans growth first.2.1.growth
      have tailSupport := fun path member => supported path (List.mem_cons_of_mem _ member)
      obtain ⟨firstMemos, firstRead, firstValid, firstRetained⟩ :=
        operand_memos operand ready.semantic costs available memos valid
      obtain ⟨saved, tailRead, tailValid, tailRetained, _⟩ :=
        ih first.1 tailInputs tailGrowth tailSupport firstCosts firstMemos firstValid
      have remaining := SourceCurrentSecondaryClassFold.fold_effects unconstrained anchor anchorSemantic anchorReady
        rest first.1 tailInputs tailGrowth tailSupport
      obtain ⟨events, nativeRead, silent, finalValid⟩ := SourceNativeGlobalMemos.scoped_memos native remaining.1
        (remaining.2.1.available _ first.2.2.1) remaining.2.2.1 first.2.2.2.1 remaining.2.2.2
        (fun _ _ => true) (by intro _ _ _; rfl) saved tailValid
      have read : FoldReads (.cons operand rest native) memos saved := .cons (native := native) firstRead tailRead nativeRead silent
      exact ⟨saved, read, finalValid, extends_trans firstRetained tailRetained, read.query_unchanged⟩

/-- The actual seeded rotation and empty fallback derive coherent tables and exact query retention. -/
theorem seeded_memos [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (unconstrained : Value Symbol Guard → Bool) (anchor : State Symbol Guard)
    (anchorSemantic : SemanticReady anchor) (anchorReady : GateReady anchor)
    {emptyGuard : Guard} {conjoin : Guard → Guard → Guard}
    {values : List (Value Symbol Guard)} {paths : List (List Int)} {result : Value Symbol Guard}
    {before after : SourceRecursiveIntersectionThunks.State width Symbol Guard}
    (trace : Seeded emptyGuard conjoin values paths before result after)
    (ready : IdleReady emptyGuard conjoin before) (available : Values before.machine.heap values)
    (growth : Grows anchor before.machine.heap)
    (supported : ∀ path ∈ paths, PathSupport unconstrained anchor path values)
    (costs : CostHeap before.machine.heap) (memos : Memos) (valid : Valid before.machine.heap memos) :
    ∃ saved, SeededReads trace memos saved ∧ Valid after.machine.heap saved ∧
      Extends memos.unfolding saved.unfolding ∧ saved.query = memos.query := by
  cases paths with
  | nil =>
      obtain ⟨rfl, rfl⟩ := trace
      exact ⟨memos, rfl, valid, extends_refl _, rfl⟩
  | cons seed rest =>
      exact fold_memos unconstrained anchor anchorSemantic anchorReady trace ready available growth
        (fun path member => supported path ((mem_seededPaths (seed :: rest) path).mp member)) costs memos valid

/-- Closed captured forests derive the same actual fold receipts without an anchor or path restriction. -/
theorem fold_closed_memos [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {emptyGuard : Guard} {conjoin : Guard → Guard → Guard}
    {values : List (Value Symbol Guard)} {paths : List (List Int)} {result : Value Symbol Guard}
    {before after : SourceRecursiveIntersectionThunks.State width Symbol Guard}
    (trace : Fold emptyGuard conjoin values paths before result after)
    (ready : IdleReady emptyGuard conjoin before) (available : Values before.machine.heap values)
    (closed : ClosedValues values) (costs : CostHeap before.machine.heap)
    (memos : Memos) (valid : Valid before.machine.heap memos) :
    ∃ saved, FoldReads trace memos saved ∧ Valid after.machine.heap saved ∧
      Extends memos.unfolding saved.unfolding ∧ saved.query = memos.query := by
  induction trace generalizing memos with
  | one operand =>
      obtain ⟨saved, read, coherent, retained⟩ := operand_memos operand ready.semantic costs available memos valid
      exact ⟨saved, .one read, coherent, retained, operand_query read⟩
  | cons operand rest native ih =>
      have first := operand.effects ready available closed
      have firstCosts := SourceEmptinessClassFoldCosts.operand_costs operand ready available costs
      have tailInputs : Values _ values := fun value member => first.2.1.available value (available value member)
      obtain ⟨firstMemos, firstRead, firstValid, firstRetained⟩ :=
        operand_memos operand ready.semantic costs available memos valid
      obtain ⟨saved, tailRead, tailValid, tailRetained, _⟩ := ih first.1 tailInputs firstCosts firstMemos firstValid
      have remaining := rest.effects first.1 tailInputs closed
      obtain ⟨events, nativeRead, silent, finalValid⟩ := SourceNativeGlobalMemos.scoped_memos native remaining.1
        (remaining.2.1.available _ first.2.2.1) remaining.2.2.1 first.2.2.2.1 remaining.2.2.2
        (fun _ _ => true) (by intro _ _ _; rfl) saved tailValid
      have read : FoldReads (.cons operand rest native) memos saved := .cons (native := native) firstRead tailRead nativeRead silent
      exact ⟨saved, read, finalValid, extends_trans firstRetained tailRetained, read.query_unchanged⟩

/-- Closed captured forests also support the exact seeded schedule and its empty fallback. -/
theorem seeded_closed_memos [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {emptyGuard : Guard} {conjoin : Guard → Guard → Guard}
    {values : List (Value Symbol Guard)} {paths : List (List Int)} {result : Value Symbol Guard}
    {before after : SourceRecursiveIntersectionThunks.State width Symbol Guard}
    (trace : Seeded emptyGuard conjoin values paths before result after)
    (ready : IdleReady emptyGuard conjoin before) (available : Values before.machine.heap values)
    (closed : ClosedValues values) (costs : CostHeap before.machine.heap)
    (memos : Memos) (valid : Valid before.machine.heap memos) :
    ∃ saved, SeededReads trace memos saved ∧ Valid after.machine.heap saved ∧
      Extends memos.unfolding saved.unfolding ∧ saved.query = memos.query := by
  cases paths with
  | nil =>
      obtain ⟨rfl, rfl⟩ := trace
      exact ⟨memos, rfl, valid, extends_refl _, rfl⟩
  | cons => exact fold_closed_memos trace ready available closed costs memos valid

end MicroCFTA.SourceClassQueryGlobalMemos
