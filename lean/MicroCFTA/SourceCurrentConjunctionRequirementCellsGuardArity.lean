import MicroCFTA.SourceCurrentConjunctionRequirementCellsExecution
import MicroCFTA.SourceCurrentConjunctionRequirementCellsValues
import MicroCFTA.SourceCurrentConstrainedCapProjectionGuardOutcome
import MicroCFTA.SourcePruningEnumerationProjectionArityOutcome

/-!
# Causal guards and arity through shared requirement forcing

The actual singleton projection preserves causal guard observations and
stored arity on every outcome. Current resident cell values supply each
pending forest. No closedness is required. Successful and failed pending
forces retain the same physical endpoint as their literal cursor run.
Cached cells, columns, and missing handles leave the native heap unchanged.
The public laws discharge their concrete projection laws internally.
-/
namespace MicroCFTA.SourceCurrentConjunctionRequirementCellsGuardArity
open InternedConstructorTemplates (Value EdgeKey)
open InternedNestedProvenance (Values)
open SourceEqualityRequiredSemanticCache (SemanticReady)
open SourceCurrentConjunctionRowsWorker (Physical Job Outcome)
open SourceCurrentConjunctionRowsAllocation (Ready Effects)
open SourceCurrentConjunctionRequirementPull (Cursor projection run)
open SourceCurrentConjunctionRequirementCells (lookup force forceStep force_step update)

section Generic
variable {Symbol Formula : Type}
local notation "Guard" => SourceSymbolicIndex.Constraint Formula
local notation "NativeHeap" => InternedConstructorTemplates.State Symbol Guard
local notation "Cells" => SourceCurrentConjunctionRequirementCells.State Symbol Formula
local notation "CostHeap" => InternedFreshOrdinaryCostHeap.Heap
variable [DecidableEq (EdgeKey Symbol (SourceSymbolicIndex.Constraint Formula))]

private abbrev ForestPreserves (property : NativeHeap → Prop) : Prop :=
  ∀ p h path (values : List (Value Symbol Guard)) (before : NativeHeap),
    SemanticReady before → CostHeap before → Values before values → property before →
      property (SourceEqualityProjectionOutcomePrimitives.reached
        (SourceEqualityProjectionWorker.forest p h path values before))

private theorem projection_preserves (property : NativeHeap → Prop) (lower : ForestPreserves property)
    (p h : Nat) (job : Job Symbol Formula) (before : Physical Symbol Formula)
    (ready : Ready before) (available : Values before.heap job.1) (known : property before.heap) :
    property (projection p h job before).state.heap := by
  rcases job with ⟨forest, path⟩
  have preserved := lower p h (path.map Int.ofNat) forest before.heap ready.semantic ready.costs available known
  cases actual : SourceEqualityProjectionWorker.forest p h (path.map Int.ofNat) forest before.heap <;>
    simpa only [projection, SourceCurrentConjunctionRowsWorker.projections, actual,
      Outcome.bind, Outcome.state, SourceEqualityProjectionOutcomePrimitives.reached] using preserved

private theorem run_preserves (property : NativeHeap → Prop) (lower : ForestPreserves property)
    (p h : Nat) : ∀ (jobs : List (Job Symbol Formula)) (collected : List (Value Symbol Guard))
      (before : Physical Symbol Formula), Ready before →
      (∀ job ∈ jobs, Values before.heap job.1) → property before.heap →
      property (run p h ⟨jobs, collected⟩ before).state.heap := by
  intro jobs
  induction jobs with
  | nil =>
      intro collected before ready available known
      exact known
  | cons job rest ih =>
      intro collected before ready available known
      have preserved := projection_preserves property lower p h job before ready
        (available job List.mem_cons_self) known
      have first := SourceCurrentConjunctionRequirementPullEffects.projection_effects p h job before ready
        (available job List.mem_cons_self)
      cases actual : projection p h job before with
      | failed fault after =>
          rw [SourceCurrentConjunctionRequirementPull.run_failed p h job rest collected before after fault actual]
          simpa only [actual, Outcome.state] using preserved
      | done value middle =>
          have kept : Effects before middle := by simpa only [actual, Outcome.state] using first
          have current : property middle.heap := by simpa only [actual, Outcome.state] using preserved
          cases tested : SourceCurrentConjunctionRequirements.isEmpty value with
          | true =>
              rw [SourceCurrentConjunctionRequirementPull.run_step]
              simpa only [SourceCurrentConjunctionRequirementPull.step, actual, Outcome.bind,
                tested, ite_true, Outcome.state] using current
          | false =>
              rw [SourceCurrentConjunctionRequirementPull.run_more p h job rest collected before middle value actual tested]
              exact ih (collected := collected ++ [value]) (before := middle) kept.ready
                (fun next member node included => kept.keeps.available node
                  (available next (List.mem_cons_of_mem _ member) node included)) current

private theorem force_preserves (property : NativeHeap → Prop) (lower : ForestPreserves property)
    (p h handle : Nat) (before : Cells) (ready : Ready before.physical)
    (values : SourceCurrentConjunctionRequirementCellsValues.Invariant before)
    (known : property before.physical.heap) : property (force p h handle before).state.physical.heap := by
  cases found : lookup handle before with
  | none =>
      rw [force_step]
      simpa only [forceStep, found, SourceCurrentConjunctionRequirementCells.Outcome.state] using known
  | some cell =>
      cases cell with
      | done nodes =>
          rw [SourceCurrentConjunctionRequirementCells.force_hit p h handle nodes before found]
          exact known
      | column nodes =>
          rw [force_step]
          simpa only [forceStep, found, update, SourceCurrentConjunctionRequirementCells.Outcome.state] using known
      | pending cursor =>
          have preserved := run_preserves property lower p h cursor.pending cursor.collected before.physical
            ready (values handle (.pending cursor) found).2 known
          cases actual : force p h handle before with
          | done nodes after =>
              have same := SourceCurrentConjunctionRequirementCellsExecution.force_pending_run found actual
              rw [same] at preserved
              exact preserved
          | failed diagnostic after =>
              obtain ⟨stopped, fault, _, same, _⟩ :=
                SourceCurrentConjunctionRequirementCellsExecution.force_pending_failed found actual
              rw [same] at preserved
              exact preserved

/-- Every actual force outcome retains the original causal guard-observation heap. -/
theorem force_guard_heap (annotation : Guard → Prop) (p h handle : Nat) (before : Cells)
    (ready : Ready before.physical)
    (values : SourceCurrentConjunctionRequirementCellsValues.Invariant before)
    (known : SourceCurrentConstrainedCapGuardHeap.Heap annotation before.physical.heap) :
    SourceCurrentConstrainedCapGuardHeap.Heap annotation (force p h handle before).state.physical.heap := by
  apply force_preserves (SourceCurrentConstrainedCapGuardHeap.Heap annotation) ?_ p h handle before ready values known
  intro p h path nodes heap semantic costs available current
  exact SourceCurrentConstrainedCapProjectionGuardOutcome.forest_heap annotation p h path nodes heap
    semantic costs available current

end Generic

section Arity
variable {Symbol : Type}
variable [DecidableEq (EdgeKey Symbol (SourceSymbolicIndex.Constraint FullSyntax.Formula))]

/-- Every actual force outcome retains stored arity without a closed-input premise. -/
theorem force_arity_heap (p h handle : Nat)
    (before : SourceCurrentConjunctionRequirementCells.State Symbol FullSyntax.Formula)
    (ready : Ready before.physical)
    (values : SourceCurrentConjunctionRequirementCellsValues.Invariant before)
    (known : SourcePruningEnumerationArityOrigins.Heap before.physical.heap) :
    SourcePruningEnumerationArityOrigins.Heap (force p h handle before).state.physical.heap := by
  apply force_preserves SourcePruningEnumerationArityOrigins.Heap ?_ p h handle before ready values known
  intro p h path nodes heap semantic costs available current
  exact SourcePruningEnumerationProjectionArityOutcome.forest_heap p h path nodes heap
    semantic costs available current

end Arity
end MicroCFTA.SourceCurrentConjunctionRequirementCellsGuardArity
