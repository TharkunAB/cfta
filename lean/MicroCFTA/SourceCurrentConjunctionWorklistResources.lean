import MicroCFTA.SourceCurrentConjunctionRowsResources
import MicroCFTA.SourceCurrentConjunctionWorker

/-!
# Initial numeric resources for current conjunction exploration

Only admission changes the heap bound. Each admitted row bounds every new
pending operand list before the suffix runs. Skips retain the original
state. The algorithmic admission budget fixes the initial numeric schedule.
-/
namespace MicroCFTA.SourceCurrentConjunctionWorklistResources
open InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open SourceCurrentMemoMergeResourceControl (Fits)
open SourceCurrentConjunctionRowsAllocation (Ready Effects)
open SourceCurrentConjunctionWorklist (Run PendingReady closed)
open SourceCurrentConjunctionTupleBounds (shapeThrough)
open HeightOrderControlled (iterate)
variable {Symbol Formula : Type}
local notation "Guard" => SourceSymbolicIndex.Constraint Formula
local notation "Physical" => SourceCurrentConjunctionRowsAllocation.State Symbol Formula
local notation "Entry" => SourceCurrentConjunctionEmptinessTable.Entry (Value Symbol Guard)

/-- One admission pays an original operand width bounded by the current scalar. -/
noncomputable def step (alphabet : List Guard) (resource : Nat) : Nat :=
  SourceCurrentConjunctionRowsResources.forecast alphabet resource (resource + 1)

/-- Admission retains the earlier scalar and a positive unit. -/
theorem step_ge (alphabet : List Guard) (resource : Nat) : resource + 1 ≤ step alphabet resource :=
  SourceCurrentConjunctionRowsResources.forecast_ge alphabet resource (resource + 1)

/-- Larger initial scalars retain the same admission envelope. -/
theorem step_mono (alphabet : List Guard) {first last : Nat} (increase : first ≤ last) :
    step alphabet first ≤ step alphabet last :=
  SourceCurrentConjunctionRowsResources.forecast_mono alphabet increase (Nat.add_le_add_right increase 1) (by omega)

/-- The initial admission budget determines the complete constructor-heap forecast. -/
noncomputable def forecast (alphabet : List Guard) (budget resource : Nat) : Nat := iterate (step alphabet) budget resource

/-- The whole worklist retains its initial scalar even when every head skips. -/
theorem forecast_ge (alphabet : List Guard) (budget resource : Nat) : resource ≤ forecast alphabet budget resource :=
  SourceCurrentMemoMergeNumericControl.iterate_ge _ (fun q => Nat.le_trans (Nat.le_succ q) (step_ge alphabet q)) budget resource

/-- Larger initial scalars retain the complete admission schedule. -/
theorem forecast_mono (alphabet : List Guard) (budget : Nat) {first last : Nat} (increase : first ≤ last) :
    forecast alphabet budget first ≤ forecast alphabet budget last :=
  SourceCurrentMemoMergeNumericControl.iterate_mono _ (step_mono alphabet) budget increase

/-- More possible admissions retain every shorter schedule. -/
theorem forecast_budget_mono (alphabet : List Guard) {first last : Nat} (increase : first ≤ last) (resource : Nat) :
    forecast alphabet first resource ≤ forecast alphabet last resource :=
  SourceCurrentMemoMergeNumericControl.iterate_count_mono _
    (fun q => Nat.le_trans (Nat.le_succ q) (step_ge alphabet q)) increase resource

/-- The final scalar supplies one shared projection worker ceiling. -/
noncomputable def workerFuel (alphabet : List Guard) (budget resource : Nat) : Nat :=
  SourceCurrentConjunctionProjectionResources.workerFuel (shapeThrough alphabet (forecast alphabet budget resource))

/-- The final scalar supplies one shared recursive reader ceiling. -/
noncomputable def readerFuel (alphabet : List Guard) (budget resource : Nat) : Nat :=
  SourceCurrentProjectionUnionResources.readFuel (forecast alphabet budget resource)

variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol (SourceSymbolicIndex.Constraint Formula))]

/-- The original forecast bounds the same actual worklist and its complete literal worker. -/
theorem bound {budget : Nat} {table final : List Entry} {pending : List (List (Value Symbol Guard))}
    {before after : Physical} (actual : Run budget table pending before final after)
    (alphabet : List Guard) (resource : Nat) (ready : Ready before) (available : PendingReady before pending)
    (fits : Fits resource before.heap) (widths : ∀ nodes ∈ pending, nodes.length ≤ resource)
    (known : SourceEqualityAnnotationHeap.Heap (fun guard => guard ∈ alphabet) before.heap) :
    Fits (forecast alphabet budget resource) after.heap ∧
      (∀ work reader, workerFuel alphabet budget resource ≤ work → readerFuel alphabet budget resource ≤ reader →
        SourceCurrentConjunctionWorker.explore work reader budget table pending before = .done final after) := by
  induction actual generalizing resource with
  | done =>
      exact ⟨fits.mono (forecast_ge alphabet _ _), by intro work reader _ _; rw [SourceCurrentConjunctionWorker.explore.eq_def]⟩
  | empty impossible rest ih =>
      have later := ih resource ready
        (fun nodes member => available nodes (List.mem_cons_of_mem _ member)) fits
        (fun nodes member => widths nodes (List.mem_cons_of_mem _ member)) known
      refine ⟨later.1, ?_⟩
      intro work reader enoughWork enoughRead
      rw [SourceCurrentConjunctionWorker.explore.eq_def]
      simpa only [impossible, ite_true] using later.2 work reader enoughWork enoughRead
  | skip nonempty skipped rest ih =>
      have later := ih resource ready
        (fun nodes member => available nodes (List.mem_cons_of_mem _ member)) fits
        (fun nodes member => widths nodes (List.mem_cons_of_mem _ member)) known
      refine ⟨later.1, ?_⟩
      intro work reader enoughWork enoughRead
      rw [SourceCurrentConjunctionWorker.explore.eq_def]
      simpa only [nonempty, Bool.false_eq_true, ite_false, skipped, ite_true] using later.2 work reader enoughWork enoughRead
  | @admit budget table nodes before requirements middle pending final after nonempty fresh rows rest ih =>
      have admitted := SourceCurrentConjunctionEmptinessTable.admitted SourceCurrentConjunctionRequirements.key closed budget table nodes fresh
      have inputs := available nodes List.mem_cons_self
      have noFree := SourceCurrentConjunctionWorklist.closed_values nodes admitted.2.1
      have physical := SourceCurrentConjunctionGuardUniverse.rows_heap (fun guard => guard ∈ alphabet)
        rows ready inputs noFree known
      have numeric := SourceCurrentConjunctionRowsResources.bound rows alphabet resource (resource + 1)
        ready inputs noFree (fits.mono (Nat.le_succ resource)) (widths nodes List.mem_cons_self) known
      have nextAvailable : PendingReady middle (requirements.flatten ++ pending) := by
        intro requirement member
        rcases List.mem_append.mp member with generated | earlier
        · obtain ⟨row, rowIn, requirementIn⟩ := List.mem_flatten.mp generated
          exact (physical.2.2 row rowIn requirement requirementIn).1
        · exact fun value included => physical.1.keeps.available value
            (available requirement (List.mem_cons_of_mem _ earlier) value included)
      have nextWidths : ∀ requirement ∈ requirements.flatten ++ pending, requirement.length ≤ step alphabet resource := by
        intro requirement member
        rcases List.mem_append.mp member with generated | earlier
        · obtain ⟨row, rowIn, requirementIn⟩ := List.mem_flatten.mp generated
          exact numeric.2.1 row rowIn requirement requirementIn
        · exact Nat.le_trans (widths requirement (List.mem_cons_of_mem _ earlier))
            (Nat.le_trans (Nat.le_succ resource) (step_ge alphabet resource))
      have later := ih (step alphabet resource) physical.1.ready nextAvailable numeric.1 nextWidths physical.2.1
      have schedule : forecast alphabet (budget - 1) (step alphabet resource) = forecast alphabet budget resource := by
        have positive := admitted.1
        have equal : budget = budget - 1 + 1 := by omega
        calc
          forecast alphabet (budget - 1) (step alphabet resource) = forecast alphabet (budget - 1 + 1) resource := rfl
          _ = forecast alphabet budget resource := congrArg (fun count => forecast alphabet count resource) equal.symm
      dsimp only [workerFuel, readerFuel] at later
      rw [schedule] at later
      refine ⟨later.1, ?_⟩
      intro work reader enoughWork enoughRead
      have resources : resource ≤ forecast alphabet budget resource := forecast_ge alphabet budget resource
      have shapes := SourceCurrentConjunctionTupleBounds.shapeThrough_mono alphabet resources
      have enough : SourceCurrentConjunctionProjectionResources.workerFuel (shapeThrough alphabet resource) ≤ work := by
        unfold SourceCurrentConjunctionProjectionResources.workerFuel
        change 2 * shapeThrough alphabet (forecast alphabet budget resource) + 1 ≤ work at enoughWork
        omega
      have initial : step alphabet resource ≤ forecast alphabet budget resource := by
        rw [← schedule]
        exact forecast_ge alphabet (budget - 1) (step alphabet resource)
      have firstDone := numeric.2.2 work reader enough
        (Nat.le_trans (SourceCurrentProjectionUnionResources.readFuel_mono initial) enoughRead)
      rw [SourceCurrentConjunctionWorker.explore.eq_def]
      simp only [nonempty, Bool.false_eq_true, ite_false, fresh, firstDone]
      exact later.2 work reader enoughWork enoughRead

/-- Initial physical facts construct the whole numeric worklist using its own finite guard carrier. -/
theorem entered (budget : Nat) (pending : List (List (Value Symbol Guard))) (before : Physical)
    (resource : Nat) (ready : Ready before) (available : PendingReady before pending)
    (fits : Fits resource before.heap) (widths : ∀ nodes ∈ pending, nodes.length ≤ resource) :
    ∃ final after, Run budget [] pending before final after ∧ Effects before after ∧
      SourceCurrentConjunctionWorklist.TableReady after final ∧ final.length ≤ budget ∧
      Fits (forecast (SourceCurrentConjunctionGuardUniverse.guards before.heap) budget resource) after.heap ∧
      (∀ work reader, workerFuel (SourceCurrentConjunctionGuardUniverse.guards before.heap) budget resource ≤ work →
        readerFuel (SourceCurrentConjunctionGuardUniverse.guards before.heap) budget resource ≤ reader →
        SourceCurrentConjunctionWorker.explore work reader budget [] pending before = .done final after) := by
  obtain ⟨final, after, actual, effects, table, length⟩ :=
    SourceCurrentConjunctionWorklist.entered budget pending before ready available
  have own := bound actual (SourceCurrentConjunctionGuardUniverse.guards before.heap) resource
    ready available fits widths (SourceCurrentConjunctionGuardUniverse.initial before.heap ready.semantic.ready.semantic.1.normal.facts)
  exact ⟨final, after, actual, effects, table, length, own⟩

end MicroCFTA.SourceCurrentConjunctionWorklistResources
