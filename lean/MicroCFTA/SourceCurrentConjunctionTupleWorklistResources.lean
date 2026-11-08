import MicroCFTA.SourceCurrentConjunctionWorklistResources
import MicroCFTA.SourceCurrentConjunctionTupleExecution

/-!
# Initial resources for raw-tuple-budget exploration

Zero admissions can grow the heap without spending budget. Each phase pays
for the old pending prefix before the next positive admission. Positive
admission prepends its actual requirements and spends its actual raw charge.
Overflow pays for exposure and drains the suffix at zero budget.
-/
namespace MicroCFTA.SourceCurrentConjunctionTupleWorklistResources
open InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values Edges)
open MergedColdReaderClosedInputs (ClosedValues ClosedEdges)
open SourceCurrentMemoMergeResourceControl (Fits)
open SourceCurrentConjunctionRowsAllocation (Ready Effects Rows RowsReady Tuples)
open SourceCurrentConjunctionTupleExecution (Admission Run)
open SourceCurrentConjunctionWorklist (PendingReady closed)
open SourceCurrentConjunctionTupleBounds (shapeThrough)
open HeightOrderControlled (iterate)
variable {Symbol Formula : Type}
local notation "Guard" => SourceSymbolicIndex.Constraint Formula
local notation "Physical" => SourceCurrentConjunctionRowsAllocation.State Symbol Formula
local notation "Entry" => SourceCurrentConjunctionEmptinessTable.Entry (Value Symbol Guard)

namespace Numeric

/-- A phase consumes the old queue prefix before descending to a smaller budget. -/
def envelope (step width : Nat → Nat) : Nat → Nat → Nat → Nat
  | 0, _, resource => resource
  | _ + 1, 0, resource => resource
  | budget + 1, pending + 1, resource =>
      let phase := iterate step (pending + 1) resource
      envelope step width budget (pending + (budget + 1) * width phase) phase

/-- Every phase retains its initial resource. -/
theorem envelope_ge (step width : Nat → Nat) (grows : ∀ resource, resource ≤ step resource)
    (budget pending resource : Nat) : resource ≤ envelope step width budget pending resource := by
  induction budget generalizing pending resource with
  | zero => exact Nat.le_refl _
  | succ budget ih =>
      cases pending with
      | zero => exact Nat.le_refl _
      | succ pending =>
          exact Nat.le_trans (SourceCurrentMemoMergeNumericControl.iterate_ge step grows _ _)
            (ih _ _)

/-- Larger queue and resource bounds retain the same phase envelope. -/
theorem envelope_mono (step width : Nat → Nat)
    (grows : ∀ resource, resource ≤ step resource)
    (stepMono : ∀ {first last}, first ≤ last → step first ≤ step last)
    (widthMono : ∀ {first last}, first ≤ last → width first ≤ width last)
    (budget : Nat) {firstPending lastPending firstResource lastResource : Nat}
    (pending : firstPending ≤ lastPending) (resources : firstResource ≤ lastResource) :
    envelope step width budget firstPending firstResource ≤ envelope step width budget lastPending lastResource := by
  induction budget generalizing firstPending lastPending firstResource lastResource with
  | zero => exact resources
  | succ budget ih =>
      cases firstPending with
      | zero => exact Nat.le_trans resources (envelope_ge step width grows _ _ _)
      | succ first =>
          cases lastPending with
          | zero => omega
          | succ last =>
              have phases : iterate step (first + 1) firstResource ≤ iterate step (last + 1) lastResource :=
                Nat.le_trans (SourceCurrentMemoMergeNumericControl.iterate_mono step stepMono _ resources)
                  (SourceCurrentMemoMergeNumericControl.iterate_count_mono step grows pending lastResource)
              have tails : first + (budget + 1) * width (iterate step (first + 1) firstResource) ≤
                  last + (budget + 1) * width (iterate step (last + 1) lastResource) :=
                Nat.add_le_add (by omega) (Nat.mul_le_mul_left _ (widthMono phases))
              exact ih tails phases

/-- One additional possible positive admission retains the previous budget envelope. -/
theorem envelope_budget_succ (step width : Nat → Nat)
    (grows : ∀ resource, resource ≤ step resource)
    (stepMono : ∀ {first last}, first ≤ last → step first ≤ step last)
    (widthMono : ∀ {first last}, first ≤ last → width first ≤ width last)
    (budget pending resource : Nat) :
    envelope step width budget pending resource ≤ envelope step width (budget + 1) pending resource := by
  induction budget generalizing pending resource with
  | zero => exact envelope_ge step width grows _ _ _
  | succ budget ih =>
      cases pending with
      | zero => exact Nat.le_refl _
      | succ pending =>
          let phase := iterate step (pending + 1) resource
          change envelope step width budget (pending + (budget + 1) * width phase) phase ≤
            envelope step width (budget + 1) (pending + (budget + 1 + 1) * width phase) phase
          exact Nat.le_trans (ih _ _)
            (envelope_mono step width grows stepMono widthMono _
              (Nat.add_le_add_left (Nat.mul_le_mul_right _ (by omega)) _) (Nat.le_refl _))

/-- A larger initial raw budget retains every smaller budget envelope. -/
theorem envelope_budget_mono (step width : Nat → Nat)
    (grows : ∀ resource, resource ≤ step resource)
    (stepMono : ∀ {first last}, first ≤ last → step first ≤ step last)
    (widthMono : ∀ {first last}, first ≤ last → width first ≤ width last)
    {first last : Nat} (budgets : first ≤ last) (pending resource : Nat) :
    envelope step width first pending resource ≤ envelope step width last pending resource := by
  obtain ⟨extra, rfl⟩ := Nat.exists_eq_add_of_le budgets
  induction extra with
  | zero => exact Nat.le_refl _
  | succ extra ih =>
      exact Nat.le_trans (ih (by omega))
        (envelope_budget_succ step width grows stepMono widthMono _ _ _)

end Numeric

/-- The final scalar bounds the number of requirements emitted by one raw tuple. -/
noncomputable def rowWidth (alphabet : List Guard) (resource : Nat) : Nat :=
  resource + shapeThrough alphabet resource

private theorem step_grows (alphabet : List Guard) (resource : Nat) :
    resource ≤ SourceCurrentConjunctionWorklistResources.step alphabet resource :=
  Nat.le_trans (Nat.le_succ _) (SourceCurrentConjunctionWorklistResources.step_ge alphabet resource)

private theorem rowWidth_mono (alphabet : List Guard) {first last : Nat} (increase : first ≤ last) :
    rowWidth alphabet first ≤ rowWidth alphabet last :=
  Nat.add_le_add increase (SourceCurrentConjunctionTupleBounds.shapeThrough_mono alphabet increase)

/-- Initial queue length and raw budget fix the complete numeric phase schedule. -/
noncomputable def forecast (alphabet : List Guard) (budget pending resource : Nat) : Nat :=
  Numeric.envelope (SourceCurrentConjunctionWorklistResources.step alphabet) (rowWidth alphabet) budget pending resource

/-- The complete schedule retains its initial scalar. -/
theorem forecast_ge (alphabet : List Guard) (budget pending resource : Nat) :
    resource ≤ forecast alphabet budget pending resource :=
  Numeric.envelope_ge _ _ (step_grows alphabet) budget pending resource

/-- Larger original queues and scalars retain the complete schedule. -/
theorem forecast_mono (alphabet : List Guard) (budget : Nat)
    {firstPending lastPending firstResource lastResource : Nat}
    (pending : firstPending ≤ lastPending) (resources : firstResource ≤ lastResource) :
    forecast alphabet budget firstPending firstResource ≤ forecast alphabet budget lastPending lastResource :=
  Numeric.envelope_mono _ _ (step_grows alphabet) (SourceCurrentConjunctionWorklistResources.step_mono alphabet)
    (rowWidth_mono alphabet) budget pending resources

/-- Larger raw budgets retain every smaller schedule. -/
theorem forecast_budget_mono (alphabet : List Guard) {first last : Nat} (budgets : first ≤ last)
    (pending resource : Nat) : forecast alphabet first pending resource ≤ forecast alphabet last pending resource :=
  Numeric.envelope_budget_mono _ _ (step_grows alphabet) (SourceCurrentConjunctionWorklistResources.step_mono alphabet)
    (rowWidth_mono alphabet) budgets pending resource

/-- Every entered admission is covered before the suffix runs. -/
theorem step_le_forecast (alphabet : List Guard) {budget : Nat} (positive : 0 < budget)
    (pending resource : Nat) : SourceCurrentConjunctionWorklistResources.step alphabet resource ≤
      forecast alphabet budget (pending + 1) resource := by
  cases budget with
  | zero => omega
  | succ budget =>
      exact Nat.le_trans (SourceCurrentMemoMergeNumericControl.iterate_ge _ (step_grows alphabet) pending _)
        (forecast_ge alphabet budget _ _)

/-- A zero admission consumes one old queue entry and pays its actual heap growth. -/
theorem forecast_zero (alphabet : List Guard) {budget : Nat} (positive : 0 < budget)
    (pending resource : Nat) :
    forecast alphabet budget pending (SourceCurrentConjunctionWorklistResources.step alphabet resource) ≤
      forecast alphabet budget (pending + 1) resource := by
  cases budget with
  | zero => omega
  | succ budget =>
      cases pending with
      | zero => exact step_le_forecast alphabet (by omega) 0 resource
      | succ pending =>
          let phase := iterate (SourceCurrentConjunctionWorklistResources.step alphabet) (pending + 1 + 1) resource
          change forecast alphabet budget (pending + (budget + 1) * rowWidth alphabet phase) phase ≤
            forecast alphabet budget (pending + 1 + (budget + 1) * rowWidth alphabet phase) phase
          exact forecast_mono alphabet budget (by omega) (Nat.le_refl _)

/-- Positive admission spends its actual charge and pays all newly prepended requirements. -/
theorem forecast_positive (alphabet : List Guard) {budget charge generated : Nat}
    (positive : 0 < charge) (spent : charge ≤ budget) (pending resource : Nat)
    (count : generated ≤ charge * rowWidth alphabet (SourceCurrentConjunctionWorklistResources.step alphabet resource)) :
    forecast alphabet (budget - charge) (generated + pending)
        (SourceCurrentConjunctionWorklistResources.step alphabet resource) ≤
      forecast alphabet budget (pending + 1) resource := by
  cases budget with
  | zero => omega
  | succ budget =>
      let phase := iterate (SourceCurrentConjunctionWorklistResources.step alphabet) (pending + 1) resource
      have stepLe : SourceCurrentConjunctionWorklistResources.step alphabet resource ≤ phase :=
        SourceCurrentMemoMergeNumericControl.iterate_ge _ (step_grows alphabet) pending _
      have generatedLe : generated ≤ (budget + 1) * rowWidth alphabet phase :=
        Nat.le_trans count (Nat.mul_le_mul spent (rowWidth_mono alphabet stepLe))
      have smaller : budget + 1 - charge ≤ budget := by omega
      change forecast alphabet (budget + 1 - charge) (generated + pending)
          (SourceCurrentConjunctionWorklistResources.step alphabet resource) ≤
        forecast alphabet budget (pending + (budget + 1) * rowWidth alphabet phase) phase
      exact Nat.le_trans (forecast_budget_mono alphabet smaller _ _)
        (forecast_mono alphabet budget (by omega) stepLe)

private theorem flatten_length_le {A : Type} (rows : List (List A)) (width : Nat)
    (bounded : ∀ row ∈ rows, row.length ≤ width) : rows.flatten.length ≤ rows.length * width := by
  induction rows with
  | nil => simp
  | cons row rows ih =>
      have first := bounded row List.mem_cons_self
      have later := ih (fun values member => bounded values (List.mem_cons_of_mem _ member))
      simp only [List.flatten_cons, List.length_append, List.length_cons, Nat.add_mul, Nat.one_mul]
      omega

variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol (SourceSymbolicIndex.Constraint Formula))]

omit [DecidableEq Symbol] in
private theorem exposure_effects {nodes : List (Value Symbol Guard)} {before : Physical}
    {edges : List (List (EdgeValue Symbol Guard))} {heap : State Symbol Guard}
    (reads : SourceCurrentConjunctionCompletionReads.Exposures nodes before.heap edges heap)
    (alphabet : List Guard) (ready : Ready before) (available : Values before.heap nodes)
    (noFree : ClosedValues nodes)
    (known : SourceEqualityAnnotationHeap.Heap (fun guard => guard ∈ alphabet) before.heap) :
    Effects before ⟨heap, before.equality⟩ ∧
      SourceEqualityAnnotationHeap.Heap (fun guard => guard ∈ alphabet) heap := by
  have physical := reads.verified (SourceCurrentConjunctionEquality.FieldAvailable before.equality)
    ready.semantic ready.costs ready.fields available noFree
  have guards := reads.verified (fun guard => guard ∈ alphabet)
    ready.semantic ready.costs known available noFree
  exact ⟨⟨physical.1.keeps, ⟨physical.1.semantic, physical.1.costs, ready.valid, physical.1.annotations⟩,
    SourceEqualityConstraintMemoAllocation.grows_refl _⟩, guards.1.annotations⟩

/-- The actual positive raw charge bounds every requirement prepended by that admission. -/
theorem positive_generated {budget predecessor : Nat} {nodes : List (Value Symbol Guard)}
    {before after : Physical} {requirements : List (List (List (Value Symbol Guard)))}
    (actual : Admission budget nodes before (.positive predecessor requirements) after)
    (alphabet : List Guard) (resource : Nat) (ready : Ready before) (available : Values before.heap nodes)
    (noFree : ClosedValues nodes) (fits : Fits resource before.heap) (length : nodes.length ≤ resource)
    (known : SourceEqualityAnnotationHeap.Heap (fun guard => guard ∈ alphabet) before.heap) :
    requirements.flatten.length ≤ (predecessor + 1) *
      rowWidth alphabet (SourceCurrentConjunctionWorklistResources.step alphabet resource) := by
  cases actual with
  | @positive predecessor nodes before after edges heap requirements reads count spent tuples =>
      let width := SourceCurrentConjunctionExposureResources.forecast resource (resource + 1)
      have exposed := SourceCurrentConjunctionExposureResources.bounded reads resource (resource + 1)
        ready.semantic ready.costs available noFree (fits.mono (Nat.le_succ _)) length
      have effects := exposure_effects reads alphabet ready available noFree known
      have resident : ∀ tuple ∈ SourceCurrentConjunctionTuples.tuples edges, Edges heap tuple :=
        fun tuple member => (SourceCurrentConjunctionTuples.tuples_verified (fun guard => guard ∈ alphabet)
          reads ready.semantic ready.costs known available noFree tuple member).2.1
      have closedTuples : ∀ tuple ∈ SourceCurrentConjunctionTuples.tuples edges, ClosedEdges tuple :=
        fun tuple member => (SourceCurrentConjunctionTuples.tuples_verified (fun guard => guard ∈ alphabet)
          reads ready.semantic ready.costs known available noFree tuple member).2.2
      have counts : ∀ tuple ∈ SourceCurrentConjunctionTuples.tuples edges, tuple.length ≤ resource := by
        intro tuple member
        rw [SourceCurrentConjunctionTupleBounds.tuple_length edges tuple member, exposed.2.1]
        exact length
      have widths : ∀ tuple ∈ SourceCurrentConjunctionTuples.tuples edges,
          ∀ edge ∈ tuple, edge.children.length ≤ width := by
        intro tuple member edge included
        have small := InternedValueMassHeap.resident heap exposed.1.stored edge (resident tuple member edge included)
        have children := InternedStoredEncodingWidth.values_length edge.children
        rw [InternedValueMass.edge_children] at small
        omega
      have carrier : ∀ tuple ∈ SourceCurrentConjunctionTuples.tuples edges,
          ∀ edge ∈ tuple, edge.entry.key.constraint ∈ alphabet :=
        fun tuple member edge included => effects.2 edge.entry.key edge (resident tuple member edge included)
      have numeric := SourceCurrentConjunctionRowsResources.tuples_bound tuples alphabet resource width
        (predecessor + 1) width effects.1.ready resident closedTuples exposed.1 counts widths carrier (Nat.le_of_eq count)
      have widthLe : width ≤ SourceCurrentConjunctionWorklistResources.step alphabet resource :=
        SourceCurrentConjunctionRowsResources.tupleSchedule_ge alphabet resource width _ width
      have rowLe : width + shapeThrough alphabet resource ≤
          rowWidth alphabet (SourceCurrentConjunctionWorklistResources.step alphabet resource) :=
        Nat.add_le_add widthLe (SourceCurrentConjunctionTupleBounds.shapeThrough_mono alphabet (step_grows alphabet resource))
      have flattened := flatten_length_le requirements
        (rowWidth alphabet (SourceCurrentConjunctionWorklistResources.step alphabet resource))
        (fun row member => Nat.le_trans (numeric.2.2.1 row member).1 rowLe)
      exact Nat.le_trans flattened (Nat.mul_le_mul_right _ numeric.2.1)

/-- Initial scalars bound the actual tuple worklist, including exposure-only zero and overflow steps. -/
theorem bound {budget : Nat} {table final : List Entry} {pending : List (List (Value Symbol Guard))}
    {before after : Physical} (actual : Run budget table pending before final after)
    (alphabet : List Guard) (resource : Nat) (ready : Ready before) (available : PendingReady before pending)
    (fits : Fits resource before.heap) (widths : ∀ nodes ∈ pending, nodes.length ≤ resource)
    (known : SourceEqualityAnnotationHeap.Heap (fun guard => guard ∈ alphabet) before.heap) :
    Fits (forecast alphabet budget pending.length resource) after.heap := by
  induction actual generalizing resource with
  | done => exact fits.mono (forecast_ge alphabet _ _ _)
  | empty impossible rest ih =>
      have later := ih resource ready
        (fun nodes member => available nodes (List.mem_cons_of_mem _ member)) fits
        (fun nodes member => widths nodes (List.mem_cons_of_mem _ member)) known
      exact later.mono (forecast_mono alphabet _ (by simp) (Nat.le_refl _))
  | skip nonempty fresh rest ih =>
      have later := ih resource ready
        (fun nodes member => available nodes (List.mem_cons_of_mem _ member)) fits
        (fun nodes member => widths nodes (List.mem_cons_of_mem _ member)) known
      exact later.mono (forecast_mono alphabet _ (by simp) (Nat.le_refl _))
  | @overflow budget table nodes before middle pending final after nonempty fresh admission rest ih =>
      have admitted := SourceCurrentConjunctionEmptinessTable.admitted
        SourceCurrentConjunctionRequirements.key closed budget table nodes fresh
      have inputs := available nodes List.mem_cons_self
      have noFree := SourceCurrentConjunctionWorklist.closed_values nodes admitted.2.1
      cases admission with
      | overflow reads tooMany =>
          have effects := exposure_effects reads alphabet ready inputs noFree known
          have numeric := SourceCurrentConjunctionExposureResources.bounded reads resource (resource + 1)
            ready.semantic ready.costs inputs noFree (fits.mono (Nat.le_succ _)) (widths nodes List.mem_cons_self)
          have stepFits : Fits (SourceCurrentConjunctionWorklistResources.step alphabet resource) _ :=
            numeric.1.mono (SourceCurrentConjunctionRowsResources.tupleSchedule_ge alphabet resource _ _ _)
          have later := ih (SourceCurrentConjunctionWorklistResources.step alphabet resource) effects.1.ready
            (fun group member value included => effects.1.keeps.available value
              (available group (List.mem_cons_of_mem _ member) value included)) stepFits
            (fun group member => Nat.le_trans (widths group (List.mem_cons_of_mem _ member))
              (step_grows alphabet resource)) effects.2
          exact later.mono (step_le_forecast alphabet admitted.1 pending.length resource)
  | @zero budget table nodes before middle pending final after nonempty fresh admission rest ih =>
      have admitted := SourceCurrentConjunctionEmptinessTable.admitted
        SourceCurrentConjunctionRequirements.key closed budget table nodes fresh
      have inputs := available nodes List.mem_cons_self
      have noFree := SourceCurrentConjunctionWorklist.closed_values nodes admitted.2.1
      have rows := admission.zero_rows
      have effects := SourceCurrentConjunctionGuardUniverse.rows_heap (fun guard => guard ∈ alphabet)
        rows ready inputs noFree known
      have numeric := SourceCurrentConjunctionRowsResources.bound rows alphabet resource (resource + 1)
        ready inputs noFree (fits.mono (Nat.le_succ _)) (widths nodes List.mem_cons_self) known
      have later := ih (SourceCurrentConjunctionWorklistResources.step alphabet resource) effects.1.ready
        (fun group member value included => effects.1.keeps.available value
          (available group (List.mem_cons_of_mem _ member) value included)) numeric.1
        (fun group member => Nat.le_trans (widths group (List.mem_cons_of_mem _ member))
          (step_grows alphabet resource)) effects.2.1
      exact later.mono (forecast_zero alphabet admitted.1 pending.length resource)
  | @positive budget table nodes before predecessor requirements middle pending final after nonempty fresh admission rest ih =>
      have admitted := SourceCurrentConjunctionEmptinessTable.admitted
        SourceCurrentConjunctionRequirements.key closed budget table nodes fresh
      have inputs := available nodes List.mem_cons_self
      have noFree := SourceCurrentConjunctionWorklist.closed_values nodes admitted.2.1
      have charged := admission.positive_rows
      have effects := SourceCurrentConjunctionGuardUniverse.rows_heap (fun guard => guard ∈ alphabet)
        charged.2 ready inputs noFree known
      have numeric := SourceCurrentConjunctionRowsResources.bound charged.2 alphabet resource (resource + 1)
        ready inputs noFree (fits.mono (Nat.le_succ _)) (widths nodes List.mem_cons_self) known
      have generated := positive_generated admission alphabet resource ready inputs noFree fits
        (widths nodes List.mem_cons_self) known
      have nextAvailable : PendingReady middle (requirements.flatten ++ pending) := by
        intro group member
        rcases List.mem_append.mp member with generated | earlier
        · obtain ⟨row, rowIn, groupIn⟩ := List.mem_flatten.mp generated
          exact (effects.2.2 row rowIn group groupIn).1
        · exact fun value included => effects.1.keeps.available value
            (available group (List.mem_cons_of_mem _ earlier) value included)
      have nextWidths : ∀ group ∈ requirements.flatten ++ pending,
          group.length ≤ SourceCurrentConjunctionWorklistResources.step alphabet resource := by
        intro group member
        rcases List.mem_append.mp member with generated | earlier
        · obtain ⟨row, rowIn, groupIn⟩ := List.mem_flatten.mp generated
          exact numeric.2.1 row rowIn group groupIn
        · exact Nat.le_trans (widths group (List.mem_cons_of_mem _ earlier)) (step_grows alphabet resource)
      have later := ih (SourceCurrentConjunctionWorklistResources.step alphabet resource) effects.1.ready
        nextAvailable numeric.1 nextWidths effects.2.1
      have schedule := forecast_positive alphabet (by omega : 0 < predecessor + 1) charged.1
        pending.length resource generated
      exact later.mono (by simpa only [List.length_append, List.length_cons] using schedule)

/-- The initial physical heap derives its fixed guard alphabet internally. -/
theorem initial_bound {budget : Nat} {table final : List Entry} {pending : List (List (Value Symbol Guard))}
    {before after : Physical} (actual : Run budget table pending before final after)
    (resource : Nat) (ready : Ready before) (available : PendingReady before pending)
    (fits : Fits resource before.heap) (widths : ∀ nodes ∈ pending, nodes.length ≤ resource) :
    Fits (forecast (SourceCurrentConjunctionGuardUniverse.guards before.heap) budget pending.length resource) after.heap :=
  bound actual _ resource ready available fits widths
    (SourceCurrentConjunctionGuardUniverse.initial before.heap ready.semantic.ready.semantic.1.normal.facts)

end MicroCFTA.SourceCurrentConjunctionTupleWorklistResources
