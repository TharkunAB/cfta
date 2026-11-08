import MicroCFTA.SourceCurrentConjunctionDemandWorklistExecution
import MicroCFTA.SourceCurrentConjunctionDemandNumeric
import MicroCFTA.SourceCurrentConjunctionDemandCompletion
import MicroCFTA.SourceCurrentConjunctionDemandAnnotations
import MicroCFTA.SourceCurrentConjunctionDemandSoundness
import MicroCFTA.SourceCurrentConjunctionTupleWorklistNumeric

/-!
# Initial numeric ceilings for demanded worklists

The initial budget enlarges the scalar once. Every recursive phase retains
the budget bound and uses the existing step and queue envelope. Current
ready operands derive complete admission and the actual worklist. Numeric
replay keeps its exact heap, equality allocations, table, and fourth memo.
These ceilings do not count native evaluation work.
-/
namespace MicroCFTA.SourceCurrentConjunctionDemandWorklistNumeric
open InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values Edges)
open MergedColdReaderClosedInputs (ClosedValues ClosedEdges)
open SourceCurrentMemoMergeResourceControl (Fits)
open SourceCurrentConjunctionRowsAllocation (Ready Effects RowsReady)
open SourceCurrentConjunctionDemandExecution (Admission)
open SourceCurrentConjunctionDemandWorklistExecution (Run Decision)
open SourceCurrentConjunctionWorklist (PendingReady TableReady closed)
open SourceCurrentConjunctionTupleBounds (shapeThrough)
open SourceCurrentConjunctionWorker (Physical Table Outcome)
local notation "oldForecast" => SourceCurrentConjunctionTupleWorklistResources.forecast
local notation "step" => SourceCurrentConjunctionWorklistResources.step
local notation "projectionFuel" => SourceCurrentConjunctionProjectionResources.workerFuel
local notation "readFuel" => SourceCurrentProjectionUnionResources.readFuel
local notation "rawWorkerFuel" => SourceCurrentConjunctionTupleWorklistNumeric.workerFuel
local notation "rawReaderFuel" => SourceCurrentConjunctionTupleWorklistNumeric.readerFuel

section Generic
variable {Symbol Formula : Type}
local notation "Guard" => SourceSymbolicIndex.Constraint Formula
local notation "Node" => Value Symbol Guard
local notation "Edge" => EdgeValue Symbol Guard
local notation "Entry" => SourceCurrentConjunctionEmptinessTable.Entry Node
local notation "key" => (SourceCurrentConjunctionRequirements.key : Node → Int)
local notation "isEmpty" => (SourceCurrentConjunctionRequirements.isEmpty : Node → Bool)
local notation "AnnotationHeap" => SourceEqualityAnnotationHeap.Heap

/-- Original resources and budget fix the same complete phase envelope. -/
noncomputable def forecast (alphabet : List Guard) (budget pending resource : Nat) : Nat :=
  oldForecast alphabet budget pending (max resource budget)

/-- The forecast retains every initial resource. -/
theorem forecast_ge (alphabet : List Guard) (budget pending resource : Nat) :
    resource ≤ forecast alphabet budget pending resource :=
  Nat.le_trans (Nat.le_max_left _ _)
    (SourceCurrentConjunctionTupleWorklistResources.forecast_ge alphabet budget pending _)

/-- Larger initial queues and resources retain the whole phase schedule. -/
theorem forecast_mono (alphabet : List Guard) (budget : Nat)
    {firstPending lastPending firstResource lastResource : Nat}
    (pending : firstPending ≤ lastPending) (resources : firstResource ≤ lastResource) :
    forecast alphabet budget firstPending firstResource ≤ forecast alphabet budget lastPending lastResource :=
  SourceCurrentConjunctionTupleWorklistResources.forecast_mono alphabet budget pending
    (Nat.max_le.mpr ⟨Nat.le_trans resources (Nat.le_max_left _ _), Nat.le_max_right _ _⟩)

/-- A larger original budget retains the smaller initial forecast. -/
theorem forecast_budget_mono (alphabet : List Guard) {first last : Nat} (budgets : first ≤ last)
    (pending resource : Nat) : forecast alphabet first pending resource ≤ forecast alphabet last pending resource :=
  Nat.le_trans
    (SourceCurrentConjunctionTupleWorklistResources.forecast_budget_mono alphabet budgets pending _)
    (SourceCurrentConjunctionTupleWorklistResources.forecast_mono alphabet last (Nat.le_refl pending)
      (Nat.max_le.mpr ⟨Nat.le_max_left _ _, Nat.le_trans budgets (Nat.le_max_right _ _)⟩))

/-- One original forecast supplies the common projection ceiling. -/
noncomputable def workerFuel (alphabet : List Guard) (budget pending resource : Nat) : Nat :=
  projectionFuel (shapeThrough alphabet (forecast alphabet budget pending resource))

/-- The same forecast supplies the common recursive reader ceiling. -/
noncomputable def readerFuel (alphabet : List Guard) (budget pending resource : Nat) : Nat :=
  readFuel (forecast alphabet budget pending resource)

private theorem projection_mono (alphabet : List Guard) {first last : Nat} (increase : first ≤ last) :
    projectionFuel (shapeThrough alphabet first) ≤ projectionFuel (shapeThrough alphabet last) := by
  have shapes := SourceCurrentConjunctionTupleBounds.shapeThrough_mono alphabet increase
  unfold SourceCurrentConjunctionProjectionResources.workerFuel
  omega

private theorem step_grows (alphabet : List Guard) (resource : Nat) : resource ≤ step alphabet resource :=
  Nat.le_trans (Nat.le_succ _) (SourceCurrentConjunctionWorklistResources.step_ge alphabet resource)

variable [DecidableEq Symbol]
  [DecidableEq (EdgeKey Symbol (SourceSymbolicIndex.Constraint Formula))]

private theorem admission_known {budget : Nat} {nodes : List Node}
    {before after : Physical Symbol Formula} {result : SourceCurrentConjunctionTupleAdmission.Result Symbol Formula}
    (actual : Admission budget nodes before result after) (alphabet : List Guard)
    (ready : Ready before) (available : Values before.heap nodes) (noFree : ClosedValues nodes)
    (known : AnnotationHeap (fun guard => guard ∈ alphabet) before.heap) :
    AnnotationHeap (fun guard => guard ∈ alphabet) after.heap := by
  obtain ⟨p, h, stable⟩ := SourceCurrentConjunctionDemandExecution.admission_complete actual
  have preserved := SourceCurrentConjunctionDemandAnnotations.run_annotation_heap (fun guard => guard ∈ alphabet)
    p h budget nodes before ready available noFree known
  simpa only [stable p h (Nat.le_refl _) (Nat.le_refl _),
    SourceCurrentConjunctionRowsWorker.Outcome.state] using preserved

private theorem positive_widths {budget predecessor : Nat} {nodes : List Node}
    {before after : Physical Symbol Formula} {requirements : List (List (List Node))}
    (actual : Admission budget nodes before (.positive predecessor requirements) after)
    (alphabet : List Guard) (resource : Nat) (ready : Ready before)
    (available : Values before.heap nodes) (noFree : ClosedValues nodes) (fits : Fits resource before.heap)
    (length : nodes.length ≤ resource) (known : AnnotationHeap (fun guard => guard ∈ alphabet) before.heap) :
    ∀ row ∈ requirements, ∀ group ∈ row, group.length ≤ step alphabet resource := by
  cases actual with
  | @positive h budget nodes before middle after first rest requirements sampled allocated =>
      let width := SourceCurrentConjunctionExposureResources.forecast resource (resource + 1)
      have physical := SourceCurrentConjunctionTuplePullTotalEffects.sample_effects h budget nodes before ready available
      have kept : Effects before middle := by
        simpa only [sampled, SourceCurrentConjunctionRowsWorker.Outcome.state] using physical.1
      have resident := physical.2 (.fit (first :: rest)) middle sampled
      have closedTuples := SourceCurrentConjunctionTuplePullClosedSample.sample_fit h budget nodes before middle
        (first :: rest) sampled ready available noFree
      have bounded : Fits width middle.heap :=
        (SourceCurrentConjunctionTuplePullResources.sample_fits h budget nodes before middle _ sampled resource
          ready available noFree fits).mono
          (SourceCurrentConjunctionExposureResources.forecast_mono length (Nat.le_succ resource))
      have counts : ∀ tuple ∈ first :: rest, tuple.length ≤ resource := by
        intro tuple member
        rw [(SourceCurrentConjunctionTuplePullShapes.sample_fit h budget nodes before middle
          (first :: rest) sampled tuple member).1]
        exact length
      have widths : ∀ tuple ∈ first :: rest, ∀ edge ∈ tuple, edge.children.length ≤ width := by
        intro tuple member edge included
        have small := InternedValueMassHeap.resident middle.heap bounded.stored edge (resident tuple member edge included)
        have children := InternedStoredEncodingWidth.values_length edge.children
        rw [InternedValueMass.edge_children] at small
        omega
      have annotations := SourceCurrentConjunctionDemandAnnotations.sample_annotation_heap
        (fun guard => guard ∈ alphabet) h budget nodes before ready.semantic ready.costs available known
      have guards : AnnotationHeap (fun guard => guard ∈ alphabet) middle.heap :=
        by simpa only [sampled, SourceCurrentConjunctionRowsWorker.Outcome.state] using annotations
      have carrier : ∀ tuple ∈ first :: rest, ∀ edge ∈ tuple, edge.entry.key.constraint ∈ alphabet :=
        fun tuple member edge included => guards edge.entry.key edge (resident tuple member edge included)
      have numeric := SourceCurrentConjunctionRowsResources.tuples_bound allocated alphabet resource width
        (first :: rest).length width kept.ready resident closedTuples bounded counts widths carrier (Nat.le_refl _)
      intro row member group included
      exact Nat.le_trans ((numeric.2.2.1 row member).2 group included)
        (SourceCurrentConjunctionRowsResources.pending_width alphabet resource (resource + 1) (by omega))

private theorem bound_core {budget : Nat} {table final : Table Symbol Formula} {pending : List (List Node)}
    {before after : Physical Symbol Formula} (actual : Run budget table pending before final after)
    (alphabet : List Guard) (resource : Nat) (ready : Ready before) (available : PendingReady before pending)
    (fits : Fits resource before.heap) (widths : ∀ nodes ∈ pending, nodes.length ≤ resource)
    (known : AnnotationHeap (fun guard => guard ∈ alphabet) before.heap) (budgetLe : budget ≤ resource) :
    Fits (oldForecast alphabet budget pending.length resource) after.heap ∧
      ∀ p h, rawWorkerFuel alphabet budget pending.length resource ≤ p →
        rawReaderFuel alphabet budget pending.length resource ≤ h →
        SourceCurrentConjunctionDemandWorker.explore p h budget table pending before = .done final after := by
  induction actual generalizing resource with
  | done =>
      exact ⟨fits.mono (SourceCurrentConjunctionTupleWorklistResources.forecast_ge alphabet _ _ _),
        by intros; exact SourceCurrentConjunctionDemandWorker.explore_nil _ _ _ _ _⟩
  | empty impossible rest ih =>
      have later := ih resource ready (fun nodes member => available nodes (List.mem_cons_of_mem _ member)) fits
        (fun nodes member => widths nodes (List.mem_cons_of_mem _ member)) known budgetLe
      refine ⟨later.1.mono (SourceCurrentConjunctionTupleWorklistResources.forecast_mono alphabet _
        (by simp) (Nat.le_refl resource)), ?_⟩
      intro p h enoughP enoughH
      exact (SourceCurrentConjunctionDemandWorker.explore_empty p h _ _ _ _ _ impossible).trans
        (later.2 p h (Nat.le_trans (projection_mono alphabet
          (SourceCurrentConjunctionTupleWorklistResources.forecast_mono alphabet _ (by simp) (Nat.le_refl resource))) enoughP)
          (Nat.le_trans (SourceCurrentProjectionUnionResources.readFuel_mono
            (SourceCurrentConjunctionTupleWorklistResources.forecast_mono alphabet _ (by simp) (Nat.le_refl resource))) enoughH))
  | skip nonempty fresh rest ih =>
      have later := ih resource ready (fun nodes member => available nodes (List.mem_cons_of_mem _ member)) fits
        (fun nodes member => widths nodes (List.mem_cons_of_mem _ member)) known budgetLe
      refine ⟨later.1.mono (SourceCurrentConjunctionTupleWorklistResources.forecast_mono alphabet _
        (by simp) (Nat.le_refl resource)), ?_⟩
      intro p h enoughP enoughH
      exact (SourceCurrentConjunctionDemandWorker.explore_skip p h _ _ _ _ _ nonempty fresh).trans
        (later.2 p h (Nat.le_trans (projection_mono alphabet
          (SourceCurrentConjunctionTupleWorklistResources.forecast_mono alphabet _ (by simp) (Nat.le_refl resource))) enoughP)
          (Nat.le_trans (SourceCurrentProjectionUnionResources.readFuel_mono
            (SourceCurrentConjunctionTupleWorklistResources.forecast_mono alphabet _ (by simp) (Nat.le_refl resource))) enoughH))
  | @overflow budget table nodes before middle pending final after nonempty fresh admission rest ih =>
      have admitted := SourceCurrentConjunctionEmptinessTable.admitted key closed budget table nodes fresh
      have inputs := available nodes List.mem_cons_self
      have noFree := SourceCurrentConjunctionWorklist.closed_values nodes admitted.2.1
      have effects := admission.effects ready inputs noFree
      have guards := admission_known admission alphabet ready inputs noFree known
      have numeric := SourceCurrentConjunctionDemandNumeric.bound admission alphabet resource ready inputs noFree fits
        (widths nodes List.mem_cons_self) known
      simp only [SourceCurrentConjunctionDemandNumeric.seed, Nat.max_eq_left budgetLe] at numeric
      have later := ih (step alphabet resource) effects.ready
        (fun group member value included => effects.keeps.available value
          (available group (List.mem_cons_of_mem _ member) value included)) numeric.1
        (fun group member => Nat.le_trans (widths group (List.mem_cons_of_mem _ member)) (step_grows alphabet resource))
        guards (Nat.zero_le _)
      have ceiling : oldForecast alphabet 0 pending.length (step alphabet resource) ≤
          oldForecast alphabet budget (nodes :: pending).length resource := by
        simpa only [SourceCurrentConjunctionTupleWorklistResources.forecast,
          SourceCurrentConjunctionTupleWorklistResources.Numeric.envelope, List.length_cons] using
          SourceCurrentConjunctionTupleWorklistResources.step_le_forecast alphabet admitted.1 pending.length resource
      have current := SourceCurrentConjunctionTupleWorklistResources.step_le_forecast alphabet admitted.1 pending.length resource
      refine ⟨later.1.mono ceiling, ?_⟩
      intro p h enoughP enoughH
      have first := numeric.2 p h
        (Nat.le_trans (projection_mono alphabet
          (SourceCurrentConjunctionTupleWorklistResources.forecast_ge alphabet budget (nodes :: pending).length resource)) enoughP)
        (Nat.le_trans (SourceCurrentProjectionUnionResources.readFuel_mono current) enoughH)
      exact (SourceCurrentConjunctionDemandWorker.explore_overflow p h _ _ _ _ _ _ nonempty fresh first).trans
        (later.2 p h (Nat.le_trans (projection_mono alphabet ceiling) enoughP)
          (Nat.le_trans (SourceCurrentProjectionUnionResources.readFuel_mono ceiling) enoughH))
  | @zero budget table nodes before middle pending final after nonempty fresh admission rest ih =>
      have admitted := SourceCurrentConjunctionEmptinessTable.admitted key closed budget table nodes fresh
      have inputs := available nodes List.mem_cons_self
      have noFree := SourceCurrentConjunctionWorklist.closed_values nodes admitted.2.1
      have effects := admission.effects ready inputs noFree
      have guards := admission_known admission alphabet ready inputs noFree known
      have numeric := SourceCurrentConjunctionDemandNumeric.bound admission alphabet resource ready inputs noFree fits
        (widths nodes List.mem_cons_self) known
      simp only [SourceCurrentConjunctionDemandNumeric.seed, Nat.max_eq_left budgetLe] at numeric
      have later := ih (step alphabet resource) effects.ready
        (fun group member value included => effects.keeps.available value
          (available group (List.mem_cons_of_mem _ member) value included)) numeric.1
        (fun group member => Nat.le_trans (widths group (List.mem_cons_of_mem _ member)) (step_grows alphabet resource))
        guards (Nat.le_trans budgetLe (step_grows alphabet resource))
      have ceiling : oldForecast alphabet budget pending.length (step alphabet resource) ≤
          oldForecast alphabet budget (nodes :: pending).length resource := by
        simpa only [List.length_cons] using
          SourceCurrentConjunctionTupleWorklistResources.forecast_zero alphabet admitted.1 pending.length resource
      have current := SourceCurrentConjunctionTupleWorklistResources.step_le_forecast alphabet admitted.1 pending.length resource
      refine ⟨later.1.mono ceiling, ?_⟩
      intro p h enoughP enoughH
      have first := numeric.2 p h
        (Nat.le_trans (projection_mono alphabet
          (SourceCurrentConjunctionTupleWorklistResources.forecast_ge alphabet budget (nodes :: pending).length resource)) enoughP)
        (Nat.le_trans (SourceCurrentProjectionUnionResources.readFuel_mono current) enoughH)
      exact (SourceCurrentConjunctionDemandWorker.explore_zero p h _ _ _ _ _ _ nonempty fresh first).trans
        (later.2 p h (Nat.le_trans (projection_mono alphabet ceiling) enoughP)
          (Nat.le_trans (SourceCurrentProjectionUnionResources.readFuel_mono ceiling) enoughH))
  | @positive budget table nodes before predecessor requirements middle pending final after nonempty fresh admission rest ih =>
      have admitted := SourceCurrentConjunctionEmptinessTable.admitted key closed budget table nodes fresh
      have inputs := available nodes List.mem_cons_self
      have noFree := SourceCurrentConjunctionWorklist.closed_values nodes admitted.2.1
      have effects := admission.verified ready inputs noFree
      have guards := admission_known admission alphabet ready inputs noFree known
      have numeric := SourceCurrentConjunctionDemandNumeric.bound admission alphabet resource ready inputs noFree fits
        (widths nodes List.mem_cons_self) known
      have generated := SourceCurrentConjunctionDemandNumeric.positive_generated admission alphabet resource ready inputs noFree fits
        (widths nodes List.mem_cons_self) known
      simp only [SourceCurrentConjunctionDemandNumeric.seed, Nat.max_eq_left budgetLe] at numeric generated
      have rowWidths := positive_widths admission alphabet resource ready inputs noFree fits
        (widths nodes List.mem_cons_self) known
      have charged := admission.positive_charge
      have nextAvailable : PendingReady middle (requirements.flatten ++ pending) := by
        intro group member
        rcases List.mem_append.mp member with added | old
        · obtain ⟨row, included, present⟩ := List.mem_flatten.mp added
          exact (effects.2 row included group present).1
        · exact fun value included => effects.1.keeps.available value
            (available group (List.mem_cons_of_mem _ old) value included)
      have nextWidths : ∀ group ∈ requirements.flatten ++ pending, group.length ≤ step alphabet resource := by
        intro group member
        rcases List.mem_append.mp member with added | old
        · obtain ⟨row, included, present⟩ := List.mem_flatten.mp added
          exact rowWidths row included group present
        · exact Nat.le_trans (widths group (List.mem_cons_of_mem _ old)) (step_grows alphabet resource)
      have later := ih (step alphabet resource) effects.1.ready nextAvailable numeric.1 nextWidths guards
        (Nat.le_trans (Nat.sub_le _ _) (Nat.le_trans budgetLe (step_grows alphabet resource)))
      have ceiling : oldForecast alphabet (budget - (predecessor + 1))
          (requirements.flatten ++ pending).length (step alphabet resource) ≤
          oldForecast alphabet budget (nodes :: pending).length resource := by
        simpa only [List.length_append, List.length_cons] using
          SourceCurrentConjunctionTupleWorklistResources.forecast_positive alphabet charged.1 charged.2 pending.length resource generated
      have current := SourceCurrentConjunctionTupleWorklistResources.step_le_forecast alphabet admitted.1 pending.length resource
      refine ⟨later.1.mono ceiling, ?_⟩
      intro p h enoughP enoughH
      have first := numeric.2 p h
        (Nat.le_trans (projection_mono alphabet
          (SourceCurrentConjunctionTupleWorklistResources.forecast_ge alphabet budget (nodes :: pending).length resource)) enoughP)
        (Nat.le_trans (SourceCurrentProjectionUnionResources.readFuel_mono current) enoughH)
      exact (SourceCurrentConjunctionDemandWorker.explore_positive p h _ _ _ _ _ _ _ _ nonempty fresh first).trans
        (later.2 p h (Nat.le_trans (projection_mono alphabet ceiling) enoughP)
          (Nat.le_trans (SourceCurrentProjectionUnionResources.readFuel_mono ceiling) enoughH))

/-- Initial scalar and budget bound the same complete actual worklist and its uniform replay. -/
theorem bound {budget : Nat} {table final : Table Symbol Formula} {pending : List (List Node)}
    {before after : Physical Symbol Formula} (actual : Run budget table pending before final after)
    (alphabet : List Guard) (resource : Nat) (ready : Ready before) (available : PendingReady before pending)
    (fits : Fits resource before.heap) (widths : ∀ nodes ∈ pending, nodes.length ≤ resource)
    (known : AnnotationHeap (fun guard => guard ∈ alphabet) before.heap) :
    Fits (forecast alphabet budget pending.length resource) after.heap ∧
      ∀ p h, workerFuel alphabet budget pending.length resource ≤ p → readerFuel alphabet budget pending.length resource ≤ h →
        SourceCurrentConjunctionDemandWorker.explore p h budget table pending before = .done final after :=
  bound_core actual alphabet (max resource budget) ready available (fits.mono (Nat.le_max_left _ _))
    (fun nodes member => Nat.le_trans (widths nodes member) (Nat.le_max_left _ _)) known (Nat.le_max_right _ _)

/-- The original heap derives its own fixed guard alphabet for numeric replay. -/
theorem initial_bound {budget : Nat} {table final : Table Symbol Formula} {pending : List (List Node)}
    {before after : Physical Symbol Formula} (actual : Run budget table pending before final after)
    (resource : Nat) (ready : Ready before) (available : PendingReady before pending)
    (fits : Fits resource before.heap) (widths : ∀ nodes ∈ pending, nodes.length ≤ resource) :
    Fits (forecast (SourceCurrentConjunctionGuardUniverse.guards before.heap) budget pending.length resource) after.heap ∧
      ∀ p h, workerFuel (SourceCurrentConjunctionGuardUniverse.guards before.heap) budget pending.length resource ≤ p →
        readerFuel (SourceCurrentConjunctionGuardUniverse.guards before.heap) budget pending.length resource ≤ h →
        SourceCurrentConjunctionDemandWorker.explore p h budget table pending before = .done final after :=
  bound actual _ resource ready available fits widths
    (SourceCurrentConjunctionGuardUniverse.initial before.heap ready.semantic.ready.semantic.1.normal.facts)

private theorem run_initial (budget : Nat) (table : Table Symbol Formula) (pending : List (List Node))
    (before : Physical Symbol Formula) (ready : Ready before) (stored : TableReady before table)
    (available : PendingReady before pending) :
    ∃ final after, Run budget table pending before final after ∧ Effects before after ∧ TableReady after final := by
  induction budget using Nat.strongRecOn generalizing table pending before with
  | ind budget smaller =>
      induction pending generalizing table before with
      | nil => exact ⟨table, before, .done, Effects.refl before ready, stored⟩
      | cons nodes rest tail =>
          have tailAvailable : PendingReady before rest := fun group member => available group (List.mem_cons_of_mem _ member)
          cases impossible : nodes.any isEmpty with
          | true =>
              obtain ⟨final, after, actual, effects, returned⟩ := tail table before ready stored tailAvailable
              exact ⟨final, after, .empty impossible actual, effects, returned⟩
          | false =>
              cases skipped : SourceCurrentConjunctionEmptinessTable.skip key closed budget table nodes with
              | true =>
                  obtain ⟨final, after, actual, effects, returned⟩ := tail table before ready stored tailAvailable
                  exact ⟨final, after, .skip impossible skipped actual, effects, returned⟩
              | false =>
                  have admitted := SourceCurrentConjunctionEmptinessTable.admitted key closed budget table nodes skipped
                  have inputs := available nodes List.mem_cons_self
                  have noFree := SourceCurrentConjunctionWorklist.closed_values nodes admitted.2.1
                  obtain ⟨result, middle, ⟨p, h, stable⟩, kept, rows⟩ :=
                    SourceCurrentConjunctionDemandCompletion.admission_complete budget nodes before ready inputs noFree
                  have admission := SourceCurrentConjunctionDemandExecution.admission_graph (stable p h (Nat.le_refl _) (Nat.le_refl _))
                  have oldTable := SourceCurrentConjunctionWorklist.table_keeps kept.keeps stored
                  have oldPending := SourceCurrentConjunctionWorklist.pending_keeps kept.keeps tailAvailable
                  cases result with
                  | overflow =>
                      obtain ⟨final, after, actual, later, returned⟩ :=
                        smaller 0 admitted.1 table rest middle kept.ready oldTable oldPending
                      exact ⟨final, after, .overflow impossible skipped admission actual, kept.trans later, returned⟩
                  | zero =>
                      have nextTable : TableReady middle (⟨nodes, []⟩ :: table) := by
                        intro entry member
                        rcases List.mem_cons.mp member with rfl | member
                        · exact ⟨fun value included => kept.keeps.available value (inputs value included), noFree,
                            impossible, by intro row absent; cases absent⟩
                        · exact oldTable entry member
                      obtain ⟨final, after, actual, later, returned⟩ :=
                        tail (⟨nodes, []⟩ :: table) middle kept.ready nextTable oldPending
                      exact ⟨final, after, .zero impossible skipped admission actual, kept.trans later, returned⟩
                  | positive predecessor requirements =>
                      have charged := admission.positive_charge
                      have nextTable : TableReady middle (⟨nodes, requirements⟩ :: table) := by
                        intro entry member
                        rcases List.mem_cons.mp member with rfl | member
                        · exact ⟨fun value included => kept.keeps.available value (inputs value included), noFree, impossible, rows⟩
                        · exact oldTable entry member
                      have nextPending : PendingReady middle (requirements.flatten ++ rest) := by
                        intro group member
                        rcases List.mem_append.mp member with added | old
                        · obtain ⟨row, present, included⟩ := List.mem_flatten.mp added
                          exact (rows row present group included).1
                        · exact oldPending group old
                      obtain ⟨final, after, actual, later, returned⟩ :=
                        smaller (budget - (predecessor + 1)) (by omega)
                          (⟨nodes, requirements⟩ :: table) (requirements.flatten ++ rest) middle kept.ready nextTable nextPending
                      exact ⟨final, after, .positive impossible skipped admission actual, kept.trans later, returned⟩

/-- Initial ready operands construct the actual worklist and its computed common ceilings. -/
theorem entered (budget : Nat) (pending : List (List Node)) (before : Physical Symbol Formula)
    (resource : Nat) (ready : Ready before) (available : PendingReady before pending)
    (fits : Fits resource before.heap) (widths : ∀ nodes ∈ pending, nodes.length ≤ resource) :
    ∃ final after, Run budget [] pending before final after ∧ Effects before after ∧ TableReady after final ∧
      Fits (forecast (SourceCurrentConjunctionGuardUniverse.guards before.heap) budget pending.length resource) after.heap ∧
      ∀ p h, workerFuel (SourceCurrentConjunctionGuardUniverse.guards before.heap) budget pending.length resource ≤ p →
        readerFuel (SourceCurrentConjunctionGuardUniverse.guards before.heap) budget pending.length resource ≤ h →
        SourceCurrentConjunctionDemandWorker.explore p h budget [] pending before = .done final after := by
  obtain ⟨final, after, actual, effects, stored⟩ := run_initial budget [] pending before ready
    (by intro entry absent; cases absent) available
  exact ⟨final, after, actual, effects, stored, initial_bound actual resource ready available fits widths⟩

variable [DecidableEq (Value Symbol (SourceSymbolicIndex.Constraint Formula))]

/-- The original singleton query and final table length determine the exact decision replay. -/
theorem decision_bound {budget : Nat} {start : Node} {before after : Physical Symbol Formula} {answer : Bool}
    (actual : Decision budget start before answer after) (alphabet : List Guard) (resource : Nat)
    (ready : Ready before) (available : Available before.heap start) (fits : Fits resource before.heap)
    (known : AnnotationHeap (fun guard => guard ∈ alphabet) before.heap) :
    Fits (forecast alphabet budget 1 resource) after.heap ∧
      ∀ p h, workerFuel alphabet budget 1 resource ≤ p → readerFuel alphabet budget 1 resource ≤ h →
        SourceCurrentConjunctionDemandWorker.decision p h budget start before = .done answer after := by
  cases actual with
  | open_input isOpen =>
      exact ⟨fits.mono (forecast_ge alphabet _ _ _),
        by intro p h _ _; exact SourceCurrentConjunctionDemandWorker.decision_open p h _ _ _ isOpen⟩
  | closed isClosed explored grown =>
      have inputs : PendingReady before [[start]] := by
        intro nodes member value included
        cases List.mem_singleton.mp member
        cases List.mem_singleton.mp included
        exact available
      have widths : ∀ nodes ∈ [[start]], nodes.length ≤ resource := by
        intro nodes member
        cases List.mem_singleton.mp member
        exact fits.stored.positive
      have numeric := bound explored alphabet resource ready inputs fits widths known
      refine ⟨numeric.1, ?_⟩
      intro p h enoughP enoughH
      exact SourceCurrentConjunctionDemandWorker.decision_closed_done p h _ _ _ _ _ _ isClosed
        (numeric.2 p h enoughP enoughH) grown

private theorem decision_initial (budget : Nat) (start : Node) (before : Physical Symbol Formula)
    (ready : Ready before) (available : Available before.heap start) :
    ∃ answer after, Decision budget start before answer after ∧ Effects before after := by
  cases admitted : closed start with
  | false =>
      have actual : Decision budget start before false before := .open_input admitted
      exact ⟨false, before, actual, Effects.refl _ ready⟩
  | true =>
      have inputs : PendingReady before [[start]] := by
        intro nodes member value included
        cases List.mem_singleton.mp member
        cases List.mem_singleton.mp included
        exact available
      obtain ⟨table, after, explored, kept, _stored⟩ := run_initial budget [] [[start]] before ready
        (by intro entry absent; cases absent) inputs
      have grown := SourceCurrentConjunctionEmptinessTable.grow_rounds_complete .empty key closed table table.length 0 (by omega)
      have actual : Decision budget start before _ after := .closed admitted explored grown
      exact ⟨_, after, actual, kept⟩

/-- Current input facts derive the complete decision with its actual final table fixed point. -/
theorem decision_complete (budget : Nat) (start : Node) (before : Physical Symbol Formula)
    (resource : Nat) (ready : Ready before) (available : Available before.heap start) (fits : Fits resource before.heap) :
    ∃ answer after, Decision budget start before answer after ∧ Effects before after ∧
      Fits (forecast (SourceCurrentConjunctionGuardUniverse.guards before.heap) budget 1 resource) after.heap ∧
      ∀ p h, workerFuel (SourceCurrentConjunctionGuardUniverse.guards before.heap) budget 1 resource ≤ p →
        readerFuel (SourceCurrentConjunctionGuardUniverse.guards before.heap) budget 1 resource ≤ h →
        SourceCurrentConjunctionDemandWorker.decision p h budget start before = .done answer after := by
  obtain ⟨answer, after, actual, effects⟩ := decision_initial budget start before ready available
  exact ⟨answer, after, actual, effects, decision_bound actual _ resource ready available fits
    (SourceCurrentConjunctionGuardUniverse.initial before.heap ready.semantic.ready.semantic.1.normal.facts)⟩

end Generic

section Concrete
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "Memo" => SourceCurrentEmptinessMemo.Memo
open SourceCurrentConjunctionDemandWorklistExecution (Call)
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Node]

/-- Warm hits and actual misses use the same original singleton-query numeric ceilings. -/
theorem call_bound {budget : Nat} {memo saved : Memo} {query : Node}
    {before after : Physical Symbol FullSyntax.Formula} {answer : Bool}
    (actual : Call budget memo query before answer after saved) (alphabet : List Guard) (resource : Nat)
    (ready : Ready before) (available : Available before.heap query) (fits : Fits resource before.heap)
    (known : SourceEqualityAnnotationHeap.Heap (fun guard => guard ∈ alphabet) before.heap) :
    Fits (forecast alphabet budget 1 resource) after.heap ∧
      ∀ p h, workerFuel alphabet budget 1 resource ≤ p → readerFuel alphabet budget 1 resource ≤ h →
        SourceCurrentConjunctionDemandWorker.call p h budget memo query before = .done (answer, saved) after := by
  cases actual with
  | hit found =>
      exact ⟨fits.mono (forecast_ge alphabet _ _ _),
        by intro p h _ _; exact SourceCurrentConjunctionDemandWorker.call_hit p h _ _ _ _ _ _ found⟩
  | miss absent actual =>
      have numeric := decision_bound actual alphabet resource ready available fits known
      refine ⟨numeric.1, ?_⟩
      intro p h enoughP enoughH
      simp only [SourceCurrentConjunctionDemandWorker.call, absent, numeric.2 p h enoughP enoughH, Outcome.bind]

/-- Current readiness derives a complete memo call without numeric resource premises. -/
theorem call_initial (budget : Nat) (memo : Memo) (query : Node) (before : Physical Symbol FullSyntax.Formula)
    (ready : Ready before) (available : Available before.heap query) :
    ∃ answer after saved, Call budget memo query before answer after saved ∧ Effects before after := by
  cases found : memo query.referenceOf with
  | some entry =>
      rcases entry with ⟨original, answer⟩
      have actual : Call budget memo query before answer before memo := .hit found
      exact ⟨answer, before, memo, actual, Effects.refl _ ready⟩
  | none =>
      obtain ⟨answer, after, decision, effects⟩ := decision_initial budget query before ready available
      have actual : Call budget memo query before answer after (SourceCurrentEmptinessMemo.insert memo query answer) :=
        .miss found decision
      exact ⟨answer, after, _, actual, effects⟩

/-- Initial query state derives its own complete memo call and stable numeric replay. -/
theorem call_complete (budget : Nat) (memo : Memo) (query : Node) (before : Physical Symbol FullSyntax.Formula)
    (resource : Nat) (ready : Ready before) (available : Available before.heap query) (fits : Fits resource before.heap) :
    ∃ answer after saved, Call budget memo query before answer after saved ∧ Effects before after ∧
      Fits (forecast (SourceCurrentConjunctionGuardUniverse.guards before.heap) budget 1 resource) after.heap ∧
      ∀ p h, workerFuel (SourceCurrentConjunctionGuardUniverse.guards before.heap) budget 1 resource ≤ p →
        readerFuel (SourceCurrentConjunctionGuardUniverse.guards before.heap) budget 1 resource ≤ h →
        SourceCurrentConjunctionDemandWorker.call p h budget memo query before = .done (answer, saved) after := by
  obtain ⟨answer, after, saved, actual, effects⟩ := call_initial budget memo query before ready available
  exact ⟨answer, after, saved, actual, effects, call_bound actual _ resource ready available fits
    (SourceCurrentConjunctionGuardUniverse.initial before.heap ready.semantic.ready.semantic.1.normal.facts)⟩
end Concrete
end MicroCFTA.SourceCurrentConjunctionDemandWorklistNumeric
