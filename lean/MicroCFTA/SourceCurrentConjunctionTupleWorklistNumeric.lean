import MicroCFTA.SourceCurrentConjunctionTupleAdmissionNumeric
import MicroCFTA.SourceCurrentConjunctionTupleSoundness

/-!
# Original numeric ceilings for actual tuple exploration

One initial forecast supplies the projection and read ceilings for every
actual admission. Each larger pair replays the same worklist and state.
These ceilings bound proof instrumentation. They do not count weighted
work, equality allocations, or native lazy evaluation.
-/
namespace MicroCFTA.SourceCurrentConjunctionTupleWorklistNumeric
open InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open SourceCurrentMemoMergeResourceControl (Fits)
open SourceCurrentConjunctionRowsAllocation (Ready Effects)
open SourceCurrentConjunctionTupleExecution (Admission Run Decision)
open SourceCurrentConjunctionWorklist (PendingReady TableReady closed)
open SourceCurrentConjunctionTupleBounds (shapeThrough)
local notation "forecast" => SourceCurrentConjunctionTupleWorklistResources.forecast
local notation "step" => SourceCurrentConjunctionWorklistResources.step
local notation "projectionFuel" => SourceCurrentConjunctionProjectionResources.workerFuel
local notation "readFuel" => SourceCurrentProjectionUnionResources.readFuel

section Generic
variable {Symbol Formula : Type}
local notation "Guard" => SourceSymbolicIndex.Constraint Formula
local notation "Physical" => SourceCurrentConjunctionRowsAllocation.State Symbol Formula
local notation "Entry" => SourceCurrentConjunctionEmptinessTable.Entry (Value Symbol Guard)

/-- The initial forecast supplies one projection ceiling for the whole queue. -/
noncomputable def workerFuel (alphabet : List Guard) (budget pending resource : Nat) : Nat :=
  projectionFuel (shapeThrough alphabet (forecast alphabet budget pending resource))

/-- The same initial forecast supplies one recursive read ceiling. -/
noncomputable def readerFuel (alphabet : List Guard) (budget pending resource : Nat) : Nat :=
  readFuel (forecast alphabet budget pending resource)

private theorem projection_mono (alphabet : List Guard) {first last : Nat} (increase : first ≤ last) :
    projectionFuel (shapeThrough alphabet first) ≤ projectionFuel (shapeThrough alphabet last) := by
  have shapes := SourceCurrentConjunctionTupleBounds.shapeThrough_mono alphabet increase
  unfold SourceCurrentConjunctionProjectionResources.workerFuel
  omega

private theorem step_grows (alphabet : List Guard) (resource : Nat) : resource ≤ step alphabet resource :=
  Nat.le_trans (Nat.le_succ _) (SourceCurrentConjunctionWorklistResources.step_ge alphabet resource)

variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol (SourceSymbolicIndex.Constraint Formula))]

/-- One initial pair of ceilings replays the complete actual tuple worklist at every larger pair. -/
theorem bound {budget : Nat} {table final : List Entry} {pending : List (List (Value Symbol Guard))}
    {before after : Physical} (actual : Run budget table pending before final after)
    (alphabet : List Guard) (resource : Nat) (ready : Ready before) (available : PendingReady before pending)
    (fits : Fits resource before.heap) (widths : ∀ nodes ∈ pending, nodes.length ≤ resource)
    (known : SourceEqualityAnnotationHeap.Heap (fun guard => guard ∈ alphabet) before.heap) :
    Fits (forecast alphabet budget pending.length resource) after.heap ∧
      ∀ p h, workerFuel alphabet budget pending.length resource ≤ p →
        readerFuel alphabet budget pending.length resource ≤ h →
        SourceCurrentConjunctionTupleWorker.explore p h budget table pending before = .done final after := by
  refine ⟨SourceCurrentConjunctionTupleWorklistResources.bound actual alphabet resource ready available fits widths known, ?_⟩
  induction actual generalizing resource with
  | done => intros; exact SourceCurrentConjunctionTupleWorker.explore_nil _ _ _ _ _
  | empty impossible rest ih =>
      have later := ih resource ready
        (fun nodes member => available nodes (List.mem_cons_of_mem _ member)) fits
        (fun nodes member => widths nodes (List.mem_cons_of_mem _ member)) known
      intro p h enoughP enoughH
      exact (SourceCurrentConjunctionTupleWorker.explore_empty p h _ _ _ _ _ impossible).trans
        (later p h
          (Nat.le_trans (projection_mono alphabet
            (SourceCurrentConjunctionTupleWorklistResources.forecast_mono alphabet _ (by simp) (Nat.le_refl resource))) enoughP)
          (Nat.le_trans (SourceCurrentProjectionUnionResources.readFuel_mono
            (SourceCurrentConjunctionTupleWorklistResources.forecast_mono alphabet _ (by simp) (Nat.le_refl resource))) enoughH))
  | skip nonempty fresh rest ih =>
      have later := ih resource ready
        (fun nodes member => available nodes (List.mem_cons_of_mem _ member)) fits
        (fun nodes member => widths nodes (List.mem_cons_of_mem _ member)) known
      intro p h enoughP enoughH
      exact (SourceCurrentConjunctionTupleWorker.explore_skip p h _ _ _ _ _ nonempty fresh).trans
        (later p h
          (Nat.le_trans (projection_mono alphabet
            (SourceCurrentConjunctionTupleWorklistResources.forecast_mono alphabet _ (by simp) (Nat.le_refl resource))) enoughP)
          (Nat.le_trans (SourceCurrentProjectionUnionResources.readFuel_mono
            (SourceCurrentConjunctionTupleWorklistResources.forecast_mono alphabet _ (by simp) (Nat.le_refl resource))) enoughH))
  | @overflow budget table nodes before middle pending final after nonempty fresh admission rest ih =>
      have admitted := SourceCurrentConjunctionEmptinessTable.admitted
        SourceCurrentConjunctionRequirements.key closed budget table nodes fresh
      have inputs := available nodes List.mem_cons_self
      have noFree := SourceCurrentConjunctionWorklist.closed_values nodes admitted.2.1
      have physical := admission.effects ready inputs noFree
      have numeric := SourceCurrentConjunctionTupleAdmissionNumeric.bound admission alphabet resource
        ready inputs noFree fits (widths nodes List.mem_cons_self) known
      cases admission with
      | overflow reads tooMany =>
          have guards := reads.verified (fun guard => guard ∈ alphabet)
            ready.semantic ready.costs known inputs noFree
          have later := ih (step alphabet resource) physical.ready
            (fun group member value included => physical.keeps.available value
              (available group (List.mem_cons_of_mem _ member) value included)) numeric.1
            (fun group member => Nat.le_trans (widths group (List.mem_cons_of_mem _ member))
              (step_grows alphabet resource)) guards.1.annotations
          intro p h enoughP enoughH
          have initial := SourceCurrentConjunctionTupleWorklistResources.forecast_ge alphabet budget (pending.length + 1) resource
          have schedule := SourceCurrentConjunctionTupleWorklistResources.step_le_forecast alphabet admitted.1 pending.length resource
          have first := numeric.2 p h (Nat.le_trans (projection_mono alphabet initial) enoughP)
            (Nat.le_trans (SourceCurrentProjectionUnionResources.readFuel_mono schedule) enoughH)
          exact (SourceCurrentConjunctionTupleWorker.explore_overflow p h _ _ _ _ _ _ nonempty fresh first).trans
            (later p h (Nat.le_trans (projection_mono alphabet schedule) enoughP)
              (Nat.le_trans (SourceCurrentProjectionUnionResources.readFuel_mono schedule) enoughH))
  | @zero budget table nodes before middle pending final after nonempty fresh admission rest ih =>
      have admitted := SourceCurrentConjunctionEmptinessTable.admitted
        SourceCurrentConjunctionRequirements.key closed budget table nodes fresh
      have inputs := available nodes List.mem_cons_self
      have noFree := SourceCurrentConjunctionWorklist.closed_values nodes admitted.2.1
      have effects := SourceCurrentConjunctionGuardUniverse.rows_heap (fun guard => guard ∈ alphabet)
        admission.zero_rows ready inputs noFree known
      have numeric := SourceCurrentConjunctionTupleAdmissionNumeric.bound admission alphabet resource
        ready inputs noFree fits (widths nodes List.mem_cons_self) known
      have later := ih (step alphabet resource) effects.1.ready
        (fun group member value included => effects.1.keeps.available value
          (available group (List.mem_cons_of_mem _ member) value included)) numeric.1
        (fun group member => Nat.le_trans (widths group (List.mem_cons_of_mem _ member))
          (step_grows alphabet resource)) effects.2.1
      intro p h enoughP enoughH
      have initial := SourceCurrentConjunctionTupleWorklistResources.forecast_ge alphabet budget (pending.length + 1) resource
      have current := SourceCurrentConjunctionTupleWorklistResources.step_le_forecast alphabet admitted.1 pending.length resource
      have schedule := SourceCurrentConjunctionTupleWorklistResources.forecast_zero alphabet admitted.1 pending.length resource
      have first := numeric.2 p h (Nat.le_trans (projection_mono alphabet initial) enoughP)
        (Nat.le_trans (SourceCurrentProjectionUnionResources.readFuel_mono current) enoughH)
      exact (SourceCurrentConjunctionTupleWorker.explore_zero p h _ _ _ _ _ _ nonempty fresh first).trans
        (later p h (Nat.le_trans (projection_mono alphabet schedule) enoughP)
          (Nat.le_trans (SourceCurrentProjectionUnionResources.readFuel_mono schedule) enoughH))
  | @positive budget table nodes before predecessor requirements middle pending final after nonempty fresh admission rest ih =>
      have admitted := SourceCurrentConjunctionEmptinessTable.admitted
        SourceCurrentConjunctionRequirements.key closed budget table nodes fresh
      have inputs := available nodes List.mem_cons_self
      have noFree := SourceCurrentConjunctionWorklist.closed_values nodes admitted.2.1
      have charged := admission.positive_rows
      have effects := SourceCurrentConjunctionGuardUniverse.rows_heap (fun guard => guard ∈ alphabet)
        charged.2 ready inputs noFree known
      have numeric := SourceCurrentConjunctionTupleAdmissionNumeric.bound admission alphabet resource
        ready inputs noFree fits (widths nodes List.mem_cons_self) known
      have rowBounds := SourceCurrentConjunctionRowsResources.bound charged.2 alphabet resource (resource + 1)
        ready inputs noFree (fits.mono (Nat.le_succ _)) (widths nodes List.mem_cons_self) known
      have generated := SourceCurrentConjunctionTupleWorklistResources.positive_generated admission alphabet resource
        ready inputs noFree fits (widths nodes List.mem_cons_self) known
      have nextAvailable : PendingReady middle (requirements.flatten ++ pending) := by
        intro group member
        rcases List.mem_append.mp member with generated | earlier
        · obtain ⟨row, rowIn, groupIn⟩ := List.mem_flatten.mp generated
          exact (effects.2.2 row rowIn group groupIn).1
        · exact fun value included => effects.1.keeps.available value
            (available group (List.mem_cons_of_mem _ earlier) value included)
      have nextWidths : ∀ group ∈ requirements.flatten ++ pending, group.length ≤ step alphabet resource := by
        intro group member
        rcases List.mem_append.mp member with generated | earlier
        · obtain ⟨row, rowIn, groupIn⟩ := List.mem_flatten.mp generated
          exact rowBounds.2.1 row rowIn group groupIn
        · exact Nat.le_trans (widths group (List.mem_cons_of_mem _ earlier)) (step_grows alphabet resource)
      have later := ih (step alphabet resource) effects.1.ready nextAvailable numeric.1 nextWidths effects.2.1
      intro p h enoughP enoughH
      have initial := SourceCurrentConjunctionTupleWorklistResources.forecast_ge alphabet budget (pending.length + 1) resource
      have current := SourceCurrentConjunctionTupleWorklistResources.step_le_forecast alphabet admitted.1 pending.length resource
      have schedule := SourceCurrentConjunctionTupleWorklistResources.forecast_positive alphabet
        (by omega : 0 < predecessor + 1) charged.1 pending.length resource generated
      have first := numeric.2 p h (Nat.le_trans (projection_mono alphabet initial) enoughP)
        (Nat.le_trans (SourceCurrentProjectionUnionResources.readFuel_mono current) enoughH)
      have pendingBound : forecast alphabet (budget - (predecessor + 1))
          (requirements.flatten ++ pending).length (step alphabet resource) ≤
          forecast alphabet budget (pending.length + 1) resource := by
        simpa only [List.length_append] using schedule
      have laterDone := later p h
        (Nat.le_trans (projection_mono alphabet pendingBound) enoughP)
        (Nat.le_trans (SourceCurrentProjectionUnionResources.readFuel_mono pendingBound) enoughH)
      exact (SourceCurrentConjunctionTupleWorker.explore_positive p h _ _ _ _ _ _ _ _ nonempty fresh first).trans laterDone

/-- The initial physical heap supplies the fixed guard alphabet for uniform replay. -/
theorem initial_bound {budget : Nat} {table final : List Entry} {pending : List (List (Value Symbol Guard))}
    {before after : Physical} (actual : Run budget table pending before final after)
    (resource : Nat) (ready : Ready before) (available : PendingReady before pending)
    (fits : Fits resource before.heap) (widths : ∀ nodes ∈ pending, nodes.length ≤ resource) :
    Fits (forecast (SourceCurrentConjunctionGuardUniverse.guards before.heap) budget pending.length resource) after.heap ∧
      ∀ p h, workerFuel (SourceCurrentConjunctionGuardUniverse.guards before.heap) budget pending.length resource ≤ p →
        readerFuel (SourceCurrentConjunctionGuardUniverse.guards before.heap) budget pending.length resource ≤ h →
        SourceCurrentConjunctionTupleWorker.explore p h budget table pending before = .done final after :=
  bound actual _ resource ready available fits widths
    (SourceCurrentConjunctionGuardUniverse.initial before.heap ready.semantic.ready.semantic.1.normal.facts)

/-- Initial ready operands derive a complete worklist with the original numeric ceilings. -/
theorem entered (budget : Nat) (pending : List (List (Value Symbol Guard))) (before : Physical)
    (resource : Nat) (ready : Ready before) (available : PendingReady before pending)
    (fits : Fits resource before.heap) (widths : ∀ nodes ∈ pending, nodes.length ≤ resource) :
    ∃ final after, Run budget [] pending before final after ∧ Effects before after ∧ TableReady after final ∧
      Fits (forecast (SourceCurrentConjunctionGuardUniverse.guards before.heap) budget pending.length resource) after.heap ∧
      ∀ p h, workerFuel (SourceCurrentConjunctionGuardUniverse.guards before.heap) budget pending.length resource ≤ p →
        readerFuel (SourceCurrentConjunctionGuardUniverse.guards before.heap) budget pending.length resource ≤ h →
        SourceCurrentConjunctionTupleWorker.explore p h budget [] pending before = .done final after := by
  obtain ⟨final, after, ⟨p, h, done⟩, effects, table⟩ :=
    SourceCurrentConjunctionTupleWorkerCompletion.entered budget pending before ready available
  have actual := SourceCurrentConjunctionTupleExecution.explore_graph (done p h (Nat.le_refl _) (Nat.le_refl _))
  have numeric := initial_bound actual resource ready available fits widths
  exact ⟨final, after, actual, effects, table, numeric⟩

variable [DecidableEq (Value Symbol (SourceSymbolicIndex.Constraint Formula))]

/-- A decision uses one original pending entry and the actual final table fixed point. -/
theorem decision_bound {budget : Nat} {start : Value Symbol Guard} {before after : Physical} {answer : Bool}
    (actual : Decision budget start before answer after) (alphabet : List Guard) (resource : Nat)
    (ready : Ready before) (available : Available before.heap start) (fits : Fits resource before.heap)
    (known : SourceEqualityAnnotationHeap.Heap (fun guard => guard ∈ alphabet) before.heap) :
    Fits (forecast alphabet budget 1 resource) after.heap ∧
      ∀ p h, workerFuel alphabet budget 1 resource ≤ p → readerFuel alphabet budget 1 resource ≤ h →
        SourceCurrentConjunctionTupleWorker.decision p h budget start before = .done answer after := by
  cases actual with
  | open_input isOpen =>
      exact ⟨fits.mono (SourceCurrentConjunctionTupleWorklistResources.forecast_ge alphabet _ _ _),
        by intro p h _ _; exact SourceCurrentConjunctionTupleWorker.decision_open p h _ _ _ isOpen⟩
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
      exact SourceCurrentConjunctionTupleWorker.decision_closed_done p h _ _ _ _ _ _ isClosed
        (numeric.2 p h enoughP enoughH) grown

/-- Initial ready query state derives its complete decision at every larger numeric ceiling. -/
theorem decision_complete (budget : Nat) (start : Value Symbol Guard) (before : Physical)
    (resource : Nat) (ready : Ready before) (available : Available before.heap start)
    (fits : Fits resource before.heap) :
    ∃ answer after, Decision budget start before answer after ∧ Effects before after ∧
      Fits (forecast (SourceCurrentConjunctionGuardUniverse.guards before.heap) budget 1 resource) after.heap ∧
      ∀ p h, workerFuel (SourceCurrentConjunctionGuardUniverse.guards before.heap) budget 1 resource ≤ p →
        readerFuel (SourceCurrentConjunctionGuardUniverse.guards before.heap) budget 1 resource ≤ h →
        SourceCurrentConjunctionTupleWorker.decision p h budget start before = .done answer after := by
  obtain ⟨answer, after, ⟨p, h, done⟩, effects⟩ :=
    SourceCurrentConjunctionTupleWorkerCompletion.decision_complete budget start before ready available
  have actual := SourceCurrentConjunctionTupleExecution.decision_graph (done p h (Nat.le_refl _) (Nat.le_refl _))
  have numeric := decision_bound actual _ resource ready available fits
    (SourceCurrentConjunctionGuardUniverse.initial before.heap ready.semantic.ready.semantic.1.normal.facts)
  exact ⟨answer, after, actual, effects, numeric⟩

end Generic

section Concrete
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "Physical" => SourceCurrentConjunctionRowsAllocation.State Symbol FullSyntax.Formula
local notation "Memo" => SourceCurrentEmptinessMemo.Memo
open SourceCurrentConjunctionTupleExecution (Call)
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Node]

/-- Both actual memo branches replay with the original singleton-query ceilings. -/
theorem call_bound {budget : Nat} {memo saved : Memo} {query : Node} {before after : Physical} {answer : Bool}
    (actual : Call budget memo query before answer after saved) (alphabet : List Guard) (resource : Nat)
    (ready : Ready before) (available : Available before.heap query) (fits : Fits resource before.heap)
    (known : SourceEqualityAnnotationHeap.Heap (fun guard => guard ∈ alphabet) before.heap) :
    Fits (forecast alphabet budget 1 resource) after.heap ∧
      ∀ p h, workerFuel alphabet budget 1 resource ≤ p → readerFuel alphabet budget 1 resource ≤ h →
        SourceCurrentConjunctionTupleWorker.call p h budget memo query before = .done (answer, saved) after := by
  cases actual with
  | hit found =>
      exact ⟨fits.mono (SourceCurrentConjunctionTupleWorklistResources.forecast_ge alphabet _ _ _),
        by intro p h _ _; exact SourceCurrentConjunctionTupleWorker.call_hit p h _ _ _ _ _ _ found⟩
  | miss absent actual =>
      have numeric := decision_bound actual alphabet resource ready available fits known
      refine ⟨numeric.1, ?_⟩
      intro p h enoughP enoughH
      simp only [SourceCurrentConjunctionTupleWorker.call, absent, numeric.2 p h enoughP enoughH,
        SourceCurrentConjunctionWorker.Outcome.bind]

/-- Initial physical query facts derive the complete concrete memo call and its numeric replay. -/
theorem call_complete (budget : Nat) (memo : Memo) (query : Node) (before : Physical)
    (resource : Nat) (ready : Ready before) (available : Available before.heap query)
    (fits : Fits resource before.heap) :
    ∃ answer after saved, Call budget memo query before answer after saved ∧ Effects before after ∧
      Fits (forecast (SourceCurrentConjunctionGuardUniverse.guards before.heap) budget 1 resource) after.heap ∧
      ∀ p h, workerFuel (SourceCurrentConjunctionGuardUniverse.guards before.heap) budget 1 resource ≤ p →
        readerFuel (SourceCurrentConjunctionGuardUniverse.guards before.heap) budget 1 resource ≤ h →
        SourceCurrentConjunctionTupleWorker.call p h budget memo query before = .done (answer, saved) after := by
  obtain ⟨answer, after, saved, ⟨p, h, done⟩, effects⟩ :=
    SourceCurrentConjunctionTupleWorkerCompletion.call_complete budget memo query before ready available
  have actual := SourceCurrentConjunctionTupleExecution.call_graph (done p h (Nat.le_refl _) (Nat.le_refl _))
  have numeric := call_bound actual _ resource ready available fits
    (SourceCurrentConjunctionGuardUniverse.initial before.heap ready.semantic.ready.semantic.1.normal.facts)
  exact ⟨answer, after, saved, actual, effects, numeric⟩

end Concrete
end MicroCFTA.SourceCurrentConjunctionTupleWorklistNumeric
