import MicroCFTA.SourceCurrentAllocatedPrimaryCompletion
import MicroCFTA.SourceCurrentConjunctionClassScan

/-!
# Literal current class gates in the checked state

Each worker executes its actual bounded class gate. Success advances only
the constructor heap. Failure retains the complete source observation and
its returned heap. The native tables, domains, and equality operations stay
in the same checked state. Memo reads are separate proof receipts.
-/
namespace MicroCFTA.SourceCurrentAllocatedGateWorker
open InternedConstructorTemplates InternedProbeProvenance EqualityNormalize
open InternedNestedProvenance (Values)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Raw" => InternedNestedConstruction.Outcome Symbol Guard (Option Bool)
local notation "source" => SourceMemoGate.unconstrained
local notation "reaches" => SourceEndpointReachability.reaches source
local notation "advanceHeap" => SourceCurrentConjunctionClassScan.advanceHeap

/-- A failed gate retains its mode and complete source observation. -/
inductive Fault where
  | primary (observation : Raw)
  | secondary (observation : Raw)

/-- Both outcomes retain the full checked state at the returned constructor heap. -/
inductive Outcome (width : Nat) : Type 1 where
  | done (answer : Bool) (state : Checked width)
  | failed (fault : Fault) (state : Checked width)

def Outcome.state : Outcome width → Checked width
  | .done _ state | .failed _ state => state

/-- A complete answer succeeds. An unfinished observation keeps its exact source payload. -/
def lift (tag : Raw → Fault) (before : Checked width) : Raw → Outcome width
  | .done (some answer) heap => .done answer (advanceHeap before heap)
  | .done none heap => .failed (tag (.done none heap)) (advanceHeap before heap)
  | .pending key heap => .failed (tag (.pending key heap)) (advanceHeap before heap)

/-- Execute the enabled primary class gate before any secondary query. -/
noncomputable def primary [DecidableEq (EdgeKey Symbol Guard)] (fuel : Nat)
    (values : List (Value Symbol Guard)) (paths : Class) (before : Checked width) : Outcome width :=
  lift .primary before (SourceCurrentMuEndpoint.classMeets true source reaches fuel
    values paths before.native.machine.heap)

/-- Execute the current secondary class gate with its closed constrained-Mu endpoint rule. -/
noncomputable def secondary [DecidableEq (EdgeKey Symbol Guard)] (fuel : Nat)
    (values : List (Value Symbol Guard)) (paths : Class) (before : Checked width) : Outcome width :=
  lift .secondary before (SourceCurrentMuEndpoint.classMeets false source reaches fuel
    values paths before.native.machine.heap)

private theorem lift_done {tag : Raw → Fault} {before after : Checked width}
    {observation : Raw} {answer : Bool} (actual : lift tag before observation = .done answer after) :
    ∃ heap, observation = .done (some answer) heap ∧ after = advanceHeap before heap := by
  cases observation with
  | pending key heap => cases actual
  | done result heap =>
      cases result with
      | none => cases actual
      | some value => cases actual; exact ⟨heap, rfl, rfl⟩

variable [DecidableEq (EdgeKey Symbol Guard)] {width : Nat}

/-- A supplied primary success exposes its literal source call and complete checked return. -/
theorem primary_done {fuel : Nat} {values : List (Value Symbol Guard)} {paths : Class}
    {before after : Checked width} {answer : Bool}
    (actual : primary fuel values paths before = .done answer after) :
    SourceCurrentMuEndpoint.classMeets true source reaches fuel values paths before.native.machine.heap =
      .done (some answer) after.native.machine.heap ∧
      after = advanceHeap before after.native.machine.heap := by
  obtain ⟨heap, returned, rfl⟩ := lift_done actual
  exact ⟨returned, rfl⟩

/-- A supplied secondary success exposes its literal source call and complete checked return. -/
theorem secondary_done {fuel : Nat} {values : List (Value Symbol Guard)} {paths : Class}
    {before after : Checked width} {answer : Bool}
    (actual : secondary fuel values paths before = .done answer after) :
    SourceCurrentMuEndpoint.classMeets false source reaches fuel values paths before.native.machine.heap =
      .done (some answer) after.native.machine.heap ∧
      after = advanceHeap before after.native.machine.heap := by
  obtain ⟨heap, returned, rfl⟩ := lift_done actual
  exact ⟨returned, rfl⟩

/-- The enabled source equivalence derives the primary graph at the supplied return heap. -/
theorem primary_graph {fuel : Nat} {values : List (Value Symbol Guard)} {paths : Class}
    {before after : Checked width} {answer : Bool}
    (actual : primary fuel values paths before = .done answer after) :
    EndpointStatefulGateTrace.ClassTrace source reaches values paths before.native.machine.heap
      answer after.native.machine.heap :=
  EndpointStatefulGateTrace.class_trace_of_done source reaches fuel values paths _ answer _
    (by simpa only [SourceCurrentMuEndpoint.primary_class] using (primary_done actual).1)

/-- The actual current secondary equivalence derives its graph at the supplied return heap. -/
theorem secondary_graph {fuel : Nat} {values : List (Value Symbol Guard)} {paths : Class}
    {before after : Checked width} {answer : Bool}
    (actual : secondary fuel values paths before = .done answer after) :
    SourceCurrentSecondaryTrace.ClassTrace source values paths before.native.machine.heap
      answer after.native.machine.heap :=
  SourceCurrentSecondaryTrace.actual_current_class_trace_of_done source reaches fuel values paths _ answer _
    (secondary_done actual).1

/-- More primary fuel retains every completed answer and the entire checked state. -/
theorem primary_done_stable {fuel larger : Nat} {values : List (Value Symbol Guard)} {paths : Class}
    {before after : Checked width} {answer : Bool}
    (actual : primary fuel values paths before = .done answer after) (enough : fuel ≤ larger) :
    primary larger values paths before = .done answer after := by
  have first := (primary_done actual).1
  rw [SourceCurrentMuEndpoint.primary_class] at first
  have later := EndpointStatefulGate.class_fuel_stable source reaches fuel (larger - fuel)
    values paths before.native.machine.heap answer after.native.machine.heap first
  rw [Nat.add_sub_of_le enough] at later
  simp only [primary, SourceCurrentMuEndpoint.primary_class, later, lift, (primary_done actual).2.symm]

/-- More secondary fuel retains every completed answer and the entire checked state. -/
theorem secondary_done_stable {fuel larger : Nat} {values : List (Value Symbol Guard)} {paths : Class}
    {before after : Checked width} {answer : Bool}
    (actual : secondary fuel values paths before = .done answer after) (enough : fuel ≤ larger) :
    secondary larger values paths before = .done answer after := by
  have first := (secondary_done actual).1
  rw [SourceCurrentSecondaryTrace.actual_current_class_eq] at first
  have later := SourceCurrentSecondaryTrace.class_fuel_stable source fuel (larger - fuel)
    values paths before.native.machine.heap answer after.native.machine.heap first
  rw [Nat.add_sub_of_le enough] at later
  simp only [secondary, SourceCurrentSecondaryTrace.actual_current_class_eq, later, lift,
    (secondary_done actual).2.symm]

/-- A completed primary graph constructs stable literal execution bounds. -/
theorem primary_complete {values : List (Value Symbol Guard)} {paths : Class}
    {before : Checked width} {answer : Bool} {heap : State Symbol Guard}
    (actual : EndpointStatefulGateTrace.ClassTrace source reaches values paths before.native.machine.heap answer heap) :
    ∃ bound, ∀ fuel, bound ≤ fuel → primary fuel values paths before = .done answer (advanceHeap before heap) := by
  obtain ⟨bound, returned⟩ := EndpointStatefulGateTrace.class_trace_complete source reaches values paths _ answer heap actual
  have done : primary bound values paths before = .done answer (advanceHeap before heap) := by
    simp only [primary, SourceCurrentMuEndpoint.primary_class, returned, lift]
  exact ⟨bound, fun fuel enough => primary_done_stable done enough⟩

/-- A completed current secondary graph constructs stable literal execution bounds. -/
theorem secondary_complete {values : List (Value Symbol Guard)} {paths : Class}
    {before : Checked width} {answer : Bool} {heap : State Symbol Guard}
    (actual : SourceCurrentSecondaryTrace.ClassTrace source values paths before.native.machine.heap answer heap) :
    ∃ bound, ∀ fuel, bound ≤ fuel → secondary fuel values paths before = .done answer (advanceHeap before heap) := by
  obtain ⟨bound, returned⟩ := SourceCurrentSecondaryTrace.actual_current_class_trace_complete source reaches
    values paths _ answer heap actual
  have done : secondary bound values paths before = .done answer (advanceHeap before heap) := by
    simp only [secondary, returned, lift]
  exact ⟨bound, fun fuel enough => secondary_done_stable done enough⟩

/-- Any two primary successes return the same answer and full checked state. -/
theorem primary_done_unique {fuel larger : Nat} {values : List (Value Symbol Guard)} {paths : Class}
    {before after later : Checked width} {first second : Bool}
    (one : primary fuel values paths before = .done first after)
    (two : primary larger values paths before = .done second later) : first = second ∧ after = later := by
  have left := primary_done_stable one (Nat.le_max_left fuel larger)
  have right := primary_done_stable two (Nat.le_max_right fuel larger)
  exact Outcome.done.inj (left.symm.trans right)

/-- Any two secondary successes return the same answer and full checked state. -/
theorem secondary_done_unique {fuel larger : Nat} {values : List (Value Symbol Guard)} {paths : Class}
    {before after later : Checked width} {first second : Bool}
    (one : secondary fuel values paths before = .done first after)
    (two : secondary larger values paths before = .done second later) : first = second ∧ after = later := by
  have left := secondary_done_stable one (Nat.le_max_left fuel larger)
  have right := secondary_done_stable two (Nat.le_max_right fuel larger)
  exact Outcome.done.inj (left.symm.trans right)

/-- Actual primary success constructs strict endpoint-indexed reads from initial memo validity. -/
theorem primary_reads {fuel : Nat} {values : List (Value Symbol Guard)} {paths : Class}
    {before after : Checked width} {answer : Bool}
    (actual : primary fuel values paths before = .done answer after)
    (ready : InternedFreshOrdinaryMemoGateTrace.Ready before.native.machine.heap)
    (available : Values before.native.machine.heap values) (memos : EndpointMemoGateTrace.Memos)
    (valid : EndpointMemoGateTrace.Valid before.native.machine.heap memos) :
    ∃ trace : EndpointStatefulGateTrace.ClassTrace source reaches values paths before.native.machine.heap
        answer after.native.machine.heap,
      ∃ saved, SourceCurrentAllocatedPrimaryReads.ClassReads trace memos saved ∧
        EndpointMemoGateTrace.Keeps before.native.machine.heap after.native.machine.heap saved := by
  let trace := primary_graph actual
  obtain ⟨saved, reads, kept⟩ := SourceCurrentAllocatedPrimaryReads.lift_class _ _ _ _ _ trace
    ready available memos valid
  exact ⟨trace, saved, reads, kept⟩

/-- Initial semantic readiness and costs construct a finite primary gate without a completion premise. -/
theorem primary_finite (values : List (Value Symbol Guard)) (paths : Class) (before : Checked width)
    (semantic : SourceEqualityRequiredSemanticCache.SemanticReady before.native.machine.heap)
    (costs : InternedFreshOrdinaryCostHeap.Heap before.native.machine.heap)
    (available : Values before.native.machine.heap values) :
    ∃ answer after bound, ∀ fuel, bound ≤ fuel → primary fuel values paths before = .done answer after := by
  obtain ⟨bound, answer, heap, trace, _⟩ := SourceCurrentClassGateCompletion.primary_class_complete
    source reaches values paths before.native.machine.heap semantic costs available
  obtain ⟨bound, stable⟩ := primary_complete (before := before) trace
  exact ⟨answer, advanceHeap before heap, bound, stable⟩

/-- Initial semantic readiness and costs construct a finite current secondary gate. -/
theorem secondary_finite (values : List (Value Symbol Guard)) (paths : Class) (before : Checked width)
    (semantic : SourceEqualityRequiredSemanticCache.SemanticReady before.native.machine.heap)
    (costs : InternedFreshOrdinaryCostHeap.Heap before.native.machine.heap)
    (available : Values before.native.machine.heap values) :
    ∃ answer after bound, ∀ fuel, bound ≤ fuel → secondary fuel values paths before = .done answer after := by
  obtain ⟨bound, answer, heap, trace, _⟩ := SourceCurrentClassGateCompletion.secondary_class_complete
    source reaches values paths before.native.machine.heap semantic costs available
  obtain ⟨bound, stable⟩ := secondary_complete (before := before) trace
  exact ⟨answer, advanceHeap before heap, bound, stable⟩

end MicroCFTA.SourceCurrentAllocatedGateWorker
