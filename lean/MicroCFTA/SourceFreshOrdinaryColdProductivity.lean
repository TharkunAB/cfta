import MicroCFTA.SourceFreshOrdinaryColdGuardedExact
import MicroCFTA.SourceRowsMinimumPublic

/-!
# Actual repaired exposure prechecks and finite minimum lookup

The source first exposes a root and then reads its finite table. A present
minimum gives an accepted term. Exact exposure then supplies a root edge.
An empty edge list therefore cannot suppress a productive minimum.
-/
namespace MicroCFTA.SourceRowsMinimumAdapter
open SourceInternedRows

/-- The raw root-row precheck does not change a present minimum. -/
theorem productive_minimum (raw : List (State × List (Transition Symbol Guard))) (root : State) :
    productiveRows raw root = (minimumSizes raw root).isSome := by
  cases found : minimumSizes raw root with
  | none => simp only [productiveRows, found, Option.isSome_none, Bool.and_false]
  | some size =>
      obtain ⟨term, accepted, _⟩ := ((minimum_exact raw root size).mp found).1
      have yes := (productive_exact raw root).mpr ⟨term, accepted⟩
      simp only [Option.isSome_some, yes]

end MicroCFTA.SourceRowsMinimumAdapter

namespace MicroCFTA.SourceFreshOrdinaryColdProductivity
open Cache Language InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open SourceRecursiveIntersectionSemanticHeap (SemanticHeap)
open SourceFreshOrdinaryColdSharedRows (Trace keys)
open SourcePreparedSharedRows (encode)

/-- Actual root exposure followed by finite cold extraction gives the exact structural productivity callback. -/
theorem prechecked_table [DecidableEq (EdgeKey Symbol Guard)] (state : State Symbol Guard)
    (semantic : SemanticHeap state) (covered : Covered [] state) (heap : InternedOpenDepthReadback.Heap state)
    (guarded : InternedGuardedProbeHeap.Heap state) (budgetHeap : InternedGuardedBudgetProbeHeap.Heap state)
    (value : Value Symbol Guard) (available : Available state value) (closed : value.free = []) :
    ∃ readFuel edges exposed rows final outer inner,
      MergedFreshOrdinaryExposure.nodeEdges readFuel value state = .done edges exposed ∧
      (∀ extra, MergedFreshOrdinaryExposure.nodeEdges (readFuel + extra) value state = .done edges exposed) ∧
      Trace exposed (fun _ => none) [value] rows final ∧
      (∀ largerOuter largerInner, outer ≤ largerOuter → inner ≤ largerInner →
        SourceFreshOrdinaryColdSharedRows.collect largerOuter largerInner exposed (fun _ => none) [value] = .done rows final) ∧
      SemanticHeap final ∧ Covered [] final ∧ InternedOpenDepthReadback.Heap final ∧
      InternedGuardedProbeHeap.Heap final ∧ InternedGuardedBudgetProbeHeap.Heap final ∧
      Grows state final ∧ Extends state.nodes.issued final.nodes.issued ∧
      (∀ meaning ambient term, Accepts (FTAValidation.rowFor (SourceInternedRows.interpretedRows meaning
        (SourceColdSharedRows.table rows (keys final rows) value))) (encode value) term ↔
        InternedGuardedLanguage.meaning meaning ambient value term) ∧
      (∀ ambient,
        (if edges.isEmpty then false else
          (SourceRowsMinimumAdapter.minimumSizes (SourceColdSharedRows.table rows (keys final rows) value) (encode value)).isSome) = true ↔
          ∃ term, InternedGuardedLanguage.meaning (fun _ _ => true) ambient value term) := by
  obtain ⟨readFuel, edges, exposed, read, exposedSemantic, exposedCovered, exposedHeap, firstGrowth, firstHistory, _, _, readStable⟩ :=
    MergedFreshOrdinaryColdTermination.read_closed value state semantic covered heap available closed
  have exposedAvailable := available.grows state exposed firstGrowth firstHistory
  have exposedGuarded : InternedGuardedProbeHeap.Heap exposed := by
    simpa only [read, MergedSourceExposure.Result.state] using
      MergedFreshOrdinaryGuardedEffects.nodeEdges_heap readFuel value state semantic covered guarded available closed
  have exposedBudget : InternedGuardedBudgetProbeHeap.Heap exposed := by
    simpa only [read, MergedSourceExposure.Result.state] using
      MergedFreshOrdinaryBudgetEffects.nodeEdges_heap readFuel value state semantic covered budgetHeap available closed
  obtain ⟨rows, final, outer, inner, trace, finalSemantic, finalCovered, finalHeap, laterGrowth, laterHistory,
      _, _, _, _, domain, stable⟩ :=
    SourceFreshOrdinaryColdSharedRows.cold_table exposed exposedSemantic exposedCovered exposedHeap value exposedAvailable closed
  have inputs : SourceColdSharedRows.Inputs exposed [value] := by
    intro child member; simpa only [List.mem_singleton.mp member] using And.intro exposedAvailable closed
  have finalAvailable := exposedAvailable.grows exposed final laterGrowth laterHistory
  have tableLanguage := SourceFreshOrdinaryColdGuardedExact.trace_table_exact exposed final value rows trace exposedSemantic exposedCovered
    exposedGuarded exposedBudget exposedAvailable closed (keys final rows) domain
  have graphLanguage := SourceFreshOrdinaryColdGuardedExact.trace_graph_exact exposed final value rows trace exposedSemantic exposedCovered
    exposedGuarded exposedBudget exposedAvailable closed
  have exactExposure := (MergedFreshOrdinaryExposureLanguage.nodeEdges_exact readFuel value state semantic covered available edges exposed final
    read laterGrowth finalSemantic finalCovered finalAvailable closed).2
  refine ⟨readFuel, edges, exposed, rows, final, outer, inner, read, readStable, trace, stable,
    finalSemantic, finalCovered, finalHeap, trace.guarded_heap exposedSemantic exposedCovered exposedGuarded inputs,
    trace.budget_heap exposedSemantic exposedCovered exposedBudget inputs, grows_trans firstGrowth laterGrowth,
    extends_trans firstHistory laterHistory, tableLanguage, ?_⟩
  intro ambient
  let raw := SourceColdSharedRows.table rows (keys final rows) value
  have rawLanguage (term : Term Symbol) : Accepts (SourceRowsMinimumAdapter.automaton raw) (encode value) term ↔
      InternedGuardedLanguage.meaning (fun _ _ => true) ambient value term := by
    rw [SourceRowsMinimumPublic.ordinary_readback]
    exact tableLanguage (fun _ _ => true) ambient term
  have minimumExact : (SourceRowsMinimumAdapter.minimumSizes raw (encode value)).isSome = true ↔
      ∃ term, InternedGuardedLanguage.meaning (fun _ _ => true) ambient value term := by
    rw [← SourceRowsMinimumAdapter.productive_minimum, SourceRowsMinimumAdapter.productive_exact]
    simp only [rawLanguage]
  by_cases empty : edges.isEmpty = true
  · simp only [empty, ↓reduceIte, Bool.false_eq_true, false_iff]
    rintro ⟨term, accepted⟩
    have graphAccepted := (graphLanguage (fun _ _ => true) ambient term).mpr accepted
    obtain ⟨edge, member, _⟩ := (exactExposure (fun _ _ => true) term).mp graphAccepted
    rw [List.isEmpty_iff.mp empty] at member
    cases member
  · simp only [empty]
    exact minimumExact

end MicroCFTA.SourceFreshOrdinaryColdProductivity
