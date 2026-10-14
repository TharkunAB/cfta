import MicroCFTA.SourceFreshOrdinaryColdBudgetCompleteness
import MicroCFTA.SourceRecursiveIntersectionBudgetExact
import MicroCFTA.SourceRecursiveIntersectionOriginalOutput

/-!
# Exact independent language of actual repaired cold tables

Budget completeness and the existing soundness identify each final graph
with the independent guarded language of its root. Actual trace invariants
then identify finite ascending tables with that same language. No execution
or language correspondence premise is supplied at closed source entry.
-/
namespace MicroCFTA.SourceFreshOrdinaryColdGuardedExact
open Cache Language InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open SourceRecursiveIntersectionSemanticHeap (SemanticHeap)
open SourceColdSharedRows (Rows ResidentRows CoveredRows Supported)
open SourceFreshOrdinaryColdSharedRows (Trace ReplayedRows)
open SourcePreparedSharedRows (encode)

/-- A replayed closed final graph has exactly its root's independent complete guarded language. -/
theorem graph_exact [DecidableEq (EdgeKey Symbol Guard)] (state : State Symbol Guard)
    (semantic : SemanticHeap state) (covered : Covered [] state) (guarded : InternedGuardedProbeHeap.Heap state)
    (budgetHeap : InternedGuardedBudgetProbeHeap.Heap state) (rows : Rows Symbol Guard)
    (replayed : ReplayedRows state rows) (resident : ResidentRows state rows) (closedRows : CoveredRows rows rows)
    (value : Value Symbol Guard) (available : Available state value) (closed : value.free = []) (supported : Supported rows value)
    (holds : Guard → Term Symbol → Bool) (ambient : InternedGuardedLanguage.Env Symbol) (term : Term Symbol) :
    EpsilonUnion.Accepts (MergedFreshOrdinaryGraph.graph state holds) value term ↔
      InternedGuardedLanguage.meaning holds ambient value term := by
  constructor
  · exact SourceFreshOrdinaryColdGuardedSoundness.graph_sound state semantic covered guarded rows holds ambient
      replayed resident closedRows value available closed supported term
  · intro accepted
    let emptyEnv : InternedGuardedBudget.Env Symbol := fun _ _ _ => False
    have original := SourceRecursiveIntersectionOriginalOutput.closed_original value state semantic.1.normal.facts.coherent available closed
    rw [SourceRecursiveIntersectionBudgetInput.erase_exact state semantic.1.normal.facts holds value original available closed emptyEnv ambient] at accepted
    obtain ⟨budget, accepted⟩ := accepted
    exact SourceFreshOrdinaryColdBudgetCompleteness.graph_complete state semantic covered budgetHeap rows replayed resident closedRows
      holds emptyEnv (by intro name before after bounded term impossible; cases impossible) value available closed supported budget term accepted

/-- An actual finite shared trace gives exact independent root language in its final graph. -/
theorem trace_graph_exact [DecidableEq (EdgeKey Symbol Guard)]
    (state final : State Symbol Guard) (value : Value Symbol Guard) (rows : Rows Symbol Guard)
    (trace : Trace state (fun _ => none) [value] rows final) (semantic : SemanticHeap state) (covered : Covered [] state)
    (guarded : InternedGuardedProbeHeap.Heap state) (budgetHeap : InternedGuardedBudgetProbeHeap.Heap state)
    (available : Available state value) (closed : value.free = [])
    (holds : Guard → Term Symbol → Bool) (ambient : InternedGuardedLanguage.Env Symbol) (term : Term Symbol) :
    EpsilonUnion.Accepts (MergedFreshOrdinaryGraph.graph final holds) value term ↔
      InternedGuardedLanguage.meaning holds ambient value term := by
  have inputs : SourceColdSharedRows.Inputs state [value] := by
    intro child member; simpa only [List.mem_singleton.mp member] using And.intro available closed
  have noRows : ResidentRows state (fun _ => none) := by intro identity edges absent; cases absent
  obtain ⟨finalSemantic, finalCovered, growth, history, _, resident⟩ := trace.correct semantic covered inputs noRows
  have replayed := trace.replayed semantic covered inputs (by intro identity edges absent; cases absent)
  have closedRows := trace.closed (by intro identity edges absent; cases absent)
  exact graph_exact final finalSemantic finalCovered (trace.guarded_heap semantic covered guarded inputs)
    (trace.budget_heap semantic covered budgetHeap inputs) rows replayed resident closedRows value
    (available.grows state final growth history) closed (trace.pending_done value List.mem_cons_self) holds ambient term

/-- The actual ascending finite table has exactly the independent complete guarded language of its original root. -/
theorem trace_table_exact [DecidableEq (EdgeKey Symbol Guard)]
    (state final : State Symbol Guard) (value : Value Symbol Guard) (rows : Rows Symbol Guard)
    (trace : Trace state (fun _ => none) [value] rows final) (semantic : SemanticHeap state) (covered : Covered [] state)
    (guarded : InternedGuardedProbeHeap.Heap state) (budgetHeap : InternedGuardedBudgetProbeHeap.Heap state)
    (available : Available state value) (closed : value.free = []) (keys : List Nat)
    (domain : ∀ identity, (∃ edges, rows identity = some edges) ↔ identity ∈ keys)
    (holds : Guard → Term Symbol → Bool) (ambient : InternedGuardedLanguage.Env Symbol) (term : Term Symbol) :
    Language.Accepts (FTAValidation.rowFor (SourceInternedRows.interpretedRows holds (SourceColdSharedRows.table rows keys value)))
      (encode value) term ↔ InternedGuardedLanguage.meaning holds ambient value term :=
  (SourceFreshOrdinaryColdTableLanguage.trace_table_language_final state final value rows trace semantic covered available closed keys domain holds term).trans
    (trace_graph_exact state final value rows trace semantic covered guarded budgetHeap available closed holds ambient term)

/-- The exact final table also denotes the actual tagged input language in its original cache. -/
theorem trace_table_input_exact [DecidableEq (EdgeKey Symbol Guard)]
    (state final : State Symbol Guard) (value : Value Symbol Guard) (rows : Rows Symbol Guard)
    (trace : Trace state (fun _ => none) [value] rows final) (semantic : SemanticHeap state) (covered : Covered [] state)
    (guarded : InternedGuardedProbeHeap.Heap state) (budgetHeap : InternedGuardedBudgetProbeHeap.Heap state)
    (available : Available state value) (closed : value.free = []) (keys : List Nat)
    (domain : ∀ identity, (∃ edges, rows identity = some edges) ↔ identity ∈ keys)
    (holds : Guard → Term Symbol → Bool) (term : Term Symbol) :
    Language.Accepts (FTAValidation.rowFor (SourceInternedRows.interpretedRows holds (SourceColdSharedRows.table rows keys value)))
      (encode value) term ↔ SourceRecursiveIntersectionInputView.InputLanguage state holds
        (SourceRecursiveIntersectionInputView.inputOf value) term := by
  rw [trace_table_exact state final value rows trace semantic covered guarded budgetHeap available closed keys domain holds (fun _ _ => False)]
  have original := SourceRecursiveIntersectionOriginalOutput.closed_original value state semantic.1.normal.facts.coherent available closed
  rw [SourceRecursiveIntersectionGuardedInput.input_exact state semantic.1.normal.facts holds value original available closed]

end MicroCFTA.SourceFreshOrdinaryColdGuardedExact
