import MicroCFTA.SourcePruningEnumerationSelectedNativeSized
import MicroCFTA.SourcePruningEnumerationSelectedConstraintHeap
import MicroCFTA.InternedFreshOrdinaryClosedCompletion
import MicroCFTA.SourceFreshOrdinaryColdConstraintHeap

/-!
# Selected native values from original source construction

Original construction derives the ready native cache and the closed value.
Actual preparation retains the original edge annotations and independent
syntax language. No completed build, prepared value, or final heap is supplied.
The query result uses the SourceCyclicRows compiler model. Data.CFTA.Sized
also has determinized and equal-child fast paths.
-/

namespace MicroCFTA.SourcePruningEnumerationSelectedSource
open Cache Language InternedConstructorTemplates InternedProbeProvenance
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks
open SourceFreshOrdinaryNativeCallback (Ready)

/-- Original source annotations establish the complete prepared native input. -/
theorem prepare {Symbol Guard : Type} [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (property : Guard → Prop) (expression : InternedNestedConstruction.Syntax Symbol Guard)
    (annotations : InternedFreshOrdinaryConstraintHeap.SyntaxValid property expression)
    (width : Nat) (emptyGuard : Guard) (conjoin : Guard → Guard → Guard) :
    ∃ value source bound prepared middle,
      InternedFreshOrdinaryConstruction.build expression [] empty = .done value source ∧
      (let state := initial width (⟨source, Cache.emptyState⟩ : Machine Symbol Guard)
       (∀ extra, SourcePruningEnumerationSelectedValue.run (bound + extra) value source =
          .done prepared middle.machine.heap) ∧
       Ready emptyGuard conjoin middle ∧
       middle.nodes = state.nodes ∧ middle.edges = state.edges ∧
       middle.machine.domains = state.machine.domains ∧ Extension state.machine middle.machine ∧
       Available middle.machine.heap prepared ∧ prepared.free = [] ∧
       InternedFreshOrdinaryConstraintHeap.Heap property middle.machine.heap ∧
       ∀ holds ambient term,
         InternedGuardedLanguage.meaning holds ambient prepared term ↔
           InternedGuardedSyntax.evaluate holds [] expression term) := by
  obtain ⟨value, source, built⟩ := InternedFreshOrdinaryClosedCompletion.closed_complete expression
  obtain ⟨ready, available, closed⟩ := SourceFreshOrdinaryColdNativeTable.constructed
    expression value source built Cache.emptyState Cache.empty_valid width emptyGuard conjoin
  obtain ⟨bound, prepared, middle, running, middleReady, nodes, edges, domains, extension,
      preparedAvailable, preparedClosed, language⟩ :=
    SourcePruningEnumerationSelectedNativeSized.prepare emptyGuard conjoin _ ready value available closed
  have sourceHeap : InternedFreshOrdinaryConstraintHeap.Heap property source := by
    simpa only [built, InternedNestedConstruction.Outcome.state] using
      InternedFreshOrdinaryConstraintHeap.build_heap property expression [] empty
        (InternedFreshOrdinaryConstraintHeap.empty_heap property) annotations
  have observed : SourcePruningEnumerationSelectedValue.run bound value source =
      .done prepared middle.machine.heap := by
    simpa only [Nat.add_zero, SourceRecursiveIntersectionThunks.initial] using running 0
  have preparedHeap := SourcePruningEnumerationSelectedConstraintHeap.run_done_heap
    property bound value source (SourceEqualityRequiredSemanticCache.constructed expression value source built)
    available closed sourceHeap prepared middle.machine.heap observed
  refine ⟨value, source, bound, prepared, middle, built, running, middleReady,
    nodes, edges, domains, extension, preparedAvailable, preparedClosed, preparedHeap, ?_⟩
  intro holds ambient term
  simpa only [InternedGuardedExecution.closed_language expression value source built holds ambient]
    using language holds ambient term

open SourceGuards SourceObservations SourceSymbolicIndex
open SourceColdSharedRows (Supported)
open SourceFreshOrdinaryColdSharedRows (Trace keys)

/-- Original source construction and actual preparation derive native queries with no final-row annotation premise. -/
theorem complete {Formula Key : Type}
    [DecidableEq Formula] [DecidableEq Key] [Ord Key]
    [DecidableEq (EdgeKey (Label Formula) (Constraint Formula))]
    (width : Nat) (emptyGuard : Constraint Formula)
    (conjoin : Constraint Formula → Constraint Formula → Constraint Formula)
    (expression : InternedNestedConstruction.Syntax (Label Formula) (Constraint Formula))
    (annotations : InternedFreshOrdinaryConstraintHeap.SyntaxValid
      (fun constraint => SourceCompactGuards.ActiveOption constraint.equalities) expression)
    (formulas : Formulas Formula) (solver : Entailment Formula) (order : Label Formula → Key) :
    ∃ value source bound prepared middle,
      InternedFreshOrdinaryConstruction.build expression [] empty = .done value source ∧
      (∀ extra, SourcePruningEnumerationSelectedValue.run (bound + extra) value source =
        .done prepared middle.machine.heap) ∧
      Ready emptyGuard conjoin middle ∧
      (let state := initial width (⟨source, Cache.emptyState⟩ : Machine (Label Formula) (Constraint Formula))
       middle.nodes = state.nodes ∧ middle.edges = state.edges ∧
       middle.machine.domains = state.machine.domains ∧ Extension state.machine middle.machine) ∧
      ∃ rows final outer inner,
      ∃ (domain : ∀ identity, (∃ edges, rows identity = some edges) ↔ identity ∈ keys final rows)
        (supported : Supported rows prepared)
        (closed : SourceDenseRowsRestrict.Closed (SourceColdSharedRows.table rows (keys final rows) prepared)),
        Trace middle.machine.heap (fun _ => none) [prepared] rows final ∧
        (∀ largerOuter largerInner, outer ≤ largerOuter → inner ≤ largerInner →
          SourceFreshOrdinaryColdSharedRows.collect largerOuter largerInner middle.machine.heap
            (fun _ => none) [prepared] = .done rows final) ∧
        ∃ active : ∀ key edge,
            edge ∈ SourceInternedRows.lookup (SourceColdSharedRows.table rows (keys final rows) prepared) key →
            SourceCompactGuards.ActiveOption edge.constraint.equalities,
        let input := SourceFreshOrdinaryColdCyclic.input rows (keys final rows) prepared domain supported closed [] active
        let native := advance middle ⟨final, middle.machine.domains⟩
        SourceFreshOrdinaryNativeCompiler.Ranges emptyGuard conjoin final rows (keys final rows) prepared
          domain supported closed [] active order native →
        ∃ result after,
          SourceFreshOrdinaryNativeCompiler.Execution emptyGuard conjoin final rows (keys final rows) prepared
            domain supported closed [] active formulas solver order native result after ∧
          Ready emptyGuard conjoin after ∧
          SourceCyclicRows.compile formulas solver input order = some result ∧
          ∀ output, result = .ok output →
            (∀ size,
              SourceSizedTableEvaluation.Evaluation output (size + 1) size input.root
                (RecursiveSize.countAt output size input.root) (RecursiveSize.compileAt output size input.root) ∧
              (RecursiveSize.enumerate output size input.root).Nodup ∧
              (∀ term, term ∈ RecursiveSize.enumerate output size input.root ↔
                InternedGuardedSyntax.evaluate (acceptsConstraint formulas solver) [] expression term ∧
                  RecursiveSize.nodeSize term = size) ∧
              RecursiveSize.countAt output size input.root = (RecursiveSize.enumerate output size input.root).length ∧
              (∀ rank, Decoder.decode (RecursiveSize.compileAt output size input.root) rank =
                (RecursiveSize.enumerate output size input.root)[rank]?) ∧
              SourceSizedReference.classes output size input.root = RecursiveSize.enumerate output size input.root) ∧
            (let classes := fun size => SourceSizedReference.classes output size input.root
             (∀ size, SourceSizedReference.ClassEvaluation output (size + 1) size input.root (classes size)) ∧
             (∀ bound, (SourceSizedQueries.through classes bound).Nodup ∧
               (SourceSizedQueries.through classes bound).Pairwise
                 (fun first second => RecursiveSize.nodeSize first ≤ RecursiveSize.nodeSize second) ∧
               ∀ term, term ∈ SourceSizedQueries.through classes bound ↔
                 InternedGuardedSyntax.evaluate (acceptsConstraint formulas solver) [] expression term ∧
                   RecursiveSize.nodeSize term ≤ bound) ∧
             (∀ term, (∃ position, SourceSizedQueries.rank classes RecursiveSize.nodeSize term = some position) ↔
               InternedGuardedSyntax.evaluate (acceptsConstraint formulas solver) [] expression term) ∧
             (∀ term position, SourceSizedQueries.rank classes RecursiveSize.nodeSize term = some position ↔
               SourceSizedQueries.unrank classes position = some term)) := by
  let property := fun constraint : Constraint Formula => SourceCompactGuards.ActiveOption constraint.equalities
  obtain ⟨value, source, bound, prepared, middle, built, running, ready, nodes, edges, domains,
      extension, available, closedValue, heap, language⟩ :=
    prepare property expression annotations width emptyGuard conjoin
  obtain ⟨rows, final, outer, inner, domain, supported, closed, trace, stable, finish⟩ :=
    SourceFreshOrdinaryColdNativeSized.complete emptyGuard conjoin middle ready prepared available closedValue
      formulas solver order (fun _ _ => False)
  have inputs : SourceColdSharedRows.Inputs middle.machine.heap [prepared] := by
    intro child member
    simpa only [List.mem_singleton.mp member] using And.intro available closedValue
  have finalHeap := trace.constraint_heap property ready.semantic ready.covered heap inputs
  obtain ⟨_semantic, _covered, _growth, _history, _inputs, resident⟩ :=
    trace.correct ready.semantic ready.covered inputs (by intro identity edges absent; cases absent)
  let active := SourceFreshOrdinaryColdSharedRows.table_constraints property final finalHeap rows resident
    (keys final rows) domain prepared
  refine ⟨value, source, bound, prepared, middle, built, running, ready,
    ⟨nodes, edges, domains, extension⟩, rows, final, outer, inner, domain, supported, closed, trace, stable, active, ?_⟩
  have completed := finish active
  simp only [language] at completed
  exact completed

end MicroCFTA.SourcePruningEnumerationSelectedSource
