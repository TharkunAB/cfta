import MicroCFTA.SourcePruningEnumerationSelectedValue
import MicroCFTA.SourceFreshOrdinaryColdNativeSized

/-!
# Native Sized compilation after actual selected-value preparation

The selected Mu and Union paths retain the warm node and edge memo tables.
The actual cold traversal and native compiler then retain exact queries at
the original selected value's independent language. Native constraint and
word-range checks remain explicit.
The compiler is the SourceCyclicRows model. Data.CFTA.Sized also has
determinized and equal-child fast paths.
-/

namespace MicroCFTA.SourcePruningEnumerationSelectedNativeSized
open Cache Language InternedConstructorTemplates InternedProbeProvenance
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks
open SourceEqualityRequiredCache SourceEqualityRequiredSemanticCache
open SourceFreshOrdinaryNativeCallback (Ready)
open SourceGuards SourceObservations SourceSymbolicIndex
open SourceColdSharedRows (Supported)
open SourceFreshOrdinaryColdSharedRows (Trace keys)

/-- Actual selected-value preparation retains warm memo tables and all compiler readiness fields. -/
theorem prepare {width : Nat} {Symbol Guard : Type}
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (emptyGuard : Guard) (conjoin : Guard → Guard → Guard)
    (state : SourceRecursiveIntersectionThunks.State width Symbol Guard)
    (ready : Ready emptyGuard conjoin state) (value : Value Symbol Guard)
    (available : Available state.machine.heap value) (closed : value.free = []) :
    ∃ bound prepared middle,
      (∀ extra, SourcePruningEnumerationSelectedValue.run (bound + extra) value state.machine.heap =
        .done prepared middle.machine.heap) ∧
      Ready emptyGuard conjoin middle ∧
      middle.nodes = state.nodes ∧ middle.edges = state.edges ∧
      middle.machine.domains = state.machine.domains ∧
      Extension state.machine middle.machine ∧
      Available middle.machine.heap prepared ∧ prepared.free = [] ∧
      ∀ holds ambient term,
        InternedGuardedLanguage.meaning holds ambient prepared term ↔
          InternedGuardedLanguage.meaning holds ambient value term := by
  have semantic : SemanticReady state.machine.heap :=
    ⟨⟨ready.semantic, ready.covered, ready.openDepth⟩, ready.guarded, ready.budget⟩
  obtain ⟨bound, prepared, heap, running, kept, heapReady, preparedAvailable, preparedClosed, language⟩ :=
    SourcePruningEnumerationSelectedValue.run_complete value state.machine.heap semantic available closed
  let middle := advance state ⟨heap, state.machine.domains⟩
  have extension : Extension state.machine middle.machine :=
    ⟨kept.growth, kept.history, extends_refl _⟩
  have valid : SourceRecursiveIntersectionKernel.Valid middle.machine :=
    ⟨heapReady.ready.semantic.1.normal.facts, ready.valid.machine.2⟩
  have middleReady : Ready emptyGuard conjoin middle :=
    ⟨advance_valid width emptyGuard conjoin state ready.valid _ valid extension,
      ready.idle.advance state _, heapReady.ready.semantic, heapReady.ready.covered,
      heapReady.ready.depth, heapReady.guarded, heapReady.budget⟩
  exact ⟨bound, prepared, middle, running, middleReady, rfl, rfl, rfl,
    extension, preparedAvailable, preparedClosed, language⟩

/-- Actual preparation, cold traversal, and warm native compilation retain every exact Sized law. -/
theorem complete {width : Nat} {Formula Key : Type}
    [DecidableEq Formula] [DecidableEq Key] [Ord Key]
    [DecidableEq (EdgeKey (Label Formula) (Constraint Formula))]
    (emptyGuard : Constraint Formula) (conjoin : Constraint Formula → Constraint Formula → Constraint Formula)
    (state : SourceRecursiveIntersectionThunks.State width (Label Formula) (Constraint Formula))
    (ready : Ready emptyGuard conjoin state)
    (value : Value (Label Formula) (Constraint Formula)) (available : Available state.machine.heap value)
    (valueClosed : value.free = [])
    (formulas : Formulas Formula) (solver : Entailment Formula) (order : Label Formula → Key)
    (ambient : InternedGuardedLanguage.Env (Label Formula)) :
    ∃ bound prepared middle,
      (∀ extra, SourcePruningEnumerationSelectedValue.run (bound + extra) value state.machine.heap =
        .done prepared middle.machine.heap) ∧
      Ready emptyGuard conjoin middle ∧
      middle.nodes = state.nodes ∧ middle.edges = state.edges ∧
      middle.machine.domains = state.machine.domains ∧ Extension state.machine middle.machine ∧
      ∃ rows final outer inner,
      ∃ (domain : ∀ identity, (∃ edges, rows identity = some edges) ↔ identity ∈ keys final rows)
        (supported : Supported rows prepared)
        (closed : SourceDenseRowsRestrict.Closed (SourceColdSharedRows.table rows (keys final rows) prepared)),
        Trace middle.machine.heap (fun _ => none) [prepared] rows final ∧
        (∀ largerOuter largerInner, outer ≤ largerOuter → inner ≤ largerInner →
          SourceFreshOrdinaryColdSharedRows.collect largerOuter largerInner middle.machine.heap
            (fun _ => none) [prepared] = .done rows final) ∧
        ∀ active : ∀ key edge,
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
                InternedGuardedLanguage.meaning (acceptsConstraint formulas solver) ambient value term ∧
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
                 InternedGuardedLanguage.meaning (acceptsConstraint formulas solver) ambient value term ∧
                   RecursiveSize.nodeSize term ≤ bound) ∧
             (∀ term, (∃ position, SourceSizedQueries.rank classes RecursiveSize.nodeSize term = some position) ↔
               InternedGuardedLanguage.meaning (acceptsConstraint formulas solver) ambient value term) ∧
             (∀ term position, SourceSizedQueries.rank classes RecursiveSize.nodeSize term = some position ↔
               SourceSizedQueries.unrank classes position = some term)) := by
  obtain ⟨bound, prepared, middle, running, middleReady, nodes, edges, domains, extension,
      preparedAvailable, preparedClosed, language⟩ :=
    prepare emptyGuard conjoin state ready value available valueClosed
  obtain ⟨rows, final, outer, inner, domain, supported, closed, trace, stable, finish⟩ :=
    SourceFreshOrdinaryColdNativeSized.complete emptyGuard conjoin middle middleReady prepared
      preparedAvailable preparedClosed formulas solver order ambient
  refine ⟨bound, prepared, middle, running, middleReady, nodes, edges, domains, extension,
    rows, final, outer, inner, domain, supported, closed, trace, stable, ?_⟩
  intro active
  have completed := finish active
  simp only [language] at completed
  exact completed

end MicroCFTA.SourcePruningEnumerationSelectedNativeSized
