import MicroCFTA.SourceSizedConjunctionCurrent
import MicroCFTA.SourceSizedConjunctionConstructed

/-!
# Current conjunction language from arbitrary original source syntax

Every original annotation satisfies the constant True heap property. Actual
construction, selected preparation, and cold collection therefore need no
normalization condition. Their returned table has derived structural
validation. Its current constraint interpretation retains the actual equality
accessor and the complete guard. Successful conjunction preparation denotes
the original independent syntax language under that same interpretation.

Classifier rejection and the actual 1024-key helper cap remain explicit.
No final table, completed worker, field inventory, or supplied fuel is an
input. Native representation, machine words, grouped order, and total-work
bounds remain separate.
-/
namespace MicroCFTA.SourceSizedConjunctionCurrentConstructed
open Language SourceGuards SourceObservations SourceSymbolicIndex Std
open InternedConstructorTemplates InternedProbeProvenance
open InternedNestedConstruction (Syntax EdgeSyntax)
open InternedFreshOrdinaryConstraintHeap (SyntaxValid ManyValid EdgesValid)
open SourceFreshOrdinaryColdSharedRows (Trace keys)
open SourcePreparedSharedRows (encode)
attribute [local instance] lexOrd

variable {Symbol Guard Formula : Type}

mutual
/-- The constant heap property imposes no condition on original syntax annotations. -/
theorem syntax_valid_true (expression : Syntax Symbol Guard) :
    SyntaxValid (fun _ => True) expression := by
  cases expression with
  | empty | var => trivial
  | node edges => exact edges_valid_true edges
  | union members => exact many_valid_true members
  | binder _ body => exact syntax_valid_true body
termination_by sizeOf expression

/-- Every original ordered child list satisfies the constant heap property. -/
theorem many_valid_true (expressions : List (Syntax Symbol Guard)) :
    ManyValid (fun _ => True) expressions := by
  cases expressions with
  | nil => trivial
  | cons first rest => exact ⟨syntax_valid_true first, many_valid_true rest⟩
termination_by sizeOf expressions

/-- Every original ordered edge list satisfies the constant heap property. -/
theorem edges_valid_true (expressions : List (EdgeSyntax Symbol Guard)) :
    EdgesValid (fun _ => True) expressions := by
  cases expressions with
  | nil => trivial
  | cons first rest =>
      cases first with
      | mk _ _ children => exact ⟨trivial, many_valid_true children, edges_valid_true rest⟩
termination_by sizeOf expressions
end

section Selected
variable [DecidableEq Formula] [Ord (Label Formula)]
  [DecidableEq (EdgeKey (Label Formula) (Constraint Formula))]

/-- Actual original construction and preparation derive the current conjunction input and its language. -/
theorem selected_table
    (expression : Syntax (Label Formula) (Constraint Formula))
    (width : Nat) (emptyGuard : Constraint Formula)
    (conjoin : Constraint Formula → Constraint Formula → Constraint Formula) :
    ∃ value source bound prepared,
    ∃ middle : SourceRecursiveIntersectionThunks.State width (Label Formula) (Constraint Formula),
    ∃ rows final outer inner,
      InternedFreshOrdinaryConstruction.build expression [] empty = .done value source ∧
      (∀ extra, SourcePruningEnumerationSelectedValue.run (bound + extra) value source =
        .done prepared middle.machine.heap) ∧
      SourceFreshOrdinaryNativeCallback.Ready emptyGuard conjoin middle ∧
      Trace middle.machine.heap (fun _ => none) [prepared] rows final ∧
      (∀ largerOuter largerInner, outer ≤ largerOuter → inner ≤ largerInner →
        SourceFreshOrdinaryColdSharedRows.collect largerOuter largerInner middle.machine.heap
          (fun _ => none) [prepared] = .done rows final) ∧
      (let original := SourceColdSharedRows.sizedTable
          (SourceColdSharedRows.table rows (keys final rows) prepared)
       SourceSizedFiniteKeys.Closed original ∧
       SourceFTAValidation.validateRows (encode prepared)
           (SourceSizedFiniteKeys.interpreted original (fun _ _ => true)) =
         .ok (SourceSizedFiniteKeys.interpreted original (fun _ _ => true)) ∧
       (∀ (formulas : Formulas Formula) (solver : Entailment Formula) term,
         Accepts (SourceSizedConjunctionCurrent.originalGraph formulas solver original) (encode prepared) term ↔
           InternedGuardedSyntax.evaluate
             (SourceConstraintEntryRaw.acceptsConstraint formulas solver) [] expression term) ∧
       (SourceSizedConjunctionPreparation.prepare original (encode prepared) = none ↔
         SourceSizedConjunctionClassified.classifyTable original = none ∨
           ∃ classified, SourceSizedConjunctionClassified.classifyTable original = some classified ∧
             SourceSizedConjunctionWorklist.prepare classified (encode prepared) = .limitExceeded) ∧
       (∀ output, SourceSizedConjunctionPreparation.prepare original (encode prepared) = some output →
         ∀ (formulas : Formulas Formula) (solver : Entailment Formula) term,
           Accepts (SourceSizedConjunctionLanguage.graph (SourceSizedFiniteKeys.lookup output)) [encode prepared] term ↔
             InternedGuardedSyntax.evaluate
               (SourceConstraintEntryRaw.acceptsConstraint formulas solver) [] expression term)) := by
  obtain ⟨value, source, bound, prepared, middle, built, running, ready, _, _, _, _, available,
      closedValue, _, language⟩ :=
    SourcePruningEnumerationSelectedSource.prepare (fun _ => True) expression
      (syntax_valid_true expression) width emptyGuard conjoin
  obtain ⟨rows, final, outer, inner, trace, stable, metadata⟩ :=
    SourceFreshOrdinaryColdNativeTable.collect emptyGuard conjoin middle ready prepared available closedValue
  obtain ⟨_, _, _, _, _, supported, _, _, _, _, domain, rawClosed, _⟩ := metadata
  let raw := SourceColdSharedRows.table rows (keys final rows) prepared
  let original := SourceColdSharedRows.sizedTable raw
  have closed : SourceSizedFiniteKeys.Closed original :=
    SourceSizedConjunctionConstructed.sized_closed raw rawClosed
  have present : encode prepared ∈ SourceDenseRows.keys original := by
    change encode prepared ∈ SourceDenseRows.keys (SourceColdSharedRows.sizedTable raw)
    rw [SourceSizedConjunctionConstructed.sized_keys]
    exact SourceFreshOrdinaryColdCyclic.root_key rows (keys final rows) prepared domain supported
  have valid := SourceSizedStructuralKeys.validation_of_closed original (encode prepared) present closed
  have exactLanguage (formulas : Formulas Formula) (solver : Entailment Formula)
      (term : Term (Label Formula)) :
      Accepts (SourceSizedConjunctionCurrent.originalGraph formulas solver original) (encode prepared) term ↔
        InternedGuardedSyntax.evaluate
          (SourceConstraintEntryRaw.acceptsConstraint formulas solver) [] expression term := by
    let ambient : InternedGuardedLanguage.Env (Label Formula) := fun _ _ => False
    change Accepts (SourceSizedDecided.automaton (SourceSizedFiniteKeys.lookup (SourceColdSharedRows.sizedTable raw))
      (SourceConstraintEntryRaw.acceptsConstraint formulas solver)) (encode prepared) term ↔ _
    rw [SourceColdSharedRows.sized_graph]
    exact (SourceFreshOrdinaryColdGuardedExact.trace_table_exact
      middle.machine.heap final prepared rows trace ready.semantic ready.covered ready.guarded ready.budget
      available closedValue (keys final rows) domain
      (SourceConstraintEntryRaw.acceptsConstraint formulas solver) ambient term).trans
        (language (SourceConstraintEntryRaw.acceptsConstraint formulas solver) ambient term)
  refine ⟨value, source, bound, prepared, middle, rows, final, outer, inner, built, running,
    ready, trace, stable, closed, valid, exactLanguage,
    SourceSizedConjunctionPreparation.none_iff original (encode prepared), ?_⟩
  intro output success formulas solver term
  exact (SourceSizedConjunctionCurrent.root_language formulas solver original (encode prepared)
    output success term).trans (exactLanguage formulas solver term)

end Selected
end MicroCFTA.SourceSizedConjunctionCurrentConstructed
