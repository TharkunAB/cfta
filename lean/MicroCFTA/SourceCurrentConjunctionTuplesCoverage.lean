import MicroCFTA.SourceCurrentConjunctionTuples

/-!
# Common accepted terms in actual conjunction tuples

Each tuple component comes from an actual completed Read. These receipts
derive accepted edge choices, rather than a global edge-list supplier.
The chosen completed read sequence retains its separate lazy-runtime boundary.
-/
namespace MicroCFTA.SourceCurrentConjunctionTuples
open Language InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values Edges)
open MergedColdReaderClosedInputs (ClosedValues ClosedEdges)
open SourceEqualityRequiredCache SourceEqualityRequiredSemanticCache
open SourceCurrentConjunctionCompletionReads
open InternedGuardedLanguage (meaning)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula

/-- Actual ordered reads supply an accepted physical edge in every returned operand list. -/
theorem accepted_rows [DecidableEq (EdgeKey Symbol Guard)]
    {values : List (Value Symbol Guard)} {before after : State Symbol Guard}
    {rows : List (List (EdgeValue Symbol Guard))} (actual : Exposures values before rows after)
    (semantic : SemanticReady before) (available : Values before values) (closed : ClosedValues values)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (ambient : InternedGuardedLanguage.Env Symbol) (term : Term Symbol)
    (accepted : ∀ value ∈ values, meaning (SourceEqualityPCSGuard.holds formulas solver) ambient value term) :
    ∀ edges ∈ rows, ∃ edge ∈ edges, SourceCurrentConjunctionEmptinessRows.EdgeAccepts
      (meaning (SourceEqualityPCSGuard.holds formulas solver) ambient) (edgeView edge) term := by
  induction actual with
  | nil => simp
  | @cons value before edges middle values more after first rest ih =>
      have own := read_accepted first semantic (available _ List.mem_cons_self) (closed _ List.mem_cons_self)
        formulas solver ambient term (accepted _ List.mem_cons_self)
      have checked := first.verified semantic (available _ List.mem_cons_self) (closed _ List.mem_cons_self)
      have later := ih checked.2.1
        (fun child member => checked.1.available child (available child (List.mem_cons_of_mem _ member)))
        (fun child member => closed child (List.mem_cons_of_mem _ member))
        (fun child member => accepted child (List.mem_cons_of_mem _ member))
      intro chosen member
      rcases List.mem_cons.mp member with rfl | included
      · exact own
      · exact later chosen included

private theorem choices (property : EdgeValue Symbol Guard → Prop)
    (rows : List (List (EdgeValue Symbol Guard)))
    (witnesses : ∀ edges ∈ rows, ∃ edge ∈ edges, property edge) :
    ∃ tuple, All₂ (fun edge edges => edge ∈ edges) tuple rows ∧ ∀ edge ∈ tuple, property edge := by
  induction rows with
  | nil => exact ⟨[], .nil, by simp⟩
  | cons edges rows ih =>
      obtain ⟨edge, member, own⟩ := witnesses edges List.mem_cons_self
      obtain ⟨tuple, selected, valid⟩ := ih (fun edges member => witnesses edges (List.mem_cons_of_mem _ member))
      exact ⟨edge :: tuple, .cons member selected, by
        intro chosen included
        rcases List.mem_cons.mp included with rfl | included
        · exact own
        · exact valid chosen included⟩

private theorem accepted_shape (relation : Value Symbol Guard → Term Symbol → Prop)
    (edge : EdgeValue Symbol Guard) (symbol : Symbol) (terms : List (Term Symbol))
    (accepted : SourceCurrentConjunctionEmptinessRows.EdgeAccepts relation (edgeView edge) (.node symbol terms)) :
    shape edge = (symbol, terms.length) := by
  obtain ⟨children, same, related, _⟩ := accepted
  have fields := Term.node.inj same
  exact Prod.ext fields.1.symm (related.length_eq.trans (congrArg List.length fields.2).symm)

private theorem accepted_matching (relation : Value Symbol Guard → Term Symbol → Prop)
    (tuple : List (EdgeValue Symbol Guard)) (term : Term Symbol)
    (accepted : ∀ edge ∈ tuple, SourceCurrentConjunctionEmptinessRows.EdgeAccepts relation (edgeView edge) term) :
    Matching tuple := by
  cases term with
  | node symbol terms =>
      induction tuple with
      | nil => exact .nil
      | cons first rest ih =>
          apply List.pairwise_cons.mpr
          constructor
          · intro edge member
            exact (accepted_shape relation first symbol terms (accepted first List.mem_cons_self)).trans
              (accepted_shape relation edge symbol terms (accepted edge (List.mem_cons_of_mem _ member))).symm
          · exact ih (fun edge member => accepted edge (List.mem_cons_of_mem _ member))

/-- A common accepted term has a literal matching tuple in the actual returned edge lists. -/
theorem accepted_tuple [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (annotation : Guard → Prop) {values : List (Value Symbol Guard)} {before after : State Symbol Guard}
    {rows : List (List (EdgeValue Symbol Guard))} (actual : Exposures values before rows after)
    (semantic : SemanticReady before) (costs : InternedFreshOrdinaryCostHeap.Heap before)
    (fields : SourceEqualityAnnotationHeap.Heap annotation before) (available : Values before values)
    (closed : ClosedValues values)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (ambient : InternedGuardedLanguage.Env Symbol) (term : Term Symbol)
    (accepted : SourceCurrentConjunctionEmptinessRows.Accepts
      (meaning (SourceEqualityPCSGuard.holds formulas solver) ambient) values term) :
    ∃ tuple ∈ tuples rows, tuple ≠ [] ∧ Edges after tuple ∧ ClosedEdges tuple ∧
      ∀ edge ∈ tuple, SourceCurrentConjunctionEmptinessRows.EdgeAccepts
        (meaning (SourceEqualityPCSGuard.holds formulas solver) ambient) (edgeView edge) term := by
  have witnesses := accepted_rows actual semantic available closed formulas solver ambient term accepted.2
  have nonempty : rows ≠ [] := by
    intro same
    have length := actual.length
    rw [same] at length
    exact accepted.1 (List.length_eq_zero_iff.mp length.symm)
  cases rows with
  | nil => exact False.elim (nonempty rfl)
  | cons first rest =>
      have rotated : ∀ edges ∈ rest ++ [first], ∃ edge ∈ edges,
          SourceCurrentConjunctionEmptinessRows.EdgeAccepts
            (meaning (SourceEqualityPCSGuard.holds formulas solver) ambient) (edgeView edge) term := by
        intro edges member
        rcases List.mem_append.mp member with later | head
        · exact witnesses edges (List.mem_cons_of_mem _ later)
        · exact witnesses edges (List.mem_cons.mpr (Or.inl (List.mem_singleton.mp head)))
      obtain ⟨tuple, selected, common⟩ := choices _ (rest ++ [first]) rotated
      have member := (tuples_mem first rest tuple).mpr ⟨selected, accepted_matching _ tuple term common⟩
      have physical := tuples_verified annotation actual semantic costs fields available closed tuple member
      exact ⟨tuple, member, tuples_nonempty _ tuple member, physical.2.1, physical.2.2, common⟩

end MicroCFTA.SourceCurrentConjunctionTuples
