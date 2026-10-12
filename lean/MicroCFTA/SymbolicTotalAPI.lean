import MicroCFTA.SymbolicRankTotal

/-!
# Complete counted-index API from allocated graph rows

Constructor allocation, copied operation rows, and compiled guards suffice
for the whole finite index API. Cardinality and every valid decode have one
common execution bound. Every supplied finite term also has a bound after
which inverse ranking either returns its exact valid index or rejects it.
-/
namespace MicroCFTA.SymbolicInternedView
open Language SymbolicGraphView SymbolicDriver

/-- The inverse answer states both membership and the actual decoder inverse. -/
def RankAnswer [DecidableEq Symbol] [Ord Symbol] [Ord Order]
    (graph : Graph Symbol) (order : Symbol → Order) (guard : SymbolicDriver.Edge Symbol → Term Symbol → Bool)
    (fuel root count : Nat) (term : Term Symbol) : Option Int → Prop
  | none => ¬ Accepts (automaton graph guard) root term
  | some rank => Accepts (automaton graph guard) root term ∧
      0 ≤ rank ∧ rank < (count : Int) ∧ unrank graph order fuel root rank = .ok term

/-- The allocated closed graph has a complete exact decoder and a total membership-checking inverse. -/
theorem allocated_total_api [DecidableEq Payload] [DecidableEq Symbol] [Ord Symbol] [Ord Order]
    (shape : Payload → List (Language.Edge Nat Symbol)) (graph : Graph Symbol) (order : Symbol → Order)
    (guard : SymbolicDriver.Edge Symbol → Term Symbol → Bool) (view : ClosedOperationRows graph guard)
    (allocated : AllocatedRows shape (automaton graph guard)) (fallback : Term Symbol)
    (compiled : ∀ node edge, edge ∈ graph.edges node → ∀ term,
      ConstraintIndicators.score (classTest term) edge.indicators = Lattice.indicator (guard edge term))
    (root : Nat) :
    let budget := closedSourceBudget graph guard view id (allocated_rank shape _ allocated)
    let meaning := closedMeaning graph guard view budget
    let count := (meaning.terms root).length
    ∃ indexBound,
      (∀ fuel, indexBound ≤ fuel →
        cardinality graph fuel root = .ok (count : Int) ∧
        ∀ index : Fin count, ∃ term,
          unrank graph order fuel root index.val = .ok term ∧ Accepts (automaton graph guard) root term) ∧
      ∀ term, ∃ inverseBound answer, ∀ fuel, max indexBound inverseBound ≤ fuel →
        rankOf graph order fuel root term = .ok answer ∧ RankAnswer graph order guard fuel root count term answer := by
  let budget := closedSourceBudget graph guard view id (allocated_rank shape _ allocated)
  let meaning := closedMeaning graph guard view budget
  have intersection : ∀ left right term, term ∈ meaning.terms (graph.intersect left right) ↔
      term ∈ meaning.terms left ∧ term ∈ meaning.terms right := by
    intro left right term
    simp only [meaning, closedMeaning, finiteTerms_exact]
    exact productRows_exact _ _ view.intersection left right term
  let counter := counterMeaningFromRows graph meaning.terms meaning.distinct intersection guard compiled
    (finite_row_equation graph guard budget)
  have sound := counter_countSound graph counter fallback
  have countTotal : ∀ node state, Eventually (fun fuel => countNode graph fuel node) state :=
    fun node state => counter_eventual graph budget (.node node) trivial state
  have coverage : ConstructorCoverage graph order meaning := constructorsAt_coverage graph order meaning (by
    intro node term member
    obtain ⟨edge, present, shape, _⟩ := (finite_row_equation graph guard budget node term).mp member
    exact ⟨edge, present, shape⟩)
  have rootExact : RootProjectionExact graph meaning := closed_rootProjection graph guard view budget
  obtain ⟨indexBound, indexCorrect⟩ := allocated_full_index shape graph order guard view allocated fallback compiled root
  refine ⟨indexBound, ?_, ?_⟩
  · intro fuel enough
    obtain ⟨counted, total, _⟩ := indexCorrect fuel enough
    refine ⟨counted, ?_⟩
    intro index
    obtain ⟨term, decoded⟩ := total index
    have accepted := (unrank_sound_and_inverse graph order meaning (SemanticCache meaning.terms)
      (semanticCache_empty meaning.terms) sound fuel root index.val term decoded).1
    exact ⟨term, decoded, (finiteTerms_exact _ _ root term).mp accepted⟩
  · intro term
    obtain ⟨inverseBound, answer, inverseStable⟩ := rankOf_eventual graph order meaning (SemanticCache meaning.terms)
      (semanticCache_empty meaning.terms) sound countTotal coverage root term
    refine ⟨inverseBound, answer, ?_⟩
    intro fuel enough
    have inverse := inverseStable fuel (by omega)
    have indexResult := indexCorrect fuel (by omega)
    refine ⟨inverse, ?_⟩
    cases answer with
    | none =>
      intro accepted
      obtain ⟨index, _, ranked, _⟩ := indexResult.2.2 term accepted
      have impossible := ranked.symm.trans inverse
      cases impossible
    | some rank =>
      have accepted := rankOf_sound graph order meaning (SemanticCache meaning.terms)
        (semanticCache_empty meaning.terms) sound rootExact fuel root term rank inverse
      exact ⟨(finiteTerms_exact _ _ root term).mp accepted,
        rankOf_checked_inverse graph order meaning (SemanticCache meaning.terms)
          (semanticCache_empty meaning.terms) sound rootExact fuel root indexResult.2.1 term rank inverse⟩

end MicroCFTA.SymbolicInternedView
