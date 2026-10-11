import MicroCFTA.SymbolicSelectionTotal

/-!
# Complete finite source indexing

The actual source counter and decoder eventually succeed at every valid
finite rank. Concrete row and guard semantics then give one rank per accepted
term, its exact inverse, and the complete distinct-term cardinality.
-/
namespace MicroCFTA.SymbolicDriver
open Language

/-- Every in-range public source decode has a stable successful output at all sufficiently large bounds. -/
theorem unrank_eventual [DecidableEq Symbol] [Ord Symbol] [Ord Order]
    (graph : Graph Symbol) (order : Symbol → Order) (meaning : FiniteMeaning graph)
    (invariant : Counts Symbol → Prop) (empty : invariant {})
    (sound : CountSound graph (fun node => (meaning.terms node).length) invariant)
    (countTotal : ∀ node state, Eventually (fun fuel => countNode graph fuel node) state)
    (coverage : ConstructorCoverage graph order meaning) (root : Nat) (rank : Int)
    (nonnegative : 0 ≤ rank) (inRange : rank < ((meaning.terms root).length : Int)) :
    ∃ bound term, ∀ fuel, bound ≤ fuel → unrank graph order fuel root rank = .ok term := by
  obtain ⟨countBound, cache, cacheValid, counted⟩ := count_eventual_exact graph meaning invariant sound countTotal root {} empty
  have heights : SubtreeHeight meaning root [] (forestHeight (meaning.terms root)) := by
    intro whole member part located
    have same := Option.some.inj located
    subst part
    exact height_le_forestHeight (meaning.terms root) whole member
  obtain ⟨selectBound, ⟨term, final, suffix⟩, after, selected⟩ :=
    selectAt_eventual graph order meaning invariant sound countTotal coverage (forestHeight (meaning.terms root))
      root [] rank cache cacheValid nonnegative inRange (fun whole _ => ⟨whole, rfl⟩) heights
  dsimp only at selected
  refine ⟨max countBound selectBound, term, ?_⟩
  intro fuel enough
  have validRank : ¬(rank < 0 ∨ ((meaning.terms root).length : Int) ≤ rank) := by omega
  simp only [unrank, counted fuel (by omega), Bind.bind, Except.bind, ite_eq_right validRank, selected fuel (by omega)]
  rfl

/-- Finitely many eventual pure executions have one common successful bound. -/
theorem uniform_finite_success (action : Nat → Input → Except Failure Output) (inputs : List Input)
    (total : ∀ input ∈ inputs, ∃ bound output, ∀ fuel, bound ≤ fuel → action fuel input = .ok output) :
    ∃ bound, ∀ input ∈ inputs, ∀ fuel, bound ≤ fuel → ∃ output, action fuel input = .ok output := by
  induction inputs with
  | nil => exact ⟨0, fun _ member => by cases member⟩
  | cons first rest ih =>
      obtain ⟨firstBound, firstOutput, firstStable⟩ := total first (by simp)
      obtain ⟨restBound, restStable⟩ := ih (fun input member => total input (by simp [member]))
      refine ⟨max firstBound restBound, ?_⟩
      intro input member fuel enough
      rcases List.mem_cons.mp member with rfl | member
      · exact ⟨firstOutput, firstStable fuel (by omega)⟩
      · exact restStable input member fuel (by omega)

/-- One sufficient source execution bound covers the entire finite range of distinct term ranks. -/
theorem decodeTotal_eventual [DecidableEq Symbol] [Ord Symbol] [Ord Order]
    (graph : Graph Symbol) (order : Symbol → Order) (meaning : FiniteMeaning graph)
    (invariant : Counts Symbol → Prop) (empty : invariant {})
    (sound : CountSound graph (fun node => (meaning.terms node).length) invariant)
    (countTotal : ∀ node state, Eventually (fun fuel => countNode graph fuel node) state)
    (coverage : ConstructorCoverage graph order meaning) (root : Nat) :
    ∃ bound, ∀ fuel, bound ≤ fuel → DecodeTotal graph order fuel root (meaning.terms root).length := by
  let ranks : List (Fin (meaning.terms root).length) := List.ofFn id
  obtain ⟨bound, uniform⟩ := uniform_finite_success
    (fun fuel (rank : Fin (meaning.terms root).length) => unrank graph order fuel root rank.val) ranks (by
      intro rank _
      exact unrank_eventual graph order meaning invariant empty sound countTotal coverage root rank.val (by omega) (by have := rank.isLt; omega))
  refine ⟨bound, ?_⟩
  intro fuel enough rank
  apply uniform rank ?_ fuel enough
  exact List.mem_ofFn.mpr ⟨rank, rfl⟩

/-- Concrete guarded graph rows give a complete exact source index after one finite bound. -/
theorem rows_full_index [DecidableEq Symbol] [Ord Symbol] [Ord Order]
    (graph : Graph Symbol) (order : Symbol → Order) (meaning : FiniteMeaning graph)
    (budget : SourceBudget graph) (fallback : Term Symbol)
    (intersection : ∀ left right term,
      term ∈ meaning.terms (graph.intersect left right) ↔ term ∈ meaning.terms left ∧ term ∈ meaning.terms right)
    (guard : Edge Symbol → Term Symbol → Bool)
    (compiled : ∀ node edge, edge ∈ graph.edges node → ∀ term,
      ConstraintIndicators.score (classTest term) edge.indicators = Lattice.indicator (guard edge term))
    (rows : ∀ node term, term ∈ meaning.terms node ↔
      ∃ edge ∈ graph.edges node, ShapeHolds meaning.terms edge term ∧ guard edge term = true)
    (root : Nat) :
    ∃ bound, ∀ fuel, bound ≤ fuel →
      cardinality graph fuel root = .ok ((meaning.terms root).length : Int) ∧
      DecodeTotal graph order fuel root (meaning.terms root).length ∧
      ∀ term, term ∈ meaning.terms root →
        ∃ rank : Fin (meaning.terms root).length,
          unrank graph order fuel root rank.val = .ok term ∧
          rankOf graph order fuel root term = .ok (some rank.val) ∧
          ∀ other : Fin (meaning.terms root).length,
            unrank graph order fuel root other.val = .ok term → other = rank := by
  let counter := counterMeaningFromRows graph meaning.terms meaning.distinct intersection guard compiled rows
  have sound := counter_countSound graph counter fallback
  have countTotal : ∀ node state, Eventually (fun fuel => countNode graph fuel node) state :=
    fun node state => counter_eventual graph budget (.node node) trivial state
  have coverage : ConstructorCoverage graph order meaning := constructorsAt_coverage graph order meaning (by
    intro node term member
    obtain ⟨edge, present, shape, _⟩ := (rows node term).mp member
    exact ⟨edge, present, shape⟩)
  obtain ⟨countBound, countExact⟩ := cardinality_total_exact graph budget counter fallback root
  obtain ⟨decodeBound, decodeTotal⟩ := decodeTotal_eventual graph order meaning (SemanticCache meaning.terms)
    (semanticCache_empty meaning.terms) sound countTotal coverage root
  refine ⟨max countBound decodeBound, ?_⟩
  intro fuel enough
  have total := decodeTotal fuel (by omega)
  refine ⟨countExact fuel (by omega), total, ?_⟩
  intro term accepted
  exact rows_rank_bijection graph order meaning fallback intersection guard compiled rows fuel root total term accepted

end MicroCFTA.SymbolicDriver
