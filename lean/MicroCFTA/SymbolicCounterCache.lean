import MicroCFTA.SymbolicExpansionDriver

/-!
# Source counter caches and graph counts

The semantic graph interface specifies finite languages, exact intersection,
and the pointwise signed edge interpretation. It does not specify counter
results. The cache invariant stores only independently defined cardinalities.
-/
namespace MicroCFTA.SymbolicDriver
open Language

/-- Pointwise graph semantics required by the source's signed edge representation. -/
structure CounterMeaning [DecidableEq Symbol] (graph : Graph Symbol) where
  terms : Nat → List (Term Symbol)
  distinct : ∀ node, (terms node).Nodup
  intersection : ∀ left right term,
    term ∈ terms (graph.intersect left right) ↔ term ∈ terms left ∧ term ∈ terms right
  indicators : ∀ node term, Symbolic.weighted
    (fun component => Lattice.indicator (@decide (term ∈ componentTerms terms component.1 component.2) (Classical.propDecidable _)))
    (expansionPieces graph node) = Lattice.indicator (@decide (term ∈ terms node) (Classical.propDecidable _))

/-- The complete signed node expression equals distinct accepted-term cardinality. -/
theorem semantic_node_count [DecidableEq Symbol] (graph : Graph Symbol) (meaning : CounterMeaning graph) (node : Nat) :
    Symbolic.weighted (semanticEdgeCount meaning.terms)
      (Symbolic.unionCoefficients (intersectEdge graph) (graph.edges node)) = ((meaning.terms node).length : Int) := by
  classical
  rw [show semanticEdgeCount meaning.terms = (fun edge => (edge.indicators.map fun (coefficient, classes) =>
    coefficient * ((componentTerms meaning.terms edge classes).length : Int)).sum) from rfl]
  rw [← expansionPieces_weighted graph node (fun edge classes => ((componentTerms meaning.terms edge classes).length : Int))]
  apply signed_lengths (fun component => componentTerms meaning.terms component.1 component.2)
    (expansionPieces graph node) (meaning.terms node)
    (fun component => componentTerms_nodup meaning.terms meaning.distinct component.1 component.2) (meaning.distinct node)
  intro term
  simpa only [Lattice.indicator, decide_eq_true_eq] using meaning.indicators node term

/-- No structural edge means no finite accepted term. -/
theorem CounterMeaning.empty [DecidableEq Symbol] (graph : Graph Symbol) (meaning : CounterMeaning graph)
    (node : Nat) (empty : (graph.edges node).isEmpty = true) : meaning.terms node = [] := by
  have noEdges := List.isEmpty_iff.mp empty
  have count := semantic_node_count graph meaning node
  simp only [noEdges, Symbolic.unionCoefficients, List.foldl_nil, Symbolic.weighted] at count
  exact List.length_eq_zero_iff.mp (by omega)

/-- A cache key denotes its normalized problem; fresh-name supply is not a logical constraint. -/
def keyProblem (key : Key Symbol) : Problem Symbol :=
  ⟨key.domains, [], key.domains.length, key.obligations⟩

/-- Both memo tables contain their independent semantic counts. -/
def SemanticCache (language : Nat → List (Term Symbol)) (counts : Counts Symbol) : Prop :=
  GraphCacheCorrect (fun node => ((language node).length : Int)) counts ∧
    ContextCacheCorrect (fun key => (solutionCount language (keyProblem key) : Int)) counts

/-- The empty source cache satisfies both semantic memo invariants. -/
theorem semanticCache_empty (language : Nat → List (Term Symbol)) : SemanticCache language {} := by
  constructor <;> intro entry member <;> cases member

/-- Storing a correct node count preserves both semantic memo tables. -/
theorem semanticCache_store_graph (language : Nat → List (Term Symbol)) (counts : Counts Symbol)
    (valid : SemanticCache language counts) (node : Nat) (count : Int) (correct : count = ((language node).length : Int)) :
    SemanticCache language {counts with graphs := insert counts.graphs node count} :=
  ⟨graph_cache_store _ counts valid.1 node count correct, valid.2⟩

/-- Storing a correct context count preserves both semantic memo tables. -/
theorem semanticCache_store_context (language : Nat → List (Term Symbol)) (counts : Counts Symbol)
    (valid : SemanticCache language counts) (key : Key Symbol) (count : Int)
    (correct : count = (solutionCount language (keyProblem key) : Int)) :
    SemanticCache language {counts with contexts := (key, count) :: counts.contexts} :=
  ⟨valid.1, context_cache_store _ counts valid.2 key count correct⟩

/-- Correct recursive edge counts prove every actual node branch, including cache lookup and insertion. -/
theorem countNode_correct [DecidableEq Symbol] [Ord Symbol] (graph : Graph Symbol) (meaning : CounterMeaning graph)
    (fuel : Nat)
    (recursive : ∀ edge before count after, SemanticCache meaning.terms before →
      countEdge graph fuel edge before = .ok (count, after) →
        count = semanticEdgeCount meaning.terms edge ∧ SemanticCache meaning.terms after)
    (node : Nat) (before after : Counts Symbol) (result : Int) (starts : SemanticCache meaning.terms before)
    (success : countNode graph (fuel + 1) node before = .ok (result, after)) :
    result = ((meaning.terms node).length : Int) ∧ SemanticCache meaning.terms after := by
  by_cases empty : (graph.edges node).isEmpty = true
  · simp only [countNode, empty, ite_true, Pure.pure, StateT.pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at success
    obtain ⟨rfl, rfl⟩ := success
    exact ⟨by rw [CounterMeaning.empty graph meaning node empty]; rfl, starts⟩
  · have nonempty : (graph.edges node).isEmpty = false := Bool.eq_false_iff.mpr empty
    cases cached : lookup before.graphs node with
    | some count =>
        rw [countNode_cached graph fuel node before count nonempty cached] at success
        cases success
        exact ⟨graph_cache_hit _ before starts.1 node result cached, starts⟩
    | none =>
        simp only [countNode, nonempty, Bool.false_eq_true, ite_false, Bind.bind, StateT.bind,
          get, getThe, MonadStateOf.get, StateT.get, Pure.pure, Except.pure, Except.bind, cached] at success
        change Except.bind (countUnion graph (countEdge graph fuel) (graph.edges node) before)
          (fun (count, cache) => .ok (count, {cache with graphs := insert cache.graphs node count})) = .ok (result, after) at success
        cases computed : countUnion graph (countEdge graph fuel) (graph.edges node) before with
        | error error => simp only [computed] at success; cases success
        | ok pair =>
            obtain ⟨count, cache⟩ := pair
            have verified := countUnion_correct graph (countEdge graph fuel) (semanticEdgeCount meaning.terms)
              (SemanticCache meaning.terms) recursive (graph.edges node) before cache count starts computed
            have correct := verified.1.trans (semantic_node_count graph meaning node)
            simp only [computed, Except.bind, Except.ok.injEq, Prod.mk.injEq] at success
            obtain ⟨rfl, rfl⟩ := success
            exact ⟨correct, semanticCache_store_graph meaning.terms cache verified.2 node count correct⟩

/-- The shape guaranteed by a successful source normalization. -/
def NormalProblem (problem : Problem Symbol) : Prop :=
  (problem.domains.map Prod.fst).Nodup ∧ problem.bindings = [] ∧
    (∀ entry ∈ problem.domains, entry.1 < problem.nextVariable) ∧ ProblemScoped problem

/-- The source normalizer establishes every local invariant required by its next solver step. -/
theorem normalize_normal [DecidableEq Symbol] [Ord Symbol] (fuel : Nat) (problem normalized : Problem Symbol)
    (success : normalize fuel problem = .ok (some normalized)) : NormalProblem normalized := by
  have fresh := normalize_fresh fuel problem normalized success
  exact ⟨fresh.1, (normalize_shape fuel problem normalized success).2.1, fresh.2,
    normalize_scoped fuel problem normalized success⟩

/-- The normalized problem's full logical count is determined by its cache key. -/
theorem normal_key_count (language : Nat → List (Term Symbol)) (problem : Problem Symbol)
    (empty : problem.bindings = []) :
    solutionCount language problem = solutionCount language (keyProblem ⟨problem.domains, problem.obligations⟩) := by
  unfold solutionCount solutionTuples
  congr 1
  apply List.filter_congr
  intro values _
  apply decide_eq_decide.mpr
  simp only [LiveSolution, keyProblem]
  rw [empty]

/-- Correct normalized solver steps prove the source empty checks, normalization, and complete context-cache path. -/
theorem solve_correct [DecidableEq Symbol] [Ord Symbol] (graph : Graph Symbol) (meaning : CounterMeaning graph)
    (fuel : Nat)
    (recursive : ∀ problem before count after, NormalProblem problem → SemanticCache meaning.terms before →
      solveStep graph fuel problem before = .ok (count, after) →
        count = (solutionCount meaning.terms problem : Int) ∧ SemanticCache meaning.terms after)
    (problem : Problem Symbol) (distinct : (problem.domains.map Prod.fst).Nodup)
    (admissible : AdmissibleBindings problem)
    (before after : Counts Symbol) (result : Int) (starts : SemanticCache meaning.terms before)
    (success : solve graph (fuel + 1) problem before = .ok (result, after)) :
    result = (solutionCount meaning.terms problem : Int) ∧ SemanticCache meaning.terms after := by
  by_cases empty : problem.domains.any (fun entry => (graph.edges entry.2).isEmpty) = true
  · obtain ⟨entry, member, noEdges⟩ := List.any_eq_true.mp empty
    have zero := empty_domain_solution_count meaning.terms problem entry member (CounterMeaning.empty graph meaning entry.2 noEdges)
    simp only [solve, empty, ite_true, Pure.pure, StateT.pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at success
    obtain ⟨rfl, rfl⟩ := success
    exact ⟨by rw [zero]; rfl, starts⟩
  · have nonempty : problem.domains.any (fun entry => (graph.edges entry.2).isEmpty) = false := Bool.eq_false_iff.mpr empty
    simp only [solve, nonempty, Bool.false_eq_true, ite_false, Bind.bind, StateT.bind,
      liftM, monadLift, MonadLift.monadLift, StateT.lift, Except.bind] at success
    cases normalized : normalize (fuel + 1) problem with
    | error error => simp only [normalized] at success; cases success
    | ok candidate =>
        cases candidate with
        | none =>
            simp only [normalized, Pure.pure, Except.pure, StateT.pure, Except.ok.injEq, Prod.mk.injEq] at success
            obtain ⟨rfl, rfl⟩ := success
            exact ⟨by rw [normalize_none_count meaning.terms (fuel + 1) problem normalized]; rfl, starts⟩
        | some current =>
            have valid := normalize_normal (fuel + 1) problem current normalized
            have sameCount := normalize_count meaning.terms (fuel + 1) problem current distinct admissible normalized
            let key : Key Symbol := ⟨current.domains, current.obligations⟩
            have keyCount := normal_key_count meaning.terms current valid.2.1
            simp only [normalized, Pure.pure, Except.pure, Bind.bind, StateT.bind,
              get, getThe, MonadStateOf.get, StateT.get, Except.bind] at success
            cases cached : before.contexts.find? (fun entry => keyEq entry.1 key) with
            | some entry =>
                obtain ⟨stored, count⟩ := entry
                have correct := context_cache_hit _ before starts.2 key stored count cached
                dsimp only [key] at cached
                simp only [cached] at success
                change Except.ok (count, before) = (Except.ok (result, after) : Except Error _) at success
                cases success
                exact ⟨by rw [correct, sameCount, keyCount], starts⟩
            | none =>
                dsimp only [key] at cached
                rw [cached] at success
                change Except.bind (solveStep graph fuel current before) (fun (count, cache) =>
                  Except.ok (count, {cache with contexts := (key, count) :: cache.contexts})) = Except.ok (result, after) at success
                cases computed : solveStep graph fuel current before with
                | error error => simp only [computed] at success; cases success
                | ok pair =>
                    obtain ⟨count, cache⟩ := pair
                    have verified := recursive current before count cache valid starts computed
                    have storedCorrect : count = (solutionCount meaning.terms (keyProblem key) : Int) := by
                      rw [verified.1, keyCount]
                    simp only [computed, Except.bind, Except.ok.injEq, Prod.mk.injEq] at success
                    obtain ⟨rfl, rfl⟩ := success
                    exact ⟨by rw [verified.1, sameCount], semanticCache_store_context meaning.terms cache verified.2 key count storedCorrect⟩

end MicroCFTA.SymbolicDriver
