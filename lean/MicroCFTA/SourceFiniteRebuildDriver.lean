import MicroCFTA.SourceFiniteRebuild
import MicroCFTA.FiniteAutomatonDriver

/-!
# Compact import primitives for the finite rebuild

Each shared term state has a singleton language. Its copied intersections
are either that same state or empty. This file derives the finite driver's
local contracts for those states and uses its actual compact edge, cache,
and ordered alternative workers. No symbolic backend contract is needed.
Native `fromFTA` identity allocation and SCC readback remain separate.
-/
namespace MicroCFTA.SourceFiniteRebuildDriver
open Language FiniteAutomatonDriver CompactGroups CompactEdgeRanks

variable [DecidableEq Symbol]

/-- A missing canonical term is the empty state. -/
def domain (state : Option (Term Symbol)) (term : Term Symbol) : Prop := state = some term

/-- Plain finite-term rows put each child in its own compact group. -/
def spec : Term Symbol → EdgeSpec (Option (Term Symbol)) Symbol
  | .node symbol children => ⟨symbol, children.map some, some (childGroups children.length [])⟩

/-- The intersection of two singleton canonical states needs no graph search. -/
def meet (first second : Option (Term Symbol)) : Option (Term Symbol) :=
  if first = second then first else none

/-- The compact source view of the shared singleton states. -/
def source : Source (Option (Term Symbol)) Symbol Unit where
  edges state := match state with | none => [] | some term => [spec term]
  flags _ := ⟨false, false, false, false, false⟩
  meet := meet
  symbolic _ := .error ()

/-- Height bounds every real child request. -/
def height : Option (Term Symbol) → Nat
  | none => 0
  | some term => term.height

theorem meet_exact (first second : Option (Term Symbol)) (term : Term Symbol) :
    domain (meet first second) term ↔ domain first term ∧ domain second term := by
  by_cases same : first = second
  · simp [meet, same, domain]
  · simp only [meet, same, ↓reduceIte, domain, reduceCtorEq, false_iff, not_and]
    intro firstEq secondEq
    exact same (firstEq.trans secondEq.symm)

omit [DecidableEq Symbol] in
theorem named_children (expected actual : List (Term Symbol)) :
    All₂ domain (expected.map some) actual ↔ actual = expected := by
  induction expected generalizing actual with
  | nil =>
    constructor
    · intro related; cases related; rfl
    · rintro rfl; exact .nil
  | cons first rest ih =>
    constructor
    · intro related
      cases related with
      | cons head tail =>
        have same := Option.some.inj head
        simp [same, (ih _).mp tail]
    · rintro rfl
      exact .cons rfl ((ih _).mpr rfl)

omit [DecidableEq Symbol] in
/-- The actual compact row accepts precisely the term that names its state. -/
theorem spec_exact (original term : Term Symbol) :
    EdgeLanguage domain (fun _ => []) (spec original) term ↔ term = original := by
  cases original with
  | node symbol children =>
    have bridge := CompactEdgeRanks.edgeTerms_source domain (FromTerms.transition (.node symbol children)) []
      (by intro values lengthEq; simp [FromTerms.transition]) term
    simp only [FromTerms.transition, List.length_map] at bridge
    simp only [EdgeLanguage, spec, Option.isSome_some, true_and, List.length_map]
    rw [bridge]
    simp [AutomatonAmbiguity.EdgeLanguage, named_children]

/-- Every local source contract follows from the singleton rows. -/
theorem semantics : Semantics (source (Symbol := Symbol)) domain (fun _ => []) where
  empty := by
    intro state empty term
    cases state with
    | none => simp [domain]
    | some original => simp [source] at empty
  symbolic := by intro state symbolic; simp [source, useSymbolic] at symbolic
  intersection := meet_exact
  parsed := by
    intro state _ edge member
    cases state with
    | none => simp [source] at member
    | some term =>
      have same : edge = spec term := by simpa [source] using member
      subst edge
      cases term with
      | node symbol children =>
        intro groups found
        have same : groups = childGroups children.length [] := by simpa [spec] using found.symm
        exact ⟨by simp [ValidClasses], by simpa [spec] using same⟩
  rows := by
    intro state _ term
    cases state with
    | none => simp [source, domain]
    | some original => simp [source, spec_exact, domain, eq_comm]
  disjoint := by
    intro state _
    cases state <;> simp [source]

/-- Copied singleton intersections never increase the child measure. -/
theorem meet_bound (first second : Option (Term Symbol)) : height (meet first second) ≤ height first := by
  unfold meet
  split
  · exact Nat.le_refl _
  · exact Nat.zero_le _

/-- Source group requests use only proper subterms of their parent. -/
theorem decreases (state requested : Option (Term Symbol))
    (member : requested ∈ requests (source (Symbol := Symbol)) state) : height requested < height state := by
  apply requests_decrease source height ?_ meet_bound state requested member
  intro state edge edgeIn child childIn
  cases state with
  | none => simp [source] at edgeIn
  | some term =>
    have same : edge = spec term := by simpa [source] using edgeIn
    subst edge
    cases term with
    | node symbol children =>
      obtain ⟨term, nested, rfl⟩ := List.mem_map.mp childIn
      exact SourceFiniteRebuild.child_height_lt symbol children term nested

/-- The source recursive primitive computation for one named term. -/
def compileTerm (term : Term Symbol) : Option (Index (Term Symbol)) := reference source height (some term)

/-- The actual compact primitive computation has an exact singleton index. -/
theorem compileTerm_exact (term : Term Symbol) : ResultExact (fun value => value = term) (compileTerm term) := by
  have precise := reference_exact source height decreases domain (fun _ => []) semantics (some term)
  exact (result_ext _ _ (by intro value; simp [domain, eq_comm]) _).mp precise

/-- A reconstructed term cannot compile to the empty result. -/
theorem compileTerm_nonempty (term : Term Symbol) : compileTerm term ≠ none := by
  intro empty
  have precise := compileTerm_exact term
  rw [empty] at precise
  exact precise term rfl

/-- The driver derives exactly one rank for each shared singleton state. -/
theorem compileTerm_count (term : Term Symbol) (result : Index (Term Symbol))
    (success : compileTerm term = some result) : result.count = 1 := by
  have precise := compileTerm_exact term
  rw [success] at precise
  have positive := precise.1
  apply Classical.byContradiction
  intro different
  have within : 1 < result.count := by omega
  obtain ⟨first, firstSelected⟩ := precise.2.1.total 0 (by omega)
  obtain ⟨second, secondSelected⟩ := precise.2.1.total 1 within
  have firstEq := (precise.2.2 first).mp ⟨0, firstSelected⟩
  have secondEq := (precise.2.2 second).mp ⟨1, secondSelected⟩
  subst first
  subst second
  have impossible := (exact_index_api _ result precise).2.2 0 1 term firstSelected secondSelected
  omega

/-- The singleton primitive decoder returns its term only at rank zero. -/
theorem compileTerm_select (term : Term Symbol) (result : Index (Term Symbol))
    (success : compileTerm term = some result) (rank : Nat) :
    result.select rank = if rank = 0 then some term else none := by
  have precise := compileTerm_exact term
  rw [success] at precise
  have count := compileTerm_count term result success
  by_cases zero : rank = 0
  · subst rank
    obtain ⟨value, selected⟩ := precise.2.1.total 0 (by omega)
    have same := (precise.2.2 value).mp ⟨0, selected⟩
    simpa [same] using selected
  · simp only [zero, ↓reduceIte]
    cases selected : result.select rank with
    | none => rfl
    | some value =>
      have within := precise.2.1.bounded rank value selected
      omega

/-- The source cache traversal terminates with the same derived singleton index. -/
theorem cached_term (term : Term Symbol) :
    ∃ after, buildNode source (term.height + 1) (some term) (fun _ => none) = some (compileTerm term, after) ∧
      ∀ state result, after state = some result → ResultExact (domain state) result := by
  obtain ⟨after, complete, valid⟩ := buildNode_terminates source height decreases (some term)
  refine ⟨after, complete, ?_⟩
  intro state result found
  rw [valid state result found]
  exact reference_exact source height decreases domain (fun _ => []) semantics state

/-- Source ordered choice combines the compiled term alternatives. -/
def compile [Ord (Term Symbol)] (input : List (Term Symbol)) : Option (Index (Term Symbol)) :=
  finishAlternatives ((SourceFromTerms.ordered input).map compileTerm)

/-- The root compact primitives give a distinct index of the complete finite input language. -/
theorem compile_exact [Ord (Term Symbol)] (input : List (Term Symbol)) :
    ResultExact (fun term => term ∈ input) (compile input) := by
  have precise := finishAlternatives_exact (SourceFromTerms.ordered input) (fun original value => value = original)
    compileTerm (fun term _ => compileTerm_exact term) ?_
  · exact (result_ext _ _ (by intro value; simp [SourceFromTerms.mem_ordered]) _).mp precise
  · exact (SourceFromTerms.ordered_nodup input).imp (by
      intro first second different value firstEq secondEq
      exact different (firstEq.symm.trans secondEq))

/-- The actual root choice sums one derived count for every term alternative. -/
theorem alternative_count (terms : List (Term Symbol)) :
    CompactIndexChoice.count (terms.filterMap compileTerm) = terms.length := by
  induction terms with
  | nil => rfl
  | cons first rest ih =>
    cases found : compileTerm first with
    | none => exact False.elim (compileTerm_nonempty first found)
    | some result =>
      simp [found, CompactIndexChoice.count, compileTerm_count first result found] at *
      omega

/-- Root choice decodes the exact constructor-row sequence. -/
theorem alternative_select (terms : List (Term Symbol)) (rank : Nat) :
    CompactIndexChoice.select (terms.filterMap compileTerm) rank = terms[rank]? := by
  induction terms generalizing rank with
  | nil => rfl
  | cons first rest ih =>
    cases found : compileTerm first with
    | none => exact False.elim (compileTerm_nonempty first found)
    | some result =>
      cases rank with
      | zero => simp [CompactIndexChoice.select, found, compileTerm_count first result found,
          compileTerm_select first result found]
      | succ rank => simp [CompactIndexChoice.select, found, compileTerm_count first result found, ih]

/-- Successful primitive compilation preserves the exact ascending distinct list count and positions. -/
theorem compile_fields [Ord (Term Symbol)] (input : List (Term Symbol)) (result : Index (Term Symbol))
    (success : compile input = some result) :
    result.count = (SourceFromTerms.ordered input).length ∧
      ∀ rank, result.select rank = (SourceFromTerms.ordered input)[rank]? := by
  have counted := alternative_count (SourceFromTerms.ordered input)
  have selected := alternative_select (SourceFromTerms.ordered input)
  simp only [compile, finishAlternatives, List.filterMap_map, Function.comp_def, id_eq] at success
  cases found : (SourceFromTerms.ordered input).filterMap compileTerm with
  | nil => simp [found, finishChoice] at success
  | cons first rest =>
    have same : CompactIndexChoice.choice (first :: rest) = result := by
      simpa [found, finishChoice] using success
    subst result
    simpa only [found, CompactIndexChoice.choice] using And.intro counted selected

/-- Empty source languages fail choice; nonempty languages have an exact index. -/
theorem compile_empty_iff [Ord (Term Symbol)] (input : List (Term Symbol)) :
    compile input = none ↔ input = [] := by
  have precise := compile_exact input
  constructor
  · intro empty
    rw [empty] at precise
    cases input with
    | nil => rfl
    | cons first rest => exact False.elim (precise first (by simp))
  · rintro rfl
    simp [compile, SourceFromTerms.ordered, CanonicalClasses.sortedSet, finishAlternatives, finishChoice]

/-- Successful source primitive indexes have both inverse laws and exact rejection. -/
theorem compile_inverse [Ord (Term Symbol)] (input : List (Term Symbol)) (result : Index (Term Symbol))
    (success : compile input = some result) :
    Correct result ∧ (∀ term, result.rank term = none ↔ term ∉ input) := by
  have precise := compile_exact input
  rw [success] at precise
  exact ⟨precise.2.1, (exact_index_api _ result precise).2.1⟩

end MicroCFTA.SourceFiniteRebuildDriver
