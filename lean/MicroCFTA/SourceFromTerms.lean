import MicroCFTA.FromTerms
import MicroCFTA.CanonicalClasses

/-!
# Ordered finite-term construction

This file follows `Data.CFTA.fromTerms`. The supplied term comparison is
the source comparison: compare the root symbols, then the child lists
lexicographically. Set readback sorts and removes duplicates before it
builds either the root row or the shared subterm rows.
-/
namespace MicroCFTA.SourceFromTerms
open Language FTAValidation CanonicalClasses Std

variable [DecidableEq Symbol] [Ord (Term Symbol)]

/-- Complete terms in ascending set order. -/
def ordered (input : List (Term Symbol)) : List (Term Symbol) := sortedSet input

/-- Shared state names in ascending set order. -/
def shared (input : List (Term Symbol)) : List (Term Symbol) :=
  sortedSet ((ordered input).flatMap FromTerms.subterms)

/-- The exact row list passed to the public validator. -/
def rows (input : List (Term Symbol)) : Rows (Option (Term Symbol)) Symbol :=
  (none, (ordered input).map FromTerms.transition) ::
    (shared input).map (fun term => (some term, [FromTerms.transition term]))

/-- Row lookup after the source has merged duplicate state keys. -/
def graph (input : List (Term Symbol)) : Automaton (Option (Term Symbol)) Symbol :=
  rowFor (rows input)

theorem mem_ordered (input : List (Term Symbol)) (term : Term Symbol) :
    term ∈ ordered input ↔ term ∈ input := mem_sortedSet _ _

theorem ordered_nodup (input : List (Term Symbol)) : (ordered input).Nodup := sortedSet_nodup _

theorem ordered_ascending [TransOrd (Term Symbol)] (input : List (Term Symbol)) :
    (ordered input).Pairwise (fun first second => (compare first second).isLE = true) :=
  sortedSet_ordered _

theorem mem_shared (input : List (Term Symbol)) (term : Term Symbol) :
    term ∈ shared input ↔ term ∈ input.flatMap FromTerms.subterms := by
  simp [shared, ordered, List.mem_flatMap, mem_sortedSet]

/-- A duplicate-free table visits its selected key exactly once. -/
theorem select_unique [DecidableEq Key] (keys : List Key) (unique : keys.Nodup)
    (values : Key → List Value) (key : Key) :
    (keys.flatMap fun next => if next = key then values next else []) =
      if key ∈ keys then values key else [] := by
  induction keys with
  | nil => simp
  | cons first rest ih =>
    obtain ⟨absent, tail⟩ := List.nodup_cons.mp unique
    by_cases same : first = key
    · subst first
      simp [absent, ih tail]
    · simp [same, Ne.symm same, ih tail]

/-- Root lookup retains the ascending complete-term alternatives exactly. -/
theorem graph_root (input : List (Term Symbol)) :
    graph input none = (ordered input).map FromTerms.transition := by
  simp [graph, rows, rowFor, List.flatMap_map]

/-- A shared subterm state has its one constructor row. -/
theorem graph_some (input : List (Term Symbol)) (term : Term Symbol) :
    graph input (some term) =
      if term ∈ input.flatMap FromTerms.subterms then [FromTerms.transition term] else [] := by
  simp only [graph, rows, rowFor, List.flatMap_cons, List.flatMap_map, Option.some.injEq]
  change ((shared input).flatMap fun next => if next = term then [FromTerms.transition next] else []) = _
  rw [select_unique (shared input) (sortedSet_nodup _) _ term]
  simp only [mem_shared]

/-- Source ordering changes no outgoing edge membership. -/
theorem graph_members (input : List (Term Symbol)) (state : Option (Term Symbol))
    (edge : Edge (Option (Term Symbol)) Symbol) :
    edge ∈ graph input state ↔ edge ∈ FromTerms.graph input state := by
  cases state with
  | none => simp [graph_root, FromTerms.graph, List.mem_map, mem_ordered, DistinctRank.mem_distinct]
  | some term => rw [graph_some]; rfl

/-- The ordered source graph accepts exactly the input finite language. -/
theorem graph_exact (input : List (Term Symbol)) (term : Term Symbol) :
    Accepts (graph input) none term ↔ term ∈ input := by
  rw [← FromTerms.fromTerms_exact input term]
  exact ⟨accepts_transfer _ _ (fun state edge => (graph_members input state edge).mp),
    accepts_transfer _ _ (fun state edge => (graph_members input state edge).mpr)⟩

/-- Shared source states accept precisely their named input subterm. -/
theorem shared_exact (input : List (Term Symbol)) (source term : Term Symbol) :
    Accepts (graph input) (some source) term ↔
      term = source ∧ source ∈ input.flatMap FromTerms.subterms := by
  rw [← FromTerms.subterm_exact input source term]
  exact ⟨accepts_transfer _ _ (fun state edge => (graph_members input state edge).mp),
    accepts_transfer _ _ (fun state edge => (graph_members input state edge).mpr)⟩

/-- The constructor emits the initial state even for an empty language. -/
theorem initial_present (input : List (Term Symbol)) : none ∈ (rows input).map Prod.fst := by
  simp [rows]

theorem keys_exact (input : List (Term Symbol)) (state : Option (Term Symbol)) :
    state ∈ (rows input).map Prod.fst ↔ state = none ∨
      ∃ term ∈ input.flatMap FromTerms.subterms, state = some term := by
  simp [rows, List.map_map, Function.comp_def, mem_shared, eq_comm]

/-- Every child state is among the emitted subterm rows. -/
theorem rows_closed (input : List (Term Symbol)) : Closed (rows input) := by
  intro edge present child member
  obtain ⟨⟨state, outgoing⟩, row, found⟩ := List.mem_flatMap.mp present
  have source : edge ∈ FromTerms.graph input state :=
    (graph_members input state edge).mp ((rowFor_exact _ _ _).mpr ⟨outgoing, row, found⟩)
  obtain ⟨term, nested, same⟩ := FromTerms.row_origin input state edge source
  subst edge
  cases term with
  | node symbol children =>
    obtain ⟨term, childIn, rfl⟩ := List.mem_map.mp member
    exact (keys_exact input _).mpr (Or.inr ⟨term, FromTerms.child_present input symbol children nested term childIn, rfl⟩)

omit [DecidableEq Symbol] [Ord (Term Symbol)] in
/-- Map normalization preserves complete alternative lists, including duplicates. -/
theorem normalize_lookup [DecidableEq State] [Ord State] (table : Rows State Symbol) (state : State) :
    rowFor (normalizeRows table) state = rowFor table state := by
  unfold normalizeRows rowFor
  simp only [List.flatMap_map]
  rw [select_unique _ ((List.mergeSort_perm _ _).nodup_iff.mpr (DistinctRank.distinct_nodup _))]
  by_cases present : state ∈ table.map Prod.fst
  · simp [DistinctRank.mem_distinct, present]
  · simp only [List.mem_mergeSort, DistinctRank.mem_distinct, present, ↓reduceIte]
    symm
    apply List.flatMap_eq_nil_iff.mpr
    intro row member
    have absent : row.1 ≠ state := by
      intro same
      exact present (List.mem_map.mpr ⟨row, member, same⟩)
    simp [absent]

/-- The actual public finite-term builder. -/
def build [Ord (Option (Term Symbol))] (input : List (Term Symbol)) := mkFTA none (rows input)

/-- Successful validation retains the exact ordered source graph. -/
theorem build_rows [Ord (Option (Term Symbol))] (input : List (Term Symbol))
    (result : Rows (Option (Term Symbol)) Symbol) (success : build input = .ok result)
    (state : Option (Term Symbol)) : rowFor result state = graph input state := by
  rw [mkFTA_returns none (rows input) result success]
  exact normalize_lookup _ _

/-- A successful finite rebuild accepts all and only the supplied terms. -/
theorem build_exact [Ord (Option (Term Symbol))] (input : List (Term Symbol))
    (result : Rows (Option (Term Symbol)) Symbol) (success : build input = .ok result)
    (term : Term Symbol) : Accepts (rowFor result) none term ↔ term ∈ input := by
  have same : rowFor result = graph input := funext (build_rows input result success)
  rw [same, graph_exact]

end MicroCFTA.SourceFromTerms
