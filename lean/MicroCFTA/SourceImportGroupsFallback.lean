import MicroCFTA.SourceImportGroupsSampling
import MicroCFTA.SourceFromTermsArity

/-!
# Observation groups of the successful bounded fallback rebuild

The source fromTerms result supplies the language equality. The split and
finite member constructors then derive coverage, unique ranks, cardinality
weights, and the uniform output law. No local group invariant is assumed.

This is a finite reference index of the constructed parts. Native fromFTA
interning, observation-map comparison, and Flat.fromAutomaton decoder order
still require their representation adapters.
-/

namespace MicroCFTA.SourceImportGroupsFallback

open Language Observation ObservationGraph FTAValidation Probability
open SourceImportGroups SourceImportGroupsSampling

variable [DecidableEq Symbol] [DecidableEq Refinement]
  [Ord (Term (Label Symbol Refinement))] [Ord (Option (Term (Label Symbol Refinement)))]
  (input : List (Term (Label Symbol Refinement)))
  (table : Rows (Option (Term (Label Symbol Refinement))) (Label Symbol Refinement))
  (success : SourceFromTerms.build input = .ok table)
  (requested : List Path)
  (before : Variant (Option (Term (Label Symbol Refinement))) Symbol Refinement →
    Variant (Option (Term (Label Symbol Refinement))) Symbol Refinement → Bool)

/-- The actual successful fallback table has a constructed grouped distinct-term index. -/
def index : DistinctRank.Index (Accepts (rowFor table) none) :=
  globalIndex (rowFor table) requested none before input (SourceFromTerms.build_exact input table success)

include success

/-- The sorted observation parts form an exact finite partition of the rebuilt term set. -/
theorem partition :
    (groups (rowFor table) requested none before input).flatten.Perm input.eraseDups ∧
      (groups (rowFor table) requested none before input).flatten.Nodup :=
  ⟨groups_perm _ _ _ _ _ (SourceFromTerms.build_exact input table success), groups_nodup _ _ _ _ _⟩

/-- All concrete graph parts receive exact finite members, including empty parts. -/
theorem part_exact (part : Variant (Option (Term (Label Symbol Refinement))) Symbol Refinement)
    (present : part ∈ ImportObservations.split (rowFor table) requested none) (term) :
    term ∈ members input requested part ↔ AcceptsNode (rowFor table) part.node term :=
  members_exact _ _ _ _ (SourceFromTerms.build_exact input table success) part present term

/-- Count fields sum to distinct fallback terms, independently of observation sort order. -/
theorem count :
    ((groups (rowFor table) requested none before input).map List.length).sum = input.eraseDups.length ∧
      (index input table success requested before).count = input.eraseDups.length :=
  ⟨groups_count _ _ _ _ _ (SourceFromTerms.build_exact input table success),
    rank_count _ _ _ _ _ (SourceFromTerms.build_exact input table success)⟩

/-- Both finite distinct-term rank laws follow from construction of the observation parts. -/
theorem inverses :
    (∀ term, (index input table success requested before).decode
      ((index input table success requested before).encode term) = term) ∧
    (∀ rank, (index input table success requested before).encode
      ((index input table success requested before).decode rank) = rank) :=
  ⟨DistinctRank.Index.decode_encode _, DistinctRank.Index.encode_decode _⟩

/-- Uniform grouping preserves every event probability of the distinct fallback term set. -/
theorem uniform_events (event : Term (Label Symbol Refinement) → Bool) :
    eventMass event (sampling (groups (rowFor table) requested none before input)) =
      eventMass event (normalize (counting input.eraseDups)) :=
  event_probability _ _ _ _ _ (SourceFromTerms.build_exact input table success) event

/-- Each original fallback term receives one equal share, regardless of duplicate input entries. -/
theorem term_probability (term : Term (Label Symbol Refinement)) (present : term ∈ input) :
    eventMass (fun found => found == term) (sampling (groups (rowFor table) requested none before input)) =
      1 / (input.eraseDups.length : Rat) :=
  uniform_term_probability _ _ _ _ _ (SourceFromTerms.build_exact input table success) term
    ((SourceFromTerms.build_exact input table success term).mpr present)

/-- The finite public PMF query normalizes and aggregates this law without changing any event. -/
theorem pmf (nonempty : input ≠ []) :
    SourcePmfQuery.finite (SourceError := Unit) (sampling (groups (rowFor table) requested none before input)) =
      .ok (SourcePmfAggregation.pmf (sampling (groups (rowFor table) requested none before input))) ∧
    ∀ event, eventMass event (SourcePmfAggregation.aggregate
      (sampling (groups (rowFor table) requested none before input))) =
        eventMass event (normalize (counting input.eraseDups)) :=
  ⟨query_pmf _ _ _ _ _ (SourceFromTerms.build_exact input table success) nonempty,
    pmf_event _ _ _ _ _ (SourceFromTerms.build_exact input table success)⟩

end MicroCFTA.SourceImportGroupsFallback
