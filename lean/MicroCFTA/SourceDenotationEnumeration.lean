import MicroCFTA.SourceDenotationRuns
import MicroCFTA.EnumerationCPSSource
import MicroCFTA.EnumerationBoundedRows

/-!
# Bounded denotation from the actual ordered enumeration protocol

The finite source protocol retains run order and residual order. A sufficient
execution bound gives all accepted terms of a bounded constructor graph.
Source extraction and lazy runtime termination remain separate from this
finite algebraic execution. Model errors are not semantic rejections.
-/

namespace MicroCFTA.SourceDenotationEnumeration

open Language EnumerationState EnumerationCorrectness EnumerationSemantics

/-- The source runs function drops the final state and retains each term and its residual list. -/
def rows (graph : Graph Symbol Guard) (marker : Symbol) (fuel root : Nat) :
    List (Term Symbol × List (Guard × Term Symbol)) :=
  (EnumerationCPSSource.runs graph marker fuel root).map Prod.fst

/-- Projection preserves the checked successful protocol's exact row order. -/
theorem rows_eq (graph : Graph Symbol Guard) (marker : Symbol) (fuel root : Nat) :
    rows graph marker fuel root = EnumerationCPSRuns.values graph marker fuel root := by
  rw [rows, EnumerationCPSSource.runs_eq]
  rfl

/-- Each term and residual list comes from an actual successful final enumeration state. -/
theorem rows_member (graph : Graph Symbol Guard) (marker : Symbol) (fuel root : Nat)
    (term : Term Symbol) (pending : List (Guard × Term Symbol)) :
    (term, pending) ∈ rows graph marker fuel root ↔
      ∃ after, .ok ((term, pending), after) ∈ EnumerationState.runs graph marker fuel root := by
  rw [rows_eq, EnumerationCPSRuns.values_member, EnumerationCPSRuns.runs_eq]

/-- A sufficient finite protocol bound retains a witness for every accepted term. -/
def Sufficient (graph : Graph Symbol Guard) (meaning : Guard → Term Symbol → Prop)
    (marker : Symbol) (root fuel : Nat) : Prop :=
  ∀ term, Accepted graph meaning root term →
    ∃ pending, (term, pending) ∈ rows graph marker fuel root ∧
      ∀ obligation ∈ pending, meaning obligation.1 obligation.2

/-- A bounded complete graph has one sufficient finite protocol bound for its entire language. -/
theorem sufficient_exists (graph : Graph Symbol Guard) (meaning : Guard → Term Symbol → Prop)
    (complete : CompleteGraph graph) (correct : IntersectionCorrect graph (Accepted graph meaning))
    (marker : Symbol) (root height : Nat)
    (bounded : ∀ term, Accepted graph meaning root term → term.height ≤ height) :
    ∃ cutoff, ∀ fuel, cutoff ≤ fuel → Sufficient graph meaning marker root fuel := by
  obtain ⟨cutoff, uniform⟩ := EnumerationLanguage.runs_uniform_height_bound graph meaning complete correct marker root height
  refine ⟨cutoff, ?_⟩
  intro fuel enough term accepted
  obtain ⟨pending, after, member, checked⟩ := (uniform fuel enough term (bounded term accepted)).mp accepted
  exact ⟨pending, (rows_member graph marker fuel root term pending).mpr ⟨after, member⟩, checked⟩

/-- Every successful residual-filtered result is sound; sufficiency supplies the converse. -/
theorem successful_exact [DecidableEq Symbol]
    (graph : Graph Symbol Guard) (meaning : Guard → Term Symbol → Prop)
    (complete : CompleteGraph graph) (correct : IntersectionCorrect graph (Accepted graph meaning))
    (marker : Symbol) (fuel root : Nat) (sufficient : Sufficient graph meaning marker root fuel)
    (holds : Guard × Term Symbol → Bool)
    (semantic : ∀ obligation, holds obligation = true ↔ meaning obligation.1 obligation.2)
    (evaluates : Guard × Term Symbol → Nat → SolverAdapter.Result → Prop)
    (adequate : SourceDenotationEffects.Adequate evaluates holds)
    (output : List (Term Symbol)) (work : Nat)
    (run : SourceDenotationRuns.Run evaluates (rows graph marker fuel root) (.ok output) work)
    (term : Term Symbol) : term ∈ output ↔ Accepted graph meaning root term := by
  rw [SourceDenotationRuns.member_iff evaluates holds adequate _ output work run term]
  constructor
  · rintro ⟨pending, member, checked⟩
    obtain ⟨after, executed⟩ := (rows_member graph marker fuel root term pending).mp member
    exact EnumerationAssignment.runs_sound graph meaning complete correct marker fuel root term pending after
      executed (fun obligation present => (semantic obligation).mp (checked obligation present))
  · intro accepted
    obtain ⟨pending, member, checked⟩ := sufficient term accepted
    exact ⟨pending, member, fun obligation present => (semantic obligation).mpr (checked obligation present)⟩

/-- Source-protocol recovery loses no checked result when all model error rows are absent. -/
theorem lossless_source_order (graph : Graph Symbol Guard) (marker : Symbol) (fuel root : Nat)
    (safe : EnumerationCPSChecked.ErrorFree (EnumerationCPSRuns.runs graph marker fuel root)) :
    (EnumerationCPSSource.runs graph marker fuel root).map Except.ok =
      EnumerationState.runs graph marker fuel root := by
  rw [EnumerationCPSSource.runs_eq, EnumerationCPSRuns.error_free_runner graph marker fuel root safe,
    EnumerationCPSRuns.runs_eq]

/-- Actual bounded constructor rows derive the sufficient-bound premise. -/
theorem bounded_sufficient [DecidableEq Symbol]
    (encode : Nat × Nat → Nat) (decode : Nat → Nat × Nat) (roundtrip : ∀ key, decode (encode key) = key)
    (source : Nat → List (EnumerationState.Edge Symbol Guard)) (meet : Nat → Nat → Nat)
    (valid : ∀ node edge, edge ∈ source node → ValidEdge edge)
    (meaning : Guard → Term Symbol → Prop)
    (sourceRows : EnumerationIntersection.HashRows (fun state => (source state).map (EnumerationLanguage.edgeView meaning)) meet)
    (marker : Symbol) (height node : Nat) :
    ∃ cutoff, ∀ fuel, cutoff ≤ fuel → Sufficient
      (EnumerationBoundedRows.graph encode decode source (EnumerationBoundedRows.boundedMeet encode decode meet))
      meaning marker (encode (height, node)) fuel := by
  apply sufficient_exists _ meaning (EnumerationBoundedRows.complete encode decode source _ valid)
    (EnumerationBoundedRows.intersection_correct encode decode roundtrip source meet valid meaning sourceRows)
    marker (encode (height, node)) height
  intro term accepted
  exact ((EnumerationBoundedRows.accepted_exact encode decode roundtrip source _ valid meaning height node term).mp accepted).2

end MicroCFTA.SourceDenotationEnumeration
