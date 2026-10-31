import MicroCFTA.SourceCurrentOpenExposureFields
import MicroCFTA.SourceCurrentConjunctionRowsEqualityEffects

set_option autoImplicit false
open scoped Classical

/-! Field admission from actual warm exposure outcomes. -/
namespace MicroCFTA.SourceCurrentConjunctionRowsExposureFields
open InternedConstructorTemplates
open InternedNestedProvenance (Values Edges)
open SourceCurrentConjunctionRowsWorker
open SourceCurrentConjunctionRowsAllocation (Ready Effects)
variable {Symbol Formula : Type}
local notation "Guard" => SourceSymbolicIndex.Constraint Formula
local notation "Physical" => SourceCurrentConjunctionRowsAllocation.State Symbol Formula

private theorem exposures_core (h : Nat) (nodes : List (Value Symbol Guard)) (before : Physical)
    (ready : Ready before) (available : Values before.heap nodes) :
    let actual := exposures h nodes before
    Effects before actual.state ∧
      ∀ rows after, actual = .done rows after → ∀ row ∈ rows, Edges after.heap row := by
  induction nodes generalizing before with
  | nil =>
    refine ⟨Effects.refl before ready, ?_⟩
    intro rows after same
    cases same
    intro row member
    cases member
  | cons value values ih =>
    have first := SourceEqualityExposureCosts.nodeEdges_verified h value before.heap
      ready.semantic ready.costs (available value List.mem_cons_self)
    have annotated := SourceCurrentOpenExposureFields.nodeEdges_heap
      (SourceCurrentConjunctionEquality.FieldAvailable before.equality) h value before.heap
      ready.semantic ready.fields (available value List.mem_cons_self)
    have head : Effects before
        (⟨(MergedFreshOrdinaryExposure.nodeEdges h value before.heap).state, before.equality⟩ : Physical) :=
      ⟨first.keeps, ⟨first.semantic, first.costs, ready.valid, annotated⟩,
        SourceEqualityConstraintMemoAllocation.grows_refl _⟩
    cases read : MergedFreshOrdinaryExposure.nodeEdges h value before.heap with
    | done edges heap =>
      rw [read] at head first
      have tail := ih (⟨heap, before.equality⟩ : Physical) head.ready
        (fun child member => head.keeps.available child (available child (List.mem_cons_of_mem _ member)))
      cases later : exposures h values (⟨heap, before.equality⟩ : Physical) with
      | done more final =>
        have kept : Effects (⟨heap, before.equality⟩ : Physical) final := by
          simpa only [later, Outcome.state] using tail.1
        have residents := tail.2 more final later
        simp only [exposures, read, later, Outcome.bind, Outcome.state]
        refine ⟨head.trans kept, ?_⟩
        intro rows after same
        cases same
        intro row member
        rcases List.mem_cons.mp member with same | rest
        · subst row
          intro edge present
          exact InternedEdgeResidency.edge_grows heap final.heap kept.keeps.growth edge
            (first.rows edges heap rfl edge present)
        · exact residents row rest
      | failed fault final =>
        have kept : Effects (⟨heap, before.equality⟩ : Physical) final := by
          simpa only [later, Outcome.state] using tail.1
        simp only [exposures, read, later, Outcome.bind, Outcome.state]
        exact ⟨head.trans kept, by intro rows after same; cases same⟩
    | pending key heap =>
      rw [read] at head
      simp only [exposures, read, Outcome.state]
      exact ⟨head, by intro rows after same; cases same⟩
    | unresolved name heap =>
      rw [read] at head
      simp only [exposures, read, Outcome.state]
      exact ⟨head, by intro rows after same; cases same⟩
    | exhausted heap =>
      rw [read] at head
      simp only [exposures, read, Outcome.state]
      exact ⟨head, by intro rows after same; cases same⟩

/-- Actual operand exposures derive full effects and every returned field load. -/
theorem exposures_effects (h : Nat) (nodes : List (Value Symbol Guard)) (before : Physical)
    (ready : Ready before) (available : Values before.heap nodes) :
    let actual := exposures h nodes before
    Effects before actual.state ∧
      match actual with
      | .done rows after => ∀ row ∈ rows, Edges after.heap row ∧
          ∀ edge ∈ row, SourceCurrentConjunctionEquality.FieldAvailable after.equality edge.entry.key.constraint
      | .failed _ _ => True := by
  have checked := exposures_core h nodes before ready available
  refine ⟨checked.1, ?_⟩
  cases actual : exposures h nodes before with
  | failed fault after => trivial
  | done rows after =>
    have kept : Effects before after := by
      simpa only [actual, Outcome.state] using checked.1
    intro row member
    have resident := checked.2 rows after actual row member
    exact ⟨resident, fun edge present => kept.ready.fields edge.entry.key edge (resident edge present)⟩

/-- Literal rows retain actual equality validity, growth, and fields on the initial heap. -/
theorem rows_cache_effects (p h : Nat) (nodes : List (Value Symbol Guard)) (before : Physical)
    (ready : Ready before) (available : Values before.heap nodes) :
    let actual := SourceCurrentConjunctionRowsWorker.rows p h nodes before
    SourceEqualityConstraintMemoAllocation.Valid actual.state.equality ∧
      SourceEqualityConstraintMemoAllocation.Grows before.equality actual.state.equality ∧
      SourceCurrentConjunctionEquality.Fields actual.state.equality before.heap := by
  have first := exposures_core h nodes before ready available
  cases observed : exposures h nodes before with
  | failed fault after =>
    have kept : Effects before after := by
      simpa only [observed, Outcome.state] using first.1
    simp only [SourceCurrentConjunctionRowsWorker.rows, observed, Outcome.bind, Outcome.state]
    exact ⟨kept.ready.valid, kept.grows, ready.fields.grows kept.grows⟩
  | done rows middle =>
    have kept : Effects before middle := by
      simpa only [observed, Outcome.state] using first.1
    have residents := first.2 rows middle observed
    have tupleResident : ∀ edges ∈ SourceCurrentConjunctionTuples.tuples rows, Edges middle.heap edges := by
      intro edges member edge present
      obtain ⟨row, included, own⟩ := List.mem_flatten.mp
        (SourceCurrentConjunctionTuples.tuples_members rows edges member edge present)
      exact residents row included edge own
    have later := SourceCurrentConjunctionRowsEqualityEffects.tuples_cache_effects p h
      (SourceCurrentConjunctionTuples.tuples rows) middle kept.ready tupleResident
    have growth := SourceCurrentConjunctionEquality.grows_trans kept.grows later.2.1
    simp only [SourceCurrentConjunctionRowsWorker.rows, observed, Outcome.bind]
    exact ⟨later.1, growth, ready.fields.grows growth⟩

end MicroCFTA.SourceCurrentConjunctionRowsExposureFields
