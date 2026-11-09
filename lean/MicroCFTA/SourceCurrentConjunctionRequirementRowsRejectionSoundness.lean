import MicroCFTA.SourceCurrentConjunctionRequirementRowsTrace
import MicroCFTA.SourceCurrentConjunctionRowsAllocation

/-!
# Contradictions in actual rejected row prefixes

Current physical readiness and resident tuple edges identify a rejected
preparation with the source combined equality contradiction. Rejection
retains the native heap and derives readiness at the returned equality
state. The actual rejection chain then identifies its skipped prefix.
No closed-edge premise or future fold result is required.
-/
namespace MicroCFTA.SourceCurrentConjunctionRequirementRowsRejectionSoundness
open Language
open InternedConstructorTemplates (Value EdgeValue)
open InternedNestedProvenance (Edges)
open SourceCurrentConjunctionRowsAllocation (Ready)
open SourceCurrentConjunctionRequirementRows
open SourceCurrentConjunctionRequirementRowsTrace (Rejected)
variable {Symbol Formula : Type}
local notation "Guard" => SourceSymbolicIndex.Constraint Formula
local notation "Node" => Value Symbol Guard
local notation "Tuple" => List (EdgeValue Symbol Guard)
local notation "Storage" => SourceCurrentConjunctionRequirementRows.State Symbol Formula
local notation "combined" => SourceCurrentConjunctionEmptinessRows.combined
local notation "edgeView" => SourceCurrentConjunctionEquality.edgeView

/-- An actual rejected tuple has contradictory combined classes and derives its exact ready endpoint. -/
theorem prepareTuple_rejected {tuple : Tuple} {before after : Storage}
    (actual : prepareTuple tuple before = .done none after) (ready : Ready before.requirements.physical)
    (resident : Edges before.requirements.physical.heap tuple) :
    combined (tuple.map edgeView) = none ∧
      after.requirements.physical.heap = before.requirements.physical.heap ∧ Ready after.requirements.physical := by
  obtain ⟨operations, folded, same⟩ := SourceCurrentConjunctionRequirementRowsTrace.prepareTuple_none actual
  obtain ⟨result, done, valid, _, classes, _, _, fields⟩ :=
    SourceCurrentConjunctionEquality.fold_heap_correct tuple before.requirements.physical.heap
      before.requirements.physical.equality ready.valid ready.fields resident
  have resultSame : result = .contradiction :=
    Option.some.inj (Except.ok.inj (done.symm.trans (congrArg Prod.fst folded)))
  subst result
  have physical : after.requirements.physical =
      ⟨before.requirements.physical.heap,
        (SourceCurrentConjunctionEquality.fold tuple before.requirements.physical.equality).2⟩ := by
    rw [same]
    rw [folded]
  refine ⟨classes.symm, ?_, ?_⟩
  · rw [same]
  · rw [physical]
    exact ⟨ready.semantic, ready.costs, valid, fields⟩

/-- Contradictory combined classes exclude every common accepted term of the tuple. -/
theorem combined_none_no_common (tuple : Tuple) (contradiction : combined (tuple.map edgeView) = none)
    (meaning : Node → Term Symbol → Prop) (term : Term Symbol) :
    ¬ ∀ edge ∈ tuple, SourceCurrentConjunctionEmptinessRows.EdgeAccepts meaning (edgeView edge) term := by
  intro accepted
  have satisfied := (SourceCurrentConjunctionEmptinessRows.combined_sat (tuple.map edgeView) term).mpr (by
    intro view member
    obtain ⟨edge, included, rfl⟩ := List.mem_map.mp member
    exact (accepted edge included).choose_spec.2.2)
  rw [contradiction] at satisfied
  exact satisfied

/-- The actual rejected chain exposes its contradictory original prefix and unchanged native heap. -/
theorem rejected_prefix {handle : Nat} {original remaining : List Tuple} {before after : Storage}
    (actual : Rejected handle original before remaining after) (ready : Ready before.requirements.physical)
    (resident : ∀ tuple ∈ original, Edges before.requirements.physical.heap tuple) :
    ∃ skipped, original = skipped ++ remaining ∧
      (∀ tuple ∈ skipped, combined (tuple.map edgeView) = none) ∧
      Ready after.requirements.physical ∧ after.requirements.physical.heap = before.requirements.physical.heap := by
  revert ready resident
  induction actual with
  | refl =>
      intro ready _
      refine ⟨[], rfl, ?_, ready, rfl⟩
      intro tuple member
      cases member
  | @step tuple rest remaining before current after prepared tail ih =>
      intro ready resident
      have first := prepareTuple_rejected prepared ready (resident tuple List.mem_cons_self)
      have suffix : ∀ next ∈ rest,
          Edges (updateSpine handle (.pending rest) current).requirements.physical.heap next := by
        intro next member
        change Edges current.requirements.physical.heap next
        rw [first.2.1]
        exact resident next (List.mem_cons_of_mem _ member)
      obtain ⟨skipped, same, contradictory, finalReady, finalHeap⟩ := ih first.2.2 suffix
      refine ⟨tuple :: skipped, congrArg (List.cons tuple) same, ?_, finalReady, finalHeap.trans first.2.1⟩
      intro next member
      rcases List.mem_cons.mp member with equal | old
      · cases equal
        exact first.1
      · exact contradictory next old

end MicroCFTA.SourceCurrentConjunctionRequirementRowsRejectionSoundness
