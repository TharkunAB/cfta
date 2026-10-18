import MicroCFTA.SourceCurrentObservationReaderSupport
import MicroCFTA.InternedStoredPlanBinderDepthNormalization

/-!
# Actual reader support for open values with zero stored-plan depth

Open ordinary nodes, unions and references need no open binder instruction.
They can contain arbitrary closed Mu values. Actual closed preparation
therefore supports these open values at the same final reader. This does
not prepare arbitrary open Mu values or compare the cold and final readers.
-/
namespace MicroCFTA.SourceCurrentZeroDepthReaderSupport
open Cache InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedNestedConstruction (Outcome)
open InternedStoredPlanBinderDepth (valueDepth)
open InternedStoredPlanBinderDepthNormalization (ordinary_child_le)
open SourceCurrentObservationReaderSupport (WarmSupport Preparation)
open SourceEqualityRequiredCache (Ready Keeps)
open MergedFreshOrdinaryGraph (successors)

variable [DecidableEq (EdgeKey Symbol Guard)]

private theorem mu_closed (entry : Interned InternedBinderProtocol.NodeKey)
    (body depth ordinary : Value Symbol Guard)
    (zero : valueDepth (.mu entry body depth ordinary) = 0) :
    (Value.mu entry body depth ordinary).free = [] := by
  rw [valueDepth.eq_def] at zero
  split at zero
  · exact List.isEmpty_iff.mp (by assumption)
  · simp only at zero
    omega

/-- Closed Mu support also supports every available value with zero stored-plan binder depth. -/
theorem warm (reader : State Symbol Guard) (ready : Ready reader)
    (closed : WarmSupport reader (fun value => Available reader value ∧ value.free = [])) :
    WarmSupport reader (fun value => Available reader value ∧ valueDepth value = 0) := by
  refine ⟨?_, ?_, ?_⟩
  · intro value included next member
    cases value with
    | empty | reference | node => cases member
    | union entry members depth free =>
        have available := included.1.children next member
        have bound := ordinary_child_le (.union entry members depth free) next reader
          ready.semantic.1.normal.facts.coherent included.1 (by intros; intro impossible; cases impossible) member
        exact ⟨available, Nat.eq_zero_of_le_zero (included.2 ▸ bound)⟩
    | mu entry body depth ordinary =>
        have free := mu_closed entry body depth ordinary included.2
        obtain ⟨available, free⟩ := closed.1 _ ⟨included.1, free⟩ next member
        exact ⟨available, InternedStoredPlanBinderDepth.closed_zero next free⟩
  · intro value included row member child present
    cases value with
    | empty | reference | union | mu => cases member
    | node entry rows depth free =>
        have selected : child ∈ rows.flatMap EdgeValue.children := List.mem_flatMap.mpr ⟨row, member, present⟩
        have bound := ordinary_child_le (.node entry rows depth free) child reader
          ready.semantic.1.normal.facts.coherent included.1 (by intros; intro impossible; cases impossible) selected
        exact ⟨included.1.children child selected, Nat.eq_zero_of_le_zero (included.2 ▸ bound)⟩
  · intro value included
    cases value with
    | empty | reference | node | union => exact ⟨_, rfl⟩
    | mu entry body depth ordinary =>
        exact closed.2.2 _ ⟨included.1, mu_closed entry body depth ordinary included.2⟩

/-- Initial Ready data constructs actual preparation and support for all available zero-depth values. -/
theorem prepare (before : State Symbol Guard) (ready : Ready before) :
    ∃ after, Preparation before after ∧ Keeps before after ∧
      WarmSupport after (fun value => Available after value ∧ valueDepth value = 0) := by
  obtain ⟨after, actual, kept, closed⟩ := SourceCurrentObservationReaderSupport.prepare before ready
  exact ⟨after, actual, kept, warm after kept.ready closed⟩

end MicroCFTA.SourceCurrentZeroDepthReaderSupport
