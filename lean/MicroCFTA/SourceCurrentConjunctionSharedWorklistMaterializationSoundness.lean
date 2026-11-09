import MicroCFTA.SourceCurrentConjunctionSharedWorklistMaterializationGraph
import MicroCFTA.SourceCurrentConjunctionSharedWorklistTableSources
import MicroCFTA.SourceCurrentConjunctionRequirementRowsOriginWitness
import MicroCFTA.SourceCurrentConjunctionRequirementRowsRejectionSoundness
import MicroCFTA.SourceCurrentConjunctionTableSoundness

/-!
# Smaller accepted witnesses in the actual materialized table

The coupled storage certificate identifies each cached head's original
chosen tuple and exact descriptor handles. Rejected source prefixes cannot
contain a common accepted tuple. Cached done cells retain the original
descriptor witnesses. The same reader graph then supplies one stored row
of smaller witnesses. The current coupled certificate remains explicit;
the actual worklist must derive it before this local materialization step.
-/
namespace MicroCFTA.SourceCurrentConjunctionSharedWorklistMaterializationSoundness
open Language
open InternedConstructorTemplates (Value EdgeValue)
open InternedGuardedLanguage (meaning)
open SourceCurrentConjunctionEmptinessRows (Accepts EdgeAccepts)
open SourceCurrentConjunctionSharedWorklistMaterializationGraph (RowsRead)
variable {Symbol Formula : Type}
local notation "Guard" => SourceSymbolicIndex.Constraint Formula
local notation "Node" => Value Symbol Guard
local notation "Tuple" => List (EdgeValue Symbol Guard)
local notation "Cell" => SourceCurrentConjunctionRequirementCells.Cell Symbol Formula
local notation "Storage" => SourceCurrentConjunctionRequirementRows.State Symbol Formula
local notation "WorkState" => SourceCurrentConjunctionSharedWorklistStep.State Symbol Formula
local notation "descriptors" => SourceCurrentConjunctionRequirementRows.descriptors
local notation "edgeView" => SourceCurrentConjunctionEquality.edgeView

private theorem all₂_preimage {α β : Type} {relation : α → β → Prop} {inputs : List α} {outputs : List β}
    (aligned : All₂ relation inputs outputs) (output : β) (member : output ∈ outputs) :
    ∃ input ∈ inputs, relation input output := by
  induction aligned with
  | nil => cases member
  | @cons input first inputs outputs own rest ih =>
      rcases List.mem_cons.mp member with same | remaining
      · cases same
        exact ⟨input, List.mem_cons_self, own⟩
      · obtain ⟨source, present, related⟩ := ih remaining
        exact ⟨source, List.mem_cons_of_mem _ present, related⟩

/-- An accepted original tuple supplies one actual cached row of strictly smaller accepted requirements. -/
theorem rows_witness (holds : Guard → Term Symbol → Bool) (ambient : InternedGuardedLanguage.Env Symbol)
    (credits : List Nat) (before : Storage) (origins : List Cell) (sources : List (List Tuple))
    (handle : Nat) (rows : List (List (List Node))) (original : List Tuple) (term : Term Symbol)
    (graph : RowsRead credits before handle rows)
    (coupled : SourceCurrentConjunctionRequirementRowsSemantics.Invariant origins sources before)
    (sourceFound : sources[handle]? = some original)
    (acceptedRaw : ∃ tuple ∈ original, tuple ≠ [] ∧ ∀ edge ∈ tuple,
      EdgeAccepts (meaning holds ambient) (edgeView edge) term) :
    ∃ row ∈ rows, ∀ nodes ∈ row, ∃ part,
      Accepts (meaning holds ambient) nodes part ∧ part.height < term.height := by
  cases term with
  | node symbol terms =>
      revert original
      induction graph with
      | @nil handle credit own cached =>
          intro original sourceFound acceptedRaw
          have rejected := coupled.spines handle original _ sourceFound cached
          obtain ⟨tuple, present, _, accepted⟩ := acceptedRaw
          exact False.elim (SourceCurrentConjunctionRequirementRowsRejectionSoundness.combined_none_no_common
            tuple (rejected tuple present) (meaning holds ambient) (.node symbol terms) accepted)
      | @cons handle credit next tail handles row rows own cached head nextFound smaller rest ih =>
          intro original sourceFound acceptedRaw
          have specification := coupled.spines handle original _ sourceFound cached
          obtain ⟨skipped, chosen, remaining, constraints, offset, source, rejected, live, ordered, registered,
            nextSource⟩ := specification
          obtain ⟨tuple, present, nonempty, accepted⟩ := acceptedRaw
          rw [source] at present
          rcases List.mem_append.mp present with skippedIn | remainingIn
          · exact False.elim (SourceCurrentConjunctionRequirementRowsRejectionSoundness.combined_none_no_common
              tuple (rejected tuple skippedIn) (meaning holds ambient) (.node symbol terms) accepted)
          · rcases List.mem_cons.mp remainingIn with chosenSame | later
            · subst tuple
              obtain ⟨actualClasses, actualLive, witnesses⟩ :=
                SourceCurrentConjunctionRequirementRowsWitness.accepted_descriptors chosen nonempty
                  holds ambient symbol terms accepted
              have same : actualClasses = constraints := Option.some.inj (actualLive.symm.trans live)
              subst actualClasses
              have read := SourceCurrentConjunctionSharedWorklistMaterializationGraph.readRow_graph handles before row head
              refine ⟨row, List.mem_cons_self, ?_⟩
              intro nodes member
              obtain ⟨cellHandle, handleIn, currentDone⟩ := all₂_preimage read nodes member
              rw [ordered] at handleIn
              obtain ⟨index, inside, position⟩ := List.mem_range'.mp handleIn
              simp only [Nat.one_mul] at position
              have handleEq : cellHandle = offset + index := by omega
              have found : (descriptors chosen constraints)[index]? = some (descriptors chosen constraints)[index] :=
                List.getElem?_eq_getElem inside
              have originFound := registered index _ found
              rw [← handleEq] at originFound
              obtain ⟨part, common, bound⟩ := witnesses _ (List.mem_of_getElem? found)
              exact ⟨part, SourceCurrentConjunctionRequirementRowsOriginWitness.stored_done_witness
                origins before.requirements cellHandle _ nodes coupled.cells originFound currentDone
                holds ambient symbol terms part common, bound⟩
            · obtain ⟨result, resultIn, witnesses⟩ := ih remaining nextSource
                ⟨tuple, later, nonempty, accepted⟩
              exact ⟨result, List.mem_cons_of_mem _ resultIn, witnesses⟩

/-- The actual pure table reader transfers the coupled source certificate to semantic table coverage. -/
theorem readTable_covered (holds : Guard → Term Symbol → Bool) (ambient : InternedGuardedLanguage.Env Symbol)
    (credits : List Nat) (before : WorkState) (table : SourceCurrentConjunctionWorker.Table Symbol Formula)
    (origins : List Cell) (sources : List (List Tuple))
    (actual : SourceCurrentConjunctionSharedWorklistMaterialization.readTable credits before = some table)
    (current : SourceCurrentConjunctionSharedWorklistTableSources.Invariant
      (meaning holds ambient) origins sources before) :
    SourceCurrentConjunctionTableSoundness.Covered (meaning holds ambient) table := by
  intro result member term accepted
  obtain ⟨original, originalIn, same, read⟩ :=
    SourceCurrentConjunctionSharedWorklistMaterializationGraph.readTable_member credits before table actual result member
  have originalAccepted : Accepts (meaning holds ambient) original.nodes term := by
    simpa only [same] using accepted
  have covered := current.table original originalIn
  cases selected : original.rows with
  | none =>
      simp only [selected] at covered
      obtain ⟨tuple, impossible, _, _⟩ := covered term originalAccepted
      cases impossible
  | some handle =>
      simp only [selected] at covered read
      obtain ⟨tuples, sourceFound, accepting⟩ := covered
      exact rows_witness holds ambient credits before.storage origins sources handle result.rows tuples term
        read current.storage sourceFound (accepting term originalAccepted)

end MicroCFTA.SourceCurrentConjunctionSharedWorklistMaterializationSoundness
