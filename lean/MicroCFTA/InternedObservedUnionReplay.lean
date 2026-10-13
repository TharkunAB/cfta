import MicroCFTA.InternedNormalizedUnionReplay
import MicroCFTA.InternedObservedRootAlternatives
import MicroCFTA.InternedUnionAlternativeClear

/-!
# Exact observed replay after source union normalization

Paired root alternatives reflect their respective bare local references.
Every other retained alternative agrees when the first filtered result
has no forbidden boundary. Ordered deduplication and actual constructor
replay then give exact complete output equality in a common cache history.
-/
namespace MicroCFTA.InternedObservedUnionReplay
open InternedConstructorTemplates InternedProbeProvenance InternedNestedFacts InternedNestedProvenance
open InternedObservedAbsence InternedObservedRootAlternatives InternedOccurrenceObservations
open InternedRootAlternativeLists InternedNormalizedUnionReplay InternedUnionNormalForm
open InternedUnionNonemptyMembers InternedLiveEdges InternedUnionFilterFusion
open InternedBinderProtocol (Reference NodeRef)

/-- Identity normalization is singleton self exactly for a nonempty list of bare self copies. -/
theorem singleton_self_iff (name : Reference) (values : List (Value Symbol Guard)) :
    distinctNodes values = [.reference name] ↔
      .reference name ∈ values ∧ ∀ value ∈ values, value = .reference name := by
  constructor
  · intro same
    refine ⟨distinctNodes_member values (.reference name) (by simp [same]), ?_⟩
    intro value member
    exact (referenceOf_self_iff name value).mp
      (InternedUnionSeparation.singleton_all values (.reference name) same value member)
  · rintro ⟨present, only⟩
    exact InternedUnionReference.distinct_reference name values present only

/-- Paired local reflection determines the canonical singleton branch before either union request. -/
theorem singleton_pair (forbidden : NodeRef → Prop) (firstName secondName : Reference)
    (first second : List (Value Symbol Guard))
    (paired : Paired (RelatedOwn forbidden firstName secondName) first second) :
    distinctNodes first = [.reference firstName] ↔ distinctNodes second = [.reference secondName] := by
  rw [singleton_self_iff, singleton_self_iff]
  apply and_congr
  · simpa only [exists_eq_right] using exists_iff paired
      (fun value => value = .reference firstName) (fun value => value = .reference secondName)
      (fun _ _ related => related.2)
  · exact all_iff paired _ _ (fun _ _ related => related.2)

/-- A forbidden bare local cannot be the observed result of the complete union and filter. -/
theorem clear_not_singleton [DecidableEq (EdgeKey Symbol Guard)] (forbidden : NodeRef → Prop)
    (name : Reference) (fresh : forbidden (.ref name)) (values : List (Value Symbol Guard)) (state : State Symbol Guard)
    (clear : Clear forbidden (run (withoutSelfReference name (run (makeUnion values) state).1)
      (run (makeUnion values) state).2).1) :
    distinctNodes (values.flatMap unionMembers) ≠ [.reference name] := by
  intro same
  rw [singleton_self name values state same] at clear
  exact clear (.ref name) (by simp [run, InternedBoundaryAtoms.atoms]) fresh

/-- Actual source normalization and own filtering preserve exact observed equality in every union branch. -/
theorem filtered_same [DecidableEq (EdgeKey Symbol Guard)] (forbidden : NodeRef → Prop)
    (firstName secondName : Reference) (fresh : forbidden (.ref firstName))
    (first second : List (Value Symbol Guard)) (left right common : State Symbol Guard)
    (lf : Facts left) (rf : Facts right) (lflat : Flat left) (rflat : Flat right)
    (lm : MembersNonempty left) (rm : MembersNonempty right) (ll : Live left)
    (li : Values left first) (ri : Values right second)
    (paired : Paired (RelatedOwn forbidden firstName secondName)
      (first.flatMap unionMembers) (second.flatMap unionMembers))
    (clear : Clear forbidden (run (withoutSelfReference firstName (run (makeUnion first) left).1)
      (run (makeUnion first) left).2).1)
    (lg : Grows (run (withoutSelfReference firstName (run (makeUnion first) left).1)
      (run (makeUnion first) left).2).2 common)
    (rg : Grows (run (withoutSelfReference secondName (run (makeUnion second) right).1)
      (run (makeUnion second) right).2).2 common) :
    (run (withoutSelfReference firstName (run (makeUnion first) left).1) (run (makeUnion first) left).2).1 =
      (run (withoutSelfReference secondName (run (makeUnion second) right).1) (run (makeUnion second) right).2).1 := by
  have notFirst := clear_not_singleton forbidden firstName fresh first left clear
  have notSecond : distinctNodes (second.flatMap unionMembers) ≠ [.reference secondName] :=
    fun same => notFirst ((singleton_pair forbidden firstName secondName _ _ paired).mpr same)
  have stripped := retained_same forbidden firstName secondName _ _ paired
    (InternedUnionAlternativeClear.clear_alternative forbidden firstName first left lf lflat ll li clear)
  have selectedSame := normalized_equal firstName secondName first second stripped
  have leftRequest := filtered_as_request firstName first left lf lflat lm li notFirst
  have rightRequest := filtered_as_request secondName second right rf rflat rm ri notSecond
  rw [leftRequest] at lg ⊢
  rw [rightRequest] at rg ⊢
  rw [selectedSame] at lg ⊢
  exact run_shared _ (run (makeUnion first) left).2 (run (makeUnion second) right).2 common
    (run_correct (makeUnion first) left lf.coherent.valid).1
    (run_correct (makeUnion second) right rf.coherent.valid).1 lg rg

end MicroCFTA.InternedObservedUnionReplay
