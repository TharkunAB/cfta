import MicroCFTA.InternedPairedSelfFilter
import MicroCFTA.InternedRootAlternativeLists
import MicroCFTA.InternedUnionReference
import MicroCFTA.InternedBoundaryShape

/-!
# Observed agreement for paired local root alternatives

The relation also reflects the exact bare local reference. A retained
alternative has no forbidden boundary when the filtered result has none.
Its paired record is therefore equal. Only paired bare locals can differ.
-/
namespace MicroCFTA.InternedObservedRootAlternatives
open Cache InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedObservedAbsence InternedOccurrenceObservations InternedPairedSelfFilter
open InternedNestedFacts InternedNestedProvenance InternedNonemptyRecords InternedLiveEdges
open InternedBinderProtocol (Reference NodeRef NodeKey)

/-- Related records also agree on whether they are their respective bare local reference. -/
def RelatedOwn (forbidden : NodeRef → Prop) (firstName secondName : Reference)
    (first second : Value Symbol Guard) : Prop :=
  Related forbidden first second ∧ (first = .reference firstName ↔ second = .reference secondName)

/-- Paired local references satisfy the relation when the first local is forbidden. -/
theorem local_related (forbidden : NodeRef → Prop) (firstName secondName : Reference)
    (fresh : forbidden (.ref firstName)) :
    RelatedOwn forbidden firstName secondName (Value.reference (Symbol := Symbol) (Guard := Guard) firstName)
      (.reference secondName) :=
  ⟨related_reference forbidden firstName secondName fresh, by simp⟩

/-- An unchanged capture is related when it is neither fresh local reference. -/
theorem capture_related (forbidden : NodeRef → Prop) (firstName secondName : Reference)
    (value : Value Symbol Guard) (firstAbsent : value ≠ .reference firstName)
    (secondAbsent : value ≠ .reference secondName) : RelatedOwn forbidden firstName secondName value value :=
  ⟨related_refl forbidden value, by simp [firstAbsent, secondAbsent]⟩

/-- Retained clear alternatives agree exactly; paired bare locals are the only possible difference. -/
theorem alternatives (forbidden : NodeRef → Prop) (firstName secondName : Reference)
    (first second : List (Value Symbol Guard)) (paired : Paired (RelatedOwn forbidden firstName secondName) first second)
    (clear : ∀ value ∈ first, value ≠ .reference firstName → Clear forbidden value) :
    Paired (fun a b => (a = .reference firstName ∧ b = .reference secondName) ∨
      (a = b ∧ a ≠ .reference firstName ∧ b ≠ .reference secondName)) first second := by
  induction paired with
  | nil => exact .nil
  | @cons a b first second related paired ih =>
      refine .cons ?_ (ih (fun value member => clear value (List.mem_cons_of_mem _ member)))
      by_cases selected : a = .reference firstName
      · exact Or.inl ⟨selected, related.2.mp selected⟩
      · exact Or.inr ⟨related.1.2 (clear a List.mem_cons_self selected), selected,
          fun same => selected (related.2.mpr same)⟩

/-- Observed absence derives exact ordered stripped alternatives without assuming their equality. -/
theorem retained_same (forbidden : NodeRef → Prop) (firstName secondName : Reference)
    (first second : List (Value Symbol Guard)) (paired : Paired (RelatedOwn forbidden firstName secondName) first second)
    (clear : ∀ value ∈ first, value ≠ .reference firstName → Clear forbidden value) :
    InternedRootAlternativeLists.remove firstName first = InternedRootAlternativeLists.remove secondName second :=
  retained_members_same firstName secondName first second (alternatives forbidden firstName secondName first second paired clear)

/-- Source union results reflect the bare-local case from their actual original operands. -/
theorem union_self_iff [DecidableEq (EdgeKey Symbol Guard)] (forbidden : NodeRef → Prop)
    (firstName secondName : Reference) (first second : List (Value Symbol Guard)) (left right : State Symbol Guard)
    (lf : Facts left) (rf : Facts right) (ln : NonemptyRecords left) (rn : NonemptyRecords right)
    (li : Values left first) (ri : Values right second)
    (paired : Paired (RelatedOwn forbidden firstName secondName) first second) :
    (run (makeUnion first) left).1 = .reference firstName ↔
      (run (makeUnion second) right).1 = .reference secondName := by
  rw [InternedUnionReference.makeUnion_reference_iff firstName first left lf.coherent ln li,
    InternedUnionReference.makeUnion_reference_iff secondName second right rf.coherent rn ri]
  apply and_congr
  · simpa only [exists_eq_right] using
      exists_iff paired (fun value => value = .reference firstName) (fun value => value = .reference secondName)
        (fun _ _ related => related.2)
  · apply all_iff paired
    intro a b related
    apply or_congr ?_ related.2
    simpa only [← InternedEmptyNormalization.reference_empty] using related.1.1

/-- Exact filtering equality follows from observed retained alternatives in both deleting branches. -/
theorem deleting_observed [DecidableEq (EdgeKey Symbol Guard)] (forbidden : NodeRef → Prop)
    (firstName secondName : Reference) (firstEntry secondEntry : Interned NodeKey)
    (firstMembers secondMembers : List (Value Symbol Guard)) (firstDepth secondDepth : Nat)
    (firstFree secondFree : List Reference) (left right common : State Symbol Guard)
    (lf : Facts left) (rf : Facts right) (ll : Live left)
    (la : Available left (.union firstEntry firstMembers firstDepth firstFree))
    (paired : Paired (RelatedOwn forbidden firstName secondName) firstMembers secondMembers)
    (present : .reference firstName ∈ firstMembers)
    (clear : Clear forbidden (run (withoutSelfReference firstName (.union firstEntry firstMembers firstDepth firstFree)) left).1)
    (lg : Grows (run (withoutSelfReference firstName (.union firstEntry firstMembers firstDepth firstFree)) left).2 common)
    (rg : Grows (run (withoutSelfReference secondName (.union secondEntry secondMembers secondDepth secondFree)) right).2 common) :
    (run (withoutSelfReference firstName (.union firstEntry firstMembers firstDepth firstFree)) left).1 =
      (run (withoutSelfReference secondName (.union secondEntry secondMembers secondDepth secondFree)) right).1 := by
  have presence : .reference firstName ∈ firstMembers ↔ .reference secondName ∈ secondMembers := by
    simpa only [exists_eq_right] using
      exists_iff paired (fun value => value = .reference firstName) (fun value => value = .reference secondName)
        (fun _ _ related => related.2)
  have retained := retained_same forbidden firstName secondName firstMembers secondMembers paired
    (retained_clear forbidden firstName firstEntry firstMembers firstDepth firstFree left lf ll la clear)
  exact deleting_same firstName secondName firstEntry secondEntry firstMembers secondMembers
    firstDepth secondDepth firstFree secondFree present (presence.mp present) retained left right common
    lf.coherent.valid rf.coherent.valid lg rg

end MicroCFTA.InternedObservedRootAlternatives
