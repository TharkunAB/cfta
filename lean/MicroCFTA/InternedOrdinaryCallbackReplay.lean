import MicroCFTA.InternedOrdinaryAbsenceReplay
import MicroCFTA.InternedObservedFilter
import MicroCFTA.InternedNestedMissReadback

/-!
# Exact observed replay for normalized ordinary source callbacks

Actual body execution derives the observation from its lexical inputs.
An allowed probe sentinel preserves that observation through source root
self filtering. No callback key equality is supplied as a premise.
-/
namespace MicroCFTA.InternedOrdinaryCallbackReplay
open Cache InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedNestedConstruction InternedNestedFacts InternedNestedProvenance
open InternedLiveEdges InternedNonemptyRecords InternedUnionNonemptyMembers InternedStoredShallowCompletion
open InternedOccurrenceObservations InternedObservedAbsence InternedOrdinaryAbsenceReplay InternedObservedFilter
open InternedNestedMissReadback InternedNestedSpecialization
open InternedBinderProtocol (Reference NodeRef)

/-- Two actual normalized probe calls inherit exact absence replay from ordinary source syntax. -/
theorem callback_related [DecidableEq (EdgeKey Symbol Guard)] (forbidden : NodeRef → Prop)
    (body : Syntax Symbol Guard) (free : BinderFree body) (name : Reference) (allowed : ¬ forbidden (.ref name))
    (first second : List (Value Symbol Guard)) (left right common : State Symbol Guard)
    (lf : Facts left) (rf : Facts right) (cf : Facts common) (ll : Live left) (rl : Live right)
    (ln : NonemptyRecords left) (rn : NonemptyRecords right) (lm : MembersNonempty left) (rm : MembersNonempty right)
    (li : Values left first) (ri : Values right second) (la : Available left (.reference name)) (ra : Available right (.reference name))
    (paired : Paired (Related forbidden) first second)
    (a b : Value Symbol Guard) (afterA afterB : State Symbol Guard)
    (leftDone : callback body first name left = .done a afterA)
    (rightDone : callback body second name right = .done b afterB)
    (lg : Grows afterA common) (rg : Grows afterB common) : Related forbidden a b := by
  have allLeft : Values left (.reference name :: first) := by
    intro value member
    rcases List.mem_cons.mp member with rfl | member
    · exact la
    · exact li value member
  have allRight : Values right (.reference name :: second) := by
    intro value member
    rcases List.mem_cons.mp member with rfl | member
    · exact ra
    · exact ri value member
  obtain ⟨rawA, middleA, bodyDoneA, filterDoneA⟩ := bind_done _ _ _ _ leftDone
  obtain ⟨rawB, middleB, bodyDoneB, filterDoneB⟩ := bind_done _ _ _ _ rightDone
  have va := build_verified body (.reference name :: first) left lf allLeft
  have vb := build_verified body (.reference name :: second) right rf allRight
  have fa : Facts middleA := by simpa only [bodyDoneA, Outcome.state] using va.facts
  have fb : Facts middleB := by simpa only [bodyDoneB, Outcome.state] using vb.facts
  have liveA : Live middleA := by simpa only [bodyDoneA, Outcome.state] using build_live body (.reference name :: first) left ll
  have liveB : Live middleB := by simpa only [bodyDoneB, Outcome.state] using build_live body (.reference name :: second) right rl
  have properA : NonemptyRecords middleA := by simpa only [bodyDoneA, Outcome.state] using build_nonempty body (.reference name :: first) left ln
  have properB : NonemptyRecords middleB := by simpa only [bodyDoneB, Outcome.state] using build_nonempty body (.reference name :: second) right rn
  have membersA : MembersNonempty middleA := by simpa only [bodyDoneA, Outcome.state] using build_membersNonempty body (.reference name :: first) left lf allLeft lm
  have membersB : MembersNonempty middleB := by simpa only [bodyDoneB, Outcome.state] using build_membersNonempty body (.reference name :: second) right rf allRight rm
  obtain ⟨originalA, finishA, originalB, finishB, doneA, doneB, observed⟩ :=
    build_related forbidden body (.reference name :: first) (.reference name :: second) left right lf rf ll rl ln rn
      allLeft allRight (.cons (related_refl forbidden _) paired) free
  have sameA := doneA.symm.trans bodyDoneA
  have sameB := doneB.symm.trans bodyDoneB
  simp only [Outcome.done.injEq] at sameA sameB
  obtain ⟨sameValueA, sameStateA⟩ := sameA
  obtain ⟨sameValueB, sameStateB⟩ := sameB
  subst originalA finishA originalB finishB
  have filterGrowthA : Grows middleA afterA := by
    simpa only [filterDoneA, Outcome.state] using (work_correct (withoutSelfReference name rawA) middleA fa.coherent.valid).2
  have filterGrowthB : Grows middleB afterB := by
    simpa only [filterDoneB, Outcome.state] using (work_correct (withoutSelfReference name rawB) middleB fb.coherent.valid).2
  have rawRelated := observed common cf (grows_trans filterGrowthA lg) (grows_trans filterGrowthB rg)
  have availableA := va.result rawA middleA bodyDoneA
  have availableB := vb.result rawB middleB bodyDoneB
  simp only [work, Outcome.done.injEq] at filterDoneA filterDoneB
  obtain ⟨rfl, rfl⟩ := filterDoneA
  obtain ⟨rfl, rfl⟩ := filterDoneB
  exact filter_related forbidden name allowed rawA rawB middleA middleB common fa fb liveA liveB properA properB
    membersA membersB availableA availableB rawRelated lg rg

end MicroCFTA.InternedOrdinaryCallbackReplay
