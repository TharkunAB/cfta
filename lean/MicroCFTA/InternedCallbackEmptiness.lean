import MicroCFTA.InternedFilterEmptiness
import MicroCFTA.InternedNestedMissReadback

/-!
# Empty results of arbitrary normalized source callbacks

Root self filtering preserves the empty status of the actual body result.
This theorem applies to arbitrary nested syntax and includes pending source
outcomes. It does not assume that the body construction completes.
-/
namespace MicroCFTA.InternedCallbackEmptiness
open InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedNestedConstruction InternedNestedFacts InternedNestedProvenance InternedNestedMissReadback
open InternedLiveEdges InternedNonemptyRecords InternedUnionNonemptyMembers InternedFilterEmptiness
open InternedBinderProtocol (Reference)

/-- Normalizing an arbitrary actual callback does not change whether it returns EmptyNode. -/
theorem callback_empty_iff [DecidableEq (EdgeKey Symbol Guard)] (body : Syntax Symbol Guard)
    (environment : List (Value Symbol Guard)) (name : Reference) (state : State Symbol Guard)
    (facts : Facts state) (inputs : Values state environment) (argument : Available state (.reference name))
    (live : Live state) (proper : NonemptyRecords state) (members : MembersNonempty state) :
    (∃ after, callback body environment name state = .done .empty after) ↔
      ∃ after, build body (.reference name :: environment) state = .done .empty after := by
  have all : Values state (.reference name :: environment) := by
    intro value member
    rcases List.mem_cons.mp member with rfl | member
    · exact argument
    · exact inputs value member
  cases returned : build body (.reference name :: environment) state with
  | pending key after => simp [callback, returned, Outcome.bind]
  | done value after =>
      have checked := build_verified body _ state facts all
      have afterFacts : Facts after := by simpa only [returned, Outcome.state] using checked.facts
      have afterLive : Live after := by
        simpa only [returned, Outcome.state] using build_live body (.reference name :: environment) state live
      have afterProper : NonemptyRecords after := by
        simpa only [returned, Outcome.state] using build_nonempty body (.reference name :: environment) state proper
      have afterMembers : MembersNonempty after := by
        simpa only [returned, Outcome.state] using build_membersNonempty body _ state facts all members
      have empty := filter_empty_iff name value after afterFacts.coherent afterFacts.linked afterLive
        afterProper afterMembers (checked.result value after returned)
      simpa [callback, returned, Outcome.bind, work, InternedEmptyNormalization.reference_empty] using empty

end MicroCFTA.InternedCallbackEmptiness
