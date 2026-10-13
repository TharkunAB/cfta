import MicroCFTA.InternedFreshOrdinaryGrowth
import MicroCFTA.InternedFreshOrdinaryFacts
import MicroCFTA.InternedNestedPendingPreservation

/-!
# Active reservation preservation under the repaired scheduler

A nested callback cannot complete an already pending ancestor record.
This holds through discarded effects and either final outcome.
It does not exclude new pending readback during the repaired execution.
-/
namespace MicroCFTA.InternedFreshOrdinaryPending
open Cache InternedConstructorTemplates
open InternedNestedConstruction (Syntax EdgeSyntax Outcome work request IsPending
  bind_correct work_correct bind_preserves_pending work_preserves_pending request_preserves_pending)
open InternedFreshOrdinaryConstruction InternedFreshOrdinaryGrowth
open InternedFreshOrdinaryFacts (callback)
open InternedBinderProtocol (MuKey NodeRef)

mutual
/-- Every arbitrary source expression preserves all already pending ancestor slots on both outcomes. -/
theorem build_preserves_pending [DecidableEq (EdgeKey Symbol Guard)] (expression : Syntax Symbol Guard)
    (environment : List (Value Symbol Guard)) (probes : MuKey NodeRef) (state : State Symbol Guard)
    (valid : InternedConstructorTemplates.Valid state) (pending : IsPending (.mu probes) state) :
    IsPending (.mu probes) (build expression environment state).state := by
  cases expression with
  | empty | var index => simpa only [build, Outcome.state] using pending
  | node edges =>
      simp only [build]
      exact bind_preserves_pending _ _ (buildEdges_correct edges environment state valid).1
        (buildEdges_preserves_pending edges environment probes state valid pending)
        (fun values current currentValid currentPending => work_preserves_pending (makeNode values) (makeNode_ordinary values)
          probes current currentValid currentPending)
  | union members =>
      simp only [build]
      exact bind_preserves_pending _ _ (buildMany_correct members environment state valid).1
        (buildMany_preserves_pending members environment probes state valid pending)
        (fun values current currentValid currentPending => work_preserves_pending (makeUnion values) (makeUnion_ordinary values)
          probes current currentValid currentPending)
  | binder smart body =>
      let callback := fun name current => (build body (.reference name :: environment) current).bind
        fun value next => work (withoutSelfReference name value) next
      have growing : ∀ name current, InternedConstructorTemplates.Valid current →
          InternedConstructorTemplates.Valid (callback name current).state ∧ Grows current (callback name current).state := by
        intro name current currentValid
        exact bind_correct _ _ current (build_correct body _ current currentValid)
          (fun value state valid => work_correct (withoutSelfReference name value) state valid)
      have preserved : ∀ name current, InternedConstructorTemplates.Valid current → IsPending (.mu probes) current →
          IsPending (.mu probes) (callback name current).state := by
        intro name current currentValid currentPending
        exact bind_preserves_pending _ _ (build_correct body _ current currentValid).1
          (build_preserves_pending body _ probes current currentValid currentPending)
          (fun value after afterValid afterPending => work_preserves_pending (withoutSelfReference name value)
            (withoutSelfReference_ordinary name value) probes after afterValid afterPending)
      rw [build]
      change IsPending (.mu probes) ((callback .depth state).bind fun depth afterDepth =>
        (callback (.uninterned (ordinaryLevel depth)) afterDepth).bind fun ordinary afterOrdinary =>
          request smart depth ordinary callback afterOrdinary).state
      apply bind_preserves_pending _ _ (growing .depth state valid).1 (preserved .depth state valid pending)
      intro depth afterDepth depthValid depthPending
      exact bind_preserves_pending _ _ (growing (.uninterned (ordinaryLevel depth)) afterDepth depthValid).1
        (preserved (.uninterned (ordinaryLevel depth)) afterDepth depthValid depthPending)
        (fun ordinary current currentValid currentPending =>
          request_preserves_pending smart depth ordinary callback probes current currentValid currentPending preserved)
termination_by sizeOf expression

/-- Ordered child computations preserve the same pending ancestor through every sibling. -/
theorem buildMany_preserves_pending [DecidableEq (EdgeKey Symbol Guard)] (expressions : List (Syntax Symbol Guard))
    (environment : List (Value Symbol Guard)) (probes : MuKey NodeRef) (state : State Symbol Guard)
    (valid : InternedConstructorTemplates.Valid state) (pending : IsPending (.mu probes) state) :
    IsPending (.mu probes) (buildMany expressions environment state).state := by
  cases expressions with
  | nil => simpa only [buildMany, Outcome.state] using pending
  | cons first rest =>
      simp only [buildMany]
      apply bind_preserves_pending _ _ (build_correct first environment state valid).1
        (build_preserves_pending first environment probes state valid pending)
      intro value after afterValid afterPending
      exact bind_preserves_pending _ _ (buildMany_correct rest environment after afterValid).1
        (buildMany_preserves_pending rest environment probes after afterValid afterPending)
        (fun _ _ _ finalPending => finalPending)
termination_by sizeOf expressions

/-- Edge construction never writes a pending node payload, including after nested child execution stops. -/
theorem buildEdges_preserves_pending [DecidableEq (EdgeKey Symbol Guard)] (expressions : List (EdgeSyntax Symbol Guard))
    (environment : List (Value Symbol Guard)) (probes : MuKey NodeRef) (state : State Symbol Guard)
    (valid : InternedConstructorTemplates.Valid state) (pending : IsPending (.mu probes) state) :
    IsPending (.mu probes) (buildEdges expressions environment state).state := by
  cases expressions with
  | nil => simpa only [buildEdges, Outcome.state] using pending
  | cons first rest =>
      cases first with
      | mk symbol constraint children =>
          simp only [buildEdges]
          apply bind_preserves_pending _ _ (buildMany_correct children environment state valid).1
            (buildMany_preserves_pending children environment probes state valid pending)
          intro values after afterValid afterPending
          apply bind_preserves_pending _ _ (work_correct (makeEdge symbol constraint values) after afterValid).1
            (work_preserves_pending (makeEdge symbol constraint values) (by simp [makeEdge, Ordinary]) probes after afterValid afterPending)
          intro edge next nextValid nextPending
          exact bind_preserves_pending _ _ (buildEdges_correct rest environment next nextValid).1
            (buildEdges_preserves_pending rest environment probes next nextValid nextPending)
            (fun _ _ _ finalPending => finalPending)
termination_by sizeOf expressions
end

/-- An actual repaired callback retains an active ancestor's missing record. -/
theorem callback_pending [DecidableEq (EdgeKey Symbol Guard)] (expression : Syntax Symbol Guard)
    (environment : List (Value Symbol Guard)) (name : InternedBinderProtocol.Reference)
    (probes : MuKey NodeRef) (state : State Symbol Guard) (valid : InternedConstructorTemplates.Valid state)
    (pending : IsPending (.mu probes) state) : IsPending (.mu probes) (callback expression environment name state).state := by
  exact bind_preserves_pending _ _ (build_correct expression _ state valid).1
    (build_preserves_pending expression _ probes state valid pending)
    (fun value after afterValid afterPending => work_preserves_pending (withoutSelfReference name value)
      (withoutSelfReference_ordinary name value) probes after afterValid afterPending)

end MicroCFTA.InternedFreshOrdinaryPending
