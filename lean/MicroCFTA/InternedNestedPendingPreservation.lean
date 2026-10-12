import MicroCFTA.InternedNestedConstructionGrowth

/-!
# Nested source execution cannot complete an active ancestor's payload

Ordinary work cannot write a Mu key. A nested request for a reserved key
with no payload stops at that key. A different completed request writes
only its own record. The active ancestor's payload stays absent throughout
both successful and pending nested outcomes.
-/
namespace MicroCFTA.InternedNestedConstruction
open Cache InternedConstructorTemplates
open InternedBinderProtocol (MuKey NodeRef)

/-- Finite ordinary source effects retain an already pending Mu reservation unchanged. -/
theorem work_preserves_pending [DecidableEq (EdgeKey Symbol Guard)] (computation : Work Symbol Guard Result)
    (ordinary : Ordinary computation) (probes : MuKey NodeRef) (state : State Symbol Guard)
    (valid : InternedConstructorTemplates.Valid state) (pending : IsPending (.mu probes) state) :
    IsPending (.mu probes) (work computation state).state := by
  obtain ⟨⟨entry, present⟩, missing⟩ := pending
  exact ⟨⟨entry, (InternedConstructorTemplates.run_correct computation state valid).2.nodes _ entry present⟩,
    (run_preserves_mu computation state ordinary probes).trans missing⟩

/-- Source sequencing preserves the exact pending slot at either its completed or stopped state. -/
theorem bind_preserves_pending (outcome : Outcome Symbol Guard First)
    (next : First → State Symbol Guard → Outcome Symbol Guard Result)
    (valid : InternedConstructorTemplates.Valid outcome.state) (pending : IsPending key outcome.state)
    (later : ∀ value state, InternedConstructorTemplates.Valid state → IsPending key state → IsPending key (next value state).state) :
    IsPending key (outcome.bind next).state := by
  cases outcome with
  | pending selected state => exact pending
  | done value state => exact later value state valid pending

/-- A Mu request can only read the pending ancestor or reserve and complete a different key. -/
theorem request_preserves_pending [DecidableEq (EdgeKey Symbol Guard)] (smart : Bool)
    (depth ordinary : Value Symbol Guard)
    (callback : InternedBinderProtocol.Reference → State Symbol Guard → Outcome Symbol Guard (Value Symbol Guard))
    (probes : MuKey NodeRef) (state : State Symbol Guard) (valid : InternedConstructorTemplates.Valid state)
    (pending : IsPending (.mu probes) state)
    (bodyPending : ∀ name current, InternedConstructorTemplates.Valid current → IsPending (.mu probes) current →
      IsPending (.mu probes) (callback name current).state) :
    IsPending (.mu probes) (request smart depth ordinary callback state).state := by
  cases found : state.nodes.table (muKey depth ordinary) with
  | some entry => cases stored : state.nodeRecords (muKey depth ordinary) <;> simpa only [request, found, stored, Outcome.state] using pending
  | none =>
      obtain ⟨⟨oldEntry, oldPresent⟩, oldMissing⟩ := pending
      let key := muKey depth ordinary
      let entry := Cache.intern state.nodes key
      let allocated := {state with nodes := entry.2}
      have different : .mu probes ≠ key := by
        intro same
        rw [same, found] at oldPresent
        cases oldPresent
      have allocatedValid : InternedConstructorTemplates.Valid allocated :=
        ⟨valid.1, (Cache.intern_correct state.nodes key valid.2).1⟩
      have allocatedPending : IsPending (.mu probes) allocated :=
        ⟨⟨oldEntry, InternedBinderProtocol.intern_grows state.nodes key _ oldEntry oldPresent⟩, oldMissing⟩
      have body := bodyPending (.interned entry.1.identity) allocated allocatedValid allocatedPending
      simp only [request, found]
      change IsPending (.mu probes) ((callback (.interned entry.1.identity) allocated).bind _).state
      cases returned : callback (.interned entry.1.identity) allocated with
      | pending selected after => simpa only [returned, Outcome.bind, Outcome.state] using body
      | done value after =>
          rw [returned] at body
          obtain ⟨⟨preserved, present⟩, missing⟩ := body
          simp only [Outcome.state] at present missing
          refine ⟨⟨preserved, present⟩, ?_⟩
          change keepFirst after.nodeRecords key _ (.mu probes) = none
          cases stored : after.nodeRecords key <;> simp [keepFirst, stored, put, different, missing]

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
        (callback (.uninterned depth.depth) afterDepth).bind fun ordinary afterOrdinary =>
          request smart depth ordinary callback afterOrdinary).state
      apply bind_preserves_pending _ _ (growing .depth state valid).1 (preserved .depth state valid pending)
      intro depth afterDepth depthValid depthPending
      exact bind_preserves_pending _ _ (growing (.uninterned depth.depth) afterDepth depthValid).1
        (preserved (.uninterned depth.depth) afterDepth depthValid depthPending)
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

end MicroCFTA.InternedNestedConstruction
