import MicroCFTA.InternedNestedConstructionGrowth
import MicroCFTA.InternedErasedEdgeReplay

/-!
# Coherent records through arbitrary nested source execution

Each ordinary constructor writes its own fields. Each Mu reservation
preserves old fields and completion adds its two actual probe references.
No complete input payload assumption is needed for this state invariant.
-/
namespace MicroCFTA.InternedNestedCoherence
open Cache InternedConstructorTemplates InternedNestedConstruction InternedRecordCoherence
open InternedErasedEdgeReplay (run_coherent)

/-- Source sequencing preserves coherent tables on either outcome. -/
theorem bind_coherent (outcome : Outcome Symbol Guard First)
    (next : First → State Symbol Guard → Outcome Symbol Guard Result)
    (first : Coherent outcome.state)
    (later : ∀ value state, outcome = .done value state → Coherent state → Coherent (next value state).state) :
    Coherent (outcome.bind next).state := by
  cases outcome with
  | pending => exact first
  | done value state => exact later value state rfl first

/-- A Mu request retains coherent old records and writes its own actual key fields. -/
theorem request_coherent [DecidableEq (EdgeKey Symbol Guard)] (smart : Bool)
    (depth ordinary : Value Symbol Guard)
    (callback : InternedBinderProtocol.Reference → State Symbol Guard → Outcome Symbol Guard (Value Symbol Guard))
    (state : State Symbol Guard) (coherent : Coherent state)
    (bodyCoherent : ∀ name current, Coherent current → Coherent (callback name current).state)
    (bodyGrowth : ∀ name current, InternedConstructorTemplates.Valid current → Grows current (callback name current).state) :
    Coherent (request smart depth ordinary callback state).state := by
  cases found : state.nodes.table (muKey depth ordinary) with
  | some entry => cases stored : state.nodeRecords (muKey depth ordinary) <;> simpa only [request, found, stored, Outcome.state] using coherent
  | none =>
      let key := muKey depth ordinary
      let entry := Cache.intern state.nodes key
      let allocated := {state with nodes := entry.2}
      have allocatedCoherent : Coherent allocated := by
        refine ⟨⟨coherent.valid.1, (Cache.intern_correct state.nodes key coherent.valid.2).1⟩, coherent.edges, ?_⟩
        intro other value present
        obtain ⟨record, stored, fields⟩ := coherent.nodes other value present
        exact ⟨record, InternedBinderProtocol.intern_grows state.nodes key other record stored, fields⟩
      simp only [request, found]
      apply bind_coherent _ _ (bodyCoherent _ allocated allocatedCoherent)
      intro body after returned afterCoherent
      change callback (.interned entry.1.identity) allocated = .done body after at returned
      have stored : after.nodes.table key = some entry.1 := by
        have retained := (bodyGrowth (.interned entry.1.identity) allocated allocatedCoherent.valid).nodes
          key entry.1 (Cache.intern_correct state.nodes key coherent.valid.2).2.1
        simpa only [returned, Outcome.state] using retained
      refine ⟨afterCoherent.valid, afterCoherent.edges, ?_⟩
      intro other value present
      rcases record_cases after.nodeRecords key other _ value present with old | ⟨same, equal⟩
      · exact afterCoherent.nodes other value old
      · subst other value
        exact ⟨entry.1, stored, rfl, rfl⟩

mutual
/-- Arbitrary source syntax preserves coherent record fields, even at a pending stop. -/
theorem build_coherent [DecidableEq (EdgeKey Symbol Guard)] (expression : Syntax Symbol Guard)
    (environment : List (Value Symbol Guard)) (state : State Symbol Guard) (coherent : Coherent state) :
    Coherent (build expression environment state).state := by
  cases expression with
  | empty | var index => simpa only [build, Outcome.state] using coherent
  | node edges =>
      simp only [build]
      exact bind_coherent _ _ (buildEdges_coherent edges environment state coherent)
        (fun values current _ currentCoherent => run_coherent (makeNode values) current (makeNode_safe values) currentCoherent)
  | union members =>
      simp only [build]
      exact bind_coherent _ _ (buildMany_coherent members environment state coherent)
        (fun values current _ currentCoherent => run_coherent (makeUnion values) current (makeUnion_safe values) currentCoherent)
  | binder smart body =>
      let callback := fun name current => (build body (.reference name :: environment) current).bind
        fun value next => work (withoutSelfReference name value) next
      have growing : ∀ name current, InternedConstructorTemplates.Valid current →
          InternedConstructorTemplates.Valid (callback name current).state ∧ Grows current (callback name current).state := by
        intro name current valid
        exact bind_correct _ _ current (build_correct body _ current valid)
          (fun value after afterValid => work_correct (withoutSelfReference name value) after afterValid)
      have retained : ∀ name current, Coherent current → Coherent (callback name current).state := by
        intro name current currentCoherent
        exact bind_coherent _ _ (build_coherent body _ current currentCoherent)
          (fun value after _ afterCoherent => run_coherent (withoutSelfReference name value) after
            (withoutSelfReference_safe name value) afterCoherent)
      rw [build]
      change Coherent ((callback .depth state).bind fun depth afterDepth =>
        (callback (.uninterned depth.depth) afterDepth).bind fun ordinary afterOrdinary =>
          request smart depth ordinary callback afterOrdinary).state
      exact bind_coherent _ _ (retained .depth state coherent) (fun depth afterDepth _ depthCoherent =>
        bind_coherent _ _ (retained (.uninterned depth.depth) afterDepth depthCoherent)
          (fun ordinary afterOrdinary _ ordinaryCoherent =>
            request_coherent smart depth ordinary callback afterOrdinary ordinaryCoherent retained
              (fun name current valid => (growing name current valid).2)))
termination_by sizeOf expression

/-- Every child preserves coherent records in source order. -/
theorem buildMany_coherent [DecidableEq (EdgeKey Symbol Guard)] (expressions : List (Syntax Symbol Guard))
    (environment : List (Value Symbol Guard)) (state : State Symbol Guard) (coherent : Coherent state) :
    Coherent (buildMany expressions environment state).state := by
  cases expressions with
  | nil => simpa only [buildMany, Outcome.state] using coherent
  | cons first rest =>
      simp only [buildMany]
      exact bind_coherent _ _ (build_coherent first environment state coherent) (fun value after _ afterCoherent =>
        bind_coherent _ _ (buildMany_coherent rest environment after afterCoherent) (fun _ _ _ finalCoherent => finalCoherent))
termination_by sizeOf expressions

/-- Edge interning preserves coherence after every actual nested child execution. -/
theorem buildEdges_coherent [DecidableEq (EdgeKey Symbol Guard)] (expressions : List (EdgeSyntax Symbol Guard))
    (environment : List (Value Symbol Guard)) (state : State Symbol Guard) (coherent : Coherent state) :
    Coherent (buildEdges expressions environment state).state := by
  cases expressions with
  | nil => simpa only [buildEdges, Outcome.state] using coherent
  | cons first rest =>
      cases first with
      | mk symbol constraint children =>
          simp only [buildEdges]
          exact bind_coherent _ _ (buildMany_coherent children environment state coherent) (fun values after _ afterCoherent =>
            bind_coherent _ _ (run_coherent (makeEdge symbol constraint values) after (makeEdge_safe _ _ _) afterCoherent)
              (fun edge next _ nextCoherent => bind_coherent _ _ (buildEdges_coherent rest environment next nextCoherent)
                (fun _ _ _ finalCoherent => finalCoherent)))
termination_by sizeOf expressions
end

end MicroCFTA.InternedNestedCoherence
