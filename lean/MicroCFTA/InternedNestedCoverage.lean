import MicroCFTA.InternedNestedRequestFacts

/-!
# Pending-key coverage through successful nested construction

Each unfinished binder permits only its own missing record. A successful
body may retain that permission while it runs. Completing the binder
installs its payload and removes the extra permission. Earlier pending
keys remain unchanged.
-/
namespace MicroCFTA.InternedNestedCoverage
open Cache InternedConstructorTemplates InternedRecordCoherence
open InternedNestedConstruction InternedNestedRequestFacts
open InternedBinderProtocol (NodeKey Reference)

/-- A successful result retains payload coverage with the specified pending keys. -/
def OnDone (pending : List NodeKey) (outcome : Outcome Symbol Guard Result) : Prop :=
  ∀ value state, outcome = .done value state → Covered pending state

/-- Source sequencing transports its earlier coverage into the successful continuation. -/
theorem bind_covered (firstPending finalPending : List NodeKey)
    (outcome : Outcome Symbol Guard First)
    (next : First → State Symbol Guard → Outcome Symbol Guard Result)
    (first : OnDone firstPending outcome)
    (later : ∀ value state, outcome = .done value state → Covered firstPending state →
      OnDone finalPending (next value state)) : OnDone finalPending (outcome.bind next) := by
  cases outcome with
  | pending key state => intro value after impossible; cases impossible
  | done value state => exact later value state rfl (first value state rfl)

/-- Ordinary finite cache effects preserve every allowed pending key. -/
theorem run_covered [DecidableEq (EdgeKey Symbol Guard)] (computation : Work Symbol Guard Result)
    (state : State Symbol Guard) (valid : InternedConstructorTemplates.Valid state)
    (covered : Covered pending state) : Covered pending (run computation state).2 := by
  induction computation generalizing state with
  | pure value => exact covered
  | edge key identify resume ih =>
      exact ih _ _ (edgeStep_correct key identify state valid).1
        (edgeStep_covered key identify state valid covered)
  | node key identify resume ih =>
      exact ih _ _ (nodeStep_correct key identify state valid).1
        (nodeStep_covered key identify state valid covered)

/-- A completed ordinary source action retains coverage in its exact returned state. -/
theorem work_covered [DecidableEq (EdgeKey Symbol Guard)] (computation : Work Symbol Guard Result)
    (state : State Symbol Guard) (valid : InternedConstructorTemplates.Valid state)
    (covered : Covered pending state) : OnDone pending (work computation state) := by
  intro value after returned
  cases returned
  exact run_covered computation state valid covered

/-- Reserving a binder permits its one missing payload in addition to the old pending keys. -/
theorem reserve_covered (key : NodeKey) (state : State Symbol Guard)
    (covered : Covered pending state) :
    Covered (key :: pending) {state with nodes := (Cache.intern state.nodes key).2} := by
  constructor
  · exact covered.edges
  · intro other entry present
    rcases intern_cases state.nodes key other entry present with old | ⟨same, _⟩
    · rcases covered.nodes other entry old with previous | complete
      · exact Or.inl (List.mem_cons_of_mem _ previous)
      · exact Or.inr complete
    · exact Or.inl (by simp [same])

/-- First-writer completion supplies the reserved payload and removes only
that key's additional permission. -/
theorem complete_covered (smart : Bool) (entry : Interned NodeKey)
    (body depth ordinary : Value Symbol Guard) (state : State Symbol Guard)
    (covered : Covered (muKey depth ordinary :: pending) state) :
    OnDone pending (complete smart entry body depth ordinary state) := by
  intro value after returned
  cases returned
  let key := muKey depth ordinary
  let candidate := Value.mu entry body depth ordinary
  constructor
  · exact covered.edges
  · intro other actual present
    rcases covered.nodes other actual present with waiting | ⟨record, stored⟩
    · rcases List.mem_cons.mp waiting with same | previous
      · subst other
        exact Or.inr (keepFirst_present state.nodeRecords key candidate)
      · exact Or.inl previous
    · exact Or.inr ⟨record, keepFirst_extends state.nodeRecords key candidate other record stored⟩

/-- A successful request retains prior pending coverage. Its body receives
the extra permission from the actual reserved key, not an arbitrary key set. -/
theorem request_covered [DecidableEq (EdgeKey Symbol Guard)] (smart : Bool)
    (depth ordinary : Value Symbol Guard)
    (callback : Reference → State Symbol Guard → Outcome Symbol Guard (Value Symbol Guard))
    (state : State Symbol Guard) (valid : InternedConstructorTemplates.Valid state)
    (covered : Covered pending state)
    (callbackCovered : ∀ keys name current, InternedConstructorTemplates.Valid current →
      Covered keys current → OnDone keys (callback name current)) :
    OnDone pending (request smart depth ordinary callback state) := by
  cases installed : state.nodes.table (muKey depth ordinary) with
  | some entry =>
      cases found : state.nodeRecords (muKey depth ordinary) with
      | none => intro value after impossible; simp [request, installed, found] at impossible
      | some value =>
          intro result after returned
          simp only [request, installed, found, Outcome.done.injEq] at returned
          rcases returned with ⟨_, rfl⟩
          exact covered
  | none =>
      let key := muKey depth ordinary
      let entry := Cache.intern state.nodes key
      let allocated := {state with nodes := entry.2}
      have allocatedValid : InternedConstructorTemplates.Valid allocated :=
        ⟨valid.1, (Cache.intern_correct state.nodes key valid.2).1⟩
      have bodyCovered := callbackCovered (key :: pending) (.interned entry.1.identity) allocated allocatedValid
        (reserve_covered key state covered)
      have result := bind_covered (key :: pending) pending (callback (.interned entry.1.identity) allocated)
        (fun body after => complete smart entry.1 body depth ordinary after) bodyCovered
        (fun body after _ coverage => complete_covered smart entry.1 body depth ordinary after coverage)
      simpa only [request, installed, complete, key, entry, allocated] using result

mutual
/-- Every successful nested expression retains coverage for arbitrary earlier pending binders. -/
theorem build_covered [DecidableEq (EdgeKey Symbol Guard)] (expression : Syntax Symbol Guard)
    (environment : List (Value Symbol Guard)) (state : State Symbol Guard)
    (valid : InternedConstructorTemplates.Valid state) (covered : Covered pending state) :
    OnDone pending (build expression environment state) := by
  cases expression with
  | empty | var index =>
      intro value after returned
      simp only [build, Outcome.done.injEq] at returned
      rcases returned with ⟨_, rfl⟩
      exact covered
  | node edges =>
      rw [build]
      apply bind_covered pending pending _ _ (buildEdges_covered edges environment state valid covered)
      intro values after returned coverage
      have afterValid : InternedConstructorTemplates.Valid after := by
        simpa [returned, Outcome.state] using (buildEdges_correct edges environment state valid).1
      exact work_covered (makeNode values) after afterValid coverage
  | union members =>
      rw [build]
      apply bind_covered pending pending _ _ (buildMany_covered members environment state valid covered)
      intro values after returned coverage
      have afterValid : InternedConstructorTemplates.Valid after := by
        simpa [returned, Outcome.state] using (buildMany_correct members environment state valid).1
      exact work_covered (makeUnion values) after afterValid coverage
  | binder smart body =>
      let callback := fun name current => (build body (.reference name :: environment) current).bind
        fun value next => work (withoutSelfReference name value) next
      have callbackCovered : ∀ keys name current, InternedConstructorTemplates.Valid current → Covered keys current →
          OnDone keys (callback name current) := by
        intro keys name current currentValid coverage
        apply bind_covered keys keys _ _ (build_covered body _ current currentValid coverage)
        intro value after returned afterCoverage
        have afterValid : InternedConstructorTemplates.Valid after := by
          simpa [returned, Outcome.state] using (build_correct body (.reference name :: environment) current currentValid).1
        exact work_covered (withoutSelfReference name value) after afterValid afterCoverage
      have callbackValid : ∀ name current, InternedConstructorTemplates.Valid current →
          InternedConstructorTemplates.Valid (callback name current).state := by
        intro name current currentValid
        exact (InternedNestedConstruction.bind_correct _ _ current (build_correct body _ current currentValid)
          (fun value next nextValid => work_correct (withoutSelfReference name value) next nextValid)).1
      rw [build]
      change OnDone pending ((callback .depth state).bind fun depth afterDepth =>
        (callback (.uninterned depth.depth) afterDepth).bind fun ordinary afterOrdinary =>
          request smart depth ordinary callback afterOrdinary)
      apply bind_covered pending pending _ _ (callbackCovered pending .depth state valid covered)
      intro depth afterDepth depthReturned depthCoverage
      have depthValid : InternedConstructorTemplates.Valid afterDepth := by
        simpa [depthReturned, Outcome.state] using callbackValid .depth state valid
      apply bind_covered pending pending _ _
        (callbackCovered pending (.uninterned depth.depth) afterDepth depthValid depthCoverage)
      intro ordinary afterOrdinary ordinaryReturned ordinaryCoverage
      have ordinaryValid : InternedConstructorTemplates.Valid afterOrdinary := by
        simpa [ordinaryReturned, Outcome.state] using callbackValid (.uninterned depth.depth) afterDepth depthValid
      exact request_covered smart depth ordinary callback afterOrdinary ordinaryValid ordinaryCoverage callbackCovered
termination_by sizeOf expression

/-- Successful child traversal restores the exact incoming pending-key allowance. -/
theorem buildMany_covered [DecidableEq (EdgeKey Symbol Guard)] (expression : List (Syntax Symbol Guard))
    (environment : List (Value Symbol Guard)) (state : State Symbol Guard)
    (valid : InternedConstructorTemplates.Valid state) (covered : Covered pending state) :
    OnDone pending (buildMany expression environment state) := by
  cases expression with
  | nil =>
      intro value after returned
      simp only [buildMany] at returned
      cases returned
      exact covered
  | cons first rest =>
      rw [buildMany]
      apply bind_covered pending pending _ _ (build_covered first environment state valid covered)
      intro value afterHead headReturned headCoverage
      have headValid : InternedConstructorTemplates.Valid afterHead := by
        simpa [headReturned, Outcome.state] using (build_correct first environment state valid).1
      apply bind_covered pending pending _ _ (buildMany_covered rest environment afterHead headValid headCoverage)
      intro values afterTail _ tailCoverage
      intro result final returned
      cases returned
      exact tailCoverage
termination_by sizeOf expression

/-- Separate edge interning preserves the pending-key allowance between nested siblings. -/
theorem buildEdges_covered [DecidableEq (EdgeKey Symbol Guard)] (expression : List (EdgeSyntax Symbol Guard))
    (environment : List (Value Symbol Guard)) (state : State Symbol Guard)
    (valid : InternedConstructorTemplates.Valid state) (covered : Covered pending state) :
    OnDone pending (buildEdges expression environment state) := by
  cases expression with
  | nil =>
      intro value after returned
      simp only [buildEdges] at returned
      cases returned
      exact covered
  | cons first rest =>
      cases first with
      | mk symbol constraint children =>
          rw [buildEdges]
          apply bind_covered pending pending _ _ (buildMany_covered children environment state valid covered)
          intro values afterChildren childrenReturned childrenCoverage
          have childrenValid : InternedConstructorTemplates.Valid afterChildren := by
            simpa [childrenReturned, Outcome.state] using (buildMany_correct children environment state valid).1
          apply bind_covered pending pending _ _ (work_covered (makeEdge symbol constraint values) afterChildren childrenValid childrenCoverage)
          intro edge afterEdge edgeReturned edgeCoverage
          have edgeValid : InternedConstructorTemplates.Valid afterEdge := by
            simpa [edgeReturned, Outcome.state] using (work_correct (makeEdge symbol constraint values) afterChildren childrenValid).1
          apply bind_covered pending pending _ _ (buildEdges_covered rest environment afterEdge edgeValid edgeCoverage)
          intro edges afterTail _ tailCoverage
          intro result final returned
          cases returned
          exact tailCoverage
termination_by sizeOf expression
end

/-- Every completed empty-table run has a payload for each installed identity. -/
theorem closed_covered [DecidableEq (EdgeKey Symbol Guard)] (expression : Syntax Symbol Guard)
    (value : Value Symbol Guard) (state : State Symbol Guard)
    (completed : build expression [] empty = .done value state) : Covered [] state :=
  build_covered expression [] empty empty_valid empty_correct.2 value state completed

end MicroCFTA.InternedNestedCoverage
