import MicroCFTA.InternedStoredShallowCompletion

/-!
# Shallow Mu records remain shallow through actual unfolding

Prepared depth-zero bodies make no new Mu request. Every Mu payload after
that source computation is an unchanged earlier record. This derives the
representation closure needed by a gate that unfolds repeatedly.
-/
namespace MicroCFTA.InternedShallowHeap
open Cache InternedConstructorTemplates InternedRecordCoherence
open InternedNestedConstruction InternedStoredSubstitution InternedStoredShallowCompletion
open InternedBinderProtocol (NodeKey)

/-- Every Mu payload in the later table is an unchanged earlier complete record. -/
def NoNewMu (before after : State Symbol Guard) : Prop :=
  ∀ key entry body depth ordinary,
    after.nodeRecords key = some (.mu entry body depth ordinary) →
      before.nodeRecords key = some (.mu entry body depth ordinary)

/-- A state introduces no Mu record into itself. -/
theorem noNewMu_refl (state : State Symbol Guard) : NoNewMu state state := by
  intro key entry body depth ordinary stored
  exact stored

/-- Source effects compose their absence of new Mu allocations. -/
theorem noNewMu_trans (first : NoNewMu before middle) (second : NoNewMu middle after) : NoNewMu before after := by
  intro key entry body depth ordinary stored
  exact first key entry body depth ordinary (second key entry body depth ordinary stored)

/-- A non-Mu candidate request can only retain an earlier Mu payload. -/
theorem nodeStep_noNewMu (key : NodeKey) (identify : Interned NodeKey → Value Symbol Guard)
    (state : State Symbol Guard)
    (notMu : ∀ actual entry body depth ordinary, identify actual ≠ .mu entry body depth ordinary) :
    NoNewMu state (nodeStep key identify state).2 := by
  intro other entry body depth ordinary stored
  rcases record_cases state.nodeRecords key other (identify (Cache.intern state.nodes key).1) (Value.mu entry body depth ordinary) stored with old | ⟨_, equal⟩
  · exact old
  · exact False.elim (notMu _ entry body depth ordinary equal.symm)

/-- Ordinary source construction makes no new Mu record. -/
theorem makeNode_noNewMu [DecidableEq (EdgeKey Symbol Guard)] (edges : List (EdgeValue Symbol Guard))
    (state : State Symbol Guard) : NoNewMu state (run (makeNode edges) state).2 := by
  unfold makeNode
  dsimp only
  split
  · exact noNewMu_refl state
  · exact nodeStep_noNewMu _ _ state (by intros; simp [identifyNode])

/-- Every source union branch preserves the existing Mu payload set. -/
theorem makeUnion_noNewMu [DecidableEq (EdgeKey Symbol Guard)] (values : List (Value Symbol Guard))
    (state : State Symbol Guard) : NoNewMu state (run (makeUnion values) state).2 := by
  unfold makeUnion
  split
  · exact noNewMu_refl state
  · exact noNewMu_refl state
  · split
    · exact makeNode_noNewMu _ state
    · simp only [run]
      exact nodeStep_noNewMu _ _ state (by intros; simp)

/-- Source sequencing retains the exact earlier origin of each completed Mu. -/
theorem bind_noNewMu (state : State Symbol Guard) (outcome : Outcome Symbol Guard First)
    (next : First → State Symbol Guard → Outcome Symbol Guard Result)
    (first : NoNewMu state outcome.state)
    (second : ∀ value after, outcome = .done value after → NoNewMu after (next value after).state) :
    NoNewMu state (outcome.bind next).state := by
  cases outcome with
  | pending => exact first
  | done value after => exact noNewMu_trans first (second value after rfl)

mutual
/-- Binder-free source expression introduces no complete Mu record, including through cache reuse. -/
theorem build_noNewMu [DecidableEq (EdgeKey Symbol Guard)] (expression : Syntax Symbol Guard)
    (environment : List (Value Symbol Guard)) (state : State Symbol Guard) (free : BinderFree expression) :
    NoNewMu state (build expression environment state).state := by
  cases expression with
  | empty | var => simpa only [build, Outcome.state] using noNewMu_refl state
  | binder => simp [BinderFree] at free
  | node edges =>
      rw [build]
      exact bind_noNewMu state _ _ (buildEdges_noNewMu edges environment state (by simpa only [BinderFree] using free))
        (fun values after _ => makeNode_noNewMu values after)
  | union members =>
      rw [build]
      exact bind_noNewMu state _ _ (buildMany_noNewMu members environment state (by simpa only [BinderFree] using free))
        (fun values after _ => makeUnion_noNewMu values after)
termination_by sizeOf expression

/-- Earlier completed Mu payloads remain the only Mu payloads through ordered child effects. -/
theorem buildMany_noNewMu [DecidableEq (EdgeKey Symbol Guard)] (expressions : List (Syntax Symbol Guard))
    (environment : List (Value Symbol Guard)) (state : State Symbol Guard) (free : ManyBinderFree expressions) :
    NoNewMu state (buildMany expressions environment state).state := by
  cases expressions with
  | nil => simpa only [buildMany, Outcome.state] using noNewMu_refl state
  | cons first rest =>
      simp only [ManyBinderFree] at free
      rw [buildMany]
      apply bind_noNewMu state _ _ (build_noNewMu first environment state free.1)
      intro value after _
      exact bind_noNewMu after _ _ (buildMany_noNewMu rest environment after free.2)
        (fun values final _ => noNewMu_refl final)
termination_by sizeOf expressions

/-- Edge allocation leaves complete node payloads unchanged. -/
theorem buildEdges_noNewMu [DecidableEq (EdgeKey Symbol Guard)] (expressions : List (EdgeSyntax Symbol Guard))
    (environment : List (Value Symbol Guard)) (state : State Symbol Guard) (free : EdgesBinderFree expressions) :
    NoNewMu state (buildEdges expressions environment state).state := by
  cases expressions with
  | nil => simpa only [buildEdges, Outcome.state] using noNewMu_refl state
  | cons first rest =>
      cases first with
      | mk symbol constraint children =>
          simp only [EdgesBinderFree] at free
          rw [buildEdges]
          apply bind_noNewMu state _ _ (buildMany_noNewMu children environment state free.1)
          intro values after _
          apply bind_noNewMu after (work (makeEdge symbol constraint values) after) _ (noNewMu_refl after)
          intro edge afterEdge _
          exact bind_noNewMu afterEdge _ _ (buildEdges_noNewMu rest environment afterEdge free.2)
            (fun edges final _ => noNewMu_refl final)
termination_by sizeOf expressions
end

/-- Every complete stored Mu has a body with cached Mu depth zero. -/
def Shallow (state : State Symbol Guard) : Prop :=
  ∀ key entry body depth ordinary,
    state.nodeRecords key = some (.mu entry body depth ordinary) → body.depth = 0

/-- Empty source tables satisfy the shallow fragment. -/
theorem empty_shallow : Shallow (empty (Symbol := Symbol) (Guard := Guard)) := by
  intro key entry body depth ordinary impossible
  cases impossible

/-- Absence of new Mu payloads preserves the source shallow representation fragment. -/
theorem shallow_preserved (before after : State Symbol Guard) (shallow : Shallow before) (unchanged : NoNewMu before after) :
    Shallow after := by
  intro key entry body depth ordinary stored
  exact shallow key entry body depth ordinary (unchanged key entry body depth ordinary stored)

/-- Actual preparation of a depth-zero stored body introduces no new Mu payload. -/
theorem execute_noNewMu [DecidableEq (EdgeKey Symbol Guard)] (value : Value Symbol Guard)
    (environment : Environment Symbol Guard) (state : State Symbol Guard) (coherent : Coherent state)
    (available : InternedProbeProvenance.Available state value) (zero : value.depth = 0) :
    NoNewMu state (execute value environment state).state :=
  build_noNewMu _ _ state (encode_zero (leaves value) [] value state coherent available zero)

end MicroCFTA.InternedShallowHeap
