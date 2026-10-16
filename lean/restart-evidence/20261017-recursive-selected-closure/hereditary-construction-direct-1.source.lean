import MicroCFTA.SourceCurrentHereditaryConstructors
import MicroCFTA.SourceCurrentHereditaryUnconstrained
import MicroCFTA.InternedFreshOrdinaryReadback
import MicroCFTA.SourceEqualityAnnotationStoredSyntax

/-!
# Local annotations through actual stored-body construction

A conditional certificate belongs to each completed Mu cache entry. It links
that body's annotations to its two complete probes. It permits unrelated
constrained records. Actual allowed construction produces the certificate
for each new body before first-writer readback. Physical Facts alone do not
supply this representation invariant for arbitrary earlier Mu records.
-/
namespace MicroCFTA.SourceCurrentHereditaryConstruction
open Cache InternedConstructorTemplates InternedProbeProvenance InternedRecordCoherence InternedNestedFacts
open InternedNestedConstruction (Syntax EdgeSyntax Outcome work request finish)
open InternedNestedProvenance (Values Edges depth_available ordinary_available)
open InternedBinderProtocol (Reference NodeKey)
open InternedFreshProbeKeys InternedFreshOrdinaryConstruction
open SourceEqualityAnnotationLanguage SourceEqualityAnnotationConstruction
open SourceCurrentHereditaryConstructors (Edge)

/-- Earlier Mu bodies inherit a predicate when both exact stored probes have that predicate. -/
def MuStored (valid : Guard → Prop) (state : State Symbol Guard) : Prop :=
  ∀ key entry body depth ordinary, state.nodeRecords key = some (.mu entry body depth ordinary) →
    Annotated valid depth → Annotated valid ordinary → Annotated valid body

/-- Empty caches have no completed Mu obligation. -/
theorem MuStored.empty (valid : Guard → Prop) : MuStored valid (empty (Symbol := Symbol) (Guard := Guard)) := by
  intro key entry body depth ordinary absent
  cases absent

/-- An operation with no new Mu preserves the conditional earlier-body certificates. -/
theorem MuStored.preserve {valid : Guard → Prop} {before after : State Symbol Guard}
    (stored : MuStored valid before) (old : InternedShallowHeap.NoNewMu before after) : MuStored valid after := by
  intro key entry body depth ordinary present
  exact stored key entry body depth ordinary (old key entry body depth ordinary present)

/-- A node constructor changes no completed Mu payload. -/
theorem MuStored.makeNode [DecidableEq (EdgeKey Symbol Guard)] {valid : Guard → Prop} {state : State Symbol Guard}
    (stored : MuStored valid state) (edges : List (EdgeValue Symbol Guard)) :
    MuStored valid (run (InternedConstructorTemplates.makeNode edges) state).2 :=
  stored.preserve (InternedShallowHeap.makeNode_noNewMu edges state)

/-- An edge constructor changes no completed Mu payload. -/
theorem MuStored.makeEdge [DecidableEq (EdgeKey Symbol Guard)] {valid : Guard → Prop} {state : State Symbol Guard}
    (stored : MuStored valid state) (symbol : Symbol) (guard : Guard) (values : List (Value Symbol Guard)) :
    MuStored valid (run (InternedConstructorTemplates.makeEdge symbol guard values) state).2 := stored

/-- A union constructor changes no completed Mu payload. -/
theorem MuStored.makeUnion [DecidableEq (EdgeKey Symbol Guard)] {valid : Guard → Prop} {state : State Symbol Guard}
    (stored : MuStored valid state) (values : List (Value Symbol Guard)) :
    MuStored valid (run (InternedConstructorTemplates.makeUnion values) state).2 :=
  stored.preserve (InternedShallowHeap.makeUnion_noNewMu values state)

/-- Reserving an identity changes no earlier complete Mu record. -/
theorem MuStored.reserve {valid : Guard → Prop} {state : State Symbol Guard}
    (stored : MuStored valid state) (key : NodeKey) :
    MuStored valid {state with nodes := (Cache.intern state.nodes key).2} := stored

/-- Smart cleanup selects the stored body, empty, or the same annotated Mu. -/
theorem finish_annotated (valid : Guard → Prop) (smart : Bool) (value : Value Symbol Guard)
    (annotated : Annotated valid value) : Annotated valid (finish smart value) := by
  cases smart with
  | false => exact annotated
  | true =>
      cases annotated with
      | empty => exact .empty
      | reference name => exact .reference name
      | node entry edges depth free guards children => exact .node entry edges depth free guards children
      | union entry members depth free children => exact .union entry members depth free children
      | mu entry body depth ordinary annotated =>
          simp only [finish, Bool.true_eq, ↓reduceIte, cleanup]
          split
          · exact annotated
          · split
            · exact .empty
            · exact .mu _ _ _ _ annotated

/-- A certificate describes actual cache retention and each actual successful returned value. -/
structure Checked (valid : Guard → Prop) (outcome : Outcome Symbol Guard A) (post : A → Prop) : Prop where
  /-- The exact stopping cache retains conditional Mu certificates. -/
  stored : MuStored valid outcome.state
  /-- Each literal successful result satisfies its local postcondition. -/
  result : ∀ value after, outcome = .done value after → post value

private theorem checked_pure (valid : Guard → Prop) (value : A) (state : State Symbol Guard) (post : A → Prop)
    (stored : MuStored valid state) (result : post value) : Checked valid (.done value state) post :=
  ⟨stored, fun _ _ same => by cases same; exact result⟩

private theorem checked_bind {valid : Guard → Prop} {outcome : Outcome Symbol Guard A} {post : A → Prop}
    {next : A → State Symbol Guard → Outcome Symbol Guard B} {last : B → Prop}
    (first : Checked valid outcome post)
    (later : ∀ value after, outcome = .done value after → post value → MuStored valid after → Checked valid (next value after) last) :
    Checked valid (outcome.bind next) last := by
  cases outcome with
  | pending key after => exact ⟨first.stored, by intro _ _ impossible; cases impossible⟩
  | done value after => exact later value after rfl (first.result value after rfl) first.stored

/-- Bare self filtering retains local annotations and conditional Mu certificates. -/
theorem filter_checked [DecidableEq (EdgeKey Symbol Guard)] (valid : Guard → Prop) (name : Reference)
    (value : Value Symbol Guard) (state : State Symbol Guard) (facts : Facts state) (available : Available state value)
    (annotated : Annotated valid value) (stored : MuStored valid state) :
    Checked valid (work (withoutSelfReference name value) state) (Annotated valid) := by
  have kept : MuStored valid (run (withoutSelfReference name value) state).2 :=
    stored.preserve (InternedStoredMuOrigins.filter_noNewMu name value state)
  refine ⟨kept, ?_⟩
  intro result after done
  obtain ⟨rfl, rfl⟩ := Outcome.done.inj done
  cases annotated with
  | empty => exact .empty
  | reference name => exact .reference name
  | node entry edges depth free guards children => exact .node entry edges depth free guards children
  | mu entry body depth ordinary annotated => exact .mu entry body depth ordinary annotated
  | union entry members depth free children =>
      unfold withoutSelfReference
      split
      · apply SourceCurrentHereditaryConstructors.makeUnion valid _ state facts
        · intro value member
          exact available.children value (List.mem_filter.mp member).1
        · intro value member
          exact children value (List.mem_filter.mp member).1
      · exact .union entry members depth free children

private theorem complete_checked (valid : Guard → Prop) (smart : Bool) (entry : Interned NodeKey)
    (body depth ordinary : Value Symbol Guard) (state : State Symbol Guard) (facts : Facts state)
    (depthAvailable : Available state depth) (ordinaryAvailable : Available state ordinary)
    (annotated : Annotated valid body) (depthAnnotated : Annotated valid depth) (ordinaryAnnotated : Annotated valid ordinary)
    (stored : MuStored valid state) :
    Checked valid (InternedNestedRequestFacts.complete smart entry body depth ordinary state) (Annotated valid) := by
  have retained : MuStored valid
      {state with nodeRecords := keepFirst state.nodeRecords (muKey depth ordinary) (.mu entry body depth ordinary)} := by
    intro key own ownBody ownDepth ownOrdinary present
    rcases record_cases state.nodeRecords (muKey depth ordinary) key (.mu entry body depth ordinary)
        (.mu own ownBody ownDepth ownOrdinary) present with old | ⟨_, same⟩
    · exact stored key own ownBody ownDepth ownOrdinary old
    · cases same
      exact fun _ _ => annotated
  refine ⟨retained, ?_⟩
  intro result after done
  obtain ⟨winner, present⟩ := keepFirst_present state.nodeRecords (muKey depth ordinary) (.mu entry body depth ordinary)
  simp only [InternedNestedRequestFacts.complete, present, Option.getD_some] at done
  cases done
  apply finish_annotated
  rcases record_cases state.nodeRecords (muKey depth ordinary) (muKey depth ordinary) (.mu entry body depth ordinary)
      winner present with old | ⟨_, same⟩
  · obtain ⟨own, ownBody, rfl⟩ := InternedProfileHeap.stored_probes depth ordinary winner state facts depthAvailable ordinaryAvailable old
    exact .mu _ _ _ _ (stored _ _ _ _ _ old depthAnnotated ordinaryAnnotated)
  · cases same
    exact .mu _ _ _ _ annotated
