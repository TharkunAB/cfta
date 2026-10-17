import MicroCFTA.InternedFreshOrdinaryConstruction
import MicroCFTA.InternedNestedRequestFacts

/-!
# Irreducible unions through actual source construction

A stored union has a member that prevents the ordinary-row merge.
Every actual constructor retains this property. Full syntax execution
retains it at successful and pending outcomes, including warm Mu reads.
The property imposes no condition on the guards of ordinary records.
-/
namespace MicroCFTA.SourceCurrentRequiredUnionNormal
open Cache InternedConstructorTemplates InternedRecordCoherence
open InternedNestedConstruction (Syntax EdgeSyntax Outcome work)
open InternedBinderProtocol (Reference NodeKey)

/-- A union payload cannot use the all-ordinary merge branch. -/
def ValueNormal : Value Symbol Guard → Prop
  | .union _ members _ _ => ordinaryEdges members = none
  | _ => True

/-- Every stored union retains its nonordinary constructor alternative. -/
def UnionNormal (state : State Symbol Guard) : Prop :=
  ∀ key value, state.nodeRecords key = some value → ValueNormal value

/-- Empty source records satisfy union irreducibility. -/
theorem empty : UnionNormal (InternedConstructorTemplates.empty (Symbol := Symbol) (Guard := Guard)) := by
  intro key value impossible
  cases impossible

/-- First-writer readback retains an old irreducible union or its proved candidate. -/
theorem nodeStep (key : NodeKey) (identify : Interned NodeKey → Value Symbol Guard)
    (state : State Symbol Guard) (normal : UnionNormal state)
    (candidate : ∀ entry, ValueNormal (identify entry)) :
    UnionNormal (InternedConstructorTemplates.nodeStep key identify state).2 := by
  intro other value present
  rcases record_cases _ key other _ value present with old | ⟨same, equal⟩
  · exact normal other value old
  · subst other value
    exact candidate _

/-- Actual edge construction leaves all node payloads unchanged. -/
theorem edge [DecidableEq (EdgeKey Symbol Guard)] (symbol : Symbol) (guard : Guard)
    (children : List (Value Symbol Guard)) (state : State Symbol Guard) (normal : UnionNormal state) :
    UnionNormal (run (makeEdge symbol guard children) state).2 := normal

/-- Actual node construction adds no union payload. -/
theorem node [DecidableEq (EdgeKey Symbol Guard)] (rows : List (EdgeValue Symbol Guard))
    (state : State Symbol Guard) (normal : UnionNormal state) :
    UnionNormal (run (makeNode rows) state).2 := by
  unfold makeNode
  dsimp only
  split
  · exact normal
  · exact nodeStep _ _ state normal (fun _ => trivial)

/-- Actual union construction stores a union only when ordinary-row merging fails. -/
theorem union [DecidableEq (EdgeKey Symbol Guard)] (values : List (Value Symbol Guard))
    (state : State Symbol Guard) (normal : UnionNormal state) :
    UnionNormal (run (makeUnion values) state).2 := by
  unfold makeUnion
  split
  · exact normal
  · exact normal
  · split
    · exact node _ state normal
    · simp only [run]
      apply nodeStep _ _ state normal
      intro entry
      assumption

/-- Actual self-reference filtering retains union irreducibility. -/
theorem filter [DecidableEq (EdgeKey Symbol Guard)] (name : Reference) (value : Value Symbol Guard)
    (state : State Symbol Guard) (normal : UnionNormal state) :
    UnionNormal (run (withoutSelfReference name value) state).2 := by
  cases value <;> simp only [withoutSelfReference] <;> try exact normal
  case union entry members depth free =>
    split
    · exact union _ state normal
    · exact normal

/-- Completing a Mu retains earlier union records, including an earlier winning payload. -/
theorem complete (smart : Bool) (entry : Interned NodeKey) (body depth ordinary : Value Symbol Guard)
    (state : State Symbol Guard) (normal : UnionNormal state) :
    UnionNormal (InternedNestedRequestFacts.complete smart entry body depth ordinary state).state := by
  intro key value present
  rcases record_cases state.nodeRecords (muKey depth ordinary) key (.mu entry body depth ordinary) value present with
    old | ⟨same, equal⟩
  · exact normal key value old
  · subst key value
    trivial

private theorem bind (outcome : Outcome Symbol Guard First)
    (next : First → State Symbol Guard → Outcome Symbol Guard Result)
    (normal : UnionNormal outcome.state)
    (later : ∀ value after, outcome = .done value after → UnionNormal after → UnionNormal (next value after).state) :
    UnionNormal (outcome.bind next).state := by
  cases outcome with
  | pending => exact normal
  | done value after => exact later value after rfl normal

/-- An actual Mu request retains the invariant through hits, pending reads, and its reserved body. -/
theorem request [DecidableEq (EdgeKey Symbol Guard)] (smart : Bool) (depth ordinary : Value Symbol Guard)
    (callback : Reference → State Symbol Guard → Outcome Symbol Guard (Value Symbol Guard))
    (state : State Symbol Guard) (normal : UnionNormal state)
    (checked : ∀ name current, UnionNormal current → UnionNormal (callback name current).state) :
    UnionNormal (InternedNestedConstruction.request smart depth ordinary callback state).state := by
  cases installed : state.nodes.table (muKey depth ordinary) with
  | some entry =>
      cases present : state.nodeRecords (muKey depth ordinary) <;>
        simpa only [InternedNestedConstruction.request, installed, present, Outcome.state] using normal
  | none =>
      let entry := Cache.intern state.nodes (muKey depth ordinary)
      let allocated := {state with nodes := entry.2}
      have reserved : UnionNormal allocated := normal
      have body := checked (.interned entry.1.identity) allocated reserved
      simp only [InternedNestedConstruction.request, installed]
      change UnionNormal ((callback (.interned entry.1.identity) allocated).bind
        (fun body after => InternedNestedRequestFacts.complete smart entry.1 body depth ordinary after)).state
      exact bind _ _ body (fun value after _ afterNormal => complete smart entry.1 value depth ordinary after afterNormal)

mutual
/-- Full repaired syntax retains union irreducibility at every actual stopping state. -/
theorem build [DecidableEq (EdgeKey Symbol Guard)] (expression : Syntax Symbol Guard)
    (environment : List (Value Symbol Guard)) (state : State Symbol Guard) (normal : UnionNormal state) :
    UnionNormal (InternedFreshOrdinaryConstruction.build expression environment state).state := by
  cases expression with
  | empty | var => simpa only [InternedFreshOrdinaryConstruction.build, Outcome.state] using normal
  | node rows =>
      rw [InternedFreshOrdinaryConstruction.build]
      exact bind _ _ (buildEdges rows environment state normal)
        (fun values after _ afterNormal => node values after afterNormal)
  | union members =>
      rw [InternedFreshOrdinaryConstruction.build]
      exact bind _ _ (buildMany members environment state normal)
        (fun values after _ afterNormal => union values after afterNormal)
  | binder smart expression =>
      let callback := fun name current =>
        (InternedFreshOrdinaryConstruction.build expression (.reference name :: environment) current).bind
          (fun value after => work (withoutSelfReference name value) after)
      have checked : ∀ name current, UnionNormal current → UnionNormal (callback name current).state := by
        intro name current currentNormal
        exact bind _ _ (build expression (.reference name :: environment) current currentNormal)
          (fun value after _ afterNormal => filter name value after afterNormal)
      rw [InternedFreshOrdinaryConstruction.build]
      change UnionNormal ((callback .depth state).bind fun depth afterDepth =>
        (callback (.uninterned (InternedFreshOrdinaryConstruction.ordinaryLevel depth)) afterDepth).bind
          fun ordinary afterOrdinary =>
            InternedNestedConstruction.request smart depth ordinary callback afterOrdinary).state
      apply bind _ _ (checked .depth state normal)
      intro depth afterDepth _ depthNormal
      apply bind _ _ (checked (.uninterned (InternedFreshOrdinaryConstruction.ordinaryLevel depth)) afterDepth depthNormal)
      intro ordinary afterOrdinary _ ordinaryNormal
      exact request smart depth ordinary callback afterOrdinary ordinaryNormal checked
termination_by sizeOf expression

/-- Ordered source children retain the invariant through every earlier child outcome. -/
theorem buildMany [DecidableEq (EdgeKey Symbol Guard)] (expressions : List (Syntax Symbol Guard))
    (environment : List (Value Symbol Guard)) (state : State Symbol Guard) (normal : UnionNormal state) :
    UnionNormal (InternedFreshOrdinaryConstruction.buildMany expressions environment state).state := by
  cases expressions with
  | nil => simpa only [InternedFreshOrdinaryConstruction.buildMany, Outcome.state] using normal
  | cons first rest =>
      rw [InternedFreshOrdinaryConstruction.buildMany]
      apply bind _ _ (build first environment state normal)
      intro value after _ afterNormal
      exact bind _ _ (buildMany rest environment after afterNormal) (fun _ _ _ finalNormal => finalNormal)
termination_by sizeOf expressions

/-- Ordered source rows retain the invariant through actual child and edge construction. -/
theorem buildEdges [DecidableEq (EdgeKey Symbol Guard)] (expressions : List (EdgeSyntax Symbol Guard))
    (environment : List (Value Symbol Guard)) (state : State Symbol Guard) (normal : UnionNormal state) :
    UnionNormal (InternedFreshOrdinaryConstruction.buildEdges expressions environment state).state := by
  cases expressions with
  | nil => simpa only [InternedFreshOrdinaryConstruction.buildEdges, Outcome.state] using normal
  | cons first rest =>
      cases first with
      | mk symbol guard children =>
          rw [InternedFreshOrdinaryConstruction.buildEdges]
          apply bind _ _ (buildMany children environment state normal)
          intro values after _ afterNormal
          apply bind (work (makeEdge symbol guard values) after) _ (edge symbol guard values after afterNormal)
          intro value middle _ middleNormal
          exact bind _ _ (buildEdges rest environment middle middleNormal) (fun _ _ _ finalNormal => finalNormal)
termination_by sizeOf expressions
end

/-- An actual closed source build supplies its union invariant without a future result premise. -/
theorem source [DecidableEq (EdgeKey Symbol Guard)] (expression : Syntax Symbol Guard) :
    UnionNormal (InternedFreshOrdinaryConstruction.build expression [] InternedConstructorTemplates.empty).state :=
  build expression [] _ empty

end MicroCFTA.SourceCurrentRequiredUnionNormal
