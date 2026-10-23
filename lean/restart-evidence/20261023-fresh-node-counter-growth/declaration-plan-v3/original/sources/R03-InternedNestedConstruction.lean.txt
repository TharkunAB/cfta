import MicroCFTA.InternedConstructionProvenance

/-!
# Syntax-directed nested Mu construction with explicit pending readback

Scoped source expression can construct binders that depend on enclosing
variables. Every binder executes both normalized probes before lookup.
A cache hit on an incomplete record reports the exact pending key.
-/
namespace MicroCFTA.InternedNestedConstruction
open Cache InternedConstructorTemplates
open InternedBinderProtocol (Reference NodeRef NodeKey)

mutual
/-- Finite source expression keeps lexical variables and constructs nested binders in place. -/
inductive Syntax (Symbol Guard : Type) where
  | empty
  | var (index : Nat)
  | node (edges : List (EdgeSyntax Symbol Guard))
  | union (members : List (Syntax Symbol Guard))
  | binder (smart : Bool) (body : Syntax Symbol Guard)

/-- Nested source edges retain the original symbol, constraint, and ordered children. -/
inductive EdgeSyntax (Symbol Guard : Type) where
  | mk (symbol : Symbol) (constraint : Guard) (children : List (Syntax Symbol Guard))
end

/-- A finite execution either returns its actual record or identifies a pending canonical request. -/
inductive Outcome (Symbol Guard Result : Type) where
  | done (value : Result) (state : InternedConstructorTemplates.State Symbol Guard)
  | pending (key : NodeKey) (state : InternedConstructorTemplates.State Symbol Guard)

/-- Later source effects run only after the earlier record has completed. -/
def Outcome.bind (outcome : Outcome Symbol Guard First)
    (next : First → InternedConstructorTemplates.State Symbol Guard → Outcome Symbol Guard Result) : Outcome Symbol Guard Result :=
  match outcome with
  | .done value state => next value state
  | .pending key state => .pending key state

/-- Execute an existing finite ordinary constructor with its exact two-cache operations. -/
def work [DecidableEq (EdgeKey Symbol Guard)] (computation : Work Symbol Guard Result)
    (state : InternedConstructorTemplates.State Symbol Guard) : Outcome Symbol Guard Result :=
  let result := run computation state
  .done result.1 result.2

/-- Raw Mu construction retains its binder; smart construction applies the source cleanup. -/
def finish (smart : Bool) (value : Value Symbol Guard) : Value Symbol Guard :=
  if smart then cleanup value else value

/-- Actual Mu readback starts only after both complete probe records are available. -/
def request [DecidableEq (EdgeKey Symbol Guard)] (smart : Bool) (depth ordinary : Value Symbol Guard)
    (callback : Reference → InternedConstructorTemplates.State Symbol Guard → Outcome Symbol Guard (Value Symbol Guard))
    (state : InternedConstructorTemplates.State Symbol Guard) : Outcome Symbol Guard (Value Symbol Guard) :=
  let key := muKey depth ordinary
  match state.nodes.table key with
  | some _ =>
      match state.nodeRecords key with
      | some value => .done (finish smart value) state
      | none => .pending key state
  | none =>
      let entry := Cache.intern state.nodes key
      let allocated := {state with nodes := entry.2}
      (callback (.interned entry.1.identity) allocated).bind fun bodyValue afterBody =>
        let candidate := Value.mu entry.1 bodyValue depth ordinary
        let records := keepFirst afterBody.nodeRecords key candidate
        .done (finish smart ((records key).getD candidate)) {afterBody with nodeRecords := records}

mutual
/-- Execute the full nested constructor schedule directly from source expression. -/
def build [DecidableEq (EdgeKey Symbol Guard)] (expression : Syntax Symbol Guard) (environment : List (Value Symbol Guard))
    (state : InternedConstructorTemplates.State Symbol Guard) : Outcome Symbol Guard (Value Symbol Guard) :=
  match expression with
  | .empty => .done .empty state
  | .var index => .done (environment[index]?.getD .empty) state
  | .node edges => (buildEdges edges environment state).bind fun values next => work (makeNode values) next
  | .union members => (buildMany members environment state).bind fun values next => work (makeUnion values) next
  | .binder smart body =>
      let callback := fun name current => (build body (.reference name :: environment) current).bind
        fun value next => work (withoutSelfReference name value) next
      (callback .depth state).bind fun depth afterDepth =>
      (callback (.uninterned depth.depth) afterDepth).bind fun ordinary afterOrdinary =>
        request smart depth ordinary callback afterOrdinary
termination_by sizeOf expression

/-- Child expression executes in source order and retains every completed value. -/
def buildMany [DecidableEq (EdgeKey Symbol Guard)] (expression : List (Syntax Symbol Guard))
    (environment : List (Value Symbol Guard)) (state : InternedConstructorTemplates.State Symbol Guard) :
    Outcome Symbol Guard (List (Value Symbol Guard)) :=
  match expression with
  | [] => .done [] state
  | first :: rest => (build first environment state).bind fun value next =>
      (buildMany rest environment next).bind fun values final => .done (value :: values) final
termination_by sizeOf expression

/-- Edge construction occurs after its actual nested child computations complete. -/
def buildEdges [DecidableEq (EdgeKey Symbol Guard)] (expression : List (EdgeSyntax Symbol Guard))
    (environment : List (Value Symbol Guard)) (state : InternedConstructorTemplates.State Symbol Guard) :
    Outcome Symbol Guard (List (EdgeValue Symbol Guard)) :=
  match expression with
  | [] => .done [] state
  | .mk symbol constraint children :: rest =>
      (buildMany children environment state).bind fun values next =>
      (work (makeEdge symbol constraint values) next).bind fun edge afterEdge =>
      (buildEdges rest environment afterEdge).bind fun edges final => .done (edge :: edges) final
termination_by sizeOf expression
end

mutual
/-- A scoped term reads only actual lexical variables; a binder supplies one additional variable. -/
def Scoped (depth : Nat) : Syntax Symbol Guard → Prop
  | .empty => True
  | .var index => index < depth
  | .node edges => EdgesScoped depth edges
  | .union members => ManyScoped depth members
  | .binder _ body => Scoped (depth + 1) body
termination_by expression => sizeOf expression

/-- Every child shares the source scope of its enclosing edge or union. -/
def ManyScoped (depth : Nat) : List (Syntax Symbol Guard) → Prop
  | [] => True
  | first :: rest => Scoped depth first ∧ ManyScoped depth rest
termination_by expression => sizeOf expression

/-- Source constraints and symbols do not change the lexical scope of edge children. -/
def EdgesScoped (depth : Nat) : List (EdgeSyntax Symbol Guard) → Prop
  | [] => True
  | .mk _ _ children :: rest => ManyScoped depth children ∧ EdgesScoped depth rest
termination_by expression => sizeOf expression
end

/-- A reported collision names an installed identity with no completed node payload. -/
def IsPending (key : NodeKey) (state : InternedConstructorTemplates.State Symbol Guard) : Prop :=
  (∃ entry, state.nodes.table key = some entry) ∧ state.nodeRecords key = none

mutual
/-- A pending result is always an actual cache lookup on an incomplete canonical record. -/
theorem build_pending [DecidableEq (EdgeKey Symbol Guard)] (expression : Syntax Symbol Guard)
    (environment : List (Value Symbol Guard)) (state : InternedConstructorTemplates.State Symbol Guard)
    (key : NodeKey) (later : InternedConstructorTemplates.State Symbol Guard)
    (blocked : build expression environment state = .pending key later) : IsPending key later := by
  cases expression with
  | empty | var index => simp [build] at blocked
  | node edges =>
      simp only [build] at blocked
      cases result : buildEdges edges environment state with
      | pending pending after =>
          simp only [result, Outcome.bind, Outcome.pending.injEq] at blocked
          rcases blocked with ⟨rfl, rfl⟩
          exact buildEdges_pending edges environment state _ _ result
      | done values after => simp [result, Outcome.bind, work] at blocked
  | union members =>
      simp only [build] at blocked
      cases result : buildMany members environment state with
      | pending pending after =>
          simp only [result, Outcome.bind, Outcome.pending.injEq] at blocked
          rcases blocked with ⟨rfl, rfl⟩
          exact buildMany_pending members environment state _ _ result
      | done values after => simp [result, Outcome.bind, work] at blocked
  | binder smart body =>
      simp only [build, request] at blocked
      cases depthResult : build body (.reference .depth :: environment) state with
      | pending pending after =>
          simp only [depthResult, Outcome.bind, Outcome.pending.injEq] at blocked
          rcases blocked with ⟨rfl, rfl⟩
          exact build_pending body _ state _ _ depthResult
      | done depthValue afterDepthValue =>
          simp only [depthResult, Outcome.bind, work] at blocked
          generalize depthEq : run (withoutSelfReference .depth depthValue) afterDepthValue = depth at blocked
          cases ordinaryResult : build body (.reference (.uninterned depth.1.depth) :: environment) depth.2 with
          | pending pending after =>
              simp only [ordinaryResult, Outcome.pending.injEq] at blocked
              rcases blocked with ⟨rfl, rfl⟩
              exact build_pending body _ depth.2 _ _ ordinaryResult
          | done ordinaryValue afterOrdinaryValue =>
              simp only [ordinaryResult] at blocked
              generalize ordinaryEq : run (withoutSelfReference (.uninterned depth.1.depth) ordinaryValue) afterOrdinaryValue = ordinary at blocked
              split at blocked
              · rename_i entry present
                split at blocked
                · contradiction
                · rename_i absent
                  simp only [Outcome.pending.injEq] at blocked
                  rcases blocked with ⟨rfl, rfl⟩
                  exact ⟨⟨entry, present⟩, absent⟩
              · rename_i missing
                cases bodyResult : build body
                  (.reference (.interned (Cache.intern ordinary.2.nodes (muKey depth.1 ordinary.1)).1.identity) :: environment)
                  {ordinary.2 with nodes := (Cache.intern ordinary.2.nodes (muKey depth.1 ordinary.1)).2} with
                | pending pending after =>
                    simp only [bodyResult, Outcome.pending.injEq] at blocked
                    rcases blocked with ⟨rfl, rfl⟩
                    exact build_pending body _ _ _ _ bodyResult
                | done bodyValue afterBodyValue => simp [bodyResult] at blocked
termination_by sizeOf expression

/-- Child traversal propagates only a concrete pending lookup from one original child. -/
theorem buildMany_pending [DecidableEq (EdgeKey Symbol Guard)] (expression : List (Syntax Symbol Guard))
    (environment : List (Value Symbol Guard)) (state : InternedConstructorTemplates.State Symbol Guard)
    (key : NodeKey) (later : InternedConstructorTemplates.State Symbol Guard)
    (blocked : buildMany expression environment state = .pending key later) : IsPending key later := by
  cases expression with
  | nil => simp [buildMany] at blocked
  | cons first rest =>
      simp only [buildMany] at blocked
      cases head : build first environment state with
      | pending pending after =>
          simp only [head, Outcome.bind, Outcome.pending.injEq] at blocked
          rcases blocked with ⟨rfl, rfl⟩
          exact build_pending first environment state _ _ head
      | done value after =>
          simp only [head, Outcome.bind] at blocked
          cases tail : buildMany rest environment after with
          | pending pending final =>
              simp only [tail, Outcome.pending.injEq] at blocked
              rcases blocked with ⟨rfl, rfl⟩
              exact buildMany_pending rest environment after _ _ tail
          | done values final => simp [tail] at blocked
termination_by sizeOf expression

/-- Edge traversal introduces no pending reads outside its actual nested child computations. -/
theorem buildEdges_pending [DecidableEq (EdgeKey Symbol Guard)] (expression : List (EdgeSyntax Symbol Guard))
    (environment : List (Value Symbol Guard)) (state : InternedConstructorTemplates.State Symbol Guard)
    (key : NodeKey) (later : InternedConstructorTemplates.State Symbol Guard)
    (blocked : buildEdges expression environment state = .pending key later) : IsPending key later := by
  cases expression with
  | nil => simp [buildEdges] at blocked
  | cons first rest =>
      cases first with
      | mk symbol constraint children =>
          simp only [buildEdges] at blocked
          cases head : buildMany children environment state with
          | pending pending after =>
              simp only [head, Outcome.bind, Outcome.pending.injEq] at blocked
              rcases blocked with ⟨rfl, rfl⟩
              exact buildMany_pending children environment state _ _ head
          | done values after =>
              simp only [head, Outcome.bind, work] at blocked
              cases tail : buildEdges rest environment (run (makeEdge symbol constraint values) after).2 with
              | pending pending final =>
                  simp only [tail, Outcome.pending.injEq] at blocked
                  rcases blocked with ⟨rfl, rfl⟩
                  exact buildEdges_pending rest environment _ _ _ tail
              | done edges final => simp [tail] at blocked
termination_by sizeOf expression
end

end MicroCFTA.InternedNestedConstruction
