import MicroCFTA.InternedFreshOrdinaryConstruction

/-!
# Exact execution of equivalent captured plans

Two plans can use different lexical slots for the same complete inputs.
Equivalent plans retain constructor order and every binder callback.
They therefore have identical outcomes and actual returned caches.
-/
namespace MicroCFTA.InternedFreshOrdinaryPlanEquivalence
open InternedConstructorTemplates
open InternedNestedConstruction (Syntax EdgeSyntax Outcome work request)
open InternedFreshOrdinaryConstruction
open InternedBinderProtocol (Reference)

mutual
/-- Different lexical plans read equal values and make the same ordered constructor requests. -/
def Equivalent (first : Syntax Symbol Guard) (firstInputs : List (Value Symbol Guard))
    (second : Syntax Symbol Guard) (secondInputs : List (Value Symbol Guard)) : Prop :=
  match first, second with
  | .empty, .empty => True
  | .var left, .var right => firstInputs[left]?.getD .empty = secondInputs[right]?.getD .empty
  | .node left, .node right => EdgesEquivalent left firstInputs right secondInputs
  | .union left, .union right => ManyEquivalent left firstInputs right secondInputs
  | .binder leftSmart left, .binder rightSmart right =>
      leftSmart = rightSmart ∧ ∀ name : Reference,
        Equivalent left (.reference name :: firstInputs) right (.reference name :: secondInputs)
  | _, _ => False
termination_by sizeOf first

/-- Equivalent ordered child plans retain each actual input value. -/
def ManyEquivalent (first : List (Syntax Symbol Guard)) (firstInputs : List (Value Symbol Guard))
    (second : List (Syntax Symbol Guard)) (secondInputs : List (Value Symbol Guard)) : Prop :=
  match first, second with
  | [], [] => True
  | left :: rest, right :: tail =>
      Equivalent left firstInputs right secondInputs ∧ ManyEquivalent rest firstInputs tail secondInputs
  | _, _ => False
termination_by sizeOf first

/-- Equivalent edge plans retain symbols, guards, child order, and edge order. -/
def EdgesEquivalent (first : List (EdgeSyntax Symbol Guard)) (firstInputs : List (Value Symbol Guard))
    (second : List (EdgeSyntax Symbol Guard)) (secondInputs : List (Value Symbol Guard)) : Prop :=
  match first, second with
  | [], [] => True
  | .mk leftSymbol leftGuard left :: rest, .mk rightSymbol rightGuard right :: tail =>
      leftSymbol = rightSymbol ∧ leftGuard = rightGuard ∧
        ManyEquivalent left firstInputs right secondInputs ∧ EdgesEquivalent rest firstInputs tail secondInputs
  | _, _ => False
termination_by sizeOf first
end

mutual
/-- Repaired execution of equivalent full plans has identical completion, pending keys, and cache effects. -/
theorem build_exact [DecidableEq (EdgeKey Symbol Guard)] (first : Syntax Symbol Guard)
    (firstInputs : List (Value Symbol Guard)) (second : Syntax Symbol Guard) (secondInputs : List (Value Symbol Guard))
    (state : State Symbol Guard) (equivalent : Equivalent first firstInputs second secondInputs) :
    build first firstInputs state = build second secondInputs state := by
  cases first <;> cases second <;> simp only [Equivalent] at equivalent <;> try contradiction
  case empty.empty => simp only [build]
  case var.var left right => simp only [build, equivalent]
  case node.node left right =>
    simp only [build, buildEdges_exact left firstInputs right secondInputs state equivalent]
  case union.union left right =>
    simp only [build, buildMany_exact left firstInputs right secondInputs state equivalent]
  case binder.binder leftSmart left rightSmart right =>
    obtain ⟨rfl, bodies⟩ := equivalent
    have callbacks :
        (fun name current => (build left (.reference name :: firstInputs) current).bind
          fun value next => work (withoutSelfReference name value) next) =
        (fun name current => (build right (.reference name :: secondInputs) current).bind
          fun value next => work (withoutSelfReference name value) next) := by
      funext name current
      rw [build_exact left _ right _ current (bodies name)]
    simp only [build]
    exact congrArg (fun callback => (callback .depth state).bind fun depth afterDepth =>
      (callback (.uninterned (ordinaryLevel depth)) afterDepth).bind fun ordinary afterOrdinary =>
        request leftSmart depth ordinary callback afterOrdinary) callbacks
termination_by sizeOf first

/-- Equivalent child lists retain every intermediate physical cache. -/
theorem buildMany_exact [DecidableEq (EdgeKey Symbol Guard)] (first : List (Syntax Symbol Guard))
    (firstInputs : List (Value Symbol Guard)) (second : List (Syntax Symbol Guard)) (secondInputs : List (Value Symbol Guard))
    (state : State Symbol Guard) (equivalent : ManyEquivalent first firstInputs second secondInputs) :
    buildMany first firstInputs state = buildMany second secondInputs state := by
  cases first <;> cases second <;> simp only [ManyEquivalent] at equivalent <;> try contradiction
  case nil.nil => simp only [buildMany]
  case cons.cons left rest right tail =>
    simp only [buildMany, build_exact left firstInputs right secondInputs state equivalent.1]
    cases done : build right secondInputs state with
    | pending => rfl
    | done value after => simp only [Outcome.bind, buildMany_exact rest firstInputs tail secondInputs after equivalent.2]
termination_by sizeOf first

/-- Equivalent edge lists retain the exact same symbols, guards, canonical entries, and final cache. -/
theorem buildEdges_exact [DecidableEq (EdgeKey Symbol Guard)] (first : List (EdgeSyntax Symbol Guard))
    (firstInputs : List (Value Symbol Guard)) (second : List (EdgeSyntax Symbol Guard)) (secondInputs : List (Value Symbol Guard))
    (state : State Symbol Guard) (equivalent : EdgesEquivalent first firstInputs second secondInputs) :
    buildEdges first firstInputs state = buildEdges second secondInputs state := by
  cases first <;> cases second <;> (try simp only [EdgesEquivalent] at equivalent) <;> try contradiction
  case nil.nil => simp only [buildEdges]
  case cons.cons left rest right tail =>
    cases left with
    | mk leftSymbol leftGuard leftChildren =>
      cases right with
      | mk rightSymbol rightGuard rightChildren =>
        simp only [EdgesEquivalent] at equivalent
        obtain ⟨rfl, rfl, children, edges⟩ := equivalent
        simp only [buildEdges, buildMany_exact leftChildren firstInputs rightChildren secondInputs state children]
        cases done : buildMany rightChildren secondInputs state with
        | pending => rfl
        | done values after =>
            simp only [Outcome.bind, work,
              buildEdges_exact rest firstInputs tail secondInputs (run (makeEdge leftSymbol leftGuard values) after).2 edges]
termination_by sizeOf first
end

end MicroCFTA.InternedFreshOrdinaryPlanEquivalence
