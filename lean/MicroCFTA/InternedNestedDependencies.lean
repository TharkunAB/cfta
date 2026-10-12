import MicroCFTA.InternedNestedConstructionReplay

/-!
# Exact nested execution depends only on source variable occurrences

The finite expression determines every lexical environment slot it reads.
Changing any other slot preserves the complete constructor computation,
including both probes, cache effects, and pending readback outcomes.
-/
namespace MicroCFTA.InternedNestedDependencies
open InternedConstructorTemplates InternedNestedConstruction

/-- A binder removes its own variable and shifts each enclosing variable index down by one. -/
def enclosing : Nat → Option Nat
  | 0 => none
  | index + 1 => some index

mutual
/-- Collect the exact lexical input slots mentioned by the original nested expression. -/
def inputs : Syntax Symbol Guard → List Nat
  | .empty => []
  | .var index => [index]
  | .node edges => edgeInputs edges
  | .union members => manyInputs members
  | .binder _ body => (inputs body).filterMap enclosing
termination_by expression => sizeOf expression

/-- Ordered child expressions contribute only their original lexical input slots. -/
def manyInputs : List (Syntax Symbol Guard) → List Nat
  | [] => []
  | first :: rest => inputs first ++ manyInputs rest
termination_by expressions => sizeOf expressions

/-- Edge declarations retain their children's lexical dependencies without reading a computed record. -/
def edgeInputs : List (EdgeSyntax Symbol Guard) → List Nat
  | [] => []
  | .mk _ _ children :: rest => manyInputs children ++ edgeInputs rest
termination_by expressions => sizeOf expressions
end

/-- Environments agree only at the slots explicitly used by the source expression. -/
def Agree (used : List Nat) (first second : List (Value Symbol Guard)) : Prop :=
  ∀ index ∈ used, first[index]?.getD .empty = second[index]?.getD .empty

mutual
/-- Syntax-derived agreement preserves the whole nested execution, with no key or callback law premise. -/
theorem build_congr [DecidableEq (EdgeKey Symbol Guard)] (expression : Syntax Symbol Guard)
    (first second : List (Value Symbol Guard)) (state : State Symbol Guard)
    (agree : Agree (inputs expression) first second) : build expression first state = build expression second state := by
  cases expression with
  | empty => simp only [build]
  | var index =>
      have same := agree index (by simp [inputs])
      simp only [build, same]
  | node edges =>
      have same := buildEdges_congr edges first second state (by simpa only [inputs] using agree)
      simp only [build, same]
  | union members =>
      have same := buildMany_congr members first second state (by simpa only [inputs] using agree)
      simp only [build, same]
  | binder smart body =>
      have bodySame : ∀ name current,
          build body (.reference name :: first) current = build body (.reference name :: second) current := by
        intro name current
        apply build_congr body _ _ current
        intro index member
        cases index with
        | zero => rfl
        | succ index =>
            have used : index ∈ inputs (.binder smart body) := by
              simp only [inputs]
              exact List.mem_filterMap.mpr ⟨index + 1, member, rfl⟩
            exact agree index used
      have callbacks :
          (fun name current => (build body (.reference name :: first) current).bind
            fun value next => work (withoutSelfReference name value) next) =
          (fun name current => (build body (.reference name :: second) current).bind
            fun value next => work (withoutSelfReference name value) next) := by
        funext name current
        rw [bodySame]
      simp only [build]
      exact congrArg (fun callback => (callback .depth state).bind fun depth afterDepth =>
        (callback (.uninterned depth.depth) afterDepth).bind fun ordinary afterOrdinary =>
          request smart depth ordinary callback afterOrdinary) callbacks
termination_by sizeOf expression

/-- Every child and its ordered effects depend only on the combined original input slots. -/
theorem buildMany_congr [DecidableEq (EdgeKey Symbol Guard)] (expressions : List (Syntax Symbol Guard))
    (first second : List (Value Symbol Guard)) (state : State Symbol Guard)
    (agree : Agree (manyInputs expressions) first second) :
    buildMany expressions first state = buildMany expressions second state := by
  cases expressions with
  | nil => simp only [buildMany]
  | cons head tail =>
      have firstAgree : Agree (inputs head) first second :=
        fun index member => agree index (by simpa only [manyInputs] using List.mem_append_left (manyInputs tail) member)
      have tailAgree : Agree (manyInputs tail) first second :=
        fun index member => agree index (by simpa only [manyInputs] using List.mem_append_right (inputs head) member)
      simp only [buildMany, build_congr head first second state firstAgree]
      congr 1
      funext value next
      rw [buildMany_congr tail first second next tailAgree]
termination_by sizeOf expressions

/-- Exact edge computation is unchanged when every original child input agrees. -/
theorem buildEdges_congr [DecidableEq (EdgeKey Symbol Guard)] (expressions : List (EdgeSyntax Symbol Guard))
    (first second : List (Value Symbol Guard)) (state : State Symbol Guard)
    (agree : Agree (edgeInputs expressions) first second) :
    buildEdges expressions first state = buildEdges expressions second state := by
  cases expressions with
  | nil => simp only [buildEdges]
  | cons head tail =>
      cases head with
      | mk symbol constraint children =>
          have childrenAgree : Agree (manyInputs children) first second :=
            fun index member => agree index (by simpa only [edgeInputs] using List.mem_append_left (edgeInputs tail) member)
          have tailAgree : Agree (edgeInputs tail) first second :=
            fun index member => agree index (by simpa only [edgeInputs] using List.mem_append_right (manyInputs children) member)
          simp only [buildEdges, buildMany_congr children first second state childrenAgree]
          congr 1
          funext values next
          congr 1
          funext edge afterEdge
          rw [buildEdges_congr tail first second afterEdge tailAgree]
termination_by sizeOf expressions
end

/-- Changed enclosing inputs that the expression never reads reuse the earlier complete result exactly. -/
theorem independent_replay [DecidableEq (EdgeKey Symbol Guard)] (expression : Syntax Symbol Guard)
    (first second : List (Value Symbol Guard)) (before after : State Symbol Guard)
    (value : Value Symbol Guard) (final : State Symbol Guard)
    (valid : InternedConstructorTemplates.Valid before) (completed : build expression first before = .done value final)
    (growth : Grows final after) (agree : Agree (inputs expression) first second) :
    build expression second after = .done value after := by
  rw [← build_congr expression first second after agree]
  exact build_replay expression first before after value final valid completed growth

/-- Replacing an unused nearest enclosing input changes no actual source effect. -/
theorem unused_head [DecidableEq (EdgeKey Symbol Guard)] (expression : Syntax Symbol Guard)
    (absent : 0 ∉ inputs expression) (first second : Value Symbol Guard) (rest : List (Value Symbol Guard))
    (state : State Symbol Guard) : build expression (first :: rest) state = build expression (second :: rest) state := by
  apply build_congr
  intro index member
  cases index with
  | zero => exact False.elim (absent member)
  | succ index => rfl

/-- An inner callback can retain its own local variable while ignoring a changed enclosing binder. -/
theorem unused_outer [DecidableEq (EdgeKey Symbol Guard)] (expression : Syntax Symbol Guard)
    (absent : 1 ∉ inputs expression) (localValue first second : Value Symbol Guard)
    (rest : List (Value Symbol Guard)) (state : State Symbol Guard) :
    build expression (localValue :: first :: rest) state = build expression (localValue :: second :: rest) state := by
  apply build_congr
  intro index member
  cases index with
  | zero => rfl
  | succ index =>
      cases index with
      | zero => exact False.elim (absent member)
      | succ index => rfl

end MicroCFTA.InternedNestedDependencies
