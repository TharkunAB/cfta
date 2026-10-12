import MicroCFTA.SupportGraph

/-!
# Closing applicative support spines

The source flattens only the left side of each private application edge.
Every argument remains an operand support. A non-application base retains
its complete constrained edge. Its label must not be private Pure or Apply.
-/
namespace MicroCFTA.SupportSpine
open Language GeneratorCombinators BinderLanguage SupportGraph SupportTerms

/-- The source's finite left application spine with arbitrary operand supports. -/
inductive Spine (Symbol : Type) where
  | pure
  | base (payload : Payload (Label Symbol)) (children : List (Support Symbol))
  | apply (functions : Spine Symbol) (argument : Support Symbol)

/-- A base has no private constructor that the spine recognizer would remove. -/
def Valid : Spine Symbol → Prop
  | .pure => True
  | .base payload _ => payload.label ≠ .pure ∧ payload.label ≠ .apply
  | .apply functions _ => Valid functions

/-- Build the source's unconstrained private application edges. -/
def graph : Spine Symbol → Support Symbol
  | .pure => edge .pure []
  | .base payload children => .branch payload children
  | .apply functions argument => edge .apply [graph functions, argument]

/-- Execute the source's ordered left-spine flattening. -/
def flatten : Spine Symbol → List (Support Symbol)
  | .pure => []
  | .base payload children => [.branch payload children]
  | .apply functions argument => flatten functions ++ [argument]

/-- Concatenated support forests preserve the exact split and child order. -/
theorem forest_append (environment : Env (Label Symbol)) (left right : List (Support Symbol))
    (terms : List (Term (Label Symbol))) :
    forest environment (left ++ right) terms ↔
      ∃ first second, forest environment left first ∧ forest environment right second ∧ terms = first ++ second := by
  induction left generalizing terms with
  | nil =>
    simp only [List.nil_append]
    constructor
    · intro accepted
      exact ⟨[], terms, by simp [forest], accepted, rfl⟩
    · rintro ⟨first, second, firstAccepted, secondAccepted, rfl⟩
      have empty : first = [] := by cases first <;> simp_all [forest]
      simpa [empty] using secondAccepted
  | cons child rest ih =>
    cases terms with
    | nil =>
      constructor
      · simp [forest]
      · rintro ⟨first, second, accepted, _, same⟩
        have empty : first = [] := List.append_eq_nil_iff.mp same.symm |>.1
        simp [empty, forest] at accepted
    | cons term terms =>
      simp only [List.cons_append, forest]
      constructor
      · rintro ⟨head, tail⟩
        obtain ⟨first, second, firstAccepted, secondAccepted, rfl⟩ := (ih terms).mp tail
        exact ⟨term :: first, second, by simp only [forest]; exact ⟨head, firstAccepted⟩, secondAccepted, rfl⟩
      · rintro ⟨first, second, firstAccepted, secondAccepted, same⟩
        cases first with
        | nil => simp [forest] at firstAccepted
        | cons value first =>
          simp only [forest] at firstAccepted
          simp only [List.cons_append, List.cons.injEq] at same
          rcases same with ⟨rfl, rfl⟩
          exact ⟨firstAccepted.1, (ih _).mpr ⟨first, second, firstAccepted.2, secondAccepted, rfl⟩⟩

/-- A one-edge application accepts precisely its two operand terms. -/
theorem apply_exact (environment : Env (Label Symbol)) (functions argument : Support Symbol)
    (term : Term (Label Symbol)) :
    meaning environment (edge .apply [functions, argument]) term ↔
      ∃ function value, meaning environment functions function ∧ meaning environment argument value ∧
        term = .node .apply [function, value] := by
  simp only [edge, meaning]
  constructor
  · rintro ⟨children, rfl, accepted, _⟩
    cases children with
    | nil => simp [forest] at accepted
    | cons first rest => cases rest with
      | nil => simp [forest] at accepted
      | cons second rest =>
        simp only [forest] at accepted
        have empty : rest = [] := by cases rest <;> simp_all [forest]
        subst rest
        exact ⟨first, second, accepted.1, accepted.2.1, rfl⟩
  · rintro ⟨function, value, first, second, rfl⟩
    refine ⟨_, rfl, ?_, trivial⟩
    simp only [forest]
    exact ⟨first, second, trivial⟩

/-- A non-private spine base remains one complete child term. -/
theorem base_children (payload : Payload (Label Symbol)) (children : List (Term (Label Symbol)))
    (valid : payload.label ≠ .pure ∧ payload.label ≠ .apply) :
    applicationLeftChildren (.node payload.label children) = [.node payload.label children] := by
  cases label : payload.label <;> simp_all [applicationLeftChildren, applicationTermChildren]

/-- Graph flattening and term flattening have exactly the same complete forest language. -/
theorem flatten_exact (environment : Env (Label Symbol)) (spine : Spine Symbol)
    (valid : Valid spine) (terms : List (Term (Label Symbol))) :
    forest environment (flatten spine) terms ↔
      ∃ original, meaning environment (graph spine) original ∧ terms = applicationLeftChildren original := by
  induction spine generalizing terms with
  | pure =>
    constructor
    · intro accepted
      have empty : terms = [] := by cases terms <;> simp_all [flatten, forest]
      subst terms
      refine ⟨.node .pure [], ?_, ?_⟩
      · simp only [graph, edge, meaning]
        exact ⟨[], rfl, by simp [forest], trivial⟩
      · simp [applicationLeftChildren]
    · rintro ⟨original, accepted, rfl⟩
      simp only [graph, edge, meaning] at accepted
      obtain ⟨children, rfl, accepted, _⟩ := accepted
      have empty : children = [] := by cases children <;> simp_all [forest]
      simp [empty, applicationLeftChildren, flatten, forest]
  | base payload children =>
    constructor
    · intro accepted
      cases terms with
      | nil => simp [flatten, forest] at accepted
      | cons first rest =>
        simp only [flatten, forest] at accepted
        have empty : rest = [] := by cases rest <;> simp_all [forest]
        subst rest
        refine ⟨first, accepted.1, ?_⟩
        have head := accepted.1
        simp only [meaning] at head
        obtain ⟨values, rfl, _, _⟩ := head
        exact (base_children payload values valid).symm
    · rintro ⟨original, accepted, rfl⟩
      simp only [graph, meaning] at accepted
      obtain ⟨values, rfl, childrenAccepted, guard⟩ := accepted
      rw [base_children payload values valid]
      simp only [flatten, forest]
      refine ⟨?_, trivial⟩
      simp only [meaning]
      exact ⟨values, rfl, childrenAccepted, guard⟩
  | apply functions argument ih =>
    simp only [flatten, forest_append]
    constructor
    · rintro ⟨first, second, firstAccepted, secondAccepted, rfl⟩
      obtain ⟨function, functionAccepted, rfl⟩ := (ih valid first).mp firstAccepted
      cases second with
      | nil => simp [forest] at secondAccepted
      | cons value rest =>
        simp only [forest] at secondAccepted
        have empty : rest = [] := by cases rest <;> simp_all [forest]
        subst rest
        refine ⟨.node .apply [function, value], ?_, ?_⟩
        · exact (apply_exact environment (graph functions) argument _).mpr ⟨function, value, functionAccepted, secondAccepted.1, rfl⟩
        · simp [applicationLeftChildren, applicationTermChildren]
    · rintro ⟨original, accepted, rfl⟩
      obtain ⟨function, value, functionAccepted, valueAccepted, rfl⟩ := (apply_exact environment (graph functions) argument original).mp accepted
      refine ⟨applicationLeftChildren function, [value], (ih valid _).mpr ⟨function, functionAccepted, rfl⟩, ?_, ?_⟩
      · simp only [forest]; exact ⟨valueAccepted, trivial⟩
      · simp [applicationLeftChildren, applicationTermChildren]

/-- Close one outer application with its exact flattened support children. -/
def close (symbol : Symbol) (functions : Spine Symbol) (argument : Support Symbol) : Support Symbol :=
  edge (.user symbol) (flatten functions ++ [argument])

/-- Closing a source application produces exactly the terms returned by its label callback. -/
theorem close_exact (environment : Env (Label Symbol)) (symbol : Symbol)
    (functions : Spine Symbol) (argument : Support Symbol) (valid : Valid functions)
    (term : Term (Label Symbol)) :
    meaning environment (close symbol functions argument) term ↔
      ∃ original, meaning environment (graph (.apply functions argument)) original ∧ term = labelTerm symbol original := by
  simp only [close, edge, meaning]
  constructor
  · rintro ⟨children, rfl, accepted, _⟩
    obtain ⟨original, originalAccepted, childrenEq⟩ := (flatten_exact environment (.apply functions argument) valid children).mp accepted
    obtain ⟨function, value, _, _, shape⟩ := (apply_exact environment (graph functions) argument original).mp originalAccepted
    refine ⟨original, originalAccepted, ?_⟩
    subst original
    simp_all [labelTerm, applicationLeftChildren, applicationTermChildren]
  · rintro ⟨original, accepted, rfl⟩
    obtain ⟨function, value, _, _, shape⟩ := (apply_exact environment (graph functions) argument original).mp accepted
    have flattened := (flatten_exact environment (.apply functions argument) valid _).mpr ⟨original, accepted, rfl⟩
    subst original
    simp only [labelTerm, applicationTermChildren, Option.getD_some]
    refine ⟨_, rfl, ?_, trivial⟩
    simpa [flatten, applicationLeftChildren, applicationTermChildren] using flattened

end MicroCFTA.SupportSpine
