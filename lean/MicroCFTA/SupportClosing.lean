import MicroCFTA.SupportSpine
import MicroCFTA.SupportRoot

/-!
# Closing finite generator layers

The model distinguishes source support shapes that select each closing case.
A choice distributes the label over all alternative roots. Each recursive
operand can remain inside the complete support graphs passed to a layer.
-/
namespace MicroCFTA.SupportClosing
open Language GeneratorCombinators BinderLanguage SupportGraph SupportTerms

/-- Labels whose root the source term callback wraps as one complete child. -/
def ordinary : Label Symbol → Bool
  | .pure | .apply | .choice _ | .joinN => false
  | _ => true

/-- Finite outer support forms made by the generator constructors. -/
inductive Layer (Symbol : Type) where
  | pure
  | application (functions : SupportSpine.Spine Symbol) (argument : Support Symbol)
  | joined (component : Nat) (operation : Support Symbol) (arguments : List (Support Symbol))
  | ordinary (payload : Payload (Label Symbol)) (children : List (Support Symbol))
  | choice (alternatives : List (Layer Symbol))

/-- The constructor cases agree with the source's private-label recognizers. -/
def Valid : Layer Symbol → Prop
  | .pure | .joined .. => True
  | .application functions _ => SupportSpine.Valid functions
  | .ordinary payload _ => ordinary payload.label = true
  | .choice alternatives => ∀ layer ∈ alternatives, Valid layer

/-- Build the source layer, with one indexed wrapper per choice alternative. -/
def graph : Layer Symbol → Support Symbol
  | .pure => edge .pure []
  | .application functions argument => SupportSpine.graph (.apply functions argument)
  | .joined component operation arguments => SupportJoin.joinNode component operation arguments
  | .ordinary payload children => .branch payload children
  | .choice alternatives => .alternatives ((alternatives.map graph).mapIdx fun index support => edge (.choice index) [support])

/-- The ordinary outgoing roots produced by source layer closing. -/
def roots (symbol : Symbol) : Layer Symbol → List (Support Symbol)
  | .pure => [edge (.user symbol) []]
  | .application functions argument => [SupportSpine.close symbol functions argument]
  | .joined component operation arguments => [SupportRoot.closeJoin symbol component operation arguments]
  | .ordinary payload children => [edge (.user symbol) [.branch payload children]]
  | .choice alternatives => alternatives.flatMap (roots symbol)

/-- Choice closing concatenates every labelled root without inserting a wrapper. -/
def close (symbol : Symbol) (layer : Layer Symbol) : Support Symbol := .alternatives (roots symbol layer)

/-- Alternative syntax means ordinary membership in its edge list. -/
theorem alternatives_exact (environment : Env (Label Symbol)) (edges : List (Support Symbol))
    (term : Term (Label Symbol)) :
    meaning environment (.alternatives edges) term ↔ ∃ edge ∈ edges, meaning environment edge term := by
  simp [meaning]

/-- A singleton alternative list retains the exact branch language. -/
theorem one_exact (environment : Env (Label Symbol)) (shape : Support Symbol) (term : Term (Label Symbol)) :
    meaning environment (.alternatives [shape]) term ↔ meaning environment shape term := by
  simp [alternatives_exact]

/-- An unconstrained leaf has exactly its displayed label and no children. -/
theorem leaf_exact (environment : Env (Label Symbol)) (label : Label Symbol) (term : Term (Label Symbol)) :
    meaning environment (edge label []) term ↔ term = .node label [] := by
  simp only [edge, meaning]
  constructor
  · rintro ⟨children, rfl, accepted, _⟩
    have empty : children = [] := by cases children <;> simp_all [forest]
    simp [empty]
  · rintro rfl
    exact ⟨[], rfl, by simp [forest], trivial⟩

/-- A unary wrapper retains exactly one accepted operand term. -/
theorem unary_exact (environment : Env (Label Symbol)) (label : Label Symbol)
    (child : Support Symbol) (term : Term (Label Symbol)) :
    meaning environment (edge label [child]) term ↔
      ∃ value, meaning environment child value ∧ term = .node label [value] := by
  simp only [edge, meaning]
  constructor
  · rintro ⟨children, rfl, accepted, _⟩
    cases children with
    | nil => simp [forest] at accepted
    | cons first rest =>
      simp only [forest] at accepted
      have empty : rest = [] := by cases rest <;> simp_all [forest]
      exact ⟨first, accepted.1, by simp [empty]⟩
  · rintro ⟨value, accepted, rfl⟩
    refine ⟨[value], rfl, ?_, trivial⟩
    simp only [forest]
    exact ⟨accepted, trivial⟩

/-- A recognized ordinary label is wrapped by the source term callback. -/
theorem ordinary_term (symbol : Symbol) (label : Label Symbol) (children : List (Term (Label Symbol)))
    (valid : ordinary label = true) : labelTerm symbol (.node label children) = .node (.user symbol) [.node label children] := by
  cases label <;> simp_all [ordinary, labelTerm, applicationTermChildren]

/-- Every accepted choice term comes from its exact indexed alternative. -/
theorem choice_exact (environment : Env (Label Symbol)) (layers : List (Layer Symbol)) (term : Term (Label Symbol)) :
    meaning environment (graph (.choice layers)) term ↔
      ∃ index, ∃ inside : index < layers.length, ∃ value,
        meaning environment (graph layers[index]) value ∧ term = .node (.choice index) [value] := by
  simp only [graph, alternatives_exact]
  constructor
  · rintro ⟨shape, member, accepted⟩
    obtain ⟨index, inside, rfl⟩ := List.mem_mapIdx.mp member
    obtain ⟨value, valueAccepted, rfl⟩ := (unary_exact environment _ _ term).mp accepted
    have bound : index < layers.length := by simpa using inside
    exact ⟨index, bound, value, by simpa using valueAccepted, rfl⟩
  · rintro ⟨index, inside, value, accepted, rfl⟩
    refine ⟨_, List.mem_mapIdx.mpr ⟨index, by simpa using inside, rfl⟩, ?_⟩
    apply (unary_exact environment _ _ _).mpr
    exact ⟨value, by simpa using accepted, rfl⟩

/-- Closing any supported finite layer agrees exactly with its term callback. -/
theorem close_exact (environment : Env (Label Symbol)) (symbol : Symbol) (layer : Layer Symbol)
    (valid : Valid layer) (term : Term (Label Symbol)) :
    meaning environment (close symbol layer) term ↔
      ∃ original, meaning environment (graph layer) original ∧ term = labelTerm symbol original := by
  induction layer using Layer.rec
    (motive_2 := fun layers => ∀ layer ∈ layers, Valid layer → ∀ term,
      meaning environment (close symbol layer) term ↔
        ∃ original, meaning environment (graph layer) original ∧ term = labelTerm symbol original)
    generalizing term with
  | pure =>
    simp only [close, roots, one_exact, leaf_exact, graph]
    constructor
    · rintro rfl
      exact ⟨.node .pure [], rfl, by simp [labelTerm]⟩
    · rintro ⟨original, accepted, rfl⟩
      rw [accepted]
      simp [labelTerm]
  | application functions argument =>
    simp only [Valid] at valid
    simpa only [close, roots, one_exact, graph] using SupportSpine.close_exact environment symbol functions argument valid term
  | joined component operation arguments =>
    simpa only [close, roots, one_exact, graph] using SupportRoot.closeJoin_exact environment symbol component operation arguments term
  | ordinary payload children =>
    simp only [Valid] at valid
    simp only [close, roots, one_exact, unary_exact, graph]
    constructor <;> rintro ⟨original, accepted, same⟩
    all_goals
      have parsed := accepted
      simp only [meaning] at parsed
      obtain ⟨values, rfl, _, _⟩ := parsed
      exact ⟨_, accepted, by simpa [ordinary_term symbol payload.label values valid] using same⟩
  | choice layers ih =>
    simp only [Valid] at valid
    simp only [close, roots, alternatives_exact]
    constructor
    · rintro ⟨shape, member, accepted⟩
      obtain ⟨child, childMember, shapeMember⟩ := List.mem_flatMap.mp member
      have closed := (alternatives_exact environment (roots symbol child) term).mpr ⟨shape, shapeMember, accepted⟩
      obtain ⟨original, originalAccepted, same⟩ := (ih child childMember (valid child childMember) term).mp closed
      obtain ⟨index, inside, selected⟩ := List.mem_iff_getElem.mp childMember
      refine ⟨.node (.choice index) [original], ?_, ?_⟩
      · apply (choice_exact environment layers _).mpr
        exact ⟨index, inside, original, selected ▸ originalAccepted, rfl⟩
      · simpa [labelTerm] using same
    · rintro ⟨original, accepted, same⟩
      obtain ⟨index, inside, value, valueAccepted, rfl⟩ := (choice_exact environment layers original).mp accepted
      have member : layers[index] ∈ layers := List.getElem_mem inside
      have closed := (ih layers[index] member (valid _ member) term).mpr
        ⟨value, valueAccepted, by simpa [labelTerm] using same⟩
      obtain ⟨shape, shapeMember, accepted⟩ := (alternatives_exact environment (roots symbol layers[index]) term).mp closed
      exact ⟨shape, List.mem_flatMap.mpr ⟨layers[index], member, shapeMember⟩, accepted⟩
  | nil => rename_i layer member valid term; simp at member
  | cons child rest first tail =>
    rename_i selected member valid term
    rcases List.mem_cons.mp member with rfl | member
    · exact first valid term
    · exact tail selected member valid term

end MicroCFTA.SupportClosing
