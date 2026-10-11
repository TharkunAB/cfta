import MicroCFTA.FTAValidation

/-!
# Exact graph construction from finite terms

The source uses `Nothing` for the initial state and `Just term` for a shared
subterm state. Each subterm state has exactly its own constructor edge.
Ordered-set iteration can change enumeration order but not membership.
-/
namespace MicroCFTA.FromTerms
open Language DistinctRank

/-- All nested subterms, including the term itself. -/
def subterms : Term Symbol → List (Term Symbol)
  | term@(.node _ children) => term :: children.flatMap subterms

/-- A complete input term names the child state of each child. -/
def transition : Term Symbol → Edge (Option (Term Symbol)) Symbol
  | .node symbol children => ⟨symbol, children.map some, fun _ => true⟩

/-- Root alternatives and one shared row for each distinct subterm. -/
def graph [DecidableEq Symbol] (input : List (Term Symbol)) : Automaton (Option (Term Symbol)) Symbol
  | none => (distinct input).map transition
  | some term => if term ∈ input.flatMap subterms then [transition term] else []

/-- Every tree occurs in its own subterm list. -/
theorem subterms_self (term : Term Symbol) : term ∈ subterms term := by
  cases term
  simp [subterms]

/-- Subterms of an existing child also occur in the containing term. -/
theorem subterms_child (symbol : Symbol) (children : List (Term Symbol)) (child value : Term Symbol)
    (member : child ∈ children) (nested : value ∈ subterms child) :
    value ∈ subterms (.node symbol children) := by
  simp only [subterms]
  exact List.mem_cons.mpr (Or.inr (List.mem_flatMap.mpr ⟨child, member, nested⟩))

/-- Descending inside a subterm remains inside the original term. -/
theorem subterms_trans (outer middle inner : Term Symbol)
    (first : middle ∈ subterms outer) (second : inner ∈ subterms middle) : inner ∈ subterms outer := by
  induction outer using Term.rec
    (motive_2 := fun terms => ∀ child ∈ terms, middle ∈ subterms child → inner ∈ subterms child) with
  | node symbol children ih =>
    simp only [subterms] at first
    rcases List.mem_cons.mp first with same | nested
    · simpa [same] using second
    · obtain ⟨child, member, nested⟩ := List.mem_flatMap.mp nested
      exact subterms_child symbol children child inner member (ih child member nested)
  | nil => simp_all
  | cons child rest hc hr =>
    rename_i selected member nested
    rcases List.mem_cons.mp member with rfl | member
    · exact hc nested
    · exact hr selected member nested

/-- An input subterm's immediate children all have graph rows. -/
theorem child_present (input : List (Term Symbol)) (symbol : Symbol) (children : List (Term Symbol))
    (present : Term.node symbol children ∈ input.flatMap subterms)
    (child : Term Symbol) (member : child ∈ children) : child ∈ input.flatMap subterms := by
  obtain ⟨outer, inputMember, nested⟩ := List.mem_flatMap.mp present
  exact List.mem_flatMap.mpr ⟨outer, inputMember,
    subterms_trans outer (.node symbol children) child nested
      (subterms_child symbol children child child member (subterms_self child))⟩

/-- Successful child runs at subterm states reproduce the original ordered children. -/
theorem children_equal {expected actual : List (Term Symbol)}
    (runs : All₂ (fun state term => ∀ source, state = some source → term = source)
      (expected.map some) actual) : actual = expected := by
  induction expected generalizing actual with
  | nil => cases runs; rfl
  | cons first rest ih =>
    cases runs with
    | cons head tail =>
      have same := head first rfl
      simp [same, ih tail]

/-- Every accepting subterm state returns only the term that names that state. -/
theorem accepted_shape [DecidableEq Symbol] (input : List (Term Symbol))
    {state : Option (Term Symbol)} {term : Term Symbol} (accepted : Accepts (graph input) state term) :
    match state with
    | none => term ∈ input
    | some source => term = source ∧ source ∈ input.flatMap subterms := by
  induction accepted using Accepts.rec
    (motive_2 := fun states terms _ => All₂ (fun state term => ∀ source, state = some source → term = source)
      states terms) with
  | @node state edge children member runs guard ih =>
    cases state with
    | none =>
      obtain ⟨source, present, equal⟩ := List.mem_map.mp member
      subst edge
      cases source with
      | node symbol expected =>
        have same := children_equal ih
        subst children
        exact (mem_distinct input _).mp present
    | some source =>
      by_cases present : source ∈ input.flatMap subterms
      · have equal : edge = transition source := by simpa [graph, present] using member
        subst edge
        cases source with
        | node symbol expected =>
          have same := children_equal ih
          subst children
          exact ⟨rfl, present⟩
      · simp [graph, present] at member
  | nil => exact .nil
  | cons head tail ihhead ihtail =>
    refine .cons ?_ ihtail
    intro source same
    subst_vars
    exact ihhead.1

/-- Every named input subterm has its own accepting run. -/
theorem subterm_complete [DecidableEq Symbol] (input : List (Term Symbol)) (term : Term Symbol)
    (present : term ∈ input.flatMap subterms) : Accepts (graph input) (some term) term := by
  induction term using Term.rec
    (motive_2 := fun terms => (∀ term ∈ terms, term ∈ input.flatMap subterms) →
      All₂ (Accepts (graph input)) (terms.map some) terms) with
  | node symbol children ih =>
    exact .node (transition (.node symbol children)) children (by simp [graph, present])
      (ih (child_present input symbol children present)) rfl
  | nil => exact .nil
  | cons first rest hf hr =>
    rename_i present
    exact .cons (hf (present first (by simp))) (hr (fun term member => present term (by simp [member])))

/-- Every input term is accepted at the initial state. -/
theorem root_complete [DecidableEq Symbol] (input : List (Term Symbol)) (term : Term Symbol)
    (member : term ∈ input) : Accepts (graph input) none term := by
  have present : term ∈ input.flatMap subterms := List.mem_flatMap.mpr ⟨term, member, subterms_self term⟩
  have accepted := subterm_complete input term present
  cases accepted with
  | node edge children edgeMember runs guard =>
    have same : edge = transition (.node edge.label children) := by simpa [graph, present] using edgeMember
    exact .node edge children (List.mem_map.mpr
      ⟨.node edge.label children, (mem_distinct input _).mpr member, same.symm⟩) runs guard

/-- The source builder accepts all and only the supplied complete terms. -/
theorem fromTerms_exact [DecidableEq Symbol] (input : List (Term Symbol)) (term : Term Symbol) :
    Accepts (graph input) none term ↔ term ∈ input :=
  ⟨fun accepted => accepted_shape input accepted, root_complete input term⟩

/-- A shared subterm state has exactly its named singleton language. -/
theorem subterm_exact [DecidableEq Symbol] (input : List (Term Symbol)) (source term : Term Symbol) :
    Accepts (graph input) (some source) term ↔ term = source ∧ source ∈ input.flatMap subterms := by
  constructor
  · exact accepted_shape input
  · rintro ⟨rfl, present⟩
    exact subterm_complete input _ present

/-- The source emits exactly these finite state names. -/
def states [DecidableEq Symbol] (input : List (Term Symbol)) : List (Option (Term Symbol)) :=
  none :: (distinct (input.flatMap subterms)).map some

/-- Every stored edge belongs to an original input subterm. -/
theorem row_origin [DecidableEq Symbol] (input : List (Term Symbol)) (state : Option (Term Symbol))
    (edge : Edge (Option (Term Symbol)) Symbol) (member : edge ∈ graph input state) :
    ∃ term ∈ input.flatMap subterms, edge = transition term := by
  cases state with
  | none =>
    obtain ⟨term, present, same⟩ := List.mem_map.mp member
    exact ⟨term, List.mem_flatMap.mpr ⟨term, (mem_distinct input term).mp present, subterms_self term⟩, same.symm⟩
  | some term =>
    by_cases present : term ∈ input.flatMap subterms
    · exact ⟨term, present, by simpa [graph, present] using member⟩
    · simp [graph, present] at member

/-- No constructed edge points to a missing state. -/
theorem graph_closed [DecidableEq Symbol] (input : List (Term Symbol)) (state : Option (Term Symbol))
    (edge : Edge (Option (Term Symbol)) Symbol) (member : edge ∈ graph input state)
    (child : Option (Term Symbol)) (childMember : child ∈ edge.children) : child ∈ states input := by
  obtain ⟨term, present, rfl⟩ := row_origin input state edge member
  cases term with
  | node symbol children =>
    obtain ⟨term, member, rfl⟩ := List.mem_map.mp childMember
    simp only [states, List.mem_cons, List.mem_map]
    exact Or.inr ⟨term, (mem_distinct _ term).mpr (child_present input symbol children present term member), rfl⟩

/-- A finite-term import can use the same canonical distinct-term rank interface. -/
def index [DecidableEq Symbol] (input : List (Term Symbol)) :
    DistinctRank.Index (fun term => Accepts (graph input) none term) :=
  ⟨distinct input, distinct_nodup input, fun term => (mem_distinct input term).trans (fromTerms_exact input term).symm⟩

/-- The imported graph has one replay rank for each distinct input term. -/
theorem index_count [DecidableEq Symbol] (input : List (Term Symbol)) :
    (index input).count = (distinct input).length := rfl

/-- The concrete finite table supplied to `mkFTA`. -/
def rows [DecidableEq Symbol] (input : List (Term Symbol)) : FTAValidation.Rows (Option (Term Symbol)) Symbol :=
  (states input).map fun state => (state, graph input state)

/-- Every nonempty source row is declared in the finite table. -/
theorem declared [DecidableEq Symbol] (input : List (Term Symbol)) (state : Option (Term Symbol))
    (edge : Edge (Option (Term Symbol)) Symbol) (member : edge ∈ graph input state) : state ∈ states input := by
  cases state with
  | none => simp [states]
  | some term =>
    by_cases present : term ∈ input.flatMap subterms
    · simpa [states, mem_distinct] using present
    · simp [graph, present] at member

/-- The emitted finite table has exactly the modeled graph rows. -/
theorem rows_exact [DecidableEq Symbol] (input : List (Term Symbol)) (state : Option (Term Symbol))
    (edge : Edge (Option (Term Symbol)) Symbol) :
    edge ∈ FTAValidation.rowFor (rows input) state ↔ edge ∈ graph input state := by
  rw [FTAValidation.rowFor_exact]
  constructor
  · rintro ⟨outgoing, member, present⟩
    obtain ⟨key, _, same⟩ := List.mem_map.mp member
    have keyEqual : key = state := congrArg Prod.fst same
    have rowEqual : graph input key = outgoing := congrArg Prod.snd same
    rw [← rowEqual, keyEqual] at present
    exact present
  · intro present
    exact ⟨graph input state, List.mem_map.mpr ⟨state, declared input state edge present, rfl⟩, present⟩

/-- Public finite-term construction includes the source's ranked-alphabet validation. -/
def build [DecidableEq Symbol] [Ord (Option (Term Symbol))] (input : List (Term Symbol)) :
    Except (FTAValidation.Error (Option (Term Symbol)) Symbol)
      (FTAValidation.Rows (Option (Term Symbol)) Symbol) := FTAValidation.mkFTA none (rows input)

/-- Every successful public finite-term import has exactly the requested language. -/
theorem build_exact [DecidableEq Symbol] [Ord (Option (Term Symbol))]
    (input : List (Term Symbol)) (result : FTAValidation.Rows (Option (Term Symbol)) Symbol)
    (success : build input = .ok result) (term : Term Symbol) :
    Accepts (FTAValidation.rowFor result) none term ↔ term ∈ input := by
  have same := FTAValidation.mkFTA_returns none (rows input) result success
  subst result
  rw [FTAValidation.normalized_language_exact]
  rw [← fromTerms_exact input term]
  exact ⟨FTAValidation.accepts_transfer _ _ (fun state edge => (rows_exact input state edge).mp),
    FTAValidation.accepts_transfer _ _ (fun state edge => (rows_exact input state edge).mpr)⟩

end MicroCFTA.FromTerms
