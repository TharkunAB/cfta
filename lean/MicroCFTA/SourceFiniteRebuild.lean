import MicroCFTA.SourceFromTermsArity
import MicroCFTA.Decoder

/-!
# Finite execution of reconstructed plain graphs

Every dependency follows a proper subterm. A height measure therefore
decreases at every child request. The ordered plain counter and decoder
recover exactly the sorted distinct input sequence after the derived bound.
These are graph and plain-plan results. Native SCC construction, smart-node
allocation, and the identity readback of `fromFTA` remain separate adapters.
-/
namespace MicroCFTA.SourceFiniteRebuild
open Language SourceFromTerms

variable [DecidableEq Symbol] [Ord (Term Symbol)]

omit [DecidableEq Symbol] [Ord (Term Symbol)] in
/-- Each listed tree fits under the maximum height of its list. -/
theorem height_le_forest (terms : List (Term Symbol)) (term : Term Symbol) (member : term ∈ terms) :
    term.height ≤ forestHeight terms := by
  induction terms with
  | nil => simp at member
  | cons first rest ih =>
    rcases List.mem_cons.mp member with rfl | member
    · exact Nat.le_max_left _ _
    · exact Nat.le_trans (ih member) (Nat.le_max_right _ _)

omit [DecidableEq Symbol] [Ord (Term Symbol)] in
/-- Child reconstruction always visits a strictly smaller term. -/
theorem child_height_lt (symbol : Symbol) (children : List (Term Symbol))
    (child : Term Symbol) (member : child ∈ children) : child.height < (Term.node symbol children).height := by
  have smaller := height_le_forest children child member
  simp only [Term.height, forestHeight] at *
  omega

/-- The synthetic root is above every complete input term. -/
def stateHeight (input : List (Term Symbol)) : Option (Term Symbol) → Nat
  | none => forestHeight input + 1
  | some term => term.height

/-- Every emitted child request strictly decreases the source height measure. -/
theorem edge_decreases (input : List (Term Symbol)) (state : Option (Term Symbol))
    (edge : Edge (Option (Term Symbol)) Symbol) (member : edge ∈ graph input state)
    (child : Option (Term Symbol)) (childIn : child ∈ edge.children) :
    stateHeight input child < stateHeight input state := by
  cases state with
  | none =>
    rw [graph_root] at member
    obtain ⟨term, termIn, same⟩ := List.mem_map.mp member
    subst edge
    cases term with
    | node symbol children =>
      obtain ⟨term, nested, rfl⟩ := List.mem_map.mp childIn
      have first := child_height_lt symbol children term nested
      have second := height_le_forest input (.node symbol children) ((mem_ordered input _).mp termIn)
      simp only [stateHeight]
      omega
  | some term =>
    rw [graph_some] at member
    split at member
    · have same := List.mem_singleton.mp member
      subst edge
      cases term with
      | node symbol children =>
        obtain ⟨term, nested, rfl⟩ := List.mem_map.mp childIn
        exact child_height_lt symbol children term nested
    · simp at member

/-- A directed dependency from one state to an immediate child. -/
def Dependency (input : List (Term Symbol)) (parent child : Option (Term Symbol)) : Prop :=
  ∃ edge ∈ graph input parent, child ∈ edge.children

/-- Reconstructing finite terms cannot create a dependency cycle. -/
theorem dependency_wellFounded (input : List (Term Symbol)) :
    WellFounded (fun child parent => Dependency input parent child) := by
  apply Subrelation.wf (r := fun child parent => stateHeight input child < stateHeight input parent)
  · intro child parent dependency
    obtain ⟨edge, member, childIn⟩ := dependency
    exact edge_decreases input parent edge member child childIn
  · exact (measure (stateHeight input)).wf

/-- Rebuilt finite terms carry no residual or equality guard. -/
theorem plain (input : List (Term Symbol)) : Decoder.Plain (graph input) := by
  intro state edge member term
  obtain ⟨source, _, same⟩ := FromTerms.row_origin input state edge ((graph_members input state edge).mp member)
  subst edge
  cases source
  rfl

omit [DecidableEq Symbol] [Ord (Term Symbol)] in
/-- Singleton child languages reconstruct the exact original child list. -/
theorem products_singletons (children : List (Term Symbol))
    (choices : Option (Term Symbol) → List (Term Symbol))
    (singletons : ∀ child ∈ children, choices (some child) = [child]) :
    products choices (children.map some) = [children] := by
  induction children with
  | nil => rfl
  | cons first rest ih =>
    simp [products, singletons first (by simp), ih (fun child member => singletons child (by simp [member]))]

/-- Every shared subterm state returns its singleton after its own height bound. -/
theorem enumerate_shared (input : List (Term Symbol)) (fuel : Nat) (term : Term Symbol)
    (present : term ∈ input.flatMap FromTerms.subterms) (enough : term.height ≤ fuel) :
    enumerate (graph input) fuel (some term) = [term] := by
  induction fuel generalizing term with
  | zero => have positive := term.height_pos; omega
  | succ fuel ih =>
    cases term with
    | node symbol children =>
      have chosen : products (enumerate (graph input) fuel) (children.map some) = [children] := by
        apply products_singletons
        intro child childIn
        apply ih child (FromTerms.child_present input symbol children present child childIn)
        have smaller := child_height_lt symbol children child childIn
        omega
      simp [enumerate, graph_some, present, FromTerms.transition, chosen]

/-- Every root alternative reproduces the complete term that named it. -/
theorem enumerate_root (input : List (Term Symbol)) (fuel : Nat)
    (enough : forestHeight input < fuel) : enumerate (graph input) fuel none = ordered input := by
  cases fuel with
  | zero => omega
  | succ fuel =>
    simp only [enumerate, graph_root, List.flatMap_map]
    have each : ∀ term ∈ ordered input,
        ((products (enumerate (graph input) fuel) (FromTerms.transition term).children).map
          (Term.node (FromTerms.transition term).label)).filter (FromTerms.transition term).guard = [term] := by
      intro term present
      cases term with
      | node symbol children =>
        have chosen : products (enumerate (graph input) fuel) (children.map some) = [children] := by
          apply products_singletons
          intro child childIn
          have nested := FromTerms.child_present input symbol children
            (List.mem_flatMap.mpr ⟨.node symbol children, (mem_ordered input _).mp present, FromTerms.subterms_self _⟩)
            child childIn
          apply enumerate_shared input fuel child nested
          have first := child_height_lt symbol children child childIn
          have second := height_le_forest input (.node symbol children) ((mem_ordered input _).mp present)
          omega
        simp [FromTerms.transition, chosen]
    calc
      _ = (ordered input).flatMap (fun term => [term]) := by
        simp only [List.flatMap]
        exact congrArg List.flatten (List.map_congr_left each)
      _ = ordered input := by simp

/-- The source plain counting recurrence counts distinct terms after the finite bound. -/
theorem count_exact (input : List (Term Symbol)) (fuel : Nat) (enough : forestHeight input < fuel) :
    Decoder.countAt (graph input) fuel none = (ordered input).length := by
  rw [Decoder.countAt_correct _ (plain input), enumerate_root input fuel enough]

/-- Plain plan decoding preserves every position of the ascending source term list. -/
theorem decode_exact (input : List (Term Symbol)) (fuel rank : Nat) (enough : forestHeight input < fuel) :
    Decoder.decode (Decoder.normalize (Decoder.compileAt (graph input) fuel none)) rank = (ordered input)[rank]? := by
  rw [Decoder.decode_compileAt _ (plain input), enumerate_root input fuel enough]

/-- The finite source index uses the actual ascending constructor-row order. -/
def index (input : List (Term Symbol)) : DistinctRank.Index (fun term => term ∈ input) :=
  ⟨ordered input, ordered_nodup input, mem_ordered input⟩

/-- A derived finite fuel gives the full ordered, distinct reconstruction. -/
theorem finite_execution (input : List (Term Symbol)) :
    enumerate (graph input) (stateHeight input none) none = (index input).members ∧
    Decoder.countAt (graph input) (stateHeight input none) none = (index input).count := by
  exact ⟨enumerate_root input _ (Nat.lt_succ_self _), count_exact input _ (Nat.lt_succ_self _)⟩

end MicroCFTA.SourceFiniteRebuild
