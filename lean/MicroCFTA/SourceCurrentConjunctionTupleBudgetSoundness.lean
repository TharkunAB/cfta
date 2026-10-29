import MicroCFTA.SourceCurrentConjunctionTupleBudget

/-!
# Conservative soundness of tuple-charged conjunction admission

Only complete fitting tuple products enter the finite table.
Overflow adds no row and leaves the conjunction outside the table.
Existing source tuple witnesses discharge finite-table soundness.
-/
namespace MicroCFTA.SourceCurrentConjunctionTupleBudget
open Language (Term All₂)
open SourceCurrentConjunctionEmptinessRows
open SourceCurrentConjunctionEmptinessTable (Entry Stored)
variable {Node Symbol : Type}

/-- Every stored entry retains all source rows, including zero-tuple admissions. -/
theorem Run.stored [DecidableEq Symbol] [DecidableEq Node]
    {empty : Node} {key : Node → Int} {closed : Node → Bool}
    {edges : Node → List (Edge Node Symbol)} {project : List Node → EqualityNormalize.Path → Node}
    {budget : Nat} {table final : List (Entry Node)} {pending : List (List Node)}
    (actual : Run empty key closed edges project budget table pending final)
    (stored : Stored empty closed (tupleRows empty key edges project) table) :
    Stored empty closed (tupleRows empty key edges project) final := by
  induction actual with
  | done => exact stored
  | empty _ _ ih => exact ih stored
  | skip _ _ _ ih => exact ih stored
  | overflow _ _ _ _ ih => exact ih stored
  | @admit budget table nodes pending final nonempty fresh fits _rest ih =>
      apply ih
      intro entry member
      rcases List.mem_cons.mp member with rfl | member
      · exact ⟨sampledRows_eq empty key edges project budget nodes fits,
          (SourceCurrentConjunctionEmptinessTable.admitted key closed budget table nodes fresh).2.1, nonempty⟩
      · exact stored entry member

/-- An actual empty-start tuple-budget run derives its conservative true verdict law. -/
theorem Run.sound [DecidableEq Symbol] [DecidableEq Node]
    (empty : Node) (key : Node → Int) (closed : Node → Bool)
    (meaning : Node → Term Symbol → Prop) (emptyFalse : ∀ term, ¬meaning empty term)
    (edges : Node → List (Edge Node Symbol))
    (expose : ∀ node term, meaning node term → ∃ edge ∈ edges node, EdgeAccepts meaning edge term)
    (project : List Node → EqualityNormalize.Path → Node)
    (projectLaw : ∀ children symbol terms path part, path ≠ [] → All₂ meaning children terms →
      (Term.node symbol terms).atPath path = some part → meaning (project children path) part)
    (faithful : SourceCurrentConjunctionEmptinessTable.KeyFaithful empty key closed)
    (budget : Nat) (start : Node) (final : List (Entry Node))
    (actual : Run empty key closed edges project budget [] [[start]] final)
    (verdict : SourceCurrentConjunctionEmptinessTable.provablyEmpty empty key closed final [start] = true) :
    ∀ term, ¬meaning start term := by
  have stored := actual.stored (by intro entry member; cases member)
  have excluded := SourceCurrentConjunctionEmptinessTable.sound empty key closed meaning emptyFalse edges expose
    project projectLaw final stored faithful [start] verdict
  intro term accepted
  exact excluded term ⟨by simp, by simpa using accepted⟩

end MicroCFTA.SourceCurrentConjunctionTupleBudget
