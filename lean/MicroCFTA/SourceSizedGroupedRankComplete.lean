import MicroCFTA.SourceSizedGroupedRankCandidates

/-!
# Complete source transition candidate lookup

A complete child position table supplies every accepted child state.
The source symbol-and-arity bucket then finds the same transition.
A passing equality check makes its position branch return a rank.

These are local inputs for the recursive bottom-up proof. No final API
contract or native map representation is supplied by this module.
-/
namespace MicroCFTA.SourceSizedGroupedRankComplete
open Language RecursiveSize SizedRank SourceSizedDecided
open SourceSizedGroupedRankCandidates
open RecursiveJoinFields (ValueIndex)

variable {State Symbol : Type}

/-- Every accepted child state has a position in its computed child table. -/
def TablesComplete (domain : State → Term Symbol → Prop)
    (tables : List (State → Option Position)) (values : List (Term Symbol)) : Prop :=
  All₂ (fun table term => ∀ state, domain state term → ∃ position, table state = some position) tables values

/-- Complete child tables supply the literal ordered child lookup. -/
theorem lookupChildren_complete (domain : State → Term Symbol → Prop)
    (tables : List (State → Option Position)) (values : List (Term Symbol))
    (complete : TablesComplete domain tables values)
    (children : List State) (accepted : All₂ domain children values) :
    ∃ positions, TablePosition.lookupChildren children tables = some positions := by
  induction complete generalizing children with
  | nil => cases accepted; exact ⟨[], rfl⟩
  | @cons table term tables terms first rest ih =>
      cases accepted with
      | cons head tail =>
          obtain ⟨position, read⟩ := first _ head
          obtain ⟨positions, readRest⟩ := ih _ tail
          exact ⟨position :: positions, by simp [TablePosition.lookupChildren, read, readRest]⟩

/-- A passing equality check makes either source transition-position branch succeed. -/
theorem transitionPosition_exists [DecidableEq Symbol]
    (indexes : State → ValueIndex (Term Symbol)) (row : Row State Symbol (List (List Nat)))
    (values : List (Term Symbol)) (positions : List Position)
    (held : SourceSizedConjunctionSemantics.holds row.constraint (.node row.label values) = true) :
    ∃ result, transitionPosition indexes row values positions = some result := by
  by_cases plain : row.constraint = [] <;> simp [transitionPosition, plain, held]

/-- An accepted source transition receives a position from complete child tables. -/
theorem candidate_exists [DecidableEq Symbol]
    (indexes : State → ValueIndex (Term Symbol)) (domain : State → Term Symbol → Prop)
    (row : Row State Symbol (List (List Nat))) (symbol : Symbol)
    (values : List (Term Symbol)) (tables : List (State → Option Position))
    (complete : TablesComplete domain tables values) (label : row.label = symbol)
    (accepted : All₂ domain row.children values)
    (held : SourceSizedConjunctionSemantics.holds row.constraint (.node row.label values) = true) :
    ∃ result, candidate indexes row symbol values tables = some result := by
  obtain ⟨positions, read⟩ := lookupChildren_complete domain tables values complete row.children accepted
  obtain ⟨result, found⟩ := transitionPosition_exists indexes row values positions held
  exact ⟨result, by simp [candidate, label, accepted.length_eq, read, found]⟩

end MicroCFTA.SourceSizedGroupedRankComplete
