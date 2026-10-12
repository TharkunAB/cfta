import MicroCFTA.InternedStoredClosedMuCompletion

/-!
# An actual open query with deeply nested closed children

The source creates two retained closed binders inside an open outer body.
The prepared source worker completes without reconstructing those closed
records. The previous depth-zero body condition excludes this query.
-/
namespace MicroCFTA.InternedStoredClosedMuExample
open Cache InternedConstructorTemplates InternedProbeProvenance
open InternedNestedConstruction InternedNestedFacts InternedNestedProvenance
open InternedUnionNormalForm InternedStoredSelfFilter InternedStoredBodyInvariant
open InternedStoredClosedMuCompletion InternedUnionHeadGuard InternedGateRank

/-- Each closed binder uses its own reference below an ordinary constructor. -/
def closedProgram : Syntax Nat Unit :=
  .binder true (.binder true (.node [.mk 1 () [.var 0, .var 1]]))

/-- The open outer body also contains both closed binders. -/
def program : Syntax Nat Unit :=
  .binder true (.node [.mk 0 () [.var 0, .var 1, closedProgram]])

def environment : List (Value Nat Unit) := [.reference (.uninterned 999)]
def original : Outcome Nat Unit (Value Nat Unit) := build program environment empty
def final : State Nat Unit := original.state
def outer : Value Nat Unit := match original with
  | .done value _ => value
  | .pending .. => .empty

def body : Value Nat Unit := match outer with
  | .mu _ value _ _ => value
  | _ => .empty

/-- All original source calls complete in the actual canonical cache. -/
theorem source_return : original = .done outer final := by cbv

theorem outer_mu : (match outer with | .mu .. => True | _ => False) := by cbv

/-- Two closed nested binders violate the earlier numeric body-depth restriction. -/
theorem body_depth : body.depth = 2 := by cbv

/-- The queried outer binder is open, so the source gate must unfold it. -/
theorem outer_open : outer.free ≠ [] := by cbv; simp

/-- Source preparation stops at the closed child and creates no binder request. -/
theorem body_prepared : PreparedWithoutMu body := by
  conv => arg 1; cbv
  apply PreparedWithoutMu.node
  intro child member
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, EdgeValue.children, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · exact .reference _
  · exact .reference _
  · exact .closed _ (by cbv)

/-- The current source path reaches the outer constructor before any nested binder. -/
theorem body_safe : HeadSafe body := by
  conv => arg 1; cbv
  apply HeadSafe.node

/-- Source inputs have complete reference provenance. -/
theorem inputs_available : Values (empty (Symbol := Nat) (Guard := Unit)) environment := by
  intro value member
  have same : value = .reference (.uninterned 999) := by simpa [environment] using member
  subst value
  exact ordinary_available empty 999

theorem checked : Verified empty original Available :=
  build_verified program environment empty empty_facts inputs_available

/-- Actual unfolding completes and strictly decreases rank despite the positive nested depth. -/
theorem ranked : ∃ value after,
    InternedStoredSubstitution.unfold outer final = .done value after ∧ headRank value < headRank outer := by
  have facts : Facts final := by simpa only [source_return, Outcome.state] using checked.facts
  have flat : Flat final := build_flat program environment empty empty_facts inputs_available empty_flat
  have clean : Clean final := build_clean program environment empty empty_facts inputs_available empty_flat empty_clean
  have available := checked.result outer final source_return
  have actual := outer_mu
  cases shape : outer with
  | empty | reference | node | union => simp [shape] at actual
  | mu entry source depth ordinary =>
      apply unfold_complete_decreases entry source depth ordinary final facts flat clean (shape ▸ available)
      · simpa only [body, shape] using body_prepared
      · simpa only [body, shape] using body_safe
      · simpa only [shape] using outer_open

end MicroCFTA.InternedStoredClosedMuExample
