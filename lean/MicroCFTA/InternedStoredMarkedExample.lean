import MicroCFTA.InternedStoredMarkedCompletion

/-!
# Actual unfolding with an open nested marked binder

The outer body contains an open nested Mu. Its original stored nullary
edge and root symbol establish completion of the prepared nested source
execution. The shallow and closed-child fragments exclude this query.
-/
namespace MicroCFTA.InternedStoredMarkedExample
open Cache InternedConstructorTemplates InternedProbeProvenance InternedRecordCoherence
open InternedNestedCoverage InternedNestedRootLabels
open InternedNestedConstruction InternedNestedFacts InternedNestedProvenance
open InternedUnionNormalForm InternedStoredSelfFilter InternedStoredBodyInvariant
open InternedStoredMarkedCompletion InternedUnionHeadGuard InternedGateRank

/-- The nested binder uses its own reference and the unresolved outer reference. -/
def nestedProgram : Syntax Nat Unit :=
  .binder true (.node [.mk 1 () [], .mk 1 () [.var 0, .var 1, .var 2]])

/-- The outer body retains both its recursive reference and the open nested binder. -/
def program : Syntax Nat Unit :=
  .binder true (.node [.mk 0 () [.var 0, .var 1, nestedProgram]])

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

/-- The actual open nested binder gives the outer body positive cached Mu depth. -/
theorem body_depth : body.depth = 1 := by cbv

/-- Select the actual nested child in the retained outer edge. -/
def inner : Value Nat Unit := match body with
  | .node _ [.mk _ children] _ _ => children[2]?.getD .empty
  | _ => .empty

/-- The nested Mu really is open; closed-leaf preparation does not apply. -/
theorem inner_open : inner.free ≠ [] := by cbv; simp

theorem inner_mu : (match inner with | .mu .. => True | _ => False) := by cbv

/-- The queried outer binder is open, so the source gate must unfold it. -/
theorem outer_open : outer.free ≠ [] := by cbv; simp

/-- Actual original edge fields supply all nested marker conditions. -/
theorem body_prepared : PreparedMarked [] body := by
  conv => arg 2; cbv
  apply PreparedMarked.node
  intro child member
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, EdgeValue.children,
    List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · exact .reference _ _
  · exact .reference _ _
  · apply PreparedMarked.mu (marker := 1)
    · simp
    · simp [StoredMarked, signature, EdgeValue.entry, EdgeValue.children]
    · intro child member
      simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, List.nil_append,
        EdgeValue.children, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl <;> exact .reference _ _

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
  have covered : Covered [] final :=
    build_covered program environment empty empty_valid empty_correct.2 outer final source_return
  have flat : Flat final := build_flat program environment empty empty_facts inputs_available empty_flat
  have clean : Clean final := build_clean program environment empty empty_facts inputs_available empty_flat empty_clean
  have available := checked.result outer final source_return
  have actual := outer_mu
  cases shape : outer with
  | empty | reference | node | union => simp [shape] at actual
  | mu entry source depth ordinary =>
      apply unfold_complete_decreases entry source depth ordinary final facts covered flat clean (shape ▸ available)
      · simpa only [body, shape] using body_prepared
      · simpa only [body, shape] using body_safe
      · simpa only [shape] using outer_open

end MicroCFTA.InternedStoredMarkedExample
