import MicroCFTA.SourceCurrentConjunctionTupleBudget

/-!
# Finite tuple-budget run existence

Positive charges decrease the remaining tuple budget.
A zero charge adds an entry with no rows and removes the pending head.
The proof needs no table-size bound or semantic supplier.
-/
namespace MicroCFTA.SourceCurrentConjunctionTupleBudget
open SourceCurrentConjunctionEmptinessRows
open SourceCurrentConjunctionEmptinessTable (Entry)
variable {Node Symbol : Type}

/-- Every finite input derives a tuple-budget run with the exact source branch order. -/
theorem run_complete [DecidableEq Symbol] [DecidableEq Node]
    (empty : Node) (key : Node → Int) (closed : Node → Bool)
    (edges : Node → List (Edge Node Symbol)) (project : List Node → EqualityNormalize.Path → Node)
    (budget : Nat) (table : List (Entry Node)) (pending : List (List Node)) :
    ∃ final, Run empty key closed edges project budget table pending final := by
  induction budget using Nat.strongRecOn generalizing table pending with
  | ind budget outer =>
      induction pending generalizing table with
      | nil => exact ⟨table, .done⟩
      | cons nodes pending inner =>
          by_cases impossible : empty ∈ nodes
          · obtain ⟨final, rest⟩ := inner table
            exact ⟨final, .empty impossible rest⟩
          · cases skipped : SourceCurrentConjunctionEmptinessTable.skip key closed budget table nodes with
            | true =>
                obtain ⟨final, rest⟩ := inner table
                exact ⟨final, .skip impossible skipped rest⟩
            | false =>
                have positive := (SourceCurrentConjunctionEmptinessTable.admitted key closed budget table nodes skipped).1
                by_cases overflow : budget < (sample budget (edgeTuples edges nodes)).length
                · obtain ⟨final, rest⟩ := outer 0 positive table pending
                  exact ⟨final, .overflow impossible skipped overflow rest⟩
                · have fits : (sample budget (edgeTuples edges nodes)).length ≤ budget := Nat.le_of_not_gt overflow
                  by_cases zero : (sample budget (edgeTuples edges nodes)).length = 0
                  · have noSample : sample budget (edgeTuples edges nodes) = [] := List.length_eq_zero_iff.mp zero
                    have noRows : sampledRows empty key edges project budget nodes = [] := by
                      simp only [sampledRows, noSample, List.filterMap_nil]
                    obtain ⟨final, rest⟩ := inner (⟨nodes, []⟩ :: table)
                    refine ⟨final, .admit impossible skipped fits ?_⟩
                    simpa only [zero, Nat.sub_zero, noRows, List.flatten_nil, List.nil_append] using rest
                  · have smaller : budget - (sample budget (edgeTuples edges nodes)).length < budget := by omega
                    obtain ⟨final, rest⟩ := outer _ smaller
                      (⟨nodes, sampledRows empty key edges project budget nodes⟩ :: table)
                      ((sampledRows empty key edges project budget nodes).flatten ++ pending)
                    exact ⟨final, .admit impossible skipped fits rest⟩

end MicroCFTA.SourceCurrentConjunctionTupleBudget
