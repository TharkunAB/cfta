import MicroCFTA.RecursiveNaryCausality
import MicroCFTA.RecursiveNaryQuery

/-!
# Concrete n-ary inverse checks

These examples retain source branch numbers and check complete private
recursive terms. The pure finite callbacks have their own direct leaf law.
-/
namespace MicroCFTA.RecursiveNaryExamples
open Language GeneratorCombinators IntegerTermViews SizedRank
open RecursiveCallbackTermination RecursiveNaryFields RecursiveNaryInverse
open RecursiveNaryBody (sparseBody sparseBranches valueRecipe)

/-- A pure leaf has one original rank at size zero. -/
def pureCallbacks [DecidableEq Symbol] : LeafCallbacks Symbol := fun {_} source view wanted =>
  match source with
  | .pure entry => if project view entry.2 = wanted then [(⟨0, 0⟩, true)] else []
  | _ => []

/-- The pure finite callback law is independent of the recursive index. -/
theorem pure_exact [DecidableEq Symbol] (entry : Value × EngineTerm Symbol) :
    FiniteExact (RecursiveCallbackAlignment.finite pureCallbacks (.pure entry)) := by
  intro view wanted position
  cases position with
  | mk size rank =>
      cases size with
      | zero =>
          cases rank with
          | zero => simp [RecursiveCallbackAlignment.finite, pureCallbacks, FiniteSource.classMembers]
          | succ rank => simp [RecursiveCallbackAlignment.finite, pureCallbacks, FiniteSource.classMembers]
      | succ size => simp [RecursiveCallbackAlignment.finite, pureCallbacks, FiniteSource.classMembers]

/-- The sparse n-ary example uses only the independently correct pure leaves. -/
theorem sparse_leaves : RecursiveNaryFields.LeavesExact (pureCallbacks (Symbol := String)) sparseBody := by
  intro ⟨index, within⟩
  have cases : index = 0 ∨ index = 1 ∨ index = 2 := by omega
  rcases cases with rfl | rfl | rfl
  · exact pure_exact _
  · exact pure_exact _
  · trivial

/-- A complete term from branch two retains its exact source class position. -/
def sparseTerm : EngineTerm String :=
  .node .recursion [.node (.choice 2) [.node (.user "U")
    [.node .recursion [.node (.choice 0) [.node (.user "L") []]]]]]

theorem branch_two_inverse :
    RecursiveNaryInverse.positions pureCallbacks sparseBody .whole [sparseTerm] = [(⟨2, 0⟩, true)] := by
  cbv

theorem branch_two_all_views :
    RecursiveNaryInverse.positions pureCallbacks sparseBody .spine [sparseTerm] = [(⟨2, 0⟩, true)] ∧
    RecursiveNaryInverse.positions pureCallbacks sparseBody .labelled [sparseTerm] = [(⟨2, 0⟩, true)] := by
  cbv

/-- Two source alternatives can have the same term after a user label removes private choices. -/
def repeatedBody : Body Nat String Nat := .label "N" (.choice 3 fun index =>
  match index with
  | ⟨0, _⟩ => .finite (.pure (0, .node .pure []))
  | ⟨1, _⟩ => .occurrence
  | ⟨2, _⟩ => .occurrence)

def repeatedTerm : EngineTerm String :=
  .node .recursion [.node (.user "N") [.node .recursion [.node (.user "N") []]]]

theorem repeated_guarded :
    RecursiveSource.guarded (valueRecipe repeatedBody) (RecursiveSource.assumption (valueRecipe repeatedBody)) = true := by
  cbv

/-- Source derivation counts can exceed the number of distinct constructor terms. -/
theorem repeated_decodes :
    rootCounts repeatedBody 2 = 2 ∧
    rootSelect repeatedBody ⟨2, 0⟩ = some repeatedTerm ∧
    rootSelect repeatedBody ⟨2, 1⟩ = some repeatedTerm := by
  cbv

/-- The inverse retains both source ranks when constructor terms coincide. -/
theorem repeated_inverse :
    RecursiveNaryInverse.positions pureCallbacks repeatedBody .whole [repeatedTerm] =
      [(⟨2, 0⟩, true), (⟨2, 1⟩, true)] := by
  cbv

end MicroCFTA.RecursiveNaryExamples
