import MicroCFTA.SourcePruningEnumerationEnabledEmpty
import MicroCFTA.SourceCurrentAllocatedConjunctionWorkerActual

/-!
# Successful enabled emptiness checks at larger bounds

The same endpoint decision selects the same fourth-memo check.
A completed check retains the answer and the entire checked state and memo.
-/
namespace MicroCFTA.SourcePruningEnumerationEnabledEmpty
open InternedConstructorTemplates SourcePruningEnumerationNodes
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Fourth" => SourceCurrentEmptinessMemo.Memo
local notation "Queries" => SourceEndpointMemo.Memos
variable {width : Nat}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]

/-- A completed actual enabled check retains every result field at larger work bounds. -/
theorem check_done_stable
    (p h P H : Nat) (query : Node) (before after : Checked width)
    (memo saved : Fourth) (queries returnedQueries : Queries) (answer : Bool)
    (observed : check p h query before memo queries = (.done answer after saved, returnedQueries))
    (enoughP : p ≤ P) (enoughH : h ≤ H) :
    check P H query before memo queries = (.done answer after saved, returnedQueries) := by
  unfold check at observed ⊢
  cases endpoint : SourceEndpointMemo.run query queries with
  | mk reached returned =>
      cases reached with
      | false => simpa only [endpoint, Bool.false_eq_true, ↓reduceIte] using observed
      | true =>
          simp only [endpoint, ↓reduceIte, Prod.mk.injEq] at observed
          obtain ⟨done, same⟩ := observed
          simp only [↓reduceIte,
            SourceCurrentAllocatedConjunctionWorkerActual.call_done_stable done enoughP enoughH, same]

end MicroCFTA.SourcePruningEnumerationEnabledEmpty
