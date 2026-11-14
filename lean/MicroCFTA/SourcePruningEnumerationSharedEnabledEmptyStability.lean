import MicroCFTA.SourcePruningEnumerationSharedEnabledEmpty
import MicroCFTA.SourceCurrentAllocatedSharedConjunctionWorkerActual

/-!
# Exact successful shared emptiness checks at larger bounds

A skipped check retains its endpoint at every bound.
A completed shared call retains its checked state, fourth memo and private snapshot.
The semantic tuple budget stays fixed.
-/
namespace MicroCFTA.SourcePruningEnumerationSharedEnabledEmpty
open InternedConstructorTemplates (Value EdgeKey)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Fourth" => SourceCurrentEmptinessMemo.Memo
local notation "Queries" => SourceEndpointMemo.Memos
local notation "Snapshot" => SourceCurrentConjunctionSharedWorklistStep.State Symbol FullSyntax.Formula
variable {width : Nat}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Node]

/-- A skipped actual check retains the exact endpoint and query memo at every bound. -/
theorem check_skipped_at_any_bounds
    {p h P H : Nat} {query : Node} {before after : Checked width}
    {memo retained : Fourth} {queries savedQueries : Queries}
    (actual : check p h query before memo queries = (.skipped after retained, savedQueries)) :
    check P H query before memo queries = (.skipped after retained, savedQueries) := by
  obtain ⟨gate, sameAfter, sameMemo⟩ :=
    check_skipped_receipt p h query before after memo retained queries savedQueries actual
  subst after
  subst retained
  exact check_skipped P H query before memo queries savedQueries gate

/-- A performed success retains all four shared fields and the exact query memo at larger bounds. -/
theorem check_performed_done_stable
    {p h P H : Nat} {query : Node} {before after : Checked width}
    {memo saved : Fourth} {snapshot : Snapshot} {answer : Bool}
    {queries savedQueries : Queries}
    (actual : check p h query before memo queries =
      (.performed (.done answer after saved snapshot), savedQueries))
    (enoughP : p ≤ P) (enoughH : h ≤ H) :
    check P H query before memo queries =
      (.performed (.done answer after saved snapshot), savedQueries) := by
  obtain ⟨gate, called⟩ := check_performed_receipt p h query before memo queries savedQueries
    (.done answer after saved snapshot) actual
  have later := SourceCurrentAllocatedSharedConjunctionWorkerActual.call_done_stable
    called enoughP enoughH
  have observation := check_performed P H query before memo queries savedQueries gate
  rw [later] at observation
  exact observation

end MicroCFTA.SourcePruningEnumerationSharedEnabledEmpty
