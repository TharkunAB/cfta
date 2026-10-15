import MicroCFTA.SourceEqualityRequiredExecution

/-!
# Derived final invariants for every completed required-path list graph

Finite completion supplies a certified graph. Unique instrumented execution
identifies every other successful graph with that result and final cache.
No child callback completion or output-residency law is supplied.
-/
namespace MicroCFTA.SourceEqualityRequiredListFacts
open InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values Edges)
open MergedColdReaderClosedInputs (ClosedValues ClosedEdges)
open SourceEqualityNeeded SourceEqualityRequiredCache SourceEqualityRequiredGraph
open SourceEqualityRequiredWorkerComplete SourceEqualityRequiredExecution

/-- Every successful child graph has the complete closed output and actual cache histories. -/
theorem children_verified [DecidableEq (EdgeKey Symbol Guard)]
    {entries : List (Int × Needed)} {index : Nat} {values results : List (Value Symbol Guard)}
    {before after : State Symbol Guard} (trace : RequireChildren entries index values before results after)
    (ready : Ready before) (available : Values before values) (closed : ClosedValues values) :
    Keeps before after ∧ Values after results ∧ ClosedValues results := by
  have callbacks : SourceEqualityRequiredListsComplete.ChildComplete (Symbol := Symbol) (Guard := Guard) entries := by
    intro key needed member value current currentReady inputAvailable inputClosed
    exact SourceEqualityRequiredComplete.complete needed value current currentReady inputAvailable inputClosed
  obtain ⟨actual, final, completed, keeps, resident, resultClosed⟩ :=
    SourceEqualityRequiredListsComplete.children_complete entries callbacks index values before ready available closed
  obtain ⟨sameValues, sameState⟩ := children_unique completed trace
  cases sameValues
  cases sameState
  exact ⟨keeps, resident, resultClosed⟩

/-- Every successful row graph retains resident rebuilt edges with closed ordered children. -/
theorem rows_verified [DecidableEq (EdgeKey Symbol Guard)]
    {entries : List (Int × Needed)} {edges results : List (EdgeValue Symbol Guard)}
    {before after : State Symbol Guard} (trace : RequireRows entries edges before results after)
    (ready : Ready before) (resident : Edges before edges) (closed : ClosedEdges edges) :
    Keeps before after ∧ Edges after results ∧ ClosedEdges results := by
  have callbacks : SourceEqualityRequiredListsComplete.ChildComplete (Symbol := Symbol) (Guard := Guard) entries := by
    intro key needed member value current currentReady inputAvailable inputClosed
    exact SourceEqualityRequiredComplete.complete needed value current currentReady inputAvailable inputClosed
  obtain ⟨actual, final, completed, keeps, outputResident, resultClosed⟩ :=
    SourceEqualityRequiredListsComplete.rows_complete entries callbacks edges before ready resident closed
  obtain ⟨sameRows, sameState⟩ := stable_unique (rows_stable completed) (rows_stable trace)
  cases sameRows
  cases sameState
  exact ⟨keeps, outputResident, resultClosed⟩

end MicroCFTA.SourceEqualityRequiredListFacts
