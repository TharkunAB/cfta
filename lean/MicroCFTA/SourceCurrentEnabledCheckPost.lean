import MicroCFTA.SourceCurrentConjunctionCallPost
import MicroCFTA.SourcePruningEnumerationEnabledEmpty

/-! The literal enabled check retains full Post at its actual saved query memo. -/
set_option autoImplicit false
namespace MicroCFTA.SourceCurrentEnabledCheckPost
open InternedConstructorTemplates InternedProbeProvenance
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedPartialInvariant (Context Post)
attribute [local instance] FormulaExecutable.formulaDecidableEq
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Memos" => EndpointMemoGateTrace.Memos
variable {width : Nat} [DecidableEq (EdgeKey Symbol Constraint)]

open scoped Classical in
/-- Every check outcome derives full Post with the same entry inventory and actual saved queries. -/
theorem check_post
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (inventory : Inventory)
    (p h : Nat) (query : Node) (before : Caller width) (memos : Memos)
    (context : Context formulas solver inventory before memos)
    (available : Available before.checked.native.machine.heap query) (closed : query.free = []) :
    let actual := SourcePruningEnumerationEnabledEmpty.check p h query before.checked before.fourth memos.query
    Post formulas solver inventory before
      (SourceCurrentAllocatedPartialState.advance before actual.1.state actual.1.memo before.merge)
      {memos with query := actual.2} := by
  letI : DecidableEq Node := fun a b => Classical.propDecidable (a = b)
  cases observed : SourceEndpointMemo.run query memos.query with
  | mk reached savedQueries =>
      have checked := SourceEndpointMemoCorrect.run_checked query before.checked.native.machine.heap
        context.ready.good.heap.semantic.1.normal.facts.coherent available memos.query context.globals.query
      have updated : Context formulas solver inventory before {memos with query := savedQueries} := by
        refine ⟨context.ready, context.admitted, context.sound, context.stored, context.covered,
          context.correct, ⟨context.globals.unfolding, ?_⟩, context.probes⟩
        simpa only [observed] using checked.valid
      cases reached with
      | false =>
          simpa [SourcePruningEnumerationEnabledEmpty.check, observed,
            SourceCurrentAllocatedPartialState.advance, SourceCurrentAllocatedConjunctionWorker.Outcome.state,
            SourceCurrentAllocatedConjunctionWorker.Outcome.memo] using Post.refl updated
      | true =>
          have called := SourceCurrentConjunctionCallPost.call_post p h 1000 query before
            {memos with query := savedQueries} updated available closed
          simpa [SourcePruningEnumerationEnabledEmpty.check, observed] using called

end MicroCFTA.SourceCurrentEnabledCheckPost
