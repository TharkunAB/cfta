import MicroCFTA.SourceCurrentAllocatedPartialActual

namespace MicroCFTA.MutualEffectsIndependent
open Cache Language InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
open InternedNestedProvenance (Values Edges)
open SourceCurrentAllocatedPartialState SourceCurrentAllocatedPartialGraph SourceCurrentAllocatedPartialSourceReads
open SourceCurrentAllocatedPartialInvariant (Context Post)
open SourceCurrentAllocatedPartialChecks
open SourceCurrentAllocatedNativeInventoryState (Inventory)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "EqReady" => SourceEqualityConstraintAllocation.Ready
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq (Value Symbol Guard)]
  {width budget : Nat}

 theorem same_root_exact_and_warm_invariants
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    {inventory : Inventory} {identity : Nat} {value result : Value Symbol Guard} {before after : Caller width}
    {actual : NodeCall budget ⟨.live identity [], value⟩ before result after} {memos final : Memos}
    (reads : NodeCallReads formulas solver actual memos final) (checks : Checks (nodeCallTrace actual))
    (initial : Context formulas solver inventory before memos)
    (inherited : EqReady before.checked.operations.constraints (.live identity []))
    (available : Available before.checked.native.machine.heap value) :
    ∃ next, Post formulas solver next before after final ∧
      Available after.checked.native.machine.heap result ∧
      InternedFreshOrdinaryProbeHeap.Heap after.checked.native.machine.heap ∧
      EndpointMemoGateTrace.Valid after.checked.native.machine.heap final ∧
      SourceCurrentEmptinessMemo.Correct formulas solver after.checked.native.machine.heap after.fourth ∧
      ∀ ambient term,
        InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver) ambient result term ↔
          InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver) ambient value term := by
  obtain ⟨next, post, resultResident, exactLanguage⟩ :=
    SourceCurrentAllocatedPartialActual.root_exact formulas solver reads checks initial inherited available
  exact ⟨next, post, resultResident, post.context.probes, post.context.globals, post.context.correct, exactLanguage⟩

 theorem indexed_walk_arity_and_law
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    {inventory : Inventory} {combined : SourceEqualityConstraintAllocation.Value} {index : Nat}
    {values results : List (Value Symbol Guard)} {before after : Caller width}
    {actual : Walk budget combined index values before results after} {memos final : Memos}
    (reads : WalkReads formulas solver actual memos final) (checks : Checks (walkTrace actual))
    (initial : Context formulas solver inventory before memos)
    (inherited : EqReady before.checked.operations.constraints combined)
    (available : Values before.checked.native.machine.heap values) :
    ∃ next, Post formulas solver next before after final ∧ Values after.checked.native.machine.heap results ∧
      results.length = values.length ∧ SourceCurrentAllocatedPartialWalkLanguage.WalkLaw formulas solver actual := by
  obtain ⟨next, post, available, law⟩ := SourceCurrentAllocatedPartialActual.walk formulas solver reads
    inventory checks initial inherited available
  exact ⟨next, post, available, actual.length, law⟩

 theorem ordered_rows_conditional_exact
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    {inventory : Inventory} {inherited : SourceEqualityConstraintAllocation.Value}
    {values results : List (EdgeValue Symbol Guard)} {before after : Caller width}
    {actual : Rows budget inherited values before results after} {memos final : Memos}
    (reads : RowsReads formulas solver actual memos final) (checks : Checks (rowsTrace actual))
    (initial : Context formulas solver inventory before memos)
    (known : EqReady before.checked.operations.constraints inherited)
    (resident : Edges before.checked.native.machine.heap values) :
    ∃ next, Post formulas solver next before after final ∧ Edges after.checked.native.machine.heap results ∧
      ∀ ambient term, SourceEqualityPrecheck.Sat term inherited.payload →
        (SourceCurrentAllocatedPartialForestLanguage.RowsMeaning formulas solver ambient results term ↔
          SourceCurrentAllocatedPartialForestLanguage.RowsMeaning formulas solver ambient values term) := by
  obtain ⟨next, post, available, law⟩ := SourceCurrentAllocatedPartialActual.rows formulas solver reads
    inventory checks initial known resident
  exact ⟨next, post, available, fun ambient term satisfied => law.exact formulas solver ambient term satisfied⟩

 theorem supplied_node_keeps_resident_mu_rebuild
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    {inventory : Inventory} {request : NodeRequest} {result : Value Symbol Guard} {before after : Caller width}
    {actual : NodeCall budget request before result after} {memos final : Memos}
    (reads : NodeCallReads formulas solver actual memos final) (checks : Checks (nodeCallTrace actual))
    (initial : Context formulas solver inventory before memos)
    (inherited : EqReady before.checked.operations.constraints request.inherited)
    (available : Available before.checked.native.machine.heap request.value) :
    ∃ next, Post formulas solver next before after final ∧
      ∀ entry body depth ordinary, Available after.checked.native.machine.heap (.mu entry body depth ordinary) →
        SourceEqualityMuReconstruction.rebuild entry body depth ordinary after.checked.native.machine.heap =
          .done (cleanup (.mu entry body depth ordinary)) after.checked.native.machine.heap := by
  obtain ⟨next, post, _, _⟩ := SourceCurrentAllocatedPartialActual.node_call formulas solver reads
    inventory checks initial inherited available
  exact ⟨next, post, fun entry body depth ordinary resident =>
    (SourceCurrentAllocatedMuRebuild.resident_rebuild after.checked post.context.ready post.context.probes
      entry body depth ordinary resident).1⟩

end MicroCFTA.MutualEffectsIndependent
