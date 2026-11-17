import MicroCFTA.SourceSynthesisCurrentRootEmptyCheckGate
import MicroCFTA.SourceEndpointMemoCorrect
import MicroCFTA.SourcePruningEnumerationSharedEnabledEmpty

namespace MicroCFTA.SourceSynthesisCurrentRootEmptyCheckGate
open Cache InternedConstructorTemplates InternedProbeProvenance
open SourceSynthesisTypeSyntax (Library Query)
open SourceSynthesisFirstOrderConstruction (Expression)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "ordinarySymbols" => SourceSynthesisUniverseCallerBoundary.ordinarySymbols
set_option autoImplicit false

/- Note [The actual enabled source check skips]
The retained source heap makes the descendant predicate false.
The current valid memos compute that same false answer.
The enabled check retains the queried state and fourth memo exactly.
Its descendant and predicate memos retain their actual updated entries.
This skip result gives no finite inhabitance claim.
-/

theorem source_retained_available_shared_empty_check_skipped
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Node]
    {width : Nat}
    (lib : Library) (query : Query) (signed : Int) (whole : Expression)
    (accepted : SourceSynthesisCurrentConstruction.firstOrderRaw lib query signed = .ok whole)
    (rootValue : Node) (sourceHeap : InternedConstructorTemplates.State Symbol Guard)
    (built : InternedFreshOrdinaryConstruction.build (ordinarySymbols whole) [] empty =
      .done rootValue sourceHeap)
    (queried : SourceEqualityNativeDemand.State width)
    (coherent : InternedRecordCoherence.Coherent queried.native.machine.heap)
    (pastInventory : InternedShallowHeap.NoNewMu sourceHeap queried.native.machine.heap)
    (value : Node) (available : Available queried.native.machine.heap value)
    (queries : SourceEndpointMemo.Memos)
    (validQueries : SourceEndpointMemo.Valid queried.native.machine.heap queries)
    (fourth : SourceCurrentEmptinessMemo.Memo) (p h : Nat) :
    let saved := (SourceEndpointMemo.run value queries).2
    SourceEndpointMemo.run value queries = (false, saved) ∧
      SourcePruningEnumerationSharedEnabledEmpty.check p h value queried fourth queries =
        (.skipped queried fourth, saved) ∧
      SourceEndpointMemo.Valid queried.native.machine.heap saved ∧
      SourceEndpointMemo.Keeps queries saved := by
  have sourceGate := source_retained_available_reaches_constrained_mu_false
    lib query signed whole accepted rootValue sourceHeap built
    queried.native.machine.heap pastInventory value available
  have observed := SourceEndpointMemoCorrect.run_checked value queried.native.machine.heap
    coherent available queries validQueries
  have falseAnswer : (SourceEndpointMemo.run value queries).1 = false :=
    observed.answer.trans sourceGate
  have actualMemo : SourceEndpointMemo.run value queries =
      (false, (SourceEndpointMemo.run value queries).2) :=
    Prod.ext falseAnswer rfl
  dsimp only
  exact ⟨actualMemo,
    SourcePruningEnumerationSharedEnabledEmpty.check_skipped p h value queried fourth
      queries (SourceEndpointMemo.run value queries).2 actualMemo,
    observed.valid, observed.keeps⟩

end MicroCFTA.SourceSynthesisCurrentRootEmptyCheckGate
