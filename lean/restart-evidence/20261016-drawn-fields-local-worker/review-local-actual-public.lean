import MicroCFTA.SourceCurrentAllocatedLocalWorkerActual
#print axioms MicroCFTA.SourceCurrentAllocatedLocalWorkerActual.sound
#check MicroCFTA.SourceCurrentAllocatedLocalWorkerActual.sound
#print axioms MicroCFTA.SourceCurrentAllocatedLocalWorkerActual.verified
#check MicroCFTA.SourceCurrentAllocatedLocalWorkerActual.verified
#print axioms MicroCFTA.SourceCurrentAllocatedLocalWorkerActual.finite
#check MicroCFTA.SourceCurrentAllocatedLocalWorkerActual.finite

namespace MicroCFTA.LocalActualIndependentProbes
open Language EqualityNormalize InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open SourceCurrentAllocatedNativeInventoryState (Inventory At)
open SourceCurrentAllocatedPartialInvariant (Context Post)
open SourceCurrentAllocatedLocalReduction (Receipt Ranges)
open SourceCurrentAllocatedLocalWorker (reduce)
open SourceCurrentAllocatedLocalWorkerActual
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Allocated" => SourceEqualityConjoinAllocation.Constraint FullSyntax.Formula
local notation "EqValue" => SourceEqualityConstraintAllocation.Value
local notation "Memo" => SourceCurrentMemoMergeGraph.Memo Symbol Guard
local notation "Fourth" => SourceCurrentEmptinessMemo.Memo
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "advance" => SourceCurrentAllocatedPartialState.advance
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq (Value Symbol Guard)]

-- Two supplied literal successes derive the second Context and At at the first computed inventory.
example (F : SourceGuards.Formulas FullSyntax.Formula) (S : SourceGuards.Entailment FullSyntax.Formula)
    {inventory : Inventory} {original firstOriginal : Guard}
    {g s r e p h m c n G T R E P H M C N budget laterBudget : Nat}
    {loaded nextLoaded : Allocated} {inherited nextInherited : EqValue}
    {values middleValues results : List (Value Symbol Guard)}
    {before : Caller width} {middle after : Checked width} {firstFourth savedFourth : Fourth}
    {firstMemo saved : Memo} {memos : Memos}
    (initial : Context F S inventory before memos)
    (cached : SourceEqualityGuardReadback.Cached original.equalities)
    (found : SourceEqualityConstraintFieldLookup.load original before.checked.operations.constraints = .ok (some loaded))
    (inheritedReady : SourceEqualityConstraintAllocation.Ready before.checked.operations.constraints inherited)
    (available : Values before.checked.native.machine.heap values)
    (ranges : Ranges budget loaded inherited values before.checked before.fourth before.merge)
    (one : reduce g s r e p h m c n budget loaded inherited values before.checked before.fourth before.merge =
      .done middleValues middle firstFourth firstMemo)
    (nextCached : SourceEqualityGuardReadback.Cached firstOriginal.equalities)
    (nextFound : SourceEqualityConstraintFieldLookup.load firstOriginal middle.operations.constraints = .ok (some nextLoaded))
    (nextInheritedReady : SourceEqualityConstraintAllocation.Ready middle.operations.constraints nextInherited)
    (nextRanges : Ranges laterBudget nextLoaded nextInherited middleValues middle firstFourth firstMemo)
    (two : reduce G T R E P H M C N laterBudget nextLoaded nextInherited middleValues middle firstFourth firstMemo =
      .done results after savedFourth saved) :
    ∃ next final latest returned,
      At F S next middle ∧ At F S latest after ∧
      Post F S next before (advance before middle firstFourth firstMemo) final ∧
      Post F S latest before (advance (advance before middle firstFourth firstMemo) after savedFourth saved) returned := by
  obtain ⟨next, final, first, reads, receipt, post⟩ := verified F S initial cached found inheritedReady available ranges one
  obtain ⟨latest, returned, second, nextReads, nextReceipt, nextPost⟩ :=
    verified F S post.context nextCached nextFound nextInheritedReady receipt.available nextRanges two
  exact ⟨next, final, latest, returned, post.context.admitted, nextPost.context.admitted, post, post.trans nextPost⟩

-- Initial facts and a literal success derive length, returned residency, and probes at that same result.
example (F : SourceGuards.Formulas FullSyntax.Formula) (S : SourceGuards.Entailment FullSyntax.Formula)
    {inventory : Inventory} {original : Guard} {g s r e p h m c n budget : Nat}
    {loaded : Allocated} {inherited : EqValue} {values results : List (Value Symbol Guard)}
    {before : Caller width} {after : Checked width} {savedFourth : Fourth} {saved : Memo} {memos : Memos}
    (initial : Context F S inventory before memos)
    (cached : SourceEqualityGuardReadback.Cached original.equalities)
    (found : SourceEqualityConstraintFieldLookup.load original before.checked.operations.constraints = .ok (some loaded))
    (inheritedReady : SourceEqualityConstraintAllocation.Ready before.checked.operations.constraints inherited)
    (available : Values before.checked.native.machine.heap values)
    (ranges : Ranges budget loaded inherited values before.checked before.fourth before.merge)
    (done : reduce g s r e p h m c n budget loaded inherited values before.checked before.fourth before.merge =
      .done results after savedFourth saved) :
    results.length = values.length ∧ Values after.native.machine.heap results ∧
      InternedFreshOrdinaryProbeHeap.Heap after.native.machine.heap := by
  obtain ⟨next, final, actual, reads, receipt, post⟩ := verified F S initial cached found inheritedReady available ranges done
  exact ⟨receipt.length, receipt.available, post.context.probes⟩

-- An unchanged precheck derives its continuation range plan and a full zero-bound caller return.
example (F : SourceGuards.Formulas FullSyntax.Formula) (S : SourceGuards.Entailment FullSyntax.Formula)
    {inventory : Inventory} {original : Guard} {budget : Nat} {loaded : Allocated} {inherited : EqValue}
    {values : List (Value Symbol Guard)} {before : Caller width} {memos : Memos}
    (initial : Context F S inventory before memos)
    (cached : SourceEqualityGuardReadback.Cached original.equalities)
    (found : SourceEqualityConstraintFieldLookup.load original before.checked.operations.constraints = .ok (some loaded))
    (inheritedReady : SourceEqualityConstraintAllocation.Ready before.checked.operations.constraints inherited)
    (available : Values before.checked.native.machine.heap values)
    (unchanged : (SourceEqualityPartialPrecheckAllocation.run loaded.stored loaded.guard inherited before.checked.operations).1 =
      .ok .unchanged) :
    ∃ next final, Post F S next before
      (advance before (SourceCurrentAllocatedPrecheck.state before.checked loaded inherited) before.fourth before.merge) final := by
  have ranges : Ranges budget loaded inherited values before.checked before.fourth before.merge := by
    intro records live
    rw [unchanged] at live
    cases live
  have done := SourceCurrentAllocatedLocalWorker.reduce_unchanged 0 0 0 0 0 0 0 0 0 budget
    loaded inherited values before.checked before.fourth before.merge unchanged
  obtain ⟨next, final, actual, reads, receipt, post⟩ := verified F S initial cached found inheritedReady available ranges done
  exact ⟨next, final, post⟩
end MicroCFTA.LocalActualIndependentProbes
