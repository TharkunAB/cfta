import MicroCFTA.SourceCurrentAllocatedTargetWorkerActual

#print axioms MicroCFTA.SourceCurrentAllocatedTargetWorkerActual.verified
#print axioms MicroCFTA.SourceCurrentAllocatedTargetWorkerActual.finite
#print axioms MicroCFTA.SourceCurrentAllocatedTargetWorkerActual.caller
#print axioms MicroCFTA.SourceCurrentAllocatedTargetWorkerActual.caller_finite
set_option pp.universes true in
#check @MicroCFTA.SourceCurrentAllocatedTargetWorkerActual.verified
set_option pp.universes true in
#check @MicroCFTA.SourceCurrentAllocatedTargetWorkerActual.finite
set_option pp.universes true in
#check @MicroCFTA.SourceCurrentAllocatedTargetWorkerActual.caller
set_option pp.universes true in
#check @MicroCFTA.SourceCurrentAllocatedTargetWorkerActual.caller_finite

namespace MicroCFTA.AllocatedTargetWorkerActualChecks
open Cache InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open SourceCurrentAllocatedNativeInventoryState (Inventory At)
open SourceCurrentAllocatedPartialInvariant (Context Post)
open SourceCurrentAllocatedTargetWorker
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Ranges" => SourceCurrentAllocatedTargetGraph.TargetRanges
local notation "Domain" => SourceEqualityProjectionPathDomain.ForestClosed
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat}

-- Two target operands yield literal bounds and preserve both outer tables and the fourth memo.
example (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) {inventory : Inventory}
    {before : Caller width} {memos : Memos} (values : List (Value Symbol Guard))
    (first second : List Int) (firstNonroot : first ≠ []) (secondNonroot : second ≠ [])
    (initial : Context formulas solver inventory before memos)
    (available : Values before.checked.native.machine.heap values)
    (domains : ∀ path ∈ [first, second], Domain path values)
    (ranges : Ranges values [first, second] before.checked before.merge) :
    ∃ p h m s n result after saved next final,
      target p h m s n values [first, second] before.checked before.merge = .done result after saved ∧
      Post formulas solver next before (SourceCurrentAllocatedPartialState.advance before after before.fourth saved) final ∧
      (SourceCurrentAllocatedPartialState.advance before after before.fourth saved).nodeResults = before.nodeResults ∧
      (SourceCurrentAllocatedPartialState.advance before after before.fourth saved).edgeResults = before.edgeResults ∧
      SourceCurrentEmptinessMemo.Correct formulas solver after.native.machine.heap before.fourth ∧
      SourceCurrentAllocatedTargetComplete.Includes formulas solver values [first, second] result := by
  obtain ⟨result, after, saved, next, final, stable, post, _, _, includes⟩ :=
    SourceCurrentAllocatedTargetWorkerActual.caller_finite formulas solver values [first, second]
      initial available domains ranges
  obtain ⟨p, h, m, s, n, done⟩ := stable
  refine ⟨p, h, m, s, n, result, after, saved, next, final,
    done p h m s n (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _),
    post, rfl, rfl, post.context.correct, includes (by simp) ?_⟩
  intro path member
  rcases List.mem_cons.mp member with rfl | member
  · exact firstNonroot
  · have same : path = second := by simpa only [List.mem_cons, List.not_mem_nil, or_false] using member
    exact same ▸ secondNonroot

-- The empty target still has a literal zero-bound return and a reflexive caller history.
example (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) {inventory : Inventory}
    {before : Caller width} {memos : Memos} (values : List (Value Symbol Guard))
    (initial : Context formulas solver inventory before memos)
    (available : Values before.checked.native.machine.heap values) :
    target 0 0 0 0 0 values [] before.checked before.merge = .done .empty before.checked before.merge ∧
    ∃ next final, Post formulas solver next before before final ∧
      Available before.checked.native.machine.heap (.empty : Value Symbol Guard) := by
  have done : target 0 0 0 0 0 values [] before.checked before.merge =
      .done .empty before.checked before.merge := rfl
  obtain ⟨next, final, post, resident, _, _⟩ := SourceCurrentAllocatedTargetWorkerActual.caller
    formulas solver (p := 0) (h := 0) (m := 0) (s := 0) (n := 0) (paths := [])
      initial available (by intro path member; cases member) trivial done
  exact ⟨done, next, final, post, resident⟩

end MicroCFTA.AllocatedTargetWorkerActualChecks
