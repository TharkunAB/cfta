import MicroCFTA.SourceCurrentAllocatedClassWorkerActual

#print axioms MicroCFTA.SourceCurrentAllocatedClassWorkerActual.finite
#print axioms MicroCFTA.SourceCurrentAllocatedClassWorkerActual.verified
#print axioms MicroCFTA.SourceCurrentAllocatedClassWorkerActual.caller
#print axioms MicroCFTA.SourceCurrentAllocatedClassWorkerActual.caller_finite
set_option pp.universes true in
#check @MicroCFTA.SourceCurrentAllocatedClassWorkerActual.finite
set_option pp.universes true in
#check @MicroCFTA.SourceCurrentAllocatedClassWorkerActual.verified
set_option pp.universes true in
#check @MicroCFTA.SourceCurrentAllocatedClassWorkerActual.caller
set_option pp.universes true in
#check @MicroCFTA.SourceCurrentAllocatedClassWorkerActual.caller_finite

namespace MicroCFTA.AllocatedClassWorkerReviewChecks
open Cache Language InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedPartialInvariant (Context Post)
open SourceCurrentAllocatedClassWorker
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Memo" => SourceCurrentMemoMergeGraph.Memo Symbol Guard
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Record" => SourceEqualityClassOrder.Record
local notation "Ranges" => SourceCurrentAllocatedClassPass.Ranges
local notation "Domain" => SourceEqualityProjectionPathDomain.ForestClosed
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat}

-- Two actual classes construct executable bounds and preserve all warm caller families.
example (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) {inventory : Inventory}
    {before : Caller width} {memos : Memos} (first second : Record) (values : List (Value Symbol Guard))
    (initial : Context formulas solver inventory before memos)
    (ranges : Ranges [first, second] values before.checked before.merge)
    (coherent : ∀ record ∈ [first, second], SourceEqualityClassOrder.Coherent record)
    (active : ∀ record ∈ [first, second], EqualityNormalize.Nontrivial record.paths)
    (available : Values before.checked.native.machine.heap values)
    (domains : ∀ record ∈ [first, second], ∀ path ∈ record.paths, Domain (path.map Int.ofNat) values)
    (ambient : InternedGuardedLanguage.Env Symbol) (symbol : Symbol) (terms : List (Term Symbol))
    (firstSat : EqualityNormalize.ClassSat (.node symbol terms) first.paths)
    (secondSat : EqualityNormalize.ClassSat (.node symbol terms) second.paths) :
    ∃ e p h m s n results after saved next final,
      pass e p h m s n [first, second] values before.checked before.merge = .done results after saved ∧
      Post formulas solver next before (SourceCurrentAllocatedPartialState.advance before after before.fourth saved) final ∧
      (SourceCurrentAllocatedPartialState.advance before after before.fourth saved).nodeResults = before.nodeResults ∧
      (SourceCurrentAllocatedPartialState.advance before after before.fourth saved).edgeResults = before.edgeResults ∧
      SourceCurrentEmptinessMemo.Correct formulas solver after.native.machine.heap before.fourth ∧
      (All₂ (InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver) ambient) results terms ↔
        All₂ (InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver) ambient) values terms) := by
  obtain ⟨results, after, saved, next, final, stable, post, _, language⟩ :=
    SourceCurrentAllocatedClassWorkerActual.caller_finite formulas solver initial ranges coherent active available domains
  obtain ⟨e, p, h, m, s, n, done⟩ := stable
  refine ⟨e, p, h, m, s, n, results, after, saved, next, final,
    done e p h m s n (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _),
    post, rfl, rfl, post.context.correct, (language ambient symbol terms).2 ?_⟩
  intro record member
  rcases List.mem_cons.mp member with rfl | member
  · exact firstSat
  · have same : record = second := by simpa only [List.mem_cons, List.not_mem_nil, or_false] using member
    exact same ▸ secondSat

-- A failed tail preserves its complete reached local state and skips the head and propagation.
example (e p h m s n : Nat) (head tail : Record) (values : List (Value Symbol Guard))
    (before : Checked width) (memo : Memo) (fault : SourceCurrentAllocatedSharedEditWorker.Fault width)
    (shared : SourceCurrentAllocatedSharedTargetState.State width)
    (failed : SourceCurrentAllocatedSharedEditWorker.editList
      (SourceCurrentAllocatedSharedEditWorker.edit tail values e p h m s n)
      (SourceCurrentAllocatedClassEditPlan.compiled tail) values
      (SourceCurrentAllocatedSharedTargetState.initial before memo) = .failed fault shared) :
    fold e p h m s n [head, tail] values before memo = .failed fault shared ∧
      pass e p h m s n [head, tail] values before memo = .failed fault shared := by
  have actual := runClass_failed e p h m s n tail values before memo fault shared failed
  have folded : fold e p h m s n [head, tail] values before memo = .failed fault shared := by
    simp only [fold, Outcome.bind, actual]
  exact ⟨folded, by simp only [pass, folded, Outcome.bind]⟩

-- No classes still propagates Empty through the complete forest without any cache or bound use.
example (value : Value Symbol Guard) (before : Checked width) (memo : Memo) :
    pass 0 0 0 0 0 0 [] [.empty, value] before memo = .done [.empty, .empty] before memo := by
  simp only [pass_nil, EqualityLeafProjectionRuntimeEmpty.propagate, List.any_cons, Value.referenceOf,
    beq_self_eq_true, Bool.true_or, ite_true, EqualityLeafProjectionRuntimeEmpty.erase, List.map_cons, List.map_nil]

end MicroCFTA.AllocatedClassWorkerReviewChecks
