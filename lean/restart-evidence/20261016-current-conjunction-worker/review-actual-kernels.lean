import MicroCFTA.SourceCurrentAllocatedConjunctionWorkerActual

namespace MicroCFTA.CurrentConjunctionWorkerActualIndependentReview
open Cache Language InternedConstructorTemplates InternedProbeProvenance
open SourceCurrentAllocatedNativeEffects (physical)
open SourceCurrentAllocatedQueryMemo (advancePhysical)
open SourceCurrentAllocatedPartialInvariant (Context Post)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Memo" => SourceCurrentEmptinessMemo.Memo
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Inventory" => SourceCurrentAllocatedNativeInventoryState.Inventory
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq (Value Symbol Guard)]

/-- Incomparable successful bounds identify the operation state and all native tables. -/
theorem success_bounds_identify_complete_state
    {p h P H budget : Nat} {query : Value Symbol Guard} {before after later : Checked width}
    {memo saved current : Memo} {answer other : Bool}
    (one : SourceCurrentAllocatedConjunctionWorker.call p h budget query before memo = .done answer after saved)
    (two : SourceCurrentAllocatedConjunctionWorker.call P H budget query before memo = .done other later current) :
    answer = other ∧ after.operations = later.operations ∧
      after.native.nodes = later.native.nodes ∧ after.native.edges = later.native.edges ∧
      after.native.machine.domains = later.native.machine.domains ∧ saved = current := by
  obtain ⟨rfl, rfl, rfl⟩ := SourceCurrentAllocatedConjunctionWorkerActual.call_done_unique one two
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Initial caller facts construct literal execution and the same inventory at the returned state. -/
theorem initial_context_constructs_full_checked_success
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (budget : Nat) (before : Caller width) (query : Value Symbol Guard) (memos : Memos)
    (initial : Context formulas solver inventory before memos)
    (available : Available before.checked.native.machine.heap query) :
    ∃ answer after saved final p h,
      (∀ P H, p ≤ P → h ≤ H → SourceCurrentAllocatedConjunctionWorker.call P H budget query before.checked before.fourth =
        .done answer after saved) ∧
      Context formulas solver inventory (SourceCurrentAllocatedPartialState.advance before after saved before.merge) final ∧
      SourceCurrentEmptinessMemo.Extends before.fourth saved ∧
      Available after.native.machine.heap query ∧
      after.native.nodes = before.checked.native.nodes ∧ after.native.edges = before.checked.native.edges ∧
      after.native.machine.domains = before.checked.native.machine.domains ∧
      final.query = memos.query ∧
      (answer = true → ∀ ambient term, ¬InternedGuardedLanguage.meaning
        (SourceEqualityPCSGuard.holds formulas solver) ambient query term) := by
  obtain ⟨answer, after, saved, final, p, h, stable, post, sound, known, _, unchanged⟩ :=
    SourceCurrentAllocatedConjunctionWorkerActual.finite formulas solver budget initial available
  obtain ⟨nodes, edges, domains⟩ := SourceCurrentAllocatedConjunctionWorker.call_tables (stable p h (Nat.le_refl _) (Nat.le_refl _))
  exact ⟨answer, after, saved, final, p, h, stable, post.context, post.fourthRetained,
    known, nodes, edges, domains, unchanged, sound.2⟩

/-- A supplied literal success constructs its own exact current call and global read receipt. -/
theorem successful_true_has_own_reads_and_initial_fourth_extension
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (p h budget : Nat) (before : Caller width) (after : Checked width)
    (query : Value Symbol Guard) (saved : Memo) (memos : Memos)
    (initial : Context formulas solver inventory before memos)
    (available : Available before.checked.native.machine.heap query)
    (done : SourceCurrentAllocatedConjunctionWorker.call p h budget query before.checked before.fourth = .done true after saved) :
    ∃ reached final, after = advancePhysical before.checked reached ∧
      ∃ actual : SourceCurrentConjunctionMemo.Call budget before.fourth query (physical before.checked) true reached saved,
        SourceCurrentConjunctionGlobalMemos.CallReads actual memos final ∧
        SourceCurrentEmptinessMemo.Correct formulas solver after.native.machine.heap saved ∧
        SourceCurrentEmptinessMemo.Extends before.fourth saved ∧
        EndpointMemoGateTrace.Valid after.native.machine.heap final ∧
        (∀ ambient term, ¬InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver) ambient query term) := by
  obtain ⟨reached, final, returned, actual, reads, post, sound, _, _, _⟩ :=
    SourceCurrentAllocatedConjunctionWorkerActual.verified formulas solver initial available done
  exact ⟨reached, final, returned, actual, reads, post.context.correct, post.fourthRetained,
    post.context.globals, sound.2 rfl⟩

/-- A second literal call uses the context derived from the first literal call. -/
theorem two_literal_calls_from_one_initial_context
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (inventory : Inventory) (firstBudget secondBudget : Nat) (before : Caller width)
    (query : Value Symbol Guard) (memos : Memos)
    (initial : Context formulas solver inventory before memos)
    (available : Available before.checked.native.machine.heap query) :
    ∃ answer middle firstMemo firstGlobals p h other after saved final P H,
      SourceCurrentAllocatedConjunctionWorker.call p h firstBudget query before.checked before.fourth = .done answer middle firstMemo ∧
      SourceCurrentAllocatedConjunctionWorker.call P H secondBudget query middle firstMemo = .done other after saved ∧
      Post formulas solver inventory before (SourceCurrentAllocatedPartialState.advance before after saved before.merge) final ∧
      SourceCurrentEmptinessMemo.Extends before.fourth saved ∧
      EndpointMemoGateTrace.Valid middle.native.machine.heap firstGlobals ∧
      EndpointMemoGateTrace.Valid after.native.machine.heap final := by
  obtain ⟨answer, middle, firstMemo, firstGlobals, p, h, first, firstPost, _, firstKnown, _, _⟩ :=
    SourceCurrentAllocatedConjunctionWorkerActual.finite formulas solver firstBudget initial available
  obtain ⟨other, after, saved, final, P, H, second, secondPost, _, _, _, _⟩ :=
    SourceCurrentAllocatedConjunctionWorkerActual.finite formulas solver secondBudget firstPost.context firstKnown
  have joined := firstPost.trans secondPost
  exact ⟨answer, middle, firstMemo, firstGlobals, p, h, other, after, saved, final, P, H,
    first p h (Nat.le_refl _) (Nat.le_refl _), second P H (Nat.le_refl _) (Nat.le_refl _),
    joined, joined.fourthRetained, firstPost.context.globals, joined.context.globals⟩

end MicroCFTA.CurrentConjunctionWorkerActualIndependentReview
