import MicroCFTA.SourceCurrentAllocatedSeededWorkerActual

namespace MicroCFTA.SeededCallerIndependentReview
open Cache Language InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open SourceEqualityRequiredCache SourceEqualityRequiredSemanticCache
open SourceCurrentAllocatedPartialInvariant (Context Post)
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentSecondaryProjectionScoped (PathSupport)
open SourceCurrentAllocatedSeededQuery (SeededRanges)
open SourceCurrentAllocatedSeededWorker (seeded)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Memos" => EndpointMemoGateTrace.Memos
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]

/-- The second literal query consumes the new result and inventory derived by the first. -/
theorem consecutive_literal_queries_derive_second_context
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (unconstrained : Value Symbol Guard → Bool) (anchor : InternedConstructorTemplates.State Symbol Guard)
    (anchorSemantic : SemanticReady anchor) (anchorReady : InternedFreshOrdinaryMemoGateTrace.Ready anchor)
    (inventory : Inventory) (before : Caller width) (memos : Memos)
    (values : List (Value Symbol Guard)) (paths : List (List Int))
    (initial : Context formulas solver inventory before memos)
    (available : Values before.checked.native.machine.heap values)
    (growth : Grows anchor before.checked.native.machine.heap)
    (supported : ∀ path ∈ paths, PathSupport unconstrained anchor path values)
    (proper : ∀ path ∈ paths, path ≠ []) (ranges : SeededRanges values paths before.checked) :
    ∃ first middle firstInventory firstGlobals result after next final p h n P H N,
      seeded p h n values paths before.checked = .done first middle ∧
      Context formulas solver firstInventory
        (SourceCurrentAllocatedPartialState.advance before middle before.fourth before.merge) firstGlobals ∧
      seeded P H N [first] [[0]] middle = .done result after ∧
      Post formulas solver next before
        (SourceCurrentAllocatedPartialState.advance before after before.fourth before.merge) final ∧
      Available after.native.machine.heap result ∧ result.free = [] ∧
      SourceCurrentAllocatedNativeInventoryState.At formulas solver next after ∧
      SourceCurrentEmptinessMemo.Correct formulas solver after.native.machine.heap before.fourth := by
  obtain ⟨first, middle, firstInventory, firstGlobals, stable, firstGraph, firstReads, firstPost,
    firstAvailable, firstClosed, _, _, _⟩ :=
    SourceCurrentAllocatedSeededWorkerActual.finite formulas solver unconstrained anchor anchorSemantic anchorReady
      values paths initial available growth supported proper ranges
  have nextKnown : Values middle.native.machine.heap [first] := by
    intro value member
    have same : value = first := by simpa only [List.mem_singleton] using member
    simpa only [same] using firstAvailable
  have nextGrowth := grows_trans growth firstPost.effects.keeps.growth
  have nextSupport : ∀ path ∈ ([[0]] : List (List Int)), PathSupport unconstrained anchor path [first] := by
    intro path member
    have same : path = [0] := by simpa only [List.mem_singleton] using member
    subst path
    refine ⟨[0], rfl, ?_⟩
    intro value found
    simp only [List.getElem?_cons_zero] at found
    cases found
    exact Or.inl firstClosed
  have nextProper : ∀ path ∈ ([[0]] : List (List Int)), path ≠ [] := by simp
  have nextRanges : SeededRanges [first] [[0]] middle := .one
  obtain ⟨result, after, next, final, nextStable, secondGraph, secondReads, secondPost,
    known, closed, _, _, _⟩ :=
    SourceCurrentAllocatedSeededWorkerActual.finite formulas solver unconstrained anchor anchorSemantic anchorReady
      [first] [[0]] firstPost.context nextKnown nextGrowth nextSupport nextProper nextRanges
  obtain ⟨p, h, n, done⟩ := stable
  obtain ⟨P, H, N, nextDone⟩ := nextStable
  have joined := firstPost.trans secondPost
  exact ⟨first, middle, firstInventory, firstGlobals, result, after, next, final, p, h, n, P, H, N,
    done p h n (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _), firstPost.context,
    nextDone P H N (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _), joined, known, closed,
    joined.context.admitted, joined.context.correct⟩

/-- A supplied literal return derives inclusion and independent state invariants for that same result. -/
theorem supplied_success_has_own_inclusion_and_full_context
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (unconstrained : Value Symbol Guard → Bool) (anchor : InternedConstructorTemplates.State Symbol Guard)
    (anchorSemantic : SemanticReady anchor) (anchorReady : InternedFreshOrdinaryMemoGateTrace.Ready anchor)
    (inventory : Inventory) (before : Caller width) (memos : Memos)
    (values : List (Value Symbol Guard)) (paths : List (List Int)) (result : Value Symbol Guard) (after : Checked width)
    (initial : Context formulas solver inventory before memos)
    (available : Values before.checked.native.machine.heap values)
    (growth : Grows anchor before.checked.native.machine.heap)
    (supported : ∀ path ∈ paths, PathSupport unconstrained anchor path values)
    (proper : ∀ path ∈ paths, path ≠ []) (ranges : SeededRanges values paths before.checked)
    (done : seeded p h n values paths before.checked = .done result after) (nonempty : paths ≠ []) :
    ∃ next final, ∃ actual : SourceCurrentAllocatedSeededQuery.Seeded values paths before.checked result after,
      SourceCurrentAllocatedSeededMemos.SeededReads actual memos final ∧
      Context formulas solver next (SourceCurrentAllocatedPartialState.advance before after before.fourth before.merge) final ∧
      SourceCurrentAllocatedSeededLanguage.Includes formulas solver values paths result ∧
      Available after.native.machine.heap result ∧ result.free = [] ∧
      SourceCurrentEmptinessMemo.Correct formulas solver after.native.machine.heap before.fourth ∧
      InternedFreshOrdinaryProbeHeap.Heap after.native.machine.heap := by
  obtain ⟨next, final, actual, reads, post, known, closed, included, _, _⟩ :=
    SourceCurrentAllocatedSeededWorkerActual.verified formulas solver unconstrained anchor anchorSemantic anchorReady
      initial available growth supported proper ranges done
  exact ⟨next, final, actual, reads, post.context, included nonempty, known, closed,
    post.context.correct, post.context.probes⟩

end MicroCFTA.SeededCallerIndependentReview
