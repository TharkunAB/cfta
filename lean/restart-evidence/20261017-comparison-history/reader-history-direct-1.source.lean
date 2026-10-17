import MicroCFTA.SourceCurrentAllocatedUnfoldHistory
import MicroCFTA.SourceCurrentAllocatedReaderConsumed
import MicroCFTA.SourceMergedComparisonEffects

/-!
# Exact unfolding histories of actual repaired row reads

Collector graphs retain every successful Mu unfold in source order.
The direct Mu probe occurs before the original-root closure fallback.
These histories retain exact returned heaps and allocation-free events.
-/
namespace MicroCFTA.SourceCurrentAllocatedReaderHistory
open Cache InternedConstructorTemplates InternedProbeProvenance
open InternedNestedConstruction (Outcome)
open SourceCurrentAllocatedReaderControl (Config Good Step)
open SourceCurrentAllocatedReaderConsumed (Run)
open SourceCurrentAllocatedUnfoldHistory (Event History)
open SourceEqualityRequiredSemanticCache (SemanticReady)
open InternedMuDepthInventory (Bounded)
open MergedFreshOrdinaryExposure (collect nodeEdges)
variable {Symbol Guard : Type} [DecidableEq (EdgeKey Symbol Guard)]

/-- A consumed collector run records every actual unfold at its exact reached heap. -/
theorem Run.history {count : Nat} {before after : Config Symbol Guard}
    {rows : List (EdgeValue Symbol Guard)} (actual : Run count before rows after) :
    ∀ limit, Good limit before → History before.heap after.heap := by
  induction actual with
  | nil heap seen => intro _ _; exact .refl heap
  | @step before middle after count step tail ih =>
      intro limit good
      have later := ih limit (step.good good)
      cases step with
      | empty | node | union_seen | union_fresh | mu_seen => exact later
      | @mu_fresh heap middle seen entry body depth ordinary result rest unvisited unfolded =>
          exact .step (.unfold (.mu entry body depth ordinary) result
            (good.available _ List.mem_cons_self) (good.closed _ List.mem_cons_self) unfolded) later

/-- Any successful collector equation derives its literal heap history from initial physical facts. -/
theorem collect_history (limit fuel : Nat) (before : State Symbol Guard) (seen : List Nat)
    (pending : List (Value Symbol Guard)) (good : Good limit ⟨before, seen, pending⟩)
    (rows : List (EdgeValue Symbol Guard)) (after : State Symbol Guard)
    (done : collect fuel before seen pending = .done rows after) : History before after := by
  obtain ⟨count, finalSeen, _enough, actual⟩ := SourceCurrentAllocatedReaderConsumed.extract
    fuel before seen pending rows after done
  exact actual.history limit good

private theorem canonical_history (limit fuel : Nat) (before : State Symbol Guard)
    (pending : List (Value Symbol Guard)) (good : Good limit ⟨before, [], pending⟩)
    (rows : List (EdgeValue Symbol Guard)) (after : State Symbol Guard)
    (done : (collect fuel before [] pending).canonical = .done rows after) : History before after := by
  cases actual : collect fuel before [] pending with
  | done original final =>
      simp only [actual, MergedSourceExposure.Result.canonical] at done
      obtain ⟨_sameRows, rfl⟩ := MergedSourceExposure.Result.done.inj done
      exact collect_history limit fuel before [] pending good original final actual
  | unresolved | pending | exhausted =>
      simp only [actual, MergedSourceExposure.Result.canonical] at done
      cases done

/-- The actual row reader records its direct Mu probe before every original-root fallback. -/
theorem nodeEdges_history (limit fuel : Nat) (value : Value Symbol Guard)
    (before : State Symbol Guard) (semantic : SemanticReady before) (bounded : Bounded before limit)
    (available : Available before value) (closed : value.free = [])
    (rows : List (EdgeValue Symbol Guard)) (after : State Symbol Guard)
    (done : nodeEdges fuel value before = .done rows after) : History before after := by
  have good : Good limit (⟨before, [], [value]⟩ : Config Symbol Guard) :=
    ⟨semantic.ready.semantic, semantic.ready.covered, semantic.ready.depth, bounded,
      by intro original member; cases List.mem_singleton.mp member; exact available,
      by intro original member; cases List.mem_singleton.mp member; exact closed⟩
  cases value with
  | empty | reference | node =>
      have same : before = after := (MergedSourceExposure.Result.done.inj done).2
      subst after
      exact .refl before
  | union entry members depth free =>
      exact canonical_history limit fuel before _ good rows after done
  | mu entry body depth ordinary =>
      obtain ⟨result, middle, unfolded, _context, _cached, _covered, _output, growth, issued⟩ :=
        InternedFreshOrdinaryStoredSubstitution.unfold_complete_decoded (.mu entry body depth ordinary)
          before semantic.ready.semantic.1 available semantic.ready.semantic.2 semantic.ready.covered
      have step : SourceCurrentAllocatedReaderControl.Step (⟨before, [], [.mu entry body depth ordinary]⟩ : Config Symbol Guard)
          ⟨middle, [entry.identity], [result]⟩ := .mu_fresh (by simp) unfolded
      have reached := step.good good
      have fallback : Good limit (⟨middle, [], [.mu entry body depth ordinary]⟩ : Config Symbol Guard) :=
        ⟨reached.semantic, reached.covered, reached.depth, reached.bounded,
          by intro original member; cases List.mem_singleton.mp member; exact available.grows before middle growth issued,
          by intro original member; cases List.mem_singleton.mp member; exact closed⟩
      have event : Event before middle := .unfold (.mu entry body depth ordinary) result available closed unfolded
      cases result with
      | node resultEntry resultRows resultDepth resultFree =>
          simp only [nodeEdges, unfolded] at done
          obtain ⟨_sameRows, rfl⟩ := MergedSourceExposure.Result.done.inj done
          exact .step event (.refl middle)
      | empty | reference | union | mu =>
          simp only [nodeEdges, unfolded] at done
          exact .step event (canonical_history limit fuel middle _ fallback rows after done)

/-- Every successful comparison read retains the exact repaired unfolding history. -/
theorem read_history (limit fuel : Nat) (value : Value Symbol Guard)
    (before : State Symbol Guard) (semantic : SemanticReady before) (bounded : Bounded before limit)
    (available : Available before value) (closed : value.free = [])
    (rows : List (EdgeValue Symbol Guard)) (after : State Symbol Guard)
    (done : MergedFreshOrdinaryExposure.read fuel value before = .done rows after) : History before after := by
  cases actual : nodeEdges fuel value before with
  | done edges final =>
      simp only [MergedFreshOrdinaryExposure.read, actual] at done
      obtain ⟨rfl, rfl⟩ := MergedSourceComparison.Result.done.inj done
      exact nodeEdges_history limit fuel value before semantic bounded available closed edges final actual
  | pending | unresolved | exhausted =>
      simp only [MergedFreshOrdinaryExposure.read, actual] at done
      cases done

end MicroCFTA.SourceCurrentAllocatedReaderHistory
