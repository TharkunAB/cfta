import MicroCFTA.SourceCurrentAllocatedReaderNumeric

/-!
# Exact exhausted collector prefixes

An exhausted collector consumes every supplied successor and leaves a
nonempty pending list. Its consumed path retains the exact returned fault
heap. Initial physical resources bound this path and its final resources.
Pending and unresolved results have separate branches. This module makes
no claim about the initial Mu unfold in nodeEdges.
-/
namespace MicroCFTA.SourceCurrentAllocatedReaderExhausted
open Cache InternedConstructorTemplates InternedProbeProvenance
open InternedRecordCoherence (Covered)
open InternedNestedProvenance (Values)
open MergedColdReaderClosedInputs (ClosedValues)
open SourceRecursiveIntersectionSemanticHeap (SemanticHeap)
open SourceCurrentAllocatedReaderControl (Config Good Fits)
open SourceCurrentAllocatedReaderConsumed (Path)
open MergedFreshOrdinaryExposure (collect)
open MergedSourceExposure (Result)
variable {Symbol Guard : Type}
variable [DecidableEq (EdgeKey Symbol Guard)]

/-- Exhaustion exposes the exact consumed path and the remaining literal work. -/
theorem extract (fuel : Nat) (heap : State Symbol Guard) (seen : List Nat)
    (pending : List (Value Symbol Guard)) (after : State Symbol Guard)
    (exhausted : collect fuel heap seen pending = .exhausted after) :
    ∃ final : Config Symbol Guard,
      Path fuel ⟨heap, seen, pending⟩ final ∧ final.heap = after ∧ final.pending ≠ [] := by
  induction fuel generalizing heap seen pending after with
  | zero =>
      cases pending with
      | nil => cases exhausted
      | cons value rest =>
          cases exhausted
          exact ⟨_, .refl _, rfl, by simp⟩
  | succ fuel ih =>
      cases pending with
      | nil => cases exhausted
      | cons value rest =>
          cases value with
          | empty =>
              obtain ⟨final, actual, same, remaining⟩ := ih heap seen rest after exhausted
              exact ⟨final, .step .empty actual, same, remaining⟩
          | reference => cases exhausted
          | node entry own depth free =>
              cases next : collect fuel heap seen rest with
              | done rows final | unresolved name final | pending key final =>
                  simp only [collect, next, Result.prepend] at exhausted
                  cases exhausted
              | exhausted final =>
                  have same : final = after := by
                    simpa only [collect, next, Result.prepend, Result.exhausted.injEq] using exhausted
                  subst final
                  obtain ⟨last, actual, same, remaining⟩ := ih heap seen rest after next
                  exact ⟨last, .step .node actual, same, remaining⟩
          | union entry members depth free =>
              by_cases visited : entry.identity ∈ seen
              · have tail : collect fuel heap seen rest = .exhausted after := by
                  simpa only [collect, ite_eq_left visited] using exhausted
                obtain ⟨final, actual, same, remaining⟩ := ih heap seen rest after tail
                exact ⟨final, .step (.union_seen visited) actual, same, remaining⟩
              · have tail : collect fuel heap (entry.identity :: seen) (members ++ rest) = .exhausted after := by
                  simpa only [collect, ite_eq_right visited] using exhausted
                obtain ⟨final, actual, same, remaining⟩ :=
                  ih heap (entry.identity :: seen) (members ++ rest) after tail
                exact ⟨final, .step (.union_fresh visited) actual, same, remaining⟩
          | mu entry body depth ordinary =>
              by_cases visited : entry.identity ∈ seen
              · have tail : collect fuel heap seen rest = .exhausted after := by
                  simpa only [collect, ite_eq_left visited] using exhausted
                obtain ⟨final, actual, same, remaining⟩ := ih heap seen rest after tail
                exact ⟨final, .step (.mu_seen visited) actual, same, remaining⟩
              · cases unfolded : InternedFreshOrdinaryStoredSubstitution.unfold (.mu entry body depth ordinary) heap with
                | pending key middle =>
                    simp only [collect, ite_eq_right visited, unfolded] at exhausted
                    cases exhausted
                | done value middle =>
                    have tail : collect fuel middle (entry.identity :: seen) (value :: rest) = .exhausted after := by
                      simpa only [collect, ite_eq_right visited, unfolded] using exhausted
                    obtain ⟨final, actual, same, remaining⟩ :=
                      ih middle (entry.identity :: seen) (value :: rest) after tail
                    exact ⟨final, .step (.mu_fresh visited unfolded) actual, same, remaining⟩

/-- Initial control bounds the exact exhausted endpoint and every consumed successor. -/
theorem control_bound (limit control fuel : Nat) (heap : State Symbol Guard) (seen : List Nat)
    (pending : List (Value Symbol Guard)) (after : State Symbol Guard)
    (good : Good limit (⟨heap, seen, pending⟩ : Config Symbol Guard))
    (fits : Fits control (⟨heap, seen, pending⟩ : Config Symbol Guard))
    (exhausted : collect fuel heap seen pending = .exhausted after) :
    ∃ final : Config Symbol Guard,
      Path fuel ⟨heap, seen, pending⟩ final ∧ final.heap = after ∧ final.pending ≠ [] ∧
      Good limit final ∧ Fits (SourceCurrentAllocatedReaderNumeric.fuel limit control) final ∧
      fuel ≤ SourceCurrentAllocatedReaderNumeric.fuel limit control := by
  obtain ⟨final, actual, same, remaining⟩ := extract fuel heap seen pending after exhausted
  obtain ⟨finalControl, afterGood, afterFits, path⟩ :=
    SourceCurrentAllocatedReaderNumeric.path_control actual control good fits
  have count := path.length_le SourceCurrentAllocatedReaderControl.g_mono SourceCurrentAllocatedReaderControl.g_strict
  have bounded := path.final_le SourceCurrentAllocatedReaderControl.g_mono SourceCurrentAllocatedReaderControl.g_strict
  exact ⟨final, actual, same, remaining, afterGood, afterFits.mono bounded, count⟩

/-- Initial counters and stored payload mass bound this literal failed collector run. -/
theorem initial_bound (fuel : Nat) (heap : State Symbol Guard) (seen : List Nat)
    (pending : List (Value Symbol Guard)) (after : State Symbol Guard) (mass : Nat)
    (semantic : SemanticHeap heap) (covered : Covered [] heap)
    (depth : InternedOpenDepthReadback.Heap heap) (available : Values heap pending) (closed : ClosedValues pending)
    (stored : InternedValueMassHeap.Stored mass heap)
    (exhausted : collect fuel heap seen pending = .exhausted after) :
    ∃ final : Config Symbol Guard,
      Path fuel ⟨heap, seen, pending⟩ final ∧ final.heap = after ∧ final.pending ≠ [] ∧
      Good mass final ∧
      Fits (SourceCurrentAllocatedReaderNumeric.collectFuel heap.nodes.next heap.edges.next mass pending.length) final ∧
      fuel ≤ SourceCurrentAllocatedReaderNumeric.collectFuel heap.nodes.next heap.edges.next mass pending.length := by
  exact control_bound mass
    (SourceCurrentAllocatedReaderNumeric.initialControl heap.nodes.next heap.edges.next mass pending.length)
    fuel heap seen pending after
    ⟨semantic, covered, depth, InternedValueMassBinderDepth.stored_bounded heap mass stored, available, closed⟩
    (SourceCurrentAllocatedReaderControl.initial_fits heap seen pending mass stored available) exhausted

end MicroCFTA.SourceCurrentAllocatedReaderExhausted
