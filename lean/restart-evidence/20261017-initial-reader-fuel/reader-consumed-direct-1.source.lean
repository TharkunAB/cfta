import MicroCFTA.SourceCurrentAllocatedReaderControl
import MicroCFTA.MergedFreshOrdinaryColdReplay

/-!
# Exact consumed steps of the repaired collector

A successful collector run records only the branches it executes. Its rows
retain their original order. The run reconstructs the same heap and rows at
its exact consumed fuel and at every larger fuel.
-/
namespace MicroCFTA.SourceCurrentAllocatedReaderConsumed
open Cache InternedConstructorTemplates
open MergedFreshOrdinaryExposure (collect)
open MergedSourceExposure (Result)
open SourceCurrentAllocatedReaderControl (Config Step)
variable {Symbol Guard : Type}

/-- An ordinary pending head emits its literal rows before the remaining rows. -/
def emitted (config : Config Symbol Guard) : List (EdgeValue Symbol Guard) :=
  match config.pending with
  | .node _ rows _ _ :: _ => rows
  | _ => []

/-- A path records the exact number of literal collector successors. -/
inductive Path [DecidableEq (EdgeKey Symbol Guard)] :
    Nat → Config Symbol Guard → Config Symbol Guard → Prop where
  /-- No successor changes the state. -/
  | refl (config : Config Symbol Guard) : Path 0 config config
  /-- One actual successor precedes the remaining path. -/
  | step (actual : Step before middle) (tail : Path count middle after) :
      Path (count + 1) before after

/-- A completed run records each emitted row prefix and ends with no pending work. -/
inductive Run [DecidableEq (EdgeKey Symbol Guard)] :
    Nat → Config Symbol Guard → List (EdgeValue Symbol Guard) → Config Symbol Guard → Prop where
  /-- An empty pending list succeeds without a successor. -/
  | nil (heap : State Symbol Guard) (seen : List Nat) :
      Run 0 ⟨heap, seen, []⟩ [] ⟨heap, seen, []⟩
  /-- An actual successor emits its rows before the remaining successful run. -/
  | step (actual : Step before middle) (tail : Run count middle rows after) :
      Run (count + 1) before (emitted before ++ rows) after

/-- Every completed run retains its exact underlying successor path. -/
theorem Run.path [DecidableEq (EdgeKey Symbol Guard)]
    {count : Nat} {before after : Config Symbol Guard} {rows : List (EdgeValue Symbol Guard)}
    (actual : Run count before rows after) : Path count before after := by
  induction actual with
  | nil heap seen => exact .refl _
  | step actual tail ih => exact .step actual ih

/-- A completed run has no pending values in its actual final state. -/
theorem Run.pending_empty [DecidableEq (EdgeKey Symbol Guard)]
    {count : Nat} {before after : Config Symbol Guard} {rows : List (EdgeValue Symbol Guard)}
    (actual : Run count before rows after) : after.pending = [] := by
  induction actual with
  | nil => rfl
  | step actual tail ih => exact ih

/-- Exact consumed fuel reconstructs the same ordered rows and complete final heap. -/
theorem Run.exact [DecidableEq (EdgeKey Symbol Guard)]
    {count : Nat} {before after : Config Symbol Guard} {rows : List (EdgeValue Symbol Guard)}
    (actual : Run count before rows after) :
    collect count before.heap before.seen before.pending = .done rows after.heap := by
  induction actual with
  | nil => rfl
  | step actual tail ih =>
      cases actual with
      | empty => simpa only [collect, emitted, List.nil_append] using ih
      | node => simp only [collect, emitted, ih, Result.prepend]
      | union_seen visited | mu_seen visited =>
          simpa only [collect, emitted, ite_eq_left visited, List.nil_append] using ih
      | union_fresh unvisited =>
          simpa only [collect, emitted, ite_eq_right unvisited, List.nil_append] using ih
      | mu_fresh unvisited unfolded =>
          simpa only [collect, emitted, ite_eq_right unvisited, unfolded, List.nil_append] using ih

/-- Every successful collector equation has a run with no padded fuel steps. -/
theorem extract [DecidableEq (EdgeKey Symbol Guard)]
    (fuel : Nat) (heap : State Symbol Guard) (seen : List Nat) (pending : List (Value Symbol Guard))
    (rows : List (EdgeValue Symbol Guard)) (after : State Symbol Guard)
    (done : collect fuel heap seen pending = .done rows after) :
    ∃ count finalSeen, count ≤ fuel ∧ Run count ⟨heap, seen, pending⟩ rows ⟨after, finalSeen, []⟩ := by
  induction fuel generalizing heap seen pending rows after with
  | zero =>
      cases pending with
      | nil => cases done; exact ⟨0, seen, Nat.le_refl _, .nil heap seen⟩
      | cons => cases done
  | succ fuel ih =>
      cases pending with
      | nil => cases done; exact ⟨0, seen, Nat.zero_le _, .nil heap seen⟩
      | cons value rest =>
          cases value with
          | empty =>
              obtain ⟨count, finalSeen, enough, actual⟩ := ih heap seen rest rows after done
              exact ⟨count + 1, finalSeen, Nat.succ_le_succ enough, .step .empty actual⟩
          | reference => cases done
          | node entry own depth free =>
              cases next : collect fuel heap seen rest with
              | unresolved | pending | exhausted =>
                  simp only [collect, next, Result.prepend] at done
                  cases done
              | done tail final =>
                  have equal : own ++ tail = rows ∧ final = after := by
                    simpa only [collect, next, Result.prepend, Result.done.injEq] using done
                  obtain ⟨count, finalSeen, enough, actual⟩ := ih heap seen rest tail final next
                  obtain ⟨rfl, rfl⟩ := equal
                  exact ⟨count + 1, finalSeen, Nat.succ_le_succ enough, .step .node actual⟩
          | union entry members depth free =>
              by_cases visited : entry.identity ∈ seen
              · have tail : collect fuel heap seen rest = .done rows after := by
                  simpa only [collect, ite_eq_left visited] using done
                obtain ⟨count, finalSeen, enough, actual⟩ := ih heap seen rest rows after tail
                exact ⟨count + 1, finalSeen, Nat.succ_le_succ enough, .step (.union_seen visited) actual⟩
              · have tail : collect fuel heap (entry.identity :: seen) (members ++ rest) = .done rows after := by
                  simpa only [collect, ite_eq_right visited] using done
                obtain ⟨count, finalSeen, enough, actual⟩ := ih heap (entry.identity :: seen) (members ++ rest) rows after tail
                exact ⟨count + 1, finalSeen, Nat.succ_le_succ enough, .step (.union_fresh visited) actual⟩
          | mu entry body depth ordinary =>
              by_cases visited : entry.identity ∈ seen
              · have tail : collect fuel heap seen rest = .done rows after := by
                  simpa only [collect, ite_eq_left visited] using done
                obtain ⟨count, finalSeen, enough, actual⟩ := ih heap seen rest rows after tail
                exact ⟨count + 1, finalSeen, Nat.succ_le_succ enough, .step (.mu_seen visited) actual⟩
              · cases unfolded : InternedFreshOrdinaryStoredSubstitution.unfold (.mu entry body depth ordinary) heap with
                | pending =>
                    simp only [collect, ite_eq_right visited, unfolded] at done
                    cases done
                | done value middle =>
                    have tail : collect fuel middle (entry.identity :: seen) (value :: rest) = .done rows after := by
                      simpa only [collect, ite_eq_right visited, unfolded] using done
                    obtain ⟨count, finalSeen, enough, actual⟩ := ih middle (entry.identity :: seen) (value :: rest) rows after tail
                    exact ⟨count + 1, finalSeen, Nat.succ_le_succ enough,
                      .step (.mu_fresh visited unfolded) actual⟩

/-- Any sufficient chosen fuel reconstructs this exact completed run. -/
theorem Run.stable [DecidableEq (EdgeKey Symbol Guard)]
    {count : Nat} {before after : Config Symbol Guard} {rows : List (EdgeValue Symbol Guard)}
    (actual : Run count before rows after) (fuel : Nat) (enough : count ≤ fuel) :
    collect fuel before.heap before.seen before.pending = .done rows after.heap := by
  have finished : MergedSourceExposure.Finished (collect count before.heap before.seen before.pending) := by
    rw [actual.exact]
    trivial
  have again := MergedFreshOrdinaryColdReplay.collect_stable count (fuel - count)
    before.heap before.seen before.pending finished
  have same : count + (fuel - count) = fuel := by omega
  rw [same] at again
  exact again.trans actual.exact

end MicroCFTA.SourceCurrentAllocatedReaderConsumed
