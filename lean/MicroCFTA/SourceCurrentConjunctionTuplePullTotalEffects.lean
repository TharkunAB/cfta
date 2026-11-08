import MicroCFTA.SourceCurrentConjunctionTuplePullTotal
import MicroCFTA.SourceCurrentConjunctionTuplePullDriveEffects

/-!
# Physical invariants of total tuple sampling

Initial readiness and available operands supply the actual sample effects.
The proof derives the finite observation from cursor termination. It does
not take a future read receipt or a transition allowance as a premise.
Every failed exposure retains its actual reached heap and equality state.
-/
namespace MicroCFTA.SourceCurrentConjunctionTuplePullTotalEffects
open InternedConstructorTemplates
open InternedNestedProvenance (Values)
open SourceCurrentConjunctionRowsWorker (Physical Outcome)
open SourceCurrentConjunctionRowsAllocation (Ready Effects)
open SourceCurrentConjunctionTuplePullTotal (sample observe)
open SourceCurrentConjunctionTuplePullDriveEffects (StatusInputs)
variable {Symbol Formula : Type}

variable [DecidableEq Symbol]
  [DecidableEq (EdgeKey Symbol (SourceSymbolicIndex.Constraint Formula))]

/-- Total sampling retains readiness and all returned tuple and cursor inputs. -/
theorem sample_effects (h budget : Nat)
    (nodes : List (Value Symbol (SourceSymbolicIndex.Constraint Formula)))
    (before : Physical Symbol Formula) (ready : Ready before)
    (available : Values before.heap nodes) :
    Effects before (sample h budget nodes before).state ∧
      ∀ result after, sample h budget nodes before = .done result after →
        StatusInputs after.heap result.toStatus := by
  obtain ⟨steps, eventual⟩ := SourceCurrentConjunctionTuplePullTotal.sample_observation h budget nodes before
  have actual := eventual 0
  simp only [Nat.add_zero] at actual
  have kept := SourceCurrentConjunctionTuplePullDriveEffects.sample_effects steps h budget nodes before ready available
  rw [actual, SourceCurrentConjunctionTuplePullTotal.observe_state] at kept
  refine ⟨kept.1, ?_⟩
  intro result after done
  exact kept.2 result.toStatus after (by simp only [done, observe])

/-- Total sampling retains clean probe heaps on successful and failed outcomes. -/
theorem sample_probes (h budget : Nat)
    (nodes : List (Value Symbol (SourceSymbolicIndex.Constraint Formula)))
    (before : Physical Symbol Formula) (ready : Ready before)
    (probes : InternedFreshOrdinaryProbeHeap.Heap before.heap)
    (available : Values before.heap nodes) :
    InternedFreshOrdinaryProbeHeap.Heap (sample h budget nodes before).state.heap := by
  obtain ⟨steps, eventual⟩ := SourceCurrentConjunctionTuplePullTotal.sample_observation h budget nodes before
  have actual := eventual 0
  simp only [Nat.add_zero] at actual
  have clean := SourceCurrentConjunctionTuplePullDriveEffects.sample_probes steps h budget nodes before
    ready probes available
  simpa only [actual, SourceCurrentConjunctionTuplePullTotal.observe_state] using clean

end MicroCFTA.SourceCurrentConjunctionTuplePullTotalEffects
