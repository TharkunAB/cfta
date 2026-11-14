import MicroCFTA.SourcePruningEnumerationSelectedValue
import MicroCFTA.MergedFreshOrdinaryColdReplay

/-!
# Replay one successful native value preparation

The actual completed value and heap stay exact at larger native bounds.
This lemma does not replay entry, child dispatch, scans, or emitted outputs.
-/
namespace MicroCFTA.SourcePruningEnumerationSelectedValue
open InternedConstructorTemplates
variable {Symbol Guard : Type}
variable [DecidableEq (EdgeKey Symbol Guard)]

/-- A successful native preparation retains its exact value and heap at every larger bound. -/
theorem run_done_moreFuel
    (fuel extra : Nat) (value result : Value Symbol Guard) (before after : State Symbol Guard)
    (observed : run fuel value before = .done result after) :
    run (fuel + extra) value before = .done result after := by
  cases value with
  | empty | reference | node | mu => simpa only [run] using observed
  | union entry members depth free =>
      cases exposed : MergedFreshOrdinaryExposure.nodeEdges fuel (.union entry members depth free) before with
      | done rows middle =>
          have finished : MergedSourceExposure.Finished
              (MergedFreshOrdinaryExposure.nodeEdges fuel (.union entry members depth free) before) := by
            rw [exposed]
            trivial
          have stable := MergedFreshOrdinaryColdReplay.nodeEdges_stable fuel extra
            (.union entry members depth free) before finished
          simpa only [run, stable] using observed
      | unresolved | pending | exhausted => simp [run, exposed] at observed

end MicroCFTA.SourcePruningEnumerationSelectedValue
