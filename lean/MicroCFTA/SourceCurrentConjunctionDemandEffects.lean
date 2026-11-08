import MicroCFTA.SourceCurrentConjunctionDemandAdmission
import MicroCFTA.SourceCurrentConjunctionTuplePullTotalEffects
import MicroCFTA.SourceCurrentConjunctionRowsWarmEffects
import MicroCFTA.SourceCurrentConjunctionRowsProbes

/-!
# Physical effects of demand admission

Every sampled outcome retains current readiness and old records.
A fitting positive sample supplies the resident tuples for requirement work.
Sampling and requirement failures retain their actual returned states.
Clean probe heaps remain clean on all outcomes.
-/
namespace MicroCFTA.SourceCurrentConjunctionDemandEffects
open InternedConstructorTemplates
open InternedNestedProvenance (Values)
open SourceCurrentConjunctionRowsWorker (Physical Outcome)
open SourceCurrentConjunctionRowsAllocation (Ready Effects)
variable {Symbol Formula : Type}
local notation "Guard" => SourceSymbolicIndex.Constraint Formula
local notation "Node" => Value Symbol Guard
local notation "ProbeHeap" => InternedFreshOrdinaryProbeHeap.Heap
private noncomputable abbrev classicalKeys (Symbol Formula : Type) :
    DecidableEq (EdgeKey Symbol (SourceSymbolicIndex.Constraint Formula)) :=
  fun a b => @InternedConstructorTemplates.instDecidableEqEdgeKey Symbol
    (SourceSymbolicIndex.Constraint Formula)
    (fun x y => Classical.propDecidable (x = y))
    (fun x y => Classical.propDecidable (x = y)) a b

variable [DecidableEq Symbol]
  [keyEq : DecidableEq (EdgeKey Symbol (SourceSymbolicIndex.Constraint Formula))]

/-- All demand and requirement outcomes preserve readiness and physical effects. -/
theorem run_effects (p h budget : Nat) (nodes : List Node) (before : Physical Symbol Formula)
    (ready : Ready before) (available : Values before.heap nodes) :
    Effects before (SourceCurrentConjunctionDemandAdmission.run p h budget nodes before).state := by
  have keys : keyEq = classicalKeys Symbol Formula := Subsingleton.elim _ _
  subst keyEq
  letI := classicalKeys Symbol Formula
  have first := SourceCurrentConjunctionTuplePullTotalEffects.sample_effects h budget nodes before ready available
  cases actual : SourceCurrentConjunctionTuplePullTotal.sample h budget nodes before with
  | failed fault middle =>
      simpa only [SourceCurrentConjunctionDemandAdmission.run, actual, Outcome.bind, Outcome.state] using first.1
  | done sampled middle =>
      have kept : Effects before middle := by simpa only [actual, Outcome.state] using first.1
      have resident := first.2 sampled middle actual
      cases sampled with
      | overflow tuples cursor => simpa only [SourceCurrentConjunctionDemandAdmission.run, actual, Outcome.bind, Outcome.state] using kept
      | fit tuples =>
          cases tuples with
          | nil => simpa only [SourceCurrentConjunctionDemandAdmission.run, actual, Outcome.bind, Outcome.state] using kept
          | cons head tail =>
              have later := SourceCurrentConjunctionRowsWarmEffects.tuples_effects p h (head :: tail)
                middle kept.ready resident
              cases processed : SourceCurrentConjunctionRowsWorker.tuples p h (head :: tail) middle <;>
                rw [processed] at later <;>
                simpa only [SourceCurrentConjunctionDemandAdmission.run, actual, Outcome.bind, processed, Outcome.state]
                  using kept.trans later

/-- Actual demand and requirement work retain clean probes on every outcome. -/
theorem run_probes (p h budget : Nat) (nodes : List Node) (before : Physical Symbol Formula)
    (ready : Ready before) (probes : ProbeHeap before.heap) (available : Values before.heap nodes) :
    ProbeHeap (SourceCurrentConjunctionDemandAdmission.run p h budget nodes before).state.heap := by
  have keys : keyEq = classicalKeys Symbol Formula := Subsingleton.elim _ _
  subst keyEq
  letI := classicalKeys Symbol Formula
  have first := SourceCurrentConjunctionTuplePullTotalEffects.sample_effects h budget nodes before ready available
  have clean := SourceCurrentConjunctionTuplePullTotalEffects.sample_probes h budget nodes before ready probes available
  cases actual : SourceCurrentConjunctionTuplePullTotal.sample h budget nodes before with
  | failed fault middle =>
      simpa only [SourceCurrentConjunctionDemandAdmission.run, actual, Outcome.bind, Outcome.state] using clean
  | done sampled middle =>
      have kept : Effects before middle := by simpa only [actual, Outcome.state] using first.1
      have middleClean : ProbeHeap middle.heap := by simpa only [actual, Outcome.state] using clean
      have resident := first.2 sampled middle actual
      cases sampled with
      | overflow tuples cursor => simpa only [SourceCurrentConjunctionDemandAdmission.run, actual, Outcome.bind, Outcome.state] using middleClean
      | fit tuples =>
          cases tuples with
          | nil => simpa only [SourceCurrentConjunctionDemandAdmission.run, actual, Outcome.bind, Outcome.state] using middleClean
          | cons head tail =>
              have later := SourceCurrentConjunctionRowsProbes.tuples_heap p h (head :: tail) middle
                kept.ready middleClean resident
              cases processed : SourceCurrentConjunctionRowsWorker.tuples p h (head :: tail) middle <;>
                rw [processed] at later <;>
                simpa only [SourceCurrentConjunctionDemandAdmission.run, actual, Outcome.bind, processed, Outcome.state] using later

end MicroCFTA.SourceCurrentConjunctionDemandEffects
