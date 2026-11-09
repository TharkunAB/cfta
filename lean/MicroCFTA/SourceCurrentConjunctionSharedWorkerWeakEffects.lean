import MicroCFTA.SourceCurrentConjunctionSharedWorkerEffects
import MicroCFTA.SourceCurrentConjunctionSharedWorklistWeakEffects

/-!
# Original weak heap effects at the actual shared call boundary

Semantic validity, coverage and a closed resident query supply every weak
heap effect. No equality readiness or cost invariant is an input. Pure table
work and memo publication retain the exact exploration snapshot. These laws
cover faults but do not certify Boolean answers from the weaker premises.
-/
namespace MicroCFTA.SourceCurrentConjunctionSharedWorkerWeakEffects
open Cache
open InternedConstructorTemplates (Value EdgeKey Grows grows_refl)
open InternedRecordCoherence (Covered)
open InternedProbeProvenance (Available)
open SourceRecursiveIntersectionSemanticHeap (SemanticHeap)
local notation "Symbol" => SourcePruningTemplates.Symbol
variable {Formula : Type}
local notation "Guard" => SourceSymbolicIndex.Constraint Formula
local notation "Node" => Value Symbol Guard
local notation "Physical" => SourceCurrentConjunctionRowsWorker.Physical Symbol Formula
variable [DecidableEq Symbol]
  [DecidableEq (EdgeKey Symbol (SourceSymbolicIndex.Constraint Formula))]
  [DecidableEq (Value Symbol (SourceSymbolicIndex.Constraint Formula))]

/-- A closed source decision retains the original weak effects on every outcome. -/
theorem decision_effects (p h budget : Nat) (query : Node) (before : Physical)
    (semantic : SemanticHeap before.heap) (covered : Covered [] before.heap)
    (available : Available before.heap query) (closed : query.free = []) :
    let after := (SourceCurrentConjunctionSharedWorker.decision p h budget query before).state.storage.requirements.physical
    SemanticHeap after.heap ∧ Covered [] after.heap ∧ Grows before.heap after.heap ∧
      Extends before.heap.nodes.issued after.heap.nodes.issued := by
  have classified : SourceCurrentConjunctionWorklist.closed query = true := by
    simp only [SourceCurrentConjunctionWorklist.closed, closed, List.isEmpty_nil]
  simpa only [SourceCurrentConjunctionSharedWorkerEffects.decision_state, classified, ite_true] using
    SourceCurrentConjunctionSharedWorklistWeakEffects.explore_effects
      p h budget query before semantic covered available

end MicroCFTA.SourceCurrentConjunctionSharedWorkerWeakEffects

namespace MicroCFTA.SourceCurrentConjunctionSharedWorkerWeakEffects
open Cache
open InternedConstructorTemplates (Value EdgeKey Grows grows_refl)
open InternedRecordCoherence (Covered)
open InternedProbeProvenance (Available)
open SourceRecursiveIntersectionSemanticHeap (SemanticHeap)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "Physical" => SourceCurrentConjunctionRowsWorker.Physical Symbol FullSyntax.Formula
local notation "Memo" => SourceCurrentEmptinessMemo.Memo
variable [DecidableEq Symbol]
  [DecidableEq (EdgeKey Symbol (SourceSymbolicIndex.Constraint FullSyntax.Formula))]
  [DecidableEq (Value Symbol (SourceSymbolicIndex.Constraint FullSyntax.Formula))]

/-- Actual hits and all miss outcomes preserve weak effects without readiness assumptions. -/
theorem call_effects (p h budget : Nat) (memo : Memo) (query : Node) (before : Physical)
    (semantic : SemanticHeap before.heap) (covered : Covered [] before.heap)
    (available : Available before.heap query) (closed : query.free = []) :
    let after := (SourceCurrentConjunctionSharedWorker.call p h budget memo query before).state.storage.requirements.physical
    SemanticHeap after.heap ∧ Covered [] after.heap ∧ Grows before.heap after.heap ∧
      Extends before.heap.nodes.issued after.heap.nodes.issued := by
  cases hit : memo query.referenceOf with
  | some entry =>
      simpa only [SourceCurrentConjunctionSharedWorkerEffects.call_state, hit,
        SourceCurrentConjunctionSharedWorklistStep.initial, SourceCurrentConjunctionRequirementRows.initial,
        SourceCurrentConjunctionRequirementCells.initial] using
        (show SemanticHeap before.heap ∧ Covered [] before.heap ∧ Grows before.heap before.heap ∧
          Extends before.heap.nodes.issued before.heap.nodes.issued from
          ⟨semantic, covered, InternedConstructorTemplates.grows_refl _, Cache.extends_refl _⟩)
  | none =>
      simpa only [SourceCurrentConjunctionSharedWorkerEffects.call_state, hit] using
        decision_effects p h budget query before semantic covered available closed

end MicroCFTA.SourceCurrentConjunctionSharedWorkerWeakEffects
