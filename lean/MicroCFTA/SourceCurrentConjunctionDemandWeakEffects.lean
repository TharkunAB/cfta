import MicroCFTA.SourceCurrentConjunctionDemandAdmission
import MicroCFTA.SourceCurrentConjunctionTuplePullWeakEffects
import MicroCFTA.SourceCurrentConjunctionRowsWorkerEffects

set_option autoImplicit false
open scoped Classical

/-!
# Weak physical effects of demand admission

Actual sampling and tuple processing retain semantic heap facts, coverage,
constructor growth, and issued identities. Successful positive requirements
remain resident and closed. Equality validity and costs are not premises.
-/
namespace MicroCFTA.SourceCurrentConjunctionDemandWeakEffects
open Cache InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedNestedProvenance (Values)
open MergedColdReaderClosedInputs (ClosedValues)
open SourceRecursiveIntersectionSemanticHeap (SemanticHeap)
open SourceCurrentConjunctionRowsWorker (Physical Outcome)
variable {Formula : Type}
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Guard" => SourceSymbolicIndex.Constraint Formula
local notation "Node" => Value Symbol Guard

/-- All demand-admission outcomes retain the selected weak heap contract. -/
theorem admission_effects (p h budget : Nat) (nodes : List Node) (before : Physical Symbol Formula)
    (semantic : SemanticHeap before.heap) (covered : Covered [] before.heap)
    (available : Values before.heap nodes) (closed : ClosedValues nodes) :
    let actual := SourceCurrentConjunctionDemandAdmission.run p h budget nodes before
    SemanticHeap actual.state.heap ∧ Covered [] actual.state.heap ∧ Grows before.heap actual.state.heap ∧
      Extends before.heap.nodes.issued actual.state.heap.nodes.issued ∧
      match actual with
      | .done (.positive _ requirements) after =>
          ∀ row ∈ requirements, ∀ operands ∈ row, Values after.heap operands ∧ ClosedValues operands
      | _ => True := by
  have first := SourceCurrentConjunctionTuplePullWeakEffects.sample_effects
    h budget nodes before semantic covered available closed
  cases sampled : SourceCurrentConjunctionTuplePullTotal.sample h budget nodes before with
  | failed fault middle =>
      simp only [sampled, Outcome.state] at first
      simp only [SourceCurrentConjunctionDemandAdmission.run, sampled, Outcome.bind, Outcome.state]
      exact ⟨first.1, first.2.1, first.2.2.1, first.2.2.2.1, trivial⟩
  | done result middle =>
      have semanticMiddle : SemanticHeap middle.heap := by simpa only [sampled, Outcome.state] using first.1
      have coveredMiddle : Covered [] middle.heap := by simpa only [sampled, Outcome.state] using first.2.1
      have growth : Grows before.heap middle.heap := by simpa only [sampled, Outcome.state] using first.2.2.1
      have history : Extends before.heap.nodes.issued middle.heap.nodes.issued := by
        simpa only [sampled, Outcome.state] using first.2.2.2.1
      have loaded := first.2.2.2.2 result middle sampled
      cases result with
      | overflow tuples cursor =>
          simp only [SourceCurrentConjunctionDemandAdmission.run, sampled, Outcome.bind, Outcome.state]
          exact ⟨semanticMiddle, coveredMiddle, growth, history, trivial⟩
      | fit tuples =>
          cases tuples with
          | nil =>
              simp only [SourceCurrentConjunctionDemandAdmission.run, sampled, Outcome.bind, Outcome.state]
              exact ⟨semanticMiddle, coveredMiddle, growth, history, trivial⟩
          | cons head tail =>
              have later := SourceCurrentConjunctionRowsWorkerEffects.tuples_effects p h (head :: tail)
                middle semanticMiddle coveredMiddle loaded.1 loaded.2
              cases processed : SourceCurrentConjunctionRowsWorker.tuples p h (head :: tail) middle <;>
                simp only [processed, Outcome.state] at later <;>
                simp only [SourceCurrentConjunctionDemandAdmission.run, sampled, Outcome.bind, processed, Outcome.state]
              · exact ⟨later.1, later.2.1, grows_trans growth later.2.2.1,
                  extends_trans history later.2.2.2.1, later.2.2.2.2⟩
              · exact ⟨later.1, later.2.1, grows_trans growth later.2.2.1,
                  extends_trans history later.2.2.2.1, trivial⟩

end MicroCFTA.SourceCurrentConjunctionDemandWeakEffects
