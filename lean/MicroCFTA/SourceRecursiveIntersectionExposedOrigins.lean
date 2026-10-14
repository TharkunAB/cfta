import MicroCFTA.SourceRecursiveIntersectionKernelFacts
import MicroCFTA.MergedFreshOrdinaryExposureLanguage

/-!
# Actual repaired row reads retain the recursive caller machine

A completed closed read extends the physical heap and issued history.
The source domain cache stays unchanged. The resulting caller machine is
valid and has the semantic heap and exact complete epsilon-origin rows.
-/
namespace MicroCFTA.SourceRecursiveIntersectionKernel
open Cache InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open SourceRecursiveIntersectionSemanticHeap (SemanticHeap)
open MergedFreshOrdinaryGraph (Origin)

/-- A completed repaired row read gives a valid later caller machine and exact full row origins. -/
theorem exposed_origins [DecidableEq (EdgeKey Symbol Guard)] (fuel : Nat)
    (before : Machine Symbol Guard) (valid : Valid before) (semantic : SemanticHeap before.heap)
    (covered : Covered [] before.heap) (value : Value Symbol Guard) (available : Available before.heap value)
    (closed : value.free = []) (edges : List (EdgeValue Symbol Guard)) (after : State Symbol Guard)
    (done : MergedFreshOrdinaryExposure.nodeEdges fuel value before.heap = .done edges after) :
    let view : Machine Symbol Guard := {before with heap := after}
    Valid view ∧ Extension before view ∧ SemanticHeap view.heap ∧
      ∀ edge, edge ∈ edges ↔ Origin view.heap [value] edge := by
  have checked := MergedFreshOrdinaryColdEffects.nodeEdges_verified fuel value before.heap semantic covered available closed
  have afterSemantic : SemanticHeap after := by simpa only [done, MergedSourceExposure.Result.state] using checked.semantic
  have growth : Grows before.heap after := by simpa only [done, MergedSourceExposure.Result.state] using checked.growth
  have history : Extends before.heap.nodes.issued after.nodes.issued := by
    simpa only [done, MergedSourceExposure.Result.state] using checked.history
  exact ⟨⟨afterSemantic.1.normal.facts, valid.2⟩, ⟨growth, history, extends_refl _⟩, afterSemantic,
    (MergedFreshOrdinaryExposureLanguage.actual_exact fuel value before.heap semantic covered available closed edges after done).1⟩

end MicroCFTA.SourceRecursiveIntersectionKernel
