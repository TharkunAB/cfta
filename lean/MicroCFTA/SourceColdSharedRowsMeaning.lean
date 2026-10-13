import MicroCFTA.SourceColdSharedRowsExecution
import MicroCFTA.MergedSourceExposureCoverage
import MicroCFTA.MergedColdGraphTransport

/-!
# Row languages through actual cold traversal effects

Each first-written row has the language of its original physical root.
Later cache growth preserves that equation for the root and all ordered
edge children. The complete trace derives these equations in its final cache.
-/
namespace MicroCFTA.SourceColdSharedRows
open Cache InternedConstructorTemplates InternedProbeProvenance InternedNestedFacts
open InternedNestedProvenance InternedEdgeResidency
open MergedPhysicalWarmup MergedColdReaderClosedInputs Language
open SourcePreparedSharedRows (reference)

/-- A resident edge has the same complete guarded language after prepared cache growth. -/
theorem edge_stable [DecidableEq (EdgeKey Symbol Guard)] (before after : State Symbol Guard)
    (facts : Facts before) (laterFacts : Facts after) (prepared : Prepared before)
    (growth : Grows before after) (history : Extends before.nodes.issued after.nodes.issued)
    (meaning : Guard → Term Symbol → Bool) (edge : EdgeValue Symbol Guard) (resident : EdgeResident before edge)
    (term : Term Symbol) :
    MergedPhysicalUnion.EdgeAccepts before meaning edge term ↔ MergedPhysicalUnion.EdgeAccepts after meaning edge term := by
  unfold MergedPhysicalUnion.EdgeAccepts
  apply exists_congr
  intro terms
  apply and_congr_right
  intro shape
  apply and_congr _ Iff.rfl
  apply MergedColdGraphTransport.runs_congr
  intro child member subterm
  exact MergedColdGraphTransport.accepts_stable before after facts laterFacts prepared growth history meaning child
    (facts.cached.edges edge.entry.key edge resident child member) subterm

/-- Each stored row retains its available closed source root and exact guarded language. -/
def MeaningRows [DecidableEq (EdgeKey Symbol Guard)] (state : State Symbol Guard)
    (rows : Rows Symbol Guard) (meaning : Guard → Term Symbol → Bool) : Prop :=
  ∀ identity edges, rows identity = some edges → ∃ value,
    Available state value ∧ reference value = some identity ∧ value.free = [] ∧ Edges state edges ∧
      ∀ term, EpsilonUnion.Accepts (MergedPhysicalLanguage.graph state meaning) value term ↔
        ∃ edge ∈ edges, MergedPhysicalUnion.EdgeAccepts state meaning edge term

/-- Later physical growth retains every earlier row's exact original root language. -/
theorem MeaningRows.grows [DecidableEq (EdgeKey Symbol Guard)] (before after : State Symbol Guard)
    (rows : Rows Symbol Guard) (meaning : Guard → Term Symbol → Bool) (correct : MeaningRows before rows meaning)
    (facts : Facts before) (laterFacts : Facts after) (prepared : Prepared before)
    (growth : Grows before after) (history : Extends before.nodes.issued after.nodes.issued) :
    MeaningRows after rows meaning := by
  intro identity edges present
  obtain ⟨value, available, same, closed, resident, exactRows⟩ := correct identity edges present
  refine ⟨value, available.grows before after growth history, same, closed,
    fun edge member => edge_grows before after growth edge (resident edge member), ?_⟩
  intro term
  have root := MergedColdGraphTransport.accepts_stable before after facts laterFacts prepared growth history meaning value available term
  have children : (∃ edge ∈ edges, MergedPhysicalUnion.EdgeAccepts before meaning edge term) ↔
      ∃ edge ∈ edges, MergedPhysicalUnion.EdgeAccepts after meaning edge term := by
    apply exists_congr
    intro edge
    apply and_congr_right
    intro member
    exact edge_stable before after facts laterFacts prepared growth history meaning edge (resident edge member) term
  exact root.symm.trans ((exactRows term).trans children)

/-- Actual cold reads derive every final stored row's exact physical guarded language. -/
theorem Trace.meaning [DecidableEq (EdgeKey Symbol Guard)]
    {state final : State Symbol Guard} {seen result : Rows Symbol Guard} {pending : List (Value Symbol Guard)}
    (trace : Trace state seen pending result final) (facts : Facts state) (prepared : Prepared state)
    (inputs : Inputs state pending) (meaning : Guard → Term Symbol → Bool) (correct : MeaningRows state seen meaning) :
    MeaningRows final result meaning := by
  induction trace with
  | nil => exact correct
  | empty rest ih | known value identity edges same present rest ih =>
      exact ih facts prepared (fun value member => inputs value (List.mem_cons_of_mem _ member)) correct
  | @read seen state after pending result final value identity fuel edges same absent done rest ih =>
      have own := inputs value List.mem_cons_self
      have tail : Inputs state pending := fun value member => inputs value (List.mem_cons_of_mem _ member)
      have checked := MergedColdReaderFacts.nodeEdges_verified fuel value state facts prepared own.1
      have afterFacts : Facts after := by simpa only [done, MergedSourceExposure.Result.state] using checked.facts
      have growth : Grows state after := by simpa only [done, MergedSourceExposure.Result.state] using checked.growth
      have history : Extends state.nodes.issued after.nodes.issued := by simpa only [done, MergedSourceExposure.Result.state] using checked.history
      have unchanged : InternedShallowHeap.NoNewMu state after := by
        simpa only [done, MergedSourceExposure.Result.state] using checked.unchanged
      have earlier := correct.grows state after seen meaning facts afterFacts prepared growth history
      have inserted : MeaningRows after (Cache.put seen identity edges) meaning := by
        intro key values present
        by_cases equal : key = identity
        · subst key
          have sameEdges : edges = values := by simpa [Cache.put] using present
          subst values
          exact ⟨value, own.1.grows state after growth history, same, own.2, checked.edges edges after done,
            (MergedSourceExposureCoverage.actual_exact fuel value state facts prepared own.1 edges after done).2 meaning⟩
        · exact earlier key values (by simpa [Cache.put, equal] using present)
      exact ih afterFacts (prepared.preserve unchanged)
        (next_inputs fuel value state facts prepared own.1 own.2 edges after pending tail done) inserted

end MicroCFTA.SourceColdSharedRows
