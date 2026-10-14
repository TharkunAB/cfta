import MicroCFTA.InternedFreshOrdinaryCostHeap
import MicroCFTA.InternedOccurrenceCostSemantics
import MicroCFTA.InternedRecordDepthExecution
import MicroCFTA.InternedBinderFreeProbeCosts
import MicroCFTA.InternedFreeOccurrenceNode

/-!
# Cost observations through actual repaired source effects

The observations compare occurrence membership, so canonical ordering and
duplicate removal do not change the property. Actual callback filtering
retains every external cost. The stored cost heap is threaded separately
from the existing semantic context and decoded depth heap.
-/
namespace MicroCFTA.InternedFreshOrdinaryCostExecutionFacts
open Cache InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedNestedConstruction (Syntax Outcome work)
open InternedNestedProvenance (Values)
open InternedFreshOrdinaryConstruction InternedFreshOrdinaryFacts InternedFreshOrdinaryContext
open InternedFreeOccurrenceRank InternedFreeOccurrenceNormalization
open InternedFreshOrdinaryCostHeap
open InternedRecordDepthShape (shape)
open InternedBinderProtocol (Reference NodeKey)

/-- Actual records have exactly the interpreted free-reference occurrence costs. -/
def Agrees (value : Value Symbol Guard) (expected : List (Reference × Nat)) : Prop :=
  ∀ name count, (name, count) ∈ costs value ↔ (name, count) ∈ expected

/-- The source outcome retains the cost heap and every returned observation. -/
structure Checked (outcome : Outcome Symbol Guard Result) (property : Result → Prop) : Prop where
  heap : Heap outcome.state
  result : ∀ value after, outcome = .done value after → property value

/-- A pure returned value leaves the complete observation heap in place. -/
theorem done_checked (value : Result) (state : State Symbol Guard) (property : Result → Prop)
    (heap : Heap state) (holds : property value) : Checked (.done value state) property := by
  refine ⟨heap, ?_⟩
  intro actual after same
  cases same
  exact holds

/-- A pending lookup retains earlier costs and returns no unchecked value. -/
theorem pending_checked (key : NodeKey) (state : State Symbol Guard) (property : Result → Prop)
    (heap : Heap state) : Checked (.pending key state) property := by
  refine ⟨heap, ?_⟩
  intro value after impossible
  cases impossible

/-- Actual sequential effects retain all earlier complete cost records. -/
theorem bind_checked (outcome : Outcome Symbol Guard First)
    (next : First → State Symbol Guard → Outcome Symbol Guard Result)
    (firstProperty : First → Prop) (property : Result → Prop)
    (checked : Checked outcome firstProperty)
    (later : ∀ value after, outcome = .done value after → Heap after → firstProperty value →
      Checked (next value after) property) : Checked (outcome.bind next) property := by
  cases outcome with
  | pending key state => exact pending_checked key state property checked.heap
  | done value state => exact later value state rfl checked.heap (checked.result value state rfl)

/-- The actual source callback derives each external cost from its symbolic captured part. -/
theorem callback_checked [DecidableEq (EdgeKey Symbol Guard)] (expression : Syntax Symbol Guard)
    (environment : List (Value Symbol Guard)) (argument : Reference) (state : State Symbol Guard)
    (context : Context state environment) (argumentAvailable : Available state (.reference argument))
    (checked : Checked (build expression (.reference argument :: environment) state)
      (fun value => Agrees value (InternedOccurrenceCostSemantics.evaluate expression
        ((.reference argument :: environment).map shape) ((.reference argument :: environment).map costs)))) :
    Checked (callback expression environment argument state)
      (fun value => ∀ name count, name ≠ argument →
        ((name, count) ∈ costs value ↔ (name, count) ∈ InternedOccurrenceCostSemantics.captured expression
          (environment.map shape) (environment.map costs))) := by
  have inputs := (context.local argument argumentAvailable).inputs
  have verified := build_verified expression _ state context.normal.facts inputs
  unfold callback
  apply bind_checked _ _ _ _ checked
  intro value after returned afterHeap same
  have afterContext : Context after (.reference argument :: environment) := by
    simpa only [returned, Outcome.state] using (context.local argument argumentAvailable).build expression
  apply done_checked
  · exact preserve after _ afterHeap (InternedStoredMuOrigins.filter_noNewMu argument value after)
  · intro name count different
    exact (InternedBinderFreeProbeCosts.filter_cost_iff argument name value after afterContext.normal.facts
      afterContext.normal.live (verified.result value after returned) different count).trans
      ((same name count).trans (by
        simpa only [List.map_cons, shape, costs] using InternedOccurrenceCostSemantics.evaluate_other expression
          (environment.map shape) (environment.map costs) argument name different count))

/-- A source node has exactly the costs of its surviving original edge list. -/
theorem makeNode_costs_surviving [DecidableEq (EdgeKey Symbol Guard)] (edges : List (EdgeValue Symbol Guard))
    (state : State Symbol Guard) (facts : InternedNestedFacts.Facts state)
    (resident : ∀ edge ∈ edges, InternedEdgeResidency.EdgeResident state edge) (item : Reference × Nat) :
    item ∈ costs (run (makeNode edges) state).1 ↔ item ∈ edgeCosts (surviving edges) := by
  rw [InternedFreeOccurrenceNode.makeNode_cost_iff edges state facts.coherent facts.linked resident, edge_member]
  constructor
  · rintro ⟨edge, member, live, child, included, present⟩
    exact ⟨edge, by simp [surviving, member, live], child, included, present⟩
  · rintro ⟨edge, member, child, included, present⟩
    have selected := List.mem_filter.mp member
    exact ⟨edge, selected.1, by simpa using selected.2, child, included, present⟩

/-- The surviving edge fold deletes exactly the occurrence list of an erased edge. -/
theorem surviving_cons_costs (edge : EdgeValue Symbol Guard) (rest : List (EdgeValue Symbol Guard)) :
    edgeCosts (surviving (edge :: rest)) =
      (if edge.children.any (fun child => child.referenceOf == .empty) then [] else manyCosts edge.children) ++
        edgeCosts (surviving rest) := by
  cases edge with
  | mk entry children =>
      cases empty : children.any (fun child => child.referenceOf == .empty) <;>
        simp [surviving, EdgeValue.children, empty, edgeCosts]

/-- Actual fresh completion has the complete cost list decoded from its probes. -/
theorem finish_agrees (smart : Bool) (entry : Interned NodeKey) (body depth ordinary : Value Symbol Guard)
    (state : State Symbol Guard) (coherent : Coherent state) (available : Available state body)
    (correct : Correct entry body depth ordinary) (decoded : InternedFreshOrdinaryDepthHeap.Correct entry body depth ordinary) :
    Agrees (InternedNestedConstruction.finish smart (.mu entry body depth ordinary)) (decodedCosts smart depth ordinary) := by
  intro name count
  exact (finish_costs smart entry body depth ordinary state coherent available correct decoded name count).trans
    (decoded_member smart depth ordinary name count).symm

/-- Actual complete canonical hits retain the same complete decoded cost list. -/
theorem hit_agrees (smart : Bool) (depth ordinary value : Value Symbol Guard) (state : State Symbol Guard)
    (facts : InternedNestedFacts.Facts state) (depthAvailable : Available state depth)
    (ordinaryAvailable : Available state ordinary) (heap : Heap state)
    (depthHeap : InternedFreshOrdinaryDepthHeap.Heap state)
    (present : state.nodeRecords (muKey depth ordinary) = some value) :
    Agrees (InternedNestedConstruction.finish smart value) (decodedCosts smart depth ordinary) := by
  intro name count
  exact (hit_costs smart depth ordinary value state facts depthAvailable ordinaryAvailable heap depthHeap present name count).trans
    (decoded_member smart depth ordinary name count).symm

end MicroCFTA.InternedFreshOrdinaryCostExecutionFacts
