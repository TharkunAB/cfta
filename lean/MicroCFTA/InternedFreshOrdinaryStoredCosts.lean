import MicroCFTA.InternedFreshOrdinaryCosts
import MicroCFTA.InternedFreshOrdinaryUnfoldCompletion

/-!
# Exact cost observations through actual repaired stored execution

Preparation uses the original stored records and actual replacement inputs.
The source cost theorem gives the exact returned occurrence membership.
General decoded completion supplies finite execution and all returned caches.
No rank decrease is claimed by this prepared-plan equality alone.
-/
namespace MicroCFTA.InternedFreshOrdinaryStoredSubstitution
open Cache InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedNestedConstruction (Outcome)
open InternedStoredSubstitution (Environment Replacements leaves input encode inputs_available)
open InternedFreshOrdinaryContext
open InternedFreshOrdinaryCostExecutionFacts (Agrees Checked)
open InternedBinderProtocol (Reference)

/-- The complete cost list of the original prepared plan under its actual replacement inputs. -/
def preparedCosts (body : Value Symbol Guard) (environment : Environment Symbol Guard) : List (Reference × Nat) :=
  InternedOccurrenceCostSemantics.evaluate (encode (leaves body) [] body)
    (((leaves body).map (input environment)).map InternedRecordDepthShape.shape)
    (((leaves body).map (input environment)).map InternedFreeOccurrenceRank.costs)

/-- Actual repaired stored execution retains the cost heap and observes its exact prepared cost list. -/
theorem execute_costs [DecidableEq (EdgeKey Symbol Guard)] (body : Value Symbol Guard)
    (environment : Environment Symbol Guard) (state : State Symbol Guard) (context : Context state captures)
    (cached : InternedFreshOrdinaryDepthHeap.Heap state) (heap : InternedFreshOrdinaryCostHeap.Heap state)
    (available : Available state body) (replacements : Replacements state environment) :
    Checked (execute body environment state) (fun value => Agrees value (preparedCosts body environment)) := by
  have inputs := inputs_available body environment state available replacements
  exact InternedFreshOrdinaryCosts.build_costs _ _ state
    ⟨context.normal, inputs, context.profiles, context.freeNames⟩ cached heap

/-- Every repaired unfolding retains weighted records in its exact complete or pending cache. -/
theorem unfold_cost_heap [DecidableEq (EdgeKey Symbol Guard)] (value : Value Symbol Guard)
    (state : State Symbol Guard) (context : Context state captures)
    (cached : InternedFreshOrdinaryDepthHeap.Heap state) (heap : InternedFreshOrdinaryCostHeap.Heap state)
    (available : Available state value) : InternedFreshOrdinaryCostHeap.Heap (unfold value state).state := by
  cases value with
  | empty | reference | node | union => exact heap
  | mu entry body depth ordinary =>
      have replacements : Replacements state (fun name => if name = .interned entry.identity then some (.mu entry body depth ordinary) else none) := by
        intro name replacement found
        dsimp only at found
        split at found
        · cases found; exact available
        · contradiction
      exact (execute_costs body _ state context cached heap (available.children body (by simp [children])) replacements).heap

/-- Finite actual stored substitution returns exact prepared costs and every required cache invariant. -/
theorem execute_complete_costs [DecidableEq (EdgeKey Symbol Guard)] (body : Value Symbol Guard)
    (environment : Environment Symbol Guard) (state : State Symbol Guard) (context : Context state captures)
    (cached : InternedFreshOrdinaryDepthHeap.Heap state) (heap : InternedFreshOrdinaryCostHeap.Heap state)
    (covered : Covered [] state) (available : Available state body) (replacements : Replacements state environment) :
    ∃ value after, execute body environment state = .done value after ∧ Context after captures ∧
      InternedFreshOrdinaryDepthHeap.Heap after ∧ Covered [] after ∧ InternedFreshOrdinaryCostHeap.Heap after ∧
      Available after value ∧ Grows state after ∧ Extends state.nodes.issued after.nodes.issued ∧
      Agrees value (preparedCosts body environment) := by
  have checked := execute_costs body environment state context cached heap available replacements
  obtain ⟨value, after, done, afterContext, afterCached, afterCovered, afterAvailable, growth, history⟩ :=
    execute_complete_decoded body environment state context available replacements cached covered
  exact ⟨value, after, done, afterContext, afterCached, afterCovered,
    by simpa only [done, Outcome.state] using checked.heap,
    afterAvailable, growth, history, checked.result value after done⟩

/-- Every available repaired unfolding completes and retains the weighted heap for later calls. -/
theorem unfold_complete_costs [DecidableEq (EdgeKey Symbol Guard)] (value : Value Symbol Guard)
    (state : State Symbol Guard) (context : Context state captures)
    (cached : InternedFreshOrdinaryDepthHeap.Heap state) (heap : InternedFreshOrdinaryCostHeap.Heap state)
    (covered : Covered [] state) (available : Available state value) :
    ∃ result after, unfold value state = .done result after ∧ Context after captures ∧
      InternedFreshOrdinaryDepthHeap.Heap after ∧ Covered [] after ∧ InternedFreshOrdinaryCostHeap.Heap after ∧
      Available after result ∧ Grows state after ∧ Extends state.nodes.issued after.nodes.issued := by
  obtain ⟨result, after, done, afterContext, afterCached, afterCovered, afterAvailable, growth, history⟩ :=
    unfold_complete_decoded value state context available cached covered
  exact ⟨result, after, done, afterContext, afterCached, afterCovered,
    by simpa only [done, Outcome.state] using unfold_cost_heap value state context cached heap available,
    afterAvailable, growth, history⟩

end MicroCFTA.InternedFreshOrdinaryStoredSubstitution
