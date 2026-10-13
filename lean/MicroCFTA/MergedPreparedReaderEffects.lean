import MicroCFTA.MergedPhysicalMergeContext
import MicroCFTA.MergedColdReaderFacts

/-!
# Exact cache effects of prepared physical row reads

Finite warmup completes every stored Mu request. Later row reads use those
results. They retain the exact cache for every fuel value and every outcome.
-/
namespace MicroCFTA.MergedPreparedReaderEffects
open InternedConstructorTemplates InternedProbeProvenance InternedNestedFacts
open InternedNestedProvenance InternedNestedConstruction
open MergedPhysicalWarmup MergedPhysicalMergeContext MergedSourceExposure

/-- Prepending ordinary edges does not change the returned cache. -/
theorem prepend_state (edges : List (EdgeValue Symbol Guard)) (result : Result Symbol Guard) :
    (result.prepend edges).state = result.state := by cases result <;> rfl

/-- Canonical edge ordering does not change the returned cache. -/
theorem canonical_state (result : Result Symbol Guard) : result.canonical.state = result.state := by
  cases result <;> rfl

/-- Every prepared worklist read retains its exact input cache, including failures. -/
theorem collect_state [DecidableEq (EdgeKey Symbol Guard)] (fuel : Nat) (state : State Symbol Guard)
    (outputs : List (Value Symbol Guard)) (context : Context state outputs)
    (seen : List Nat) (pending : List (Value Symbol Guard)) (inputs : Values state pending) :
    (collect fuel state seen pending).state = state := by
  induction fuel generalizing seen pending with
  | zero => cases pending <;> rfl
  | succ fuel ih =>
      cases pending with
      | nil => rfl
      | cons value rest =>
          have available := inputs value List.mem_cons_self
          have tail : Values state rest := fun child member => inputs child (List.mem_cons_of_mem _ member)
          cases value with
          | empty => exact ih seen rest tail
          | reference => rfl
          | node entry edges depth free =>
              simpa only [collect, prepend_state] using ih seen rest tail
          | union entry members depth free =>
              by_cases visited : entry.identity ∈ seen
              · simpa only [collect, ite_eq_left visited] using ih seen rest tail
              · have next : Values state (members ++ rest) := by
                  intro child member
                  rcases List.mem_append.mp member with first | later
                  · exact available.children child first
                  · exact tail child later
                simpa only [collect, ite_eq_right visited] using ih (entry.identity :: seen) (members ++ rest) next
          | mu entry body depth ordinary =>
              by_cases visited : entry.identity ∈ seen
              · simpa only [collect, ite_eq_left visited] using ih seen rest tail
              · obtain ⟨result, member, done⟩ := context.ready entry body depth ordinary available
                have next : Values state (result :: rest) := by
                  intro child member'
                  rcases List.mem_cons.mp member' with same | later
                  · rw [same]; exact context.retained result member
                  · exact tail child later
                simpa only [collect, ite_eq_right visited, done] using ih (entry.identity :: seen) (result :: rest) next

/-- The direct Mu path and its fallback both retain the exact prepared cache. -/
theorem nodeEdges_state [DecidableEq (EdgeKey Symbol Guard)] (fuel : Nat) (value : Value Symbol Guard)
    (state : State Symbol Guard) (outputs : List (Value Symbol Guard)) (context : Context state outputs)
    (available : Available state value) :
    (MergedSourceExposure.nodeEdges fuel value state).state = state := by
  have fallback (root : Value Symbol Guard) (input : Available state root) :
      (collect fuel state [] [root]).canonical.state = state := by
    rw [canonical_state]
    exact collect_state fuel state outputs context [] [root] (by simpa [Values] using input)
  cases value with
  | empty | reference | node => rfl
  | union entry members depth free => exact fallback _ available
  | mu entry body depth ordinary =>
      obtain ⟨result, _, done⟩ := context.ready entry body depth ordinary available
      simp only [MergedSourceExposure.nodeEdges, done]
      cases result <;> try exact fallback _ available
      rfl

/-- A successful prepared row read returns the identical cache. -/
theorem done_state [DecidableEq (EdgeKey Symbol Guard)] (fuel : Nat) (value : Value Symbol Guard)
    (state : State Symbol Guard) (outputs : List (Value Symbol Guard)) (context : Context state outputs)
    (available : Available state value) (edges : List (EdgeValue Symbol Guard)) (after : State Symbol Guard)
    (done : MergedSourceExposure.nodeEdges fuel value state = .done edges after) : after = state := by
  simpa only [done, Result.state] using nodeEdges_state fuel value state outputs context available

end MicroCFTA.MergedPreparedReaderEffects
