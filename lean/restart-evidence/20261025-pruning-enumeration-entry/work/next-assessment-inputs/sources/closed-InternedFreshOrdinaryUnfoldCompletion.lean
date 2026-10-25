import MicroCFTA.InternedFreshOrdinaryStoredFreeSupport
import MicroCFTA.InternedRecordDepthCompletion
import MicroCFTA.InternedFreshOrdinaryCoverage

/-!
# General repaired stored substitution and single unfolding

Complete semantic caches supply successful source execution for arbitrary
stored bodies and available replacements. Exact returned caches retain all
semantic heaps and payload coverage. A closed Mu has a closed unfolding.
Repeated cold-reader traversal remains a separate termination obligation.
-/
namespace MicroCFTA.InternedFreshOrdinaryStoredSubstitution
open Cache InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedNestedConstruction (Outcome)
open InternedStoredSubstitution (Environment Replacements leaves input encode inputs_available)
open InternedFreshOrdinaryContext
open InternedBinderProtocol (Reference)

/-- Arbitrary repaired stored substitution completes and retains the exact complete semantic cache. -/
theorem execute_complete_decoded [DecidableEq (EdgeKey Symbol Guard)] (body : Value Symbol Guard)
    (environment : Environment Symbol Guard) (state : State Symbol Guard) (context : Context state captures)
    (available : Available state body) (replacements : Replacements state environment)
    (heap : InternedFreshOrdinaryDepthHeap.Heap state) (covered : Covered [] state) :
    ∃ value after, execute body environment state = .done value after ∧ Context after captures ∧
      InternedFreshOrdinaryDepthHeap.Heap after ∧ Covered [] after ∧ Available after value ∧
      Grows state after ∧ Extends state.nodes.issued after.nodes.issued := by
  have inputs := inputs_available body environment state available replacements
  have sourceContext : Context state ((leaves body).map (input environment)) :=
    ⟨context.normal, inputs, context.profiles, context.freeNames⟩
  let expression := encode (leaves body) [] body
  have verified := InternedFreshOrdinaryFacts.build_verified expression _ state context.normal.facts inputs
  have finalContext := sourceContext.build expression
  have finalDepth := InternedRecordDepthExecution.build_depth expression _ state sourceContext heap
  obtain ⟨value, after, done⟩ := InternedRecordDepthCompletion.source_complete expression _ state sourceContext heap covered
  have afterContext : Context after ((leaves body).map (input environment)) := by simpa only [done, Outcome.state] using finalContext
  refine ⟨value, after, done, ⟨afterContext.normal, ?_, afterContext.profiles, afterContext.freeNames⟩, ?_, ?_,
    verified.result value after done, ?_, ?_⟩
  · intro original member
    simpa only [done, Outcome.state] using verified.available original (context.inputs original member)
  · simpa only [done, Outcome.state] using finalDepth.heap
  · exact InternedFreshOrdinaryCoverage.build_covered expression _ state context.normal.facts.coherent.valid covered value after done
  · simpa only [done, Outcome.state] using verified.growth
  · simpa only [done, Outcome.state] using verified.history

/-- Every available record has a successful single repaired unfolding in a complete semantic cache. -/
theorem unfold_complete_decoded [DecidableEq (EdgeKey Symbol Guard)] (value : Value Symbol Guard)
    (state : State Symbol Guard) (context : Context state captures) (available : Available state value)
    (heap : InternedFreshOrdinaryDepthHeap.Heap state) (covered : Covered [] state) :
    ∃ result after, unfold value state = .done result after ∧ Context after captures ∧
      InternedFreshOrdinaryDepthHeap.Heap after ∧ Covered [] after ∧ Available after result ∧
      Grows state after ∧ Extends state.nodes.issued after.nodes.issued := by
  cases value with
  | empty | reference | node | union => exact ⟨_, state, rfl, context, heap, covered, available, grows_refl _, extends_refl _⟩
  | mu entry body depth ordinary =>
      apply execute_complete_decoded body _ state context (available.children body (by simp [children])) ?_ heap covered
      intro name replacement found
      dsimp only at found
      split at found
      · cases found
        exact available
      · cases found

/-- An actual repaired unfolding of a closed available record remains closed without preparation. -/
theorem unfold_closed [DecidableEq (EdgeKey Symbol Guard)] (value : Value Symbol Guard)
    (state : State Symbol Guard) (context : Context state captures) (available : Available state value)
    (closed : value.free = []) (result : Value Symbol Guard) (after : State Symbol Guard)
    (done : unfold value state = .done result after) : result.free = [] := by
  cases value with
  | empty | reference | node | union => cases done; exact closed
  | mu entry body depth ordinary =>
      have replacements : Replacements state (fun name => if name = .interned entry.identity then some (.mu entry body depth ordinary) else none) := by
        intro name replacement found
        dsimp only at found
        split at found
        · cases found
          exact available
        · cases found
      apply List.eq_nil_iff_forall_not_mem.mpr
      intro name member
      obtain ⟨original, originalFree, named⟩ := free_support body _ state context
        (available.children body (by simp [children])) replacements result after done name member
      have own : original = .interned entry.identity := by
        by_cases different : original = .interned entry.identity
        · exact different
        · exact False.elim (by
          have retained : original ∈ (Value.mu entry body depth ordinary).free := by
            simp only [Value.free, List.mem_filter, bne_iff_ne]
            exact ⟨originalFree, different⟩
          rw [closed] at retained
          cases retained)
      simp only [own, ↓reduceIte, Option.getD_some, closed, List.not_mem_nil] at named

end MicroCFTA.InternedFreshOrdinaryStoredSubstitution
