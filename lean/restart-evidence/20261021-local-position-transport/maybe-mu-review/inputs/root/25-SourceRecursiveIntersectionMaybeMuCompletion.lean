import MicroCFTA.SourceRecursiveIntersectionMaybeMuCoverage
import MicroCFTA.InternedRecordDepthCompletion

/-!
# Complete optional binders with arbitrary stored captures

The actual stored substitution compiles to the repaired source executor.
Available leaves supply its full lexical context. Source completion applies
without a prepared-body condition. Semantic heaps remain valid afterward.
-/
namespace MicroCFTA.SourceRecursiveIntersectionMaybeMu
open Cache InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedNestedConstruction (Outcome)
open InternedStoredSubstitution
open InternedFreshOrdinaryContext
open InternedBinderProtocol (NodeKey)

/-- Actual optional-binder execution retains the complete source context and decoded depth heap. -/
theorem semantic_context [DecidableEq (EdgeKey Symbol Guard)] (key : Nat × Nat) (body : Value Symbol Guard)
    (state : State Symbol Guard) (context : Context state environment) (available : Available state body)
    (heap : InternedFreshOrdinaryDepthHeap.Heap state) :
    Context (maybeMu key body state).state environment ∧ InternedFreshOrdinaryDepthHeap.Heap (maybeMu key body state).state := by
  have leavesContext : Context state (leaves body) :=
    ⟨context.normal, leaves_available body state available, context.profiles, context.freeNames⟩
  have checked := verified key body state context.normal.facts available
  rw [maybeMu_eq key body state state context.normal.facts available]
  split
  · have afterContext := leavesContext.build (.binder true (encode (leaves body) [.intersection key.1 key.2] body))
    have afterDepth := InternedRecordDepthExecution.build_depth
      (.binder true (encode (leaves body) [.intersection key.1 key.2] body)) (leaves body) state leavesContext heap
    refine ⟨⟨afterContext.normal, ?_, afterContext.profiles, afterContext.freeNames⟩, afterDepth.heap⟩
    intro value member
    have retained := checked.available value (context.inputs value member)
    rw [maybeMu_eq key body state state context.normal.facts available] at retained
    simp_all only [↓reduceIte]
  · exact ⟨context, heap⟩

/-- An available body in a complete coherent decoded cache never leaves an unfinished optional binder. -/
theorem not_pending [DecidableEq (EdgeKey Symbol Guard)] (pair : Nat × Nat) (body : Value Symbol Guard)
    (state : State Symbol Guard) (context : Context state environment) (available : Available state body)
    (heap : InternedFreshOrdinaryDepthHeap.Heap state) (covered : Covered [] state)
    (key : NodeKey) (final : State Symbol Guard) : maybeMu pair body state ≠ .pending key final := by
  rw [maybeMu_eq pair body state state context.normal.facts available]
  split
  · have leavesContext : Context state (leaves body) :=
      ⟨context.normal, leaves_available body state available, context.profiles, context.freeNames⟩
    exact InternedRecordDepthCompletion.source_not_pending _ (leaves body) state leavesContext heap covered key final
  · intro impossible
    cases impossible

/-- Arbitrary available stored bodies derive successful optional binders and their exact final semantic context. -/
theorem complete_decoded [DecidableEq (EdgeKey Symbol Guard)] (pair : Nat × Nat) (body : Value Symbol Guard)
    (state : State Symbol Guard) (context : Context state environment) (available : Available state body)
    (heap : InternedFreshOrdinaryDepthHeap.Heap state) (covered : Covered [] state) :
    ∃ value final, maybeMu pair body state = .done value final ∧ Context final environment ∧
      InternedFreshOrdinaryDepthHeap.Heap final ∧ Covered [] final ∧ Available final value ∧
      Grows state final ∧ Extends state.nodes.issued final.nodes.issued := by
  have contexts := semantic_context pair body state context available heap
  have checked := verified pair body state context.normal.facts available
  cases result : maybeMu pair body state with
  | pending key final => exact False.elim (not_pending pair body state context available heap covered key final result)
  | done value final =>
      refine ⟨value, final, rfl, ?_, ?_, ?_, checked.result _ _ result, ?_, ?_⟩
      · simpa only [result, Outcome.state] using contexts.1
      · simpa only [result, Outcome.state] using contexts.2
      · exact maybeMu_covered pair body state context.normal.facts.coherent.valid covered value final result
      · simpa only [result, Outcome.state] using checked.growth
      · simpa only [result, Outcome.state] using checked.history

end MicroCFTA.SourceRecursiveIntersectionMaybeMu
