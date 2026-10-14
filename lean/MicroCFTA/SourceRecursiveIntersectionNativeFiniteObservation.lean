import MicroCFTA.SourceRecursiveIntersectionNativeCodeProgress

/-!
# Finite native observations from derived semantic request bounds

Strong induction on the least semantic request bound supplies every smaller
compiled body. Structural code induction follows actual continuations.
No completed native trace or body termination contract is assumed. Source
failure and pending construction remain distinct from successful results.
-/
namespace MicroCFTA.SourceRecursiveIntersectionNative
open Cache InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency InternedNestedFacts
open InternedBinderProtocol IntersectionFlatMemoKeyDomain
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceRecursiveIntersectionInputView IntersectSchedule

/-- Derived strict request limits give a finite actual terminal observation, with explicit checked words. -/
theorem code_terminal [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (source : InternedConstructorTemplates.State Symbol Guard) (facts : Facts source)
    (holds : Guard → Language.Term Symbol → Bool) (emptyGuard : Guard) (conjoin : Guard → Guard → Guard) (bound : Nat) :
    ∀ {A : Type} (code : Code Symbol Guard A) (state : SourceRecursiveIntersectionThunks.State width Symbol Guard)
    (post : Machine Symbol Guard → A → Prop), Safe code state.machine post → Below source holds bound code state.machine →
    SourceRecursiveIntersectionThunks.Valid width emptyGuard conjoin state → Grows source state.machine.heap →
    Extends source.nodes.issued state.machine.heap.nodes.issued → ActiveAbove (view source holds) holds bound state →
    WordRanges emptyGuard conjoin code state → ∃ fuel, Terminal (execute emptyGuard conjoin fuel code state) := by
  induction bound using Nat.strongRecOn with
  | ind bound ih =>
      have bodies : BodiesBelow source holds bound width emptyGuard conjoin := by
        constructor
        · intro request scope complete smaller state valid ready growth history active ranges
          exact ih (requiredFuel (view source holds) (nodeSemantic request) complete) smaller
            (compileNode request) state (fun after value => Available after.heap value)
            (compileNode_safe request state.machine valid.machine ready)
            (compileNode_below source facts holds request scope complete state.machine valid.machine ready growth history)
            valid growth history active ranges
        · intro request scope complete smaller state valid ready growth history active ranges
          exact ih (requiredFuel (view source holds) (edgeSemantic holds request) complete) smaller
            (compileEdge emptyGuard conjoin request) state (fun after value => EdgeResident after.heap value)
            (compileEdge_safe emptyGuard conjoin request state.machine valid.machine ready)
            (compileEdge_below source facts holds emptyGuard conjoin request scope complete state.machine valid.machine ready)
            valid growth history active ranges
      intro A code state post safe below valid growth history active ranges
      exact code_terminal_of_bodies source holds bound emptyGuard conjoin bodies code state post safe below valid growth history active ranges

end MicroCFTA.SourceRecursiveIntersectionNative
