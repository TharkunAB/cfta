import MicroCFTA.SourceRecursiveIntersectionNativeIdle
import MicroCFTA.SourceRecursiveIntersectionNativeSuccessful

/-!
# Successful checked native calls from idle warm memo states

The actual input view supplies a finite semantic request bound. Idle memo
tables satisfy the active-bound premise without being empty. The existing
native progress proof gives a finite observation. Complete semantic heaps
exclude pending construction. The returned state is idle for the next call.
-/
namespace MicroCFTA.SourceRecursiveIntersectionNative
open Cache InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance InternedNestedFacts
open InternedBinderProtocol IntersectionFlatMemoKeyDomain
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceRecursiveIntersectionInputView IntersectSchedule
open SourceRecursiveIntersectionSemanticHeap (SemanticHeap)

/-- Closed original physical operands have a finite actual terminal observation from any valid idle memo state. -/
theorem warm_node_terminal [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (emptyGuard : Guard) (conjoin : Guard → Guard → Guard)
    (state : SourceRecursiveIntersectionThunks.State width Symbol Guard)
    (valid : SourceRecursiveIntersectionThunks.Valid width emptyGuard conjoin state) (idle : Idle state)
    (holds : Guard → Language.Term Symbol → Bool)
    (left right : Value Symbol Guard) (leftOriginal : Original left) (rightOriginal : Original right)
    (leftAvailable : Available state.machine.heap left) (rightAvailable : Available state.machine.heap right)
    (leftClosed : left.free = []) (rightClosed : right.free = [])
    (ranges : WordRanges emptyGuard conjoin (.node ⟨IntersectionEmptyDomain.emptyDomain, left, right⟩ .pure) state) :
    ∃ fuel, ReturnsOrPending (execute emptyGuard conjoin fuel (.node ⟨IntersectionEmptyDomain.emptyDomain, left, right⟩ .pure) state) := by
  let source := state.machine.heap
  have facts := valid.machine.1
  let request : NodeRequest Symbol Guard := ⟨IntersectionEmptyDomain.emptyDomain, left, right⟩
  have complete : Completes (view source holds) (nodeSemantic request) :=
    SourceRecursiveIntersectionRequestProgress.initial_complete source facts holds left right leftOriginal rightOriginal
      leftAvailable rightAvailable leftClosed rightClosed
  let bound := requiredFuel (view source holds) (nodeSemantic request) complete + 1
  have ready : NodeReady state.machine request := ⟨empty_domain _, leftAvailable, rightAvailable⟩
  have below : NodeBelow source holds bound request :=
    ⟨initial_scope source left right leftOriginal rightOriginal leftAvailable rightAvailable, complete, Nat.lt_succ_self _⟩
  exact code_terminal source facts holds emptyGuard conjoin bound (.node request .pure) state
    (fun after value => Available after.heap value) (safe_requestNode _ _ _ _ ready)
    (below_requestNode source holds bound request _ below) valid (grows_refl _) (extends_refl _)
    (idle.active (view source holds) holds bound state) ranges

/-- Idle warm calls complete without a supplied native execution and return exact cache invariants and idle memos. -/
theorem warm_node_complete [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (emptyGuard : Guard) (conjoin : Guard → Guard → Guard)
    (state : SourceRecursiveIntersectionThunks.State width Symbol Guard)
    (valid : SourceRecursiveIntersectionThunks.Valid width emptyGuard conjoin state) (idle : Idle state)
    (semantic : SemanticHeap state.machine.heap) (covered : Covered [] state.machine.heap)
    (holds : Guard → Language.Term Symbol → Bool)
    (left right : Value Symbol Guard) (leftOriginal : Original left) (rightOriginal : Original right)
    (leftAvailable : Available state.machine.heap left) (rightAvailable : Available state.machine.heap right)
    (leftClosed : left.free = []) (rightClosed : right.free = [])
    (ranges : WordRanges emptyGuard conjoin (.node ⟨IntersectionEmptyDomain.emptyDomain, left, right⟩ .pure) state) :
    ∃ fuel value after,
      execute emptyGuard conjoin fuel (.node ⟨IntersectionEmptyDomain.emptyDomain, left, right⟩ .pure) state = .done value after ∧
      Correct emptyGuard conjoin (.node ⟨IntersectionEmptyDomain.emptyDomain, left, right⟩ .pure) state value after
        (fun final value => Available final.heap value) ∧
      SemanticHeap after.machine.heap ∧ Covered [] after.machine.heap ∧ Idle after ∧
      ∀ extra, execute emptyGuard conjoin (fuel + extra) (.node ⟨IntersectionEmptyDomain.emptyDomain, left, right⟩ .pure) state = .done value after := by
  let request : NodeRequest Symbol Guard := ⟨IntersectionEmptyDomain.emptyDomain, left, right⟩
  have ready : NodeReady state.machine request := ⟨empty_domain _, leftAvailable, rightAvailable⟩
  have safe := safe_requestNode request.domain left right state.machine ready
  have certificate := semantic_requestNode request.domain left right state.machine ready
  have clean : BodyCode (Code.node request Code.pure) := by intro value; trivial
  obtain ⟨fuel, terminal⟩ := warm_node_terminal emptyGuard conjoin state valid idle holds left right
    leftOriginal rightOriginal leftAvailable rightAvailable leftClosed rightClosed ranges
  generalize observed : execute emptyGuard conjoin fuel (.node request .pure) state = outcome at terminal
  cases terminal with
  | done value after =>
      have evaluated := evaluation_of_done emptyGuard conjoin fuel (.node request .pure) state after value observed
      have bounds := evaluated.bounds_of_ranges ranges
      have correct := bounds.correct (fun final value => Available final.heap value) clean safe valid
      have retained := bounds.semantic_heap (fun final value => Available final.heap value) clean safe valid certificate semantic
      obtain ⟨steps, _, trace⟩ := done_trace emptyGuard conjoin fuel (.node request .pure) state after value observed
      have payloads := trace.covered emptyGuard conjoin steps _ _ state after valid.machine.1.coherent.valid covered
      exact ⟨fuel, value, after, observed, correct, retained, payloads.2,
        done_idle emptyGuard conjoin fuel _ state after value clean (shape_of_valid emptyGuard conjoin state valid) idle observed,
        fun extra => done_stable emptyGuard conjoin fuel extra _ state after value observed⟩
  | constructor key remaining after =>
      exact False.elim (no_constructor emptyGuard conjoin fuel (.node request .pure) state after key remaining
        (fun final value => Available final.heap value) clean safe valid certificate semantic covered ranges observed)

end MicroCFTA.SourceRecursiveIntersectionNative
