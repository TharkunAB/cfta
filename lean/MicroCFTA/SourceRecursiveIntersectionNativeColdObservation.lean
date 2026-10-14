import MicroCFTA.SourceRecursiveIntersectionNativeFiniteObservation

/-!
# Finite first observations for closed original source roots

Actual closed available roots derive the semantic bound and empty active
state. The native driver then reaches a finite return, source failure, or
actual pending constructor. No native completion witness is supplied.
Successful returns derive complete memo facts and guarded kernel meaning.
-/
namespace MicroCFTA.SourceRecursiveIntersectionNative
open Cache InternedConstructorTemplates InternedProbeProvenance InternedNestedFacts
open InternedBinderProtocol IntersectionFlatMemoKeyDomain
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceRecursiveIntersectionInputView IntersectSchedule

/-- Closed original physical roots have a finite first native observation with checked request words. -/
theorem cold_node_terminal [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (source : InternedConstructorTemplates.State Symbol Guard) (facts : Facts source)
    (domains : Cache.State DomainKey) (domainsValid : Cache.Valid domains)
    (holds : Guard → Language.Term Symbol → Bool) (emptyGuard : Guard) (conjoin : Guard → Guard → Guard)
    (left right : Value Symbol Guard) (leftOriginal : Original left) (rightOriginal : Original right)
    (leftAvailable : Available source left) (rightAvailable : Available source right)
    (leftClosed : left.free = []) (rightClosed : right.free = [])
    (ranges : WordRanges emptyGuard conjoin (.node ⟨IntersectionEmptyDomain.emptyDomain, left, right⟩ .pure)
      (initial width ⟨source, domains⟩)) :
    ∃ fuel, Terminal (execute emptyGuard conjoin fuel (.node ⟨IntersectionEmptyDomain.emptyDomain, left, right⟩ .pure)
      (initial width ⟨source, domains⟩)) := by
  let request : NodeRequest Symbol Guard := ⟨IntersectionEmptyDomain.emptyDomain, left, right⟩
  have complete : Completes (view source holds) (nodeSemantic request) :=
    SourceRecursiveIntersectionRequestProgress.initial_complete source facts holds left right leftOriginal rightOriginal
      leftAvailable rightAvailable leftClosed rightClosed
  let bound := requiredFuel (view source holds) (nodeSemantic request) complete + 1
  have ready : NodeReady (⟨source, domains⟩ : Machine Symbol Guard) request :=
    ⟨empty_domain _, leftAvailable, rightAvailable⟩
  have below : NodeBelow source holds bound request :=
    ⟨initial_scope source left right leftOriginal rightOriginal leftAvailable rightAvailable, complete, Nat.lt_succ_self _⟩
  exact code_terminal source facts holds emptyGuard conjoin bound (.node request .pure) (initial width ⟨source, domains⟩)
    (fun after value => Available after.heap value) (safe_requestNode _ _ _ _ ready)
    (below_requestNode source holds bound request _ below) (initial_valid width emptyGuard conjoin _ ⟨facts, domainsValid⟩)
    (grows_refl _) (extends_refl _) (active_initial (view source holds) holds bound _) ranges

/-- A finite native return derives strong invariants and exact guarded source meaning from prefix word checks. -/
theorem done_correct_of_ranges [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (emptyGuard : Guard) (conjoin : Guard → Guard → Guard) (code : Code Symbol Guard A)
    (state after : SourceRecursiveIntersectionThunks.State width Symbol Guard) (value : A)
    (post : Machine Symbol Guard → A → Prop) (clean : BodyCode code) (safe : Safe code state.machine post)
    (valid : SourceRecursiveIntersectionThunks.Valid width emptyGuard conjoin state)
    (ranges : WordRanges emptyGuard conjoin code state) (fuel : Nat)
    (done : execute emptyGuard conjoin fuel code state = .done value after) :
    Correct emptyGuard conjoin code state value after post :=
  ((evaluation_of_done emptyGuard conjoin fuel code state after value done).bounds_of_ranges ranges).correct post clean safe valid

end MicroCFTA.SourceRecursiveIntersectionNative
