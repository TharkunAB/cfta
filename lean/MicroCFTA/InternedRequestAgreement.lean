import MicroCFTA.InternedNestedErasureReplay
import MicroCFTA.InternedNestedMissReadback

/-!
# Exact agreement of completed source requests

Two successful requests for the same probe pair return the same complete
value when both actual result caches extend to one cache. Each completed
request replays in that cache. The later callback is irrelevant on the hit.
-/
namespace MicroCFTA.InternedRequestAgreement
open InternedConstructorTemplates InternedNestedConstruction InternedRecordCoherence
open InternedNestedErasureReplay InternedNestedMissReadback InternedNestedSpecialization
open InternedBinderProtocol (Reference NodeKey)
open InternedProbeProvenance InternedFreshProbeKeys

/-- Two completed requests with the same probes and cleanup flag agree in an actual common extension. -/
theorem request_same [DecidableEq (EdgeKey Symbol Guard)] (smart : Bool)
    (depth ordinary : Value Symbol Guard)
    (firstCallback secondCallback : Reference → State Symbol Guard → Outcome Symbol Guard (Value Symbol Guard))
    (firstStart secondStart firstEnd secondEnd common : State Symbol Guard)
    (firstValue secondValue : Value Symbol Guard)
    (firstValid : InternedConstructorTemplates.Valid firstStart)
    (secondValid : InternedConstructorTemplates.Valid secondStart)
    (firstGrowing : ∀ name, Growing (firstCallback name))
    (secondGrowing : ∀ name, Growing (secondCallback name))
    (firstDone : request smart depth ordinary firstCallback firstStart = .done firstValue firstEnd)
    (secondDone : request smart depth ordinary secondCallback secondStart = .done secondValue secondEnd)
    (firstGrowth : Grows firstEnd common) (secondGrowth : Grows secondEnd common) :
    firstValue = secondValue := by
  have firstReplay := request_after_done smart depth ordinary firstCallback firstCallback
    firstStart common firstValue firstEnd firstValid firstGrowing firstDone firstGrowth
  have secondReplay := request_after_done smart depth ordinary secondCallback firstCallback
    secondStart common secondValue secondEnd secondValid secondGrowing secondDone secondGrowth
  exact (Outcome.done.inj (firstReplay.symm.trans secondReplay)).1

/-- Every finite source callback preserves existing cache entries on both outcomes. -/
theorem callback_growing [DecidableEq (EdgeKey Symbol Guard)] (body : Syntax Symbol Guard)
    (environment : List (Value Symbol Guard)) (name : Reference) : Growing (callback body environment name) := by
  intro state valid
  exact bind_correct _ _ state (build_correct body _ state valid)
    (fun value after afterValid => work_correct (withoutSelfReference name value) after afterValid)

/-- Arbitrary nested source bodies agree on completed requests with identical actual probe records. -/
theorem source_request_same [DecidableEq (EdgeKey Symbol Guard)] (smart : Bool)
    (depth ordinary : Value Symbol Guard) (firstBody secondBody : Syntax Symbol Guard)
    (firstEnvironment secondEnvironment : List (Value Symbol Guard))
    (firstStart secondStart firstEnd secondEnd common : State Symbol Guard)
    (firstValue secondValue : Value Symbol Guard)
    (firstValid : InternedConstructorTemplates.Valid firstStart)
    (secondValid : InternedConstructorTemplates.Valid secondStart)
    (firstDone : request smart depth ordinary (callback firstBody firstEnvironment) firstStart = .done firstValue firstEnd)
    (secondDone : request smart depth ordinary (callback secondBody secondEnvironment) secondStart = .done secondValue secondEnd)
    (firstGrowth : Grows firstEnd common) (secondGrowth : Grows secondEnd common) :
    firstValue = secondValue :=
  request_same smart depth ordinary _ _ firstStart secondStart firstEnd secondEnd common firstValue secondValue
    firstValid secondValid (callback_growing firstBody firstEnvironment) (callback_growing secondBody secondEnvironment)
    firstDone secondDone firstGrowth secondGrowth

/-- Equal canonical probe keys suffice when all four actual probe records are resident in the common cache. -/
theorem source_request_key_same [DecidableEq (EdgeKey Symbol Guard)] (smart : Bool)
    (firstDepth firstOrdinary secondDepth secondOrdinary : Value Symbol Guard)
    (firstBody secondBody : Syntax Symbol Guard)
    (firstEnvironment secondEnvironment : List (Value Symbol Guard))
    (firstStart secondStart firstEnd secondEnd common : State Symbol Guard)
    (firstValue secondValue : Value Symbol Guard)
    (firstValid : InternedConstructorTemplates.Valid firstStart)
    (secondValid : InternedConstructorTemplates.Valid secondStart)
    (coherent : Coherent common)
    (firstDepthResident : Resident common firstDepth) (firstOrdinaryResident : Resident common firstOrdinary)
    (secondDepthResident : Resident common secondDepth) (secondOrdinaryResident : Resident common secondOrdinary)
    (sameKey : muKey firstDepth firstOrdinary = muKey secondDepth secondOrdinary)
    (firstDone : request smart firstDepth firstOrdinary (callback firstBody firstEnvironment) firstStart = .done firstValue firstEnd)
    (secondDone : request smart secondDepth secondOrdinary (callback secondBody secondEnvironment) secondStart = .done secondValue secondEnd)
    (firstGrowth : Grows firstEnd common) (secondGrowth : Grows secondEnd common) :
    firstValue = secondValue := by
  have references : firstDepth.referenceOf = secondDepth.referenceOf ∧
      firstOrdinary.referenceOf = secondOrdinary.referenceOf := by
    simpa only [muKey, NodeKey.mu.injEq, InternedBinderProtocol.MuKey.mk.injEq] using sameKey
  have depthSame := resident_reference_injective common coherent firstDepth secondDepth
    firstDepthResident secondDepthResident references.1
  have ordinarySame := resident_reference_injective common coherent firstOrdinary secondOrdinary
    firstOrdinaryResident secondOrdinaryResident references.2
  subst secondDepth
  subst secondOrdinary
  exact source_request_same smart firstDepth firstOrdinary firstBody secondBody firstEnvironment secondEnvironment
    firstStart secondStart firstEnd secondEnd common firstValue secondValue firstValid secondValid
    firstDone secondDone firstGrowth secondGrowth

end MicroCFTA.InternedRequestAgreement
