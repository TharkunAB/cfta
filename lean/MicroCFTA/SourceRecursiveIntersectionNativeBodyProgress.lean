import MicroCFTA.SourceRecursiveIntersectionNativeConstructorObservation

/-!
# Smaller compiled body observations

This induction interface requires finite observations only for requests
strictly below the current semantic limit. It retains actual source growth,
active cells, and checked words. The final bound induction must derive both
fields. A pending constructor remains a separate terminal observation.
-/
namespace MicroCFTA.SourceRecursiveIntersectionNative
open Cache InternedConstructorTemplates InternedBinderProtocol IntersectionFlatMemoKeyDomain
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceRecursiveIntersectionInputView IntersectSchedule

/-- The outer bound induction supplies finite observations for strictly smaller original bodies. -/
structure BodiesBelow [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (source : InternedConstructorTemplates.State Symbol Guard) (holds : Guard → Language.Term Symbol → Bool)
    (bound width : Nat) (emptyGuard : Guard) (conjoin : Guard → Guard → Guard) : Prop where
  nodes : ∀ (request : NodeRequest Symbol Guard), NodeScope source request →
    ∀ complete : Completes (view source holds) (nodeSemantic request),
    requiredFuel (view source holds) (nodeSemantic request) complete < bound →
    ∀ state : SourceRecursiveIntersectionThunks.State width Symbol Guard,
    SourceRecursiveIntersectionThunks.Valid width emptyGuard conjoin state → NodeReady state.machine request →
    Grows source state.machine.heap → Extends source.nodes.issued state.machine.heap.nodes.issued →
    ActiveAbove (view source holds) holds (requiredFuel (view source holds) (nodeSemantic request) complete) state →
    WordRanges emptyGuard conjoin (compileNode request) state →
    ∃ fuel, ReturnsOrPending (execute emptyGuard conjoin fuel (compileNode request) state)
  edges : ∀ (request : EdgeRequest Symbol Guard), EdgeScope source request →
    ∀ complete : Completes (view source holds) (edgeSemantic holds request),
    requiredFuel (view source holds) (edgeSemantic holds request) complete < bound →
    ∀ state : SourceRecursiveIntersectionThunks.State width Symbol Guard,
    SourceRecursiveIntersectionThunks.Valid width emptyGuard conjoin state → EdgeReady state.machine request →
    Grows source state.machine.heap → Extends source.nodes.issued state.machine.heap.nodes.issued →
    ActiveAbove (view source holds) holds (requiredFuel (view source holds) (edgeSemantic holds request) complete) state →
    WordRanges emptyGuard conjoin (compileEdge emptyGuard conjoin request) state →
    ∃ fuel, ReturnsOrPending (execute emptyGuard conjoin fuel (compileEdge emptyGuard conjoin request) state)

end MicroCFTA.SourceRecursiveIntersectionNative
