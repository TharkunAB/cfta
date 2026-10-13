import MicroCFTA.InternedFreeNameHeap

/-!
# Free-name readback from a completed recursive request

The request returns the free names decoded from its actual probe pair.
This follows from the complete record stored after the request. It applies
to cache hits and misses and to both cleanup modes.
-/
namespace MicroCFTA.InternedRequestFreeReadback
open InternedConstructorTemplates InternedNestedConstruction InternedNestedFacts
open InternedProbeProvenance InternedNestedMissReadback InternedFreeNameDecoder
open InternedBinderProtocol (Reference)

/-- A completed source request reads its probe pair through the final free-name invariant. -/
theorem request_free [DecidableEq (EdgeKey Symbol Guard)] (smart : Bool)
    (body : Syntax Symbol Guard) (environment : List (Value Symbol Guard))
    (depth ordinary : Value Symbol Guard) (state : State Symbol Guard)
    (facts : Facts state) (depthAvailable : Available state depth)
    (ordinaryAvailable : Available state ordinary)
    (value : Value Symbol Guard) (final : State Symbol Guard)
    (completed : request smart depth ordinary (callback body environment) state = .done value final)
    (heap : InternedFreeNameHeap.Heap final) (name : Reference) :
    name ∈ value.free ↔ name ∈ decode .depth (.uninterned depth.depth) depth.free ordinary.free := by
  cases installed : state.nodes.table (muKey depth ordinary) with
  | none =>
      obtain ⟨actual, afterBody, _, present, same⟩ := request_miss_record smart body environment
        depth ordinary state facts.coherent installed value final completed
      rw [same, finish_free]
      exact heap _ _ actual depth ordinary present name
  | some entry =>
      cases present : state.nodeRecords (muKey depth ordinary) with
      | none => simp [request, installed, present] at completed
      | some stored =>
          have result : finish smart stored = value ∧ state = final := by
            simpa only [request, installed, present, Outcome.done.injEq] using completed
          have states := result.2
          subst final
          rw [← result.1]
          exact InternedFreeNameHeap.hit_free smart depth ordinary stored state facts
            depthAvailable ordinaryAvailable heap present name

/-- Absence of an interned free name excludes it from both actual normalized probes. -/
theorem interned_probe_absent [DecidableEq (EdgeKey Symbol Guard)] (smart : Bool)
    (body : Syntax Symbol Guard) (environment : List (Value Symbol Guard))
    (depth ordinary : Value Symbol Guard) (state : State Symbol Guard)
    (facts : Facts state) (depthAvailable : Available state depth)
    (ordinaryAvailable : Available state ordinary)
    (value : Value Symbol Guard) (final : State Symbol Guard)
    (completed : request smart depth ordinary (callback body environment) state = .done value final)
    (heap : InternedFreeNameHeap.Heap final) (identity : Nat)
    (absent : .interned identity ∉ value.free) :
    .interned identity ∉ depth.free ∧ .interned identity ∉ ordinary.free := by
  have decoded := request_free smart body environment depth ordinary state facts depthAvailable
    ordinaryAvailable value final completed heap (.interned identity)
  simpa [decode] using absent ∘ decoded.mpr

end MicroCFTA.InternedRequestFreeReadback
