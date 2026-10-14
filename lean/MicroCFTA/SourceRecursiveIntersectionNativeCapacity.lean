import MicroCFTA.SourceRecursiveIntersectionNativeWordRanges
import MicroCFTA.IntersectionFlatMemoKeyPhysical

/-!
# Native request word checks from actual cache counters

Node keys reserve two tag bits and the all-ones empty sentinel. Domain keys
reserve zero and shift raw identities by one. Edge keys use raw identities.
The actual three cache counters derive these distinct machine-word bounds.
-/
namespace MicroCFTA.SourceRecursiveIntersectionNativeCapacity
open Cache InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedEdgeResidency InternedBinderProtocol IntersectionFlatMemoKeyDomain
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode

/-- Actual source supplies fit the node tags, shifted domains, and raw edge words. -/
structure Capacity (bits : Nat) (machine : Machine Symbol Guard) : Prop where
  nodes : machine.heap.nodes.next < 2 ^ bits
  domains : machine.domains.next < 2 ^ (bits + 1)
  edges : machine.heap.edges.next ≤ 2 ^ (bits + 2)

/-- A represented source domain is bounded after its actual reserved-zero shift. -/
theorem domain_bounded (bits : Nat) (machine : Machine Symbol Guard)
    (valid : SourceRecursiveIntersectionKernel.Valid machine) (capacity : Capacity bits machine)
    (domain : Interned DomainKey) (known : Domain machine domain) : domain.identity < 2 ^ (bits + 1) := by
  by_cases empty : domain.key = IntersectionEmptyDomain.emptyKey
  · have zero : domain.identity = 0 := by simpa only [empty, ite_true] using known.represented.2
    rw [zero]
    exact Nat.two_pow_pos _
  · obtain ⟨raw, stored, shifted⟩ := (show ∃ raw, machine.domains.table domain.key = some raw ∧
        domain.identity = raw.identity + 1 from by simpa only [empty, ite_false] using known.represented.2)
    have issued := (valid.2.2 domain.key raw stored).2
    have bounded := valid.2.1 raw.identity domain.key issued
    have room := capacity.domains
    omega

/-- Each resident edge has a raw identity below the actual edge supply. -/
theorem edge_bounded (machine : Machine Symbol Guard) (valid : SourceRecursiveIntersectionKernel.Valid machine)
    (edge : EdgeValue Symbol Guard) (resident : EdgeResident machine.heap edge) :
    edge.entry.identity < machine.heap.edges.next := by
  have stored := (valid.1.coherent.edges edge.entry.key edge resident).1
  exact valid.1.coherent.valid.1.1 edge.entry.identity edge.entry.key
    ((valid.1.coherent.valid.1.2 edge.entry.key edge.entry stored).2)

/-- An actual memoized available node request satisfies every tagged key bound. -/
theorem node_key_safe (bits : Nat) (machine : Machine Symbol Guard)
    (valid : SourceRecursiveIntersectionKernel.Valid machine) (capacity : Capacity bits machine)
    (request : NodeRequest Symbol Guard) (ready : NodeReady machine request) (key : Triple (bits + 2))
    (memoized : SourceRecursiveIntersectionMemo.requestKey (bits + 2) request.domain request.left request.right = some key) :
    SourceRecursiveIntersectionMemo.KeySafe (bits + 2) request.domain request.left request.right := by
  cases first : IntersectionFlatMemoKey.input request.left.referenceOf with
  | none => simp [SourceRecursiveIntersectionMemo.requestKey, sourceKey, IntersectionFlatMemoKey.key, first] at memoized
  | some left =>
      cases second : IntersectionFlatMemoKey.input request.right.referenceOf with
      | none => simp [SourceRecursiveIntersectionMemo.requestKey, sourceKey, IntersectionFlatMemoKey.key, second] at memoized
      | some right =>
          refine ⟨by omega, ?_, left, right, first, second, ?_, ?_⟩
          · simpa only [show bits + 2 - 1 = bits + 1 from by omega] using domain_bounded bits machine valid capacity request.domain ready.1
          · exact IntersectionFlatMemoKeyPhysical.available_safe bits machine.heap valid.1 capacity.nodes request.left ready.2.1 left first
          · exact IntersectionFlatMemoKeyPhysical.available_safe bits machine.heap valid.1 capacity.nodes request.right ready.2.2 right second

/-- An actual resident edge request satisfies both raw identity bounds and the shifted domain bound. -/
theorem edge_key_safe (bits : Nat) (machine : Machine Symbol Guard)
    (valid : SourceRecursiveIntersectionKernel.Valid machine) (capacity : Capacity bits machine)
    (request : EdgeRequest Symbol Guard) (ready : EdgeReady machine request) :
    SourceRecursiveIntersectionEdgeMemo.KeySafe (bits + 2) request.domain request.left request.right := by
  refine ⟨by omega, ?_, ?_, ?_⟩
  · simpa only [show bits + 2 - 1 = bits + 1 from by omega] using domain_bounded bits machine valid capacity request.domain ready.1
  · exact Nat.lt_of_lt_of_le (edge_bounded machine valid request.left ready.2.1) capacity.edges
  · exact Nat.lt_of_lt_of_le (edge_bounded machine valid request.right ready.2.2) capacity.edges

/-- Current request instructions retain their actual source operand provenance. -/
def RequestReady [DecidableEq (EdgeKey Symbol Guard)] (code : Code Symbol Guard A) (machine : Machine Symbol Guard) : Prop :=
  match code with
  | .node request _ => NodeReady machine request
  | .edge request _ => EdgeReady machine request
  | _ => True

/-- A source safety derivation supplies the current request provenance without word assumptions. -/
theorem request_ready [DecidableEq (EdgeKey Symbol Guard)] (code : Code Symbol Guard A) (machine : Machine Symbol Guard)
    (post : Machine Symbol Guard → A → Prop) (safe : Safe code machine post) : RequestReady code machine := by
  cases code <;> first | exact safe.1 | trivial

/-- Actual cache capacity and current request provenance derive the complete native word check. -/
theorem words [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (bits : Nat) (code : Code Symbol Guard A) (machine : Machine Symbol Guard)
    (valid : SourceRecursiveIntersectionKernel.Valid machine) (capacity : Capacity bits machine)
    (ready : RequestReady code machine) : SourceRecursiveIntersectionNative.Words (bits + 2) code := by
  cases code with
  | node request next => exact fun key memoized => node_key_safe bits machine valid capacity request ready key memoized
  | edge request next => exact edge_key_safe bits machine valid capacity request ready
  | _ => trivial

end MicroCFTA.SourceRecursiveIntersectionNativeCapacity
