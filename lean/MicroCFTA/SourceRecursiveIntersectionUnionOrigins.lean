import MicroCFTA.SourceRecursiveIntersectionUnionReadback
import MicroCFTA.MergedFreshOrdinaryUnionOrigins

/-!
# Actual union calls expose exactly their child-call edge origins

Ordered replay supplies actual physical child representatives. The union
constructor preserves their complete repaired epsilon origins. The resulting
equation uses successful calls in one common cache and permits arbitrary
later views of the repaired graph. It assumes no product-language contract.
-/
namespace MicroCFTA.SourceRecursiveIntersectionKernel
open Cache Language InternedConstructorTemplates InternedProbeProvenance
open InternedBinderProtocol IntersectionFlatMemoKeyDomain
open MergedFreshOrdinaryGraph (Origin)

/-- Actual union output origins are exactly the complete origins of successful member-call results. -/
theorem union_call_origins [DecidableEq (EdgeKey Symbol Guard)]
    (call : Interned DomainKey → Value Symbol Guard → Value Symbol Guard → Machine Symbol Guard → Result Symbol Guard (Value Symbol Guard))
    (calls : Calls call) (replay : Replays call) (domain : Interned DomainKey) (members : List (Value Symbol Guard))
    (other : Value Symbol Guard) (left : Bool) (before after : Machine Symbol Guard) (valid : Valid before)
    (afterValid : Valid after) (live : InternedLiveEdges.Live after.heap) (known : Domain before domain)
    (available : Available before.heap other) (membersAvailable : ∀ member ∈ members, Available before.heap member)
    (value : Value Symbol Guard) (final : Machine Symbol Guard)
    (done : (walk (fun member => if left then call domain member other else call domain other member) members before).bind
      (fun values current => work (makeUnion values) current) = .done value final) (growth : Extension final after)
    (view : InternedConstructorTemplates.State Symbol Guard) (edge : EdgeValue Symbol Guard) :
    Origin view [value] edge ↔ ∃ member ∈ members, ∃ result,
      (if left then call domain member other else call domain other member) after = .done result after ∧ Origin view [result] edge := by
  obtain ⟨values, resident, paired, built⟩ :=
    union_values_replay call calls replay domain members other left before after valid known available membersAvailable value final done growth
  have exactOrigins := MergedFreshOrdinaryUnionOrigins.union_origins after.heap view afterValid.1 live values resident edge
  rw [← (work_done (makeUnion values) after value after built).1] at exactOrigins
  apply exactOrigins.trans
  constructor
  · rintro ⟨result, present, origin⟩
    obtain ⟨member, included, returned⟩ := (pointwise_result_member
      (fun member => (if left then call domain member other else call domain other member) after) members values after paired result).mp present
    exact ⟨member, included, result, returned, origin⟩
  · rintro ⟨member, included, result, returned, origin⟩
    exact ⟨result, (pointwise_result_member
      (fun member => (if left then call domain member other else call domain other member) after) members values after paired result).mpr
      ⟨member, included, returned⟩, origin⟩

end MicroCFTA.SourceRecursiveIntersectionKernel
