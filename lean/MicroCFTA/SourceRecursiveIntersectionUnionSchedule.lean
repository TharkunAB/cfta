import MicroCFTA.SourceRecursiveIntersectionUnionReadback
import MicroCFTA.SourceRecursiveIntersectionScheduleConstructors
import MicroCFTA.IntersectWalkRelated

/-!
# Actual union branches transport ordered semantic requests

Completed source union work retains each original member occurrence and
its actual result in one final cache. Corresponding semantic child calls
then supply the exact semantic walk and normalized union language.
-/
namespace MicroCFTA.SourceRecursiveIntersectionKernel
open Cache Language Binding InternedConstructorTemplates InternedProbeProvenance
open InternedBinderProtocol IntersectionFlatMemoKeyDomain
open SourceRecursiveIntersectionScheduleConstructors (Corresponds)

/-- Actual union completion transports local child correspondences through the ordered walk and constructor. -/
theorem union_schedule_body [DecidableEq (EdgeKey Symbol Guard)]
    (call : Interned DomainKey → Value Symbol Guard → Value Symbol Guard → Machine Symbol Guard → Result Symbol Guard (Value Symbol Guard))
    (calls : Calls call) (replay : Replays call) (domain : Interned DomainKey) (members : List (Value Symbol Guard))
    (other : Value Symbol Guard) (left : Bool) (before after : Machine Symbol Guard) (valid : Valid before)
    (afterValid : Valid after) (known : Domain before domain) (available : Available before.heap other)
    (membersAvailable : ∀ member ∈ members, Available before.heap member)
    (value : Value Symbol Guard) (final : Machine Symbol Guard)
    (done : (walk (fun member => if left then call domain member other else call domain other member) members before).bind
      (fun values current => work (makeUnion values) current) = .done value final) (growth : Extension final after)
    (holds : Guard → Term Symbol → Bool) (action : Value Symbol Guard → Except IntersectSchedule.Error (Shape (BinderLanguage.Payload Symbol)))
    (children : ∀ member ∈ members, ∀ result,
      (if left then call domain member other else call domain other member) after = .done result after →
      ∃ shape, action member = .ok shape ∧ Corresponds holds result shape) :
    ∃ shapes, IntersectSchedule.walk action members = .ok shapes ∧ Corresponds holds value (.alternatives shapes) := by
  obtain ⟨values, resident, paired, built⟩ :=
    union_values_replay call calls replay domain members other left before after valid known available membersAvailable value final done growth
  have related := SourcePhysicalSharedRows.all₂_both_imp _ _ members values paired
    (fun member present result _ completed => children member present result completed)
  obtain ⟨shapes, walked, meanings⟩ := IntersectSchedule.walk_related action (Corresponds holds) members values related
  refine ⟨shapes, walked, ?_⟩
  rw [(work_done (makeUnion values) after value after built).1]
  exact SourceRecursiveIntersectionScheduleConstructors.makeUnion holds values shapes meanings after.heap afterValid.1 resident

end MicroCFTA.SourceRecursiveIntersectionKernel
