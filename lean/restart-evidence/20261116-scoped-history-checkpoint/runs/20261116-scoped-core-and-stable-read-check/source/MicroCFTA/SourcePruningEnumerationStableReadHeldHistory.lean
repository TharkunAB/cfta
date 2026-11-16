import MicroCFTA.SourcePruningEnumerationOpaqueSuffixIsolation
import MicroCFTA.SourcePruningEnumerationIsolationReads

namespace MicroCFTA.EnumerationDischargeHistory
open EnumerationState EnumerationCorrectness EnumerationSchedule EnumerationDependencies EnumerationDriver
local notation "Symbol" => SourcePruningTemplates.Symbol
variable {Guard : Type}
set_option autoImplicit false

/-- A stable read retains old expanded slots and their exact stored fragments. -/
theorem HeldFragmentHistory.of_renderStable
    (held handle : Nat) (before after : State Symbol Guard)
    (isolated : IsolatedPending held handle before)
    (stable : RenderStable before after) :
    HeldFragmentHistory held handle before after
 := by
  have isolatedAfter := isolated.through_renderStable stable
  refine ⟨isolatedAfter, ⟨?_, isolatedAfter.root, stable.classes held⟩, ?_, ?_⟩
  · exact congrArg (fun values => values[held]?) stable.values
  · intro slot fragment stored
    have afterStored : after.values[slot]? = some (.enumerated fragment) := by
      rw [stable.values]
      exact stored
    exact ⟨congrArg (fun values => values[slot]?) stable.values,
      (enumerated_root after stable.safe slot fragment afterStored).2, stable.classes slot⟩
  · intro slot fragment stored
    exact Or.inl (by simpa only [stable.values] using stored)

end MicroCFTA.EnumerationDischargeHistory

#check MicroCFTA.EnumerationDischargeHistory.HeldFragmentHistory.of_renderStable
#print axioms MicroCFTA.EnumerationDischargeHistory.HeldFragmentHistory.of_renderStable
