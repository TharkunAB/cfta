import MicroCFTA.SourcePruningEnumerationOpaqueSuffixIsolation
import MicroCFTA.SourcePruningEnumerationIsolationReads

namespace MicroCFTA.EnumerationDischargeHistory
open EnumerationState EnumerationSchedule EnumerationDependencies EnumerationDriver
local notation "Symbol" => SourcePruningTemplates.Symbol
variable {Guard : Type}
set_option autoImplicit false

/- Stable rendering retains held and expanded payloads without an ancestry condition. -/
theorem HeldFragmentHistory.of_renderStable
    (held handle : Nat) (before after : State Symbol Guard) (_safe : Safe before)
    (isolated : IsolatedPending held handle before) (stable : RenderStable before after) :
    HeldFragmentHistory held handle before after
 := by
  have isolatedAfter := isolated.through_renderStable stable
  refine ⟨isolatedAfter, ?_, ?_, ?_⟩
  · exact ⟨congrArg (fun values => values[held]?) stable.values,
      isolatedAfter.root, stable.classes held⟩
  · intro slot fragment stored
    have afterStored : after.values[slot]? = some (.enumerated fragment) := by
      rw [stable.values]
      exact stored
    exact ⟨congrArg (fun values => values[slot]?) stable.values,
      (enumerated_root after stable.safe slot fragment afterStored).2, stable.classes slot⟩
  · intro slot fragment stored
    rw [stable.values] at stored
    exact Or.inl stored

end MicroCFTA.EnumerationDischargeHistory
