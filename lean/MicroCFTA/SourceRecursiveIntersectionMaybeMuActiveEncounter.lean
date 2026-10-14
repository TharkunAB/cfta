import MicroCFTA.SourceRecursiveIntersectionMaybeMuCoverage
import MicroCFTA.InternedFreshOrdinaryActiveSite
import MicroCFTA.InternedFreshOrdinaryJointMismatch

/-!
# Full repaired active source paths for actual optional binders

The source body's available leaves determine its actual captured values.
The existing semantic source context supplies both repaired heaps.
A pending result derives the ancestor's actual callbacks, raw Depth body,
and full descendant path. No path, callback execution, or origin is supplied.
-/
namespace MicroCFTA.SourceRecursiveIntersectionMaybeMu
open Cache InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedStoredSubstitution InternedStoredSubstitutionRebind
open InternedBinderProtocol (NodeKey)

/-- An actual pending optional binder derives its full repaired active ancestor and source path for arbitrary captured values. -/
theorem active_pending_encounter [DecidableEq (EdgeKey Symbol Guard)] (pair : Nat × Nat) (body : Value Symbol Guard)
    (state final : State Symbol Guard) (key : NodeKey)
    (context : InternedFreshOrdinaryContext.Context state environment) (available : Available state body)
    (covered : Covered [] state) (stopped : maybeMu pair body state = .pending key final) :
    InternedFreshOrdinaryActiveEncounter.Encounter key final := by
  have leavesContext : InternedFreshOrdinaryContext.Context state (leaves body) :=
    ⟨context.normal, leaves_available body state available, context.profiles, context.freeNames⟩
  rw [maybeMu_eq pair body state state context.normal.facts available] at stopped
  split at stopped
  · exact InternedFreshOrdinaryActiveEncounter.complete_encounter _ (leaves body) state leavesContext covered key final stopped
  · cases stopped

/-- The actual pending constructor derives one source path with both exact original ancestor probes. -/
theorem active_pending_site [DecidableEq (EdgeKey Symbol Guard)] (pair : Nat × Nat) (body : Value Symbol Guard)
    (state final : State Symbol Guard) (key : NodeKey)
    (context : InternedFreshOrdinaryContext.Context state environment) (available : Available state body)
    (covered : Covered [] state) (stopped : maybeMu pair body state = .pending key final) :
    ∃ origin : InternedFreshOrdinaryActiveOrigins.Origin Symbol Guard key,
      Nonempty (InternedFreshOrdinaryActiveSite.Site origin final) :=
  InternedFreshOrdinaryActiveSite.encounter_site key final
    (active_pending_encounter pair body state final key context available covered stopped)

/-- An actual pending optional binder derives an earlier completed route and its live ordinary mismatch. -/
theorem active_pending_mismatch [DecidableEq (EdgeKey Symbol Guard)] (pair : Nat × Nat) (body : Value Symbol Guard)
    (state final : State Symbol Guard) (key : NodeKey)
    (context : InternedFreshOrdinaryContext.Context state environment) (available : Available state body)
    (covered : Covered [] state) (stopped : maybeMu pair body state = .pending key final) :
    ∃ origin : InternedFreshOrdinaryActiveOrigins.Origin Symbol Guard key,
      ∃ site : InternedFreshOrdinaryActiveSite.Site origin final,
        InternedFreshOrdinaryJointMismatch.Mismatch site := by
  obtain ⟨origin, ⟨site⟩⟩ := active_pending_site pair body state final key context available covered stopped
  exact ⟨origin, site, InternedFreshOrdinaryJointMismatch.Site.mismatch site⟩

end MicroCFTA.SourceRecursiveIntersectionMaybeMu
