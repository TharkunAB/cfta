import MicroCFTA.InternedProfileComposition
import MicroCFTA.InternedRootProfileReflection

/-!
# Finite tracked root references

Keep pure root references only when every name is tracked. Other nonempty
root alternatives are opaque. An empty tracking list retains only Empty.
Nested scopes can extend the list with a fresh available local marker.
-/
namespace MicroCFTA.SourceCurrentTrackedRootProfile
open InternedConstructorTemplates InternedRootProfile
open InternedBinderProtocol (Reference)
open InternedProfileSemantics (isEmpty)

/-- Keep a pure root profile only when every root name is tracked. -/
def mask (markers : List Reference) : Profile → Profile
  | none => none
  | some names => if names.all markers.contains then some names else none

/-- Observe tracked literal root references and opacity in one value. -/
def observe (markers : List Reference) (value : Value Symbol Guard) : Profile := mask markers (profile value)

/-- Values agree on tracked root reference sets and on opacity. -/
def Related (markers : List Reference) (first second : Value Symbol Guard) : Prop :=
  Equivalent (observe markers first) (observe markers second)

/-- Every value has the same tracked root profile as itself. -/
theorem Related.refl (markers : List Reference) (value : Value Symbol Guard) : Related markers value value :=
  InternedProfileEquivalence.refl _

/-- Reversing a tracked comparison retains its profile equivalence. -/
theorem Related.symm {markers : List Reference} {first second : Value Symbol Guard}
    (same : Related markers first second) : Related markers second first :=
  InternedProfileEquivalence.symm same

/-- Tracking changes no physical empty-list profile decision. -/
theorem mask_empty (markers : List Reference) (value : Profile) : isEmpty (mask markers value) = isEmpty value := by
  cases value with
  | none => rfl
  | some names =>
      cases names with
      | nil => rfl
      | cons first rest =>
          simp only [mask]
          split <;> rfl

end MicroCFTA.SourceCurrentTrackedRootProfile
