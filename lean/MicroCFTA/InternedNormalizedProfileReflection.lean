import MicroCFTA.InternedProfileRenaming
import MicroCFTA.InternedRootProfileReflection

/-!
# Actual empty and direct-local reflection from mapped body profiles

The complete syntax interpretation commutes with external-name maps.
Actual normalized source values therefore agree on EmptyNode and on their
paired bare locals when their checked profiles follow that interpretation.
Other captured names may merge under the map.
-/
namespace MicroCFTA.InternedNormalizedProfileReflection
open InternedConstructorTemplates InternedNestedConstruction InternedProbeProvenance
open InternedStoredMuOrigins InternedRootProfile InternedProfileSemantics
open InternedProfileRenaming InternedProfileComposition InternedRootProfileNode InternedRootProfileReflection
open InternedBinderProtocol (Reference)

/-- Two checked normalized source results reflect emptiness and their exact paired bare locals. -/
theorem reflects (expression : Syntax Symbol Guard) (function : Reference → Reference)
    (firstName secondName : Reference) (localName : ∀ name, function name = secondName ↔ name = firstName)
    (firstEnvironment secondEnvironment : List Profile)
    (mapped : secondEnvironment = firstEnvironment.map (mapNames function))
    (first second : Value Symbol Guard) (left right : State Symbol Guard)
    (ln : Normal left) (rn : Normal right) (la : Available left first) (ra : Available right second)
    (firstSame : Equivalent (profile first)
      (normalize firstName (evaluate expression (some [firstName] :: firstEnvironment))))
    (secondSame : Equivalent (profile second)
      (normalize secondName (evaluate expression (some [secondName] :: secondEnvironment)))) :
    (first.referenceOf = .empty ↔ second.referenceOf = .empty) ∧
      (first = .reference firstName ↔ second = .reference secondName) := by
  have mappedBody := body_mapped expression function firstName secondName ((localName firstName).mpr rfl)
    firstEnvironment secondEnvironment mapped
  rw [mappedBody] at secondSame
  have normalized := normalized_reflections function firstName secondName localName
    (evaluate expression (some [firstName] :: firstEnvironment))
  constructor
  · rw [InternedEmptyNormalization.reference_empty, InternedEmptyNormalization.reference_empty,
      ← profile_empty_iff first left ln.proper la, ← profile_empty_iff second right rn.proper ra]
    exact (empty_same firstSame).trans (normalized.1.trans (empty_same secondSame).symm)
  · rw [← profile_single_iff first left ln la firstName, ← profile_single_iff second right rn ra secondName]
    exact (single_equivalent firstName firstSame).trans
      (normalized.2.trans (single_equivalent secondName secondSame).symm)

end MicroCFTA.InternedNormalizedProfileReflection
