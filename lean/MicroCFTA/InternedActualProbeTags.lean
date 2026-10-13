import MicroCFTA.InternedNestedProfiles
import MicroCFTA.InternedRootProfileReflection

/-!
# Exact empty and direct-self body tags from source probe profiles

The complete syntax model supplies the captured-reference form. Available
source records reflect empty and singleton profiles into exact records.
Two distinct sentinels then determine the actual body's two cleanup tags.
-/
namespace MicroCFTA.InternedActualProbeTags
open Cache InternedConstructorTemplates InternedNestedConstruction InternedProbeProvenance
open InternedStoredMuOrigins InternedRootProfile InternedProfileSemantics
open InternedProfileCallbackForm InternedProfileOrigins InternedProfileEquivalence
open InternedRootProfileNode InternedRootProfileReflection InternedTwoProbeProfiles
open InternedBinderProtocol (Reference NodeKey)

/-- These exact body records are determined by the two actual normalized probe records. -/
def Tags (entry : Interned NodeKey) (body depth ordinary : Value Symbol Guard) : Prop :=
  (body = .empty ↔ depth = .empty ∧ ordinary = .empty) ∧
    (body = .reference (.interned entry.identity) ↔
      depth = .reference .depth ∧ ordinary = .reference (.uninterned depth.depth))

/-- Equivalent profiles agree on whether their only root name is the selected reference. -/
theorem single_equivalent (name : Reference) {first second : Profile} (same : Equivalent first second) :
    Single name (first.getD []) ↔ Single name (second.getD []) := by
  constructor
  · intro selected
    exact ⟨(same.2 name).mp selected.1, fun other member => selected.2 other ((same.2 other).mpr member)⟩
  · intro selected
    exact ⟨(same.2 name).mpr selected.1, fun other member => selected.2 other ((same.2 other).mp member)⟩

/-- An actual empty record reflects the empty case of its source pure callback form. -/
theorem empty_form (value : Value Symbol Guard) (state : State Symbol Guard) (normal : Normal state)
    (available : Available state value) (captured : List Reference) (uses : Bool) (argument : Reference)
    (same : Equivalent (profile value) (probe captured uses argument)) :
    value = .empty ↔ captured = [] ∧ uses = false := by
  rw [← profile_empty_iff value state normal.proper available, InternedProfileComposition.empty_same same,
    probe_empty]

/-- Exact bare-reference identity reflects the selected singleton callback profile. -/
theorem self_form (value : Value Symbol Guard) (state : State Symbol Guard) (normal : Normal state)
    (available : Available state value) (captured : List Reference) (uses : Bool) (argument : Reference)
    (same : Equivalent (profile value) (probe captured uses argument)) :
    value = .reference argument ↔ Single argument ((probe captured uses argument).getD []) := by
  rw [← profile_single_iff value state normal available argument]
  exact single_equivalent argument same

/-- An opaque profile excludes both exact cleanup tags. -/
theorem opaque_tags (value : Value Symbol Guard) (name : Reference) (hidden : profile value = none) :
    value ≠ .empty ∧ value ≠ .reference name := by
  constructor
  · intro same
    simp [same, profile] at hidden
  · intro same
    simp [same, profile] at hidden

/-- Three recursive source profile results determine both exact stored-body cleanup tags. -/
theorem from_profiles (expression : Syntax Symbol Guard) (environment : List Profile)
    (entry : Interned NodeKey) (body depth ordinary : Value Symbol Guard)
    (state : State Symbol Guard) (normal : Normal state)
    (bodyAvailable : Available state body) (depthAvailable : Available state depth) (ordinaryAvailable : Available state ordinary)
    (fresh : ∀ captured ∈ environment, .interned entry.identity ∉ captured.getD [])
    (depthSame : Equivalent (profile depth) (normalize .depth (evaluate expression (some [.depth] :: environment))))
    (ordinarySame : Equivalent (profile ordinary)
      (normalize (.uninterned depth.depth) (evaluate expression (some [.uninterned depth.depth] :: environment))))
    (bodySame : Equivalent (profile body)
      (normalize (.interned entry.identity) (evaluate expression (some [.interned entry.identity] :: environment)))) :
    Tags entry body depth ordinary := by
  cases computed : symbolic expression environment with
  | none =>
      have bodyHidden : profile body = none := bodySame.1.mpr (by rw [opaque_form expression environment computed]; rfl)
      have depthHidden : profile depth = none := depthSame.1.mpr (by rw [opaque_form expression environment computed]; rfl)
      have bodyTags := opaque_tags body (.interned entry.identity) bodyHidden
      have depthTags := opaque_tags depth .depth depthHidden
      simp [Tags, bodyTags.1, bodyTags.2, depthTags.1, depthTags.2]
  | some names =>
      let captured := captures names
      let uses := usesArgument names
      have form : ∀ name, Equivalent (normalize name (evaluate expression (some [name] :: environment))) (probe captured uses name) :=
        fun name => normalize_same name (pure_form expression environment names computed name)
      have bodyForm := trans bodySame (form (.interned entry.identity))
      have depthForm := trans depthSame (form .depth)
      have ordinaryForm := trans ordinarySame (form (.uninterned depth.depth))
      constructor
      · rw [empty_form body state normal bodyAvailable captured uses _ bodyForm,
          empty_form depth state normal depthAvailable captured uses _ depthForm,
          empty_form ordinary state normal ordinaryAvailable captured uses _ ordinaryForm]
        exact ⟨fun same => ⟨same, same⟩, And.left⟩
      · rw [self_form body state normal bodyAvailable captured uses _ bodyForm,
          self_form depth state normal depthAvailable captured uses _ depthForm,
          self_form ordinary state normal ordinaryAvailable captured uses _ ordinaryForm]
        exact source_body_self_iff captured uses entry.identity depth.depth
          (captures_fresh expression environment names computed (.interned entry.identity) fresh)

end MicroCFTA.InternedActualProbeTags
