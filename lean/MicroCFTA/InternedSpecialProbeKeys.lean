import MicroCFTA.InternedProfileTraceSites
import MicroCFTA.InternedCallbackTransport
import MicroCFTA.InternedSourceProbeTags

/-!
# Exact source keys for the two smart-empty callback classes

The source probes determine these keys before reservation. The proof uses
full nested syntax profiles and actual normalized record reflection.
Captured sentinel aliases do not add a third key to these classes.
-/
namespace MicroCFTA.InternedSpecialProbeKeys
open Cache InternedConstructorTemplates InternedNestedConstruction InternedNestedMissReadback InternedNestedSpecialization
open InternedProbeProvenance InternedNestedProvenance InternedStoredMuOrigins
open InternedRootProfile InternedProfileSemantics InternedProfileCallbackForm
open InternedProfileEquivalence InternedActualProbeTags InternedTwoProbeProfiles
open InternedCallbackTransport InternedProfileTraceSites
open InternedBinderProtocol (Reference NodeKey NodeRef)

/-- The argument-use flag selects the two canonical smart-empty probe pairs. -/
def key (uses : Bool) : NodeKey :=
  if uses then .mu ⟨.ref .depth, .ref (.uninterned 0)⟩ else .mu ⟨.empty, .empty⟩

/-- The symbolic body has no captured root reference. -/
def Classified (body : Syntax Symbol Guard) (environment : List Profile) (uses : Bool) : Prop :=
  ∃ names, symbolic body environment = some names ∧ captures names = [] ∧ usesArgument names = uses

/-- The two exact canonical pairs have different keys. -/
theorem key_injective : Function.Injective key := by
  intro first second same
  cases first <;> cases second <;> simp_all [key]

/-- Actual normalized probes reflect the symbolic no-capture class exactly. -/
theorem profiles_classified (body : Syntax Symbol Guard) (environment : List Profile)
    (depth ordinary : Value Symbol Guard) (state : State Symbol Guard) (normal : Normal state)
    (depthAvailable : Available state depth) (ordinaryAvailable : Available state ordinary)
    (depthSame : Equivalent (profile depth) (normalize .depth (evaluate body (some [.depth] :: environment))))
    (ordinarySame : Equivalent (profile ordinary)
      (normalize (.uninterned depth.depth) (evaluate body (some [.uninterned depth.depth] :: environment))))
    (uses : Bool) : muKey depth ordinary = key uses ↔ Classified body environment uses := by
  have keysEmpty : muKey depth ordinary = key false ↔ depth = .empty ∧ ordinary = .empty := by
    simp only [muKey, key, Bool.false_eq_true, ↓reduceIte, NodeKey.mu.injEq, InternedBinderProtocol.MuKey.mk.injEq]
    rw [InternedEmptyNormalization.reference_empty, InternedEmptyNormalization.reference_empty]
  have keysSelf : muKey depth ordinary = key true ↔ depth = .reference .depth ∧ ordinary = .reference (.uninterned depth.depth) := by
    have reference : ∀ (value : Value Symbol Guard) name, value.referenceOf = .ref name ↔ value = .reference name := by
      intro value name
      cases value <;> simp [Value.referenceOf]
    simp only [muKey, key, ↓reduceIte, NodeKey.mu.injEq, InternedBinderProtocol.MuKey.mk.injEq, reference]
    constructor
    · rintro ⟨rfl, same⟩; exact ⟨rfl, same⟩
    · rintro ⟨rfl, same⟩; exact ⟨rfl, same⟩
  cases computed : symbolic body environment with
  | none =>
      have depthHidden : profile depth = none := depthSame.1.mpr (by rw [opaque_form body environment computed]; rfl)
      have hidden := opaque_tags depth .depth depthHidden
      have notClassified : ¬ Classified body environment uses := by
        rintro ⟨names, form, _, _⟩
        rw [computed] at form
        cases form
      cases uses <;> simp only [keysEmpty, keysSelf, hidden.1, hidden.2, false_and, notClassified]
  | some names =>
      have form : ∀ name, Equivalent (normalize name (evaluate body (some [name] :: environment)))
          (probe (captures names) (usesArgument names) name) :=
        fun name => normalize_same name (pure_form body environment names computed name)
      have depthForm := trans depthSame (form .depth)
      have ordinaryForm := trans ordinarySame (form (.uninterned depth.depth))
      have classified : Classified body environment uses ↔ captures names = [] ∧ usesArgument names = uses := by
        constructor
        · rintro ⟨other, shape, captured, used⟩
          have same : other = names := Option.some.inj (shape.symm.trans computed)
          simpa only [same] using And.intro captured used
        · rintro ⟨captured, used⟩
          exact ⟨names, computed, captured, used⟩
      rw [classified]
      cases uses with
      | false =>
          rw [keysEmpty, empty_form depth state normal depthAvailable _ _ _ depthForm,
            empty_form ordinary state normal ordinaryAvailable _ _ _ ordinaryForm]
          exact ⟨And.left, fun same => ⟨same, same⟩⟩
      | true =>
          rw [keysSelf, self_form depth state normal depthAvailable _ _ _ depthForm,
            self_form ordinary state normal ordinaryAvailable _ _ _ ordinaryForm]
          exact two_single _ _ _ _ (by simp)

/-- Two completed actual source callbacks derive their canonical key class. -/
theorem source_classified [DecidableEq (EdgeKey Symbol Guard)] (body : Syntax Symbol Guard)
    (environment : List (Value Symbol Guard)) (before afterDepth final : State Symbol Guard)
    (context : Context before environment) (depth ordinary : Value Symbol Guard)
    (depthDone : callback body environment .depth before = .done depth afterDepth)
    (ordinaryDone : callback body environment (.uninterned depth.depth) afterDepth = .done ordinary final)
    (uses : Bool) : muKey depth ordinary = key uses ↔ Classified body (environment.map profile) uses := by
  have all : Values before (.reference .depth :: environment) := context.depth.inputs
  have verified := callback_verified body environment .depth before context.normal.facts all
  obtain ⟨depthNormal, depthAvailable, depthSame⟩ := callback_completed body environment .depth before
    context.normal context.inputs (depth_available before) context.heap depth afterDepth depthDone
  have afterInputs : Values afterDepth environment := fun value member => by
    simpa only [depthDone, Outcome.state] using verified.available value (context.inputs value member)
  have afterHeap : InternedProfileHeap.Heap afterDepth := by
    simpa only [depthDone, Outcome.state] using
      (InternedSourceProbeTags.callback_profile body environment .depth before context.normal all context.heap).heap
  obtain ⟨finalNormal, ordinaryAvailable, ordinarySame⟩ := callback_completed body environment (.uninterned depth.depth) afterDepth
    depthNormal afterInputs (ordinary_available afterDepth depth.depth) afterHeap ordinary final ordinaryDone
  have ordinaryInputs : Values afterDepth (.reference (.uninterned depth.depth) :: environment) := by
    intro value member
    rcases List.mem_cons.mp member with rfl | member
    · exact ordinary_available afterDepth depth.depth
    · exact afterInputs value member
  have ordinaryVerified := callback_verified body environment (.uninterned depth.depth) afterDepth depthNormal.facts ordinaryInputs
  have finalDepth : Available final depth := by
    simpa only [ordinaryDone, Outcome.state] using ordinaryVerified.available depth depthAvailable
  exact profiles_classified body _ depth ordinary final finalNormal finalDepth ordinaryAvailable depthSame ordinarySame uses

/-- A completed source request leaves its complete payload installed. -/
theorem request_complete [DecidableEq (EdgeKey Symbol Guard)] (smart : Bool) (depth ordinary : Value Symbol Guard)
    (invoke : Reference → State Symbol Guard → Outcome Symbol Guard (Value Symbol Guard))
    (before final : State Symbol Guard) (value : Value Symbol Guard)
    (completed : request smart depth ordinary invoke before = .done value final) :
    ∃ record, final.nodeRecords (muKey depth ordinary) = some record := by
  cases found : before.nodes.table (muKey depth ordinary) with
  | some entry =>
      cases stored : before.nodeRecords (muKey depth ordinary) with
      | none => simp [request, found, stored] at completed
      | some record =>
          simp only [request, found, stored, Outcome.done.injEq] at completed
          rcases completed with ⟨_, rfl⟩
          exact ⟨record, stored⟩
  | none =>
      simp only [request, found] at completed
      obtain ⟨body, afterBody, _, assembled⟩ := bind_done _ _ _ _ completed
      obtain ⟨_, rfl⟩ := Outcome.done.inj assembled
      exact keepFirst_present _ _ _

/-- A completed source binder installs every special key selected by its symbolic body. -/
theorem build_complete [DecidableEq (EdgeKey Symbol Guard)] (smart : Bool) (body : Syntax Symbol Guard)
    (environment : List (Value Symbol Guard)) (before final : State Symbol Guard)
    (context : Context before environment) (value : Value Symbol Guard)
    (completed : build (.binder smart body) environment before = .done value final)
    (uses : Bool) (classified : Classified body (environment.map profile) uses) :
    ∃ record, final.nodeRecords (key uses) = some record := by
  rw [build] at completed
  obtain ⟨depth, afterDepth, depthDone, later⟩ := bind_done _ _ _ _ completed
  obtain ⟨ordinary, afterOrdinary, ordinaryDone, requested⟩ := bind_done _ _ _ _ later
  have keySame := (source_classified body environment before afterDepth afterOrdinary context depth ordinary depthDone ordinaryDone uses).mpr classified
  rw [← keySame]
  exact request_complete smart depth ordinary _ afterOrdinary final value requested

end MicroCFTA.InternedSpecialProbeKeys
