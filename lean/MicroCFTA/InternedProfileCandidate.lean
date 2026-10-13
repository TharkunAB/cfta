import MicroCFTA.InternedRootProfileCleanup
import MicroCFTA.InternedProfileHeap

/-!
# The local recursive miss establishes its profile invariant

The actual three normalized body calls supply their recursive profile
results. The source syntax determines one symbolic callback form. Actual
smart cleanup has its capture profile, and the ordered probe pair decodes
that same profile. No whole-callback equality law is assumed.
-/
namespace MicroCFTA.InternedProfileCandidate
open Cache InternedConstructorTemplates InternedNestedConstruction InternedProbeProvenance
open InternedStoredMuOrigins InternedRootProfile InternedProfileSemantics
open InternedProfileCallbackForm InternedProfileOrigins InternedRootProfileCleanup
open InternedProfileEquivalence InternedProbeDecoder InternedSyntaxProbeDecoder
open InternedBinderProtocol (Reference NodeKey)

/-- The actual normalized fresh body determines the original smart-binder interpretation. -/
theorem smart_evaluate (expression : Syntax Symbol Guard) (environment : List Profile)
    (entry : Interned NodeKey) (body depth ordinary : Value Symbol Guard)
    (state : State Symbol Guard) (normal : Normal state) (available : Available state body)
    (fresh : ∀ captured ∈ environment, .interned entry.identity ∉ captured.getD [])
    (bodySame : Equivalent (profile body)
      (normalize (.interned entry.identity) (evaluate expression (some [.interned entry.identity] :: environment)))) :
    Equivalent (profile (finish true (.mu entry body depth ordinary))) (evaluate (.binder true expression) environment) := by
  cases computed : symbolic expression environment with
  | none =>
      have actual := opaque_form expression environment computed (.interned entry.identity)
      have hidden : profile body = none := bodySame.1.mpr (by rw [actual]; rfl)
      have result : evaluate (.binder true expression) environment = none := by
        rw [evaluate]
        change lower (symbolic expression environment) = none
        rw [computed]
        rfl
      rw [opaque_finish entry body depth ordinary hidden, result]
      exact refl _
  | some names =>
      have localFresh := captures_fresh expression environment names computed (.interned entry.identity) fresh
      have bodyForm := normalize_same (.interned entry.identity)
        (pure_form expression environment names computed (.interned entry.identity))
      have actual := smart_profile entry body depth ordinary state normal available (captures names)
        (usesArgument names) localFresh (trans bodySame bodyForm)
      have result : evaluate (.binder true expression) environment = some (captures names) := by
        rw [evaluate]
        change lower (symbolic expression environment) = some (captures names)
        rw [computed]
        simp only [lower, captures]
        congr 1
        apply congrArg (fun function => names.filterMap function)
        funext name
        cases name <;> rfl
      rw [result]
      exact actual

/-- Three actual recursive profile results establish both the stored candidate invariant and its returned profile. -/
theorem candidate (expression : Syntax Symbol Guard) (environment : List Profile) (smart : Bool)
    (entry : Interned NodeKey) (body depth ordinary : Value Symbol Guard)
    (state : State Symbol Guard) (normal : Normal state) (available : Available state body)
    (fresh : ∀ captured ∈ environment, .interned entry.identity ∉ captured.getD [])
    (depthSame : Equivalent (profile depth) (normalize .depth (evaluate expression (some [.depth] :: environment))))
    (ordinarySame : Equivalent (profile ordinary)
      (normalize (.uninterned depth.depth) (evaluate expression (some [.uninterned depth.depth] :: environment))))
    (bodySame : Equivalent (profile body)
      (normalize (.interned entry.identity) (evaluate expression (some [.interned entry.identity] :: environment)))) :
    InternedProfileHeap.Correct entry body depth ordinary ∧
      Equivalent (profile (finish smart (.mu entry body depth ordinary))) (evaluate (.binder smart expression) environment) := by
  have bodyResult := smart_evaluate expression environment entry body depth ordinary state normal available fresh bodySame
  have decoded := trans (decode_same .depth (.uninterned depth.depth) depthSame ordinarySame)
    (source_evaluate_decoded expression environment depth.depth)
  refine ⟨trans bodyResult (symm decoded), ?_⟩
  cases smart with
  | false => simp [finish, profile, evaluate, Equivalent]
  | true => exact bodyResult

end MicroCFTA.InternedProfileCandidate
