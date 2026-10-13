import MicroCFTA.InternedProfileCandidate
import MicroCFTA.InternedRootProfileCleanup
import MicroCFTA.InternedFreshOrdinaryProfileHeap

/-!
# A repaired recursive miss establishes its profile invariant

The actual three normalized body calls supply their recursive profile
results. The source syntax determines one symbolic callback form. Actual
smart cleanup has its capture profile, and the ordered probe pair decodes
that same profile. No whole-callback equality law is assumed.
-/
namespace MicroCFTA.InternedFreshOrdinaryProfileCandidate
open Cache InternedConstructorTemplates InternedNestedConstruction InternedProbeProvenance
open InternedStoredMuOrigins InternedRootProfile InternedProfileSemantics
open InternedProfileCallbackForm InternedProfileOrigins InternedRootProfileCleanup
open InternedProfileEquivalence InternedProbeDecoder InternedSyntaxProbeDecoder
open InternedFreshOrdinaryConstruction (ordinaryLevel)
open InternedBinderProtocol (Reference NodeKey)

/-- Three actual recursive profile results establish both the stored candidate invariant and its returned profile. -/
theorem candidate (expression : Syntax Symbol Guard) (environment : List Profile) (smart : Bool)
    (entry : Interned NodeKey) (body depth ordinary : Value Symbol Guard)
    (state : State Symbol Guard) (normal : Normal state) (available : Available state body)
    (fresh : ∀ captured ∈ environment, .interned entry.identity ∉ captured.getD [])
    (depthSame : Equivalent (profile depth) (normalize .depth (evaluate expression (some [.depth] :: environment))))
    (ordinarySame : Equivalent (profile ordinary)
      (normalize (.uninterned (ordinaryLevel depth)) (evaluate expression (some [.uninterned (ordinaryLevel depth)] :: environment))))
    (bodySame : Equivalent (profile body)
      (normalize (.interned entry.identity) (evaluate expression (some [.interned entry.identity] :: environment)))) :
    InternedFreshOrdinaryProfileHeap.Correct entry body depth ordinary ∧
      Equivalent (profile (finish smart (.mu entry body depth ordinary))) (evaluate (.binder smart expression) environment) := by
  have bodyResult := InternedProfileCandidate.smart_evaluate expression environment entry body depth ordinary state normal available fresh bodySame
  have decoded := trans (decode_same .depth (.uninterned (ordinaryLevel depth)) depthSame ordinarySame)
    (source_evaluate_decoded expression environment (ordinaryLevel depth))
  refine ⟨trans bodyResult (symm decoded), ?_⟩
  cases smart with
  | false => simp [finish, profile, evaluate, Equivalent]
  | true => exact bodyResult

end MicroCFTA.InternedFreshOrdinaryProfileCandidate
