import MicroCFTA.SourceEqualityRequiredCache
import MicroCFTA.InternedRecordDepthSource
import MicroCFTA.InternedStoredSubstitutionScope

/-!
# Pure physical Empty tests for complete stored execution

The test evaluates the full encoded source plan with resolved capture
profiles. A closed value remains a literal capture. An open Mu uses its
full stored body under a smart binder. The test does not replace that body
with the original Mu's decoded shape. Source and filter fusion is separate.
-/
namespace MicroCFTA.SourceCurrentStoredEmptyInterpreter
open Cache InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedNestedConstruction (Outcome)
open InternedFreshOrdinaryConstruction (build)
open InternedFreshOrdinaryStoredSubstitution (execute)
open InternedStoredSubstitution (Environment Replacements leaves input encode inputs_available)
open InternedRootProfile (profile)
open SourceEqualityRequiredCache (Ready)
open InternedBinderProtocol (Reference NodeKey)

/-- Interpret the complete stored plan after its reference captures are resolved. -/
def test (value : Value Symbol Guard) (environment : Environment Symbol Guard) : Bool :=
  InternedProfileSemantics.isEmpty (InternedProfileSemantics.evaluate
    (encode (leaves value) [] value) ((leaves value).map (fun leaf => profile (input environment leaf))))

/-- The literal closed shortcut retains the original capture's root profile. -/
theorem closed (value : Value Symbol Guard) (environment : Environment Symbol Guard)
    (closed : value.free = []) : test value environment = InternedProfileSemantics.isEmpty (profile value) := by
  unfold test
  simp only [leaves.eq_def,closed,List.isEmpty_nil,ite_true,encode.eq_def,List.length_nil,Nat.zero_add]
  simp only [InternedStoredSubstitution.slot,List.findIdx_cons,beq_self_eq_true,ite_true]
  simp [InternedProfileSemantics.evaluate,InternedStoredSubstitutionScope.input_closed value environment closed]

/-- A reference tests its actual optional replacement or its original literal reference. -/
theorem reference (name : Reference) (environment : Environment Symbol Guard) :
    test (.reference name) environment =
      InternedProfileSemantics.isEmpty (profile ((environment name).getD (.reference name))) := by
  simp [test,leaves.eq_def,encode.eq_def,Value.free,InternedStoredSubstitution.slot,
    input,InternedProfileSemantics.evaluate]

/-- An open stored Mu evaluates its full encoded body with the fresh symbolic local. -/
theorem open_mu (entry : Interned NodeKey) (body depth ordinary : Value Symbol Guard)
    (environment : Environment Symbol Guard)
    (opened : (Value.mu entry body depth ordinary).free.isEmpty = false) :
    test (.mu entry body depth ordinary) environment =
      InternedProfileSemantics.isEmpty (InternedProfileSemantics.lower
        (InternedProfileSemantics.evaluate
          (encode (leaves body) [.interned entry.identity] body)
          (some [Sum.inl ()] :: ((leaves body).map (fun leaf => profile (input environment leaf))).map
            (InternedProfileSemantics.mapNames Sum.inr)))) := by
  have captured : leaves (.mu entry body depth ordinary) = leaves body := by
    rw [leaves.eq_def]
    simp only [opened,Bool.false_eq_true,ite_false]
  have plan : encode (leaves body) [] (.mu entry body depth ordinary) =
      .binder true (encode (leaves body) [.interned entry.identity] body) := by
    rw [encode.eq_def]
    simp only [opened,Bool.false_eq_true,ite_false]
  unfold test
  rw [captured,plan,InternedProfileSemantics.evaluate]

/-- Actual repaired stored execution has exactly the pure plan's physical Empty test. -/
theorem execute_test [DecidableEq (EdgeKey Symbol Guard)]
    (value : Value Symbol Guard) (environment : Environment Symbol Guard)
    (before : State Symbol Guard) (ready : Ready before) (available : Available before value)
    (replacements : Replacements before environment) (result : Value Symbol Guard) (after : State Symbol Guard)
    (actual : execute value environment before = .done result after) :
    (result.referenceOf == .empty) = test value environment := by
  let inputs := (leaves value).map (input environment)
  let plan := encode (leaves value) [] value
  have context : InternedFreshOrdinaryContext.Context before inputs :=
    ⟨ready.semantic.1.normal,inputs_available value environment before available replacements,
      ready.semantic.1.profiles,ready.semantic.1.freeNames⟩
  have called : build plan inputs before = .done result after := actual
  have kept : InternedFreshOrdinaryContext.Context after inputs := by
    simpa only [called,Outcome.state] using context.build plan
  have output := (InternedFreshOrdinaryFacts.build_verified plan inputs before context.normal.facts
    context.inputs).result result after called
  have matched := (InternedFreshOrdinaryProfiles.build_profile plan inputs before context.normal context.inputs
    context.profiles).result result after called
  rw [← InternedRootProfileNode.isEmpty_profile result after kept.normal.proper output]
  simpa only [test,inputs,plan,List.map_map,Function.comp_def] using
    InternedProfileComposition.isEmpty_same matched

end MicroCFTA.SourceCurrentStoredEmptyInterpreter
