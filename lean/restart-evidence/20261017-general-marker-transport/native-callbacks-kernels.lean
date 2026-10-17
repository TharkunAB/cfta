import MicroCFTA.SourceCurrentConstrainedCapNativeCallbacks

set_option linter.all true
set_option pp.explicit true
set_option pp.proofs true
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000
set_option format.width 200

namespace MicroCFTA.NativeCallbackKernels
open Cache InternedConstructorTemplates InternedProbeProvenance
open InternedNestedConstruction (Outcome)
open InternedBinderProtocol (Reference)
open SourceCurrentConstrainedCap (Cap)
open SourceCurrentConstrainedCapPairOccurrences (Classified)
open SourceCurrentConstrainedCapPairOccurrenceCallbacks (mark)
open SourceCurrentHereditaryConstruction (MuStored)
open SourceEqualityRequiredCache (Ready Keeps)

/-- Initial data constructs two successive general callbacks through their actual changed caches. -/
theorem serial {Symbol Guard : Type} [DecidableEq (EdgeKey Symbol Guard)]
    (annotation : Guard → Prop) (depth : Nat) (body : Value Symbol Guard) (old first second : Reference)
    (state : State Symbol Guard) (ready : Ready state) (available : Available state body)
    (firstAvailable : Available state (.reference first)) (secondAvailable : Available state (.reference second))
    (bounded : Cap annotation depth body) (stored : MuStored annotation state)
    (weight : Reference → Nat) (bound : Nat) (oldWeight : weight old = bound)
    (classified : Classified weight bound body) (firstFresh : first ∉ body.free) (secondFresh : second ∉ body.free) :
    ∃ left middle right final,
      SourceRecursiveIntersectionMaybeMu.callback old body first state = .done left middle ∧
      SourceRecursiveIntersectionMaybeMu.callback old body second middle = .done right final ∧
      Cap annotation depth left ∧ Cap annotation depth right ∧
      Classified (mark weight first bound) bound left ∧ Classified (mark weight second bound) bound right ∧
      MuStored annotation final ∧ Keeps state final := by
  obtain ⟨left, middle, firstDone, firstCap, firstClassified, middleStored, _, firstEffects, _⟩ :=
    SourceCurrentConstrainedCapNativeCallbacks.complete annotation depth body old first state ready available firstAvailable
      bounded stored weight bound oldWeight classified firstFresh
  obtain ⟨right, final, secondDone, secondCap, secondClassified, finalStored, _, secondEffects, _⟩ :=
    SourceCurrentConstrainedCapNativeCallbacks.complete annotation depth body old second middle firstEffects.ready
      (firstEffects.available body available) (firstEffects.available (.reference second) secondAvailable)
      bounded middleStored weight bound oldWeight classified secondFresh
  exact ⟨left, middle, right, final, firstDone, secondDone, firstCap, secondCap, firstClassified, secondClassified,
    finalStored, firstEffects.trans secondEffects⟩

#print axioms serial
#check @serial
end MicroCFTA.NativeCallbackKernels
