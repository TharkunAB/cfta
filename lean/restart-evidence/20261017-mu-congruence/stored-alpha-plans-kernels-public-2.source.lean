import MicroCFTA.SourceCurrentStoredAlphaPlans
import MicroCFTA.InternedFreshOrdinaryFacts
import MicroCFTA.InternedFreshOrdinaryDepthHeap

set_option linter.all true
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000

namespace MicroCFTA.StoredAlphaPlanKernels
open Cache InternedConstructorTemplates InternedProbeProvenance InternedRecordCoherence
open InternedNestedConstruction (Syntax Outcome)
open InternedFreshOrdinaryConstruction (build ordinaryLevel)
open InternedStoredSubstitutionRebind (replacement resolve)
open InternedBinderProtocol (NodeKey Reference)
open SourceCurrentStoredAlphaPlans

private def expression : Syntax Nat Bool :=
  .binder false (.node [.mk 0 false [.var 0,
    .binder false (.node [.mk 1 true [.var 0, .var 1]]), .node [.mk 2 true []]]])
private def built := build expression [] empty
private def root : Value Nat Bool := match built with | .done value _ => value | .pending .. => .empty
private def heap := built.state
private def fields : Value Nat Bool → Interned NodeKey × Value Nat Bool × Value Nat Bool × Value Nat Bool
  | .mu entry body depth ordinary => (entry, body, depth, ordinary)
  | _ => (⟨0, .node []⟩, .empty, .empty, .empty)
private def entry := (fields root).1
private def body := (fields root).2.1
private def depth := (fields root).2.2.1
private def ordinary := (fields root).2.2.2
private def own : Reference := .interned entry.identity
private def argument : Reference := .uninterned (ordinaryLevel depth)
private def nestedUsed : Value Nat Bool → Bool
  | .node _ [row] _ _ => match row.children with
    | [_, .mu _ _ depth ordinary, _] => InternedFreshOrdinaryDepthHeap.usesLocal depth ordinary
    | _ => false
  | _ => false

private theorem actual : build expression [] empty = .done (.mu entry body depth ordinary) heap := by cbv
private theorem different : body ≠ ordinary := by
  intro same
  have ids := congrArg Value.referenceOf same
  cbv at ids
  cases ids

set_option cbv.maxSteps 100000000 in
private theorem related (value : Value Nat Bool) :
    Alpha [] [] [] [] (replacement own value) (replacement argument value) body ordinary := by
  cbv
  simp
  intro argument
  cbv

/-- Actual nested used Mu callbacks have distinct stored payloads and a structural alpha proof for every replacement. -/
theorem constructed_nested_used_mu :
    ∃ entry body depth ordinary before,
      build expression [] empty = .done (.mu entry body depth ordinary) before ∧
      InternedFreshOrdinaryDepthHeap.usesLocal depth ordinary = true ∧ nestedUsed body = true ∧ body ≠ ordinary ∧
      (∀ value, Alpha [] [] [] [] (replacement (.interned entry.identity) value)
        (replacement (.uninterned (ordinaryLevel depth)) value) body ordinary) ∧
      ∀ value current,
        InternedFreshOrdinaryStoredSubstitution.execute body (replacement (.interned entry.identity) value) current =
          InternedFreshOrdinaryStoredSubstitution.execute ordinary
            (replacement (.uninterned (ordinaryLevel depth)) value) current := by
  have verified := InternedFreshOrdinaryFacts.closed_verified expression
  have available := verified.result (.mu entry body depth ordinary) heap actual
  have coherent : Coherent heap := by
    simpa only [actual, Outcome.state] using verified.facts.coherent
  have bodyAvailable : Available heap body := available.children body (by simp [children])
  have ordinaryAvailable : Available heap ordinary := available.children ordinary (by simp [children])
  refine ⟨entry, body, depth, ordinary, heap, actual, by cbv, by cbv, different, related, ?_⟩
  intro value current
  exact execute_exact body ordinary (replacement own value) (replacement argument value) heap current
    coherent bodyAvailable ordinaryAvailable (related value)

end MicroCFTA.StoredAlphaPlanKernels

set_option linter.all true
set_option pp.all true
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.proofs true
set_option pp.proofs.threshold 254
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000

#check @MicroCFTA.StoredAlphaPlanKernels.constructed_nested_used_mu
#print axioms MicroCFTA.StoredAlphaPlanKernels.constructed_nested_used_mu
