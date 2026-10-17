import MicroCFTA.SourceCurrentNativeRootErasure

set_option linter.all true
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.proofs true
set_option pp.proofs.threshold 254
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option cbv.maxSteps 200000000

namespace MicroCFTA.NativeRootErasureKernels
open InternedConstructorTemplates SourceCurrentNativeCallbackErasure
open InternedBinderProtocol (Reference)

private def seed : List (Value Nat Unit) × State Nat Unit :=
  run (do
    let firstEdge ← makeEdge 0 () []
    let first ← makeNode [firstEdge]
    let secondEdge ← makeEdge 1 () []
    let second ← makeNode [secondEdge]
    pure [first, second]) empty

private def filtered (name : Reference) (state : State Nat Unit) :=
  let original := run (makeUnion (.reference name :: seed.1 ++ seed.1)) state
  let result := run (withoutSelfReference name original.1) original.2
  (eraseSelf name result.1, result.2)

/-- Singleton self filtering retains the reference until final erasure and allocates no record. -/
theorem singleton_self :
    let original := run (makeUnion [Value.reference (Symbol := Nat) (Guard := Unit) (.uninterned 4)]) empty
    let result := run (withoutSelfReference (.uninterned 4) original.1) original.2
    result.1 = .reference (.uninterned 4) ∧
      (eraseSelf (.uninterned 4) result.1, result.2) = (.empty, empty) := by
  cbv

/-- Removing self merges ordered ordinary rows; a warm repeat retains the exact returned heap. -/
theorem ordinary_merge_and_warm :
    let cold := filtered (.uninterned 4) seed.2
    filtered (.uninterned 4) cold.2 = cold ∧
      (filtered (.intersection 7 8) cold.2).1 = cold.1 ∧
      (∃ entry depth free,
        cold.1 = .node entry
          [(run (makeEdge 0 () []) empty).1, (run (makeEdge 1 () []) (run (makeEdge 0 () []) empty).2).1]
          depth free) ∧
      seed.2.nodes.next < cold.2.nodes.next := by
  cbv

#check @singleton_self
#print axioms singleton_self
#check @ordinary_merge_and_warm
#print axioms ordinary_merge_and_warm
end MicroCFTA.NativeRootErasureKernels
