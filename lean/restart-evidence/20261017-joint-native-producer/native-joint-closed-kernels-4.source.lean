import MicroCFTA.SourceCurrentConstrainedCapNativeJointClosed

set_option linter.all true
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.proofs true
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000

namespace MicroCFTA.NativeJointClosedIntegration
open Cache InternedConstructorTemplates InternedProbeProvenance InternedRecordCoherence
open InternedBinderProtocol IntersectionFlatMemoKeyDomain
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceRecursiveIntersectionNative
open SourceCurrentConstrainedCap (Cap)
open SourceCurrentConstrainedCapPairOccurrences (Classified sourceWeight)
open SourceCurrentConstrainedCapNonplainRank (pairRank)
open SourceCurrentConstrainedCapKernelJoint (Context)
variable {Symbol Guard : Type} [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]

private theorem ranges_pure (emptyGuard : Guard) (conjoin : Guard → Guard → Guard)
    (value : A) (state : SourceRecursiveIntersectionThunks.State width Symbol Guard) :
    WordRanges emptyGuard conjoin (.pure value) state := by
  intro fuel next after trace
  cases trace with
  | refl => trivial
  | cons _ _ _ _ _ _ _ impossible _ => cases impossible

private theorem ranges_prepend (emptyGuard : Guard) (conjoin : Guard → Guard → Guard)
    (code next : Code Symbol Guard A) (state after : SourceRecursiveIntersectionThunks.State width Symbol Guard)
    (words : Words width code) (one : step emptyGuard conjoin code state = .yielded next after)
    (ranges : WordRanges emptyGuard conjoin next after) : WordRanges emptyGuard conjoin code state := by
  intro fuel final result trace
  cases trace with
  | refl => exact words
  | cons _ _ _ _ _ _ rest actual tail =>
      rw [one] at actual
      cases actual
      exact ranges rest final result tail

/-- Own cold completion and a literal warm repeat retain joint laws at the same full native state. -/
theorem cold_then_warm_self (annotation : Guard → Prop) (depth : Nat)
    (source : InternedConstructorTemplates.State Symbol Guard)
    (semantic : SourceRecursiveIntersectionSemanticHeap.SemanticHeap source) (covered : Covered [] source)
    (guards : SourceCurrentConstrainedCapGuardHeap.Heap annotation source)
    (domains : Cache.State DomainKey) (domainsValid : Cache.Valid domains)
    (holds : Guard → Language.Term Symbol → Bool) (emptyGuard : Guard) (conjoin : Guard → Guard → Guard)
    (emptyValid : annotation emptyGuard)
    (conjoinValid : ∀ first second, annotation first → annotation second → annotation (conjoin first second))
    (input : Value Symbol Guard) (available : Available source input) (closed : input.free = [])
    (bounded : Cap annotation depth input)
    (key : Triple width)
    (requested : SourceRecursiveIntersectionMemo.requestKey width IntersectionEmptyDomain.emptyDomain input input = some key)
    (safe : SourceRecursiveIntersectionMemo.KeySafe width IntersectionEmptyDomain.emptyDomain input input)
    (branch : SourceRecursiveIntersectionControl.decision IntersectionEmptyDomain.emptyDomain.key input input = .self) :
    ∃ (fuel : Nat) (after : SourceRecursiveIntersectionThunks.State width Symbol Guard),
      SourceRecursiveIntersectionNative.execute emptyGuard conjoin fuel
        (.node ⟨IntersectionEmptyDomain.emptyDomain, input, input⟩ .pure) (initial width ⟨source, domains⟩) = .done input after ∧
      SourceRecursiveIntersectionNative.execute emptyGuard conjoin 2
        (.node ⟨IntersectionEmptyDomain.emptyDomain, input, input⟩ .pure) after = .done input after ∧
      Context annotation source after.machine ∧ Cap annotation depth input ∧
      Classified (sourceWeight annotation source) (pairRank annotation input input) input := by
  let request : NodeRequest Symbol Guard := ⟨IntersectionEmptyDomain.emptyDomain, input, input⟩
  let machine : Machine Symbol Guard := ⟨source, domains⟩
  let before := initial width machine
  let chosen := (lookupNode width request before).2
  let running := (demandNode 0 chosen).2
  let after := finishNode 0 input running
  have selected : lookupNode width request before = (.memoized 0, chosen) := by
    simp [chosen, before, initial, lookupNode, requested, FlatMemoThunk.lookupOrInsert, FlatMemoThunk.empty, request]
  have demanded : demandNode 0 chosen = (.evaluate request, running) := by
    simp [running, chosen, before, initial, lookupNode, requested, demandNode,
      FlatMemoThunk.lookupOrInsert, FlatMemoThunk.empty, FlatMemoThunk.demand, Cache.put, request]
  have selectedBranch : SourceRecursiveIntersectionControl.decision request.domain.key request.left request.right = .self := branch
  have compiled : compileNode request = .pure input := by
    simp only [compileNode, selectedBranch]
    rfl
  have first : step emptyGuard conjoin (.node request .pure) before =
      .yielded (.finishNode 0 input (.pure input)) running := by
    simp only [step, selected, demanded, compiled, Code.bind]
  have finish : step emptyGuard conjoin (.finishNode 0 input (.pure input)) running =
      .yielded (.pure input) after := rfl
  have ranges : WordRanges emptyGuard conjoin (.node request .pure) before :=
    ranges_prepend emptyGuard conjoin _ _ _ _ (fun _ _ => safe) first
      (ranges_prepend emptyGuard conjoin _ _ _ _ trivial finish (ranges_pure emptyGuard conjoin input after))
  have literal : SourceRecursiveIntersectionNative.execute emptyGuard conjoin 3 (.node request .pure) before = .done input after := by
    rw [SourceRecursiveIntersectionNative.execute, first]
    rfl
  obtain ⟨fuel, value, actualAfter, done, correct, _finalSemantic, _finalCovered, stable, context,
      resultCap, classified, _resultClosed, _original, _fresh⟩ :=
    SourceCurrentConstrainedCapNativeJointClosed.cold_complete annotation depth source semantic covered guards domains domainsValid
      holds emptyGuard conjoin emptyValid conjoinValid input input available available closed closed bounded bounded ranges
  have same := stable 3
  have repeated := SourceRecursiveIntersectionNative.done_stable emptyGuard conjoin 3 fuel (.node request .pure) before after input literal
  rw [Nat.add_comm 3 fuel] at repeated
  rw [repeated] at same
  cases same
  have cell : after.nodes.cells 0 = some ⟨request, .returned input⟩ := by
    simp [after, running, chosen, before, initial, lookupNode, requested, demandNode, finishNode,
      FlatMemoThunk.lookupOrInsert, FlatMemoThunk.empty, FlatMemoThunk.demand, FlatMemoThunk.finish,
      FlatMemoThunk.setStatus, Cache.put, request]
  have published : after.nodes.table key = some 0 := by
    simp [after, running, chosen, before, initial, lookupNode, requested, demandNode, finishNode,
      FlatMemoThunk.lookupOrInsert, FlatMemoThunk.empty, FlatMemoThunk.demand, FlatMemoThunk.finish,
      FlatMemoThunk.setStatus, Cache.put, request]
  have requestKey : SourceRecursiveIntersectionMemo.requestKey width request.domain request.left request.right = some key := requested
  have warmLookup : lookupNode width request after = (.memoized 0, after) := by
    simp only [lookupNode, requestKey, FlatMemoThunk.lookupOrInsert, published]
  have warmDemand : demandNode 0 after = (.ready input, after) := by
    simp only [demandNode, FlatMemoThunk.demand, cell]
  have warmStep : step emptyGuard conjoin (.node request .pure) after = .yielded (.pure input) after := by
    simp only [step, warmLookup, warmDemand]
  have warmDone : SourceRecursiveIntersectionNative.execute emptyGuard conjoin 2 (.node request .pure) after = .done input after := by
    rw [SourceRecursiveIntersectionNative.execute, warmStep]
    rfl
  have warmRanges : WordRanges emptyGuard conjoin (.node request .pure) after :=
    ranges_prepend emptyGuard conjoin _ _ _ _ (fun _ _ => safe) warmStep
    (ranges_pure emptyGuard conjoin input after)
  have known : Domain after.machine request.domain := empty_domain _
  have inputs := SourceCurrentConstrainedCapOriginalSupport.closed_inputs source semantic.1.normal.facts request.domain
    input input available available closed closed
  have verified := SourceCurrentConstrainedCapNativeJointClosed.done_joint_of_ranges annotation source semantic.1.normal.facts
    emptyGuard conjoin emptyValid conjoinValid depth request after after input correct.valid context known
    (SourceCurrentConstrainedCapOriginalSupport.empty annotation source) inputs bounded bounded warmRanges 2 warmDone
  exact ⟨fuel, after, done, warmDone, verified.2.1, verified.2.2.2.1, verified.2.2.2.2.1⟩

/-- A literal nonhereditary row obtains its cap from empty children before both actual native calls. -/
theorem constrained_cold_then_warm (annotation : Guard → Prop)
    (source : InternedConstructorTemplates.State Symbol Guard)
    (semantic : SourceRecursiveIntersectionSemanticHeap.SemanticHeap source) (covered : Covered [] source)
    (guards : SourceCurrentConstrainedCapGuardHeap.Heap annotation source)
    (domains : Cache.State DomainKey) (domainsValid : Cache.Valid domains)
    (holds : Guard → Language.Term Symbol → Bool) (emptyGuard : Guard) (conjoin : Guard → Guard → Guard)
    (emptyValid : annotation emptyGuard)
    (conjoinValid : ∀ first second, annotation first → annotation second → annotation (conjoin first second))
    (entry : Interned NodeKey) (edge : EdgeValue Symbol Guard) (level : Nat)
    (children : edge.children = []) (outside : ¬ annotation edge.entry.key.constraint)
    (available : Available source (.node entry [edge] level [])) (key : Triple width)
    (requested : SourceRecursiveIntersectionMemo.requestKey width IntersectionEmptyDomain.emptyDomain
      (.node entry [edge] level []) (.node entry [edge] level []) = some key)
    (safe : SourceRecursiveIntersectionMemo.KeySafe width IntersectionEmptyDomain.emptyDomain
      (.node entry [edge] level []) (.node entry [edge] level [])) :
    let input := Value.node entry [edge] level []
    ∃ (fuel : Nat) (after : SourceRecursiveIntersectionThunks.State width Symbol Guard),
      SourceRecursiveIntersectionNative.execute emptyGuard conjoin fuel
        (.node ⟨IntersectionEmptyDomain.emptyDomain, input, input⟩ .pure) (initial width ⟨source, domains⟩) = .done input after ∧
      SourceRecursiveIntersectionNative.execute emptyGuard conjoin 2
        (.node ⟨IntersectionEmptyDomain.emptyDomain, input, input⟩ .pure) after = .done input after ∧
      Context annotation source after.machine ∧ Cap annotation 1 input ∧
      Classified (sourceWeight annotation source) (pairRank annotation input input) input ∧
      ¬ SourceEqualityAnnotationLanguage.Annotated annotation input := by
  let input := Value.node entry [edge] level []
  have bounded : Cap annotation 1 input := by
    apply Cap.node 0
    intro child member
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, children, List.not_mem_nil] at member
  have branch : SourceRecursiveIntersectionControl.decision IntersectionEmptyDomain.emptyDomain.key input input = .self := by
    simp [input, SourceRecursiveIntersectionControl.decision, SourceRecursiveIntersectionControl.hasEmpty,
      SourceRecursiveIntersectionControl.reset, SourceRecursiveIntersectionControl.closedSelf, Value.referenceOf, Value.free,
      IntersectionEmptyDomain.emptyDomain, IntersectionEmptyDomain.emptyKey]
  obtain ⟨fuel, after, done, warm, context, capped, classified⟩ :=
    cold_then_warm_self annotation 1 source semantic covered guards domains domainsValid holds emptyGuard conjoin emptyValid
      conjoinValid input available rfl bounded key requested safe branch
  refine ⟨fuel, after, done, warm, context, capped, classified, ?_⟩
  intro annotated
  exact outside (SourceCurrentHereditaryConstructors.node_edge annotated edge List.mem_cons_self).1

#print axioms cold_then_warm_self
#check @cold_then_warm_self
#print axioms constrained_cold_then_warm
#check @constrained_cold_then_warm
end MicroCFTA.NativeJointClosedIntegration
