import MicroCFTA.SourceCurrentConstrainedCapNativeCache
import MicroCFTA.SourceCurrentHereditaryNativeCache

set_option linter.all true
set_option pp.explicit true
set_option pp.proofs true
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000
set_option format.width 200

namespace MicroCFTA.CapCacheIntegration
open InternedConstructorTemplates SourceRecursiveIntersectionThunks
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionCode
open SourceCurrentConstrainedCap SourceCurrentHereditaryNativeScope
variable {Symbol Guard : Type} {width : Nat}

/-- Every finite-cap cell law supplies the existing hereditary law at zero. -/
theorem node_hereditary (annotation : Guard → Prop) (source : InternedConstructorTemplates.State Symbol Guard)
    (request : NodeRequest Symbol Guard) (result : Value Symbol Guard)
    (law : SourceCurrentConstrainedCapNativeLaws.NodeLaw annotation source request result) :
    SourceCurrentHereditaryNativeCode.NodeLaw annotation source request result := by
  intro bindings left right
  exact (law 0 bindings (.plain 0 left) (.plain 0 right)).annotated rfl

/-- The zero row law retains its guard and every actual child annotation. -/
theorem edge_hereditary (annotation : Guard → Prop) (source : InternedConstructorTemplates.State Symbol Guard)
    (request : EdgeRequest Symbol Guard) (result : EdgeValue Symbol Guard)
    (law : SourceCurrentConstrainedCapNativeLaws.EdgeLaw annotation source request result) :
    SourceCurrentHereditaryNativeCode.EdgeLaw annotation source request result :=
  law 0

/-- A cap store supplies the older hereditary store without another heap premise. -/
theorem store_hereditary (annotation : Guard → Prop) (source : InternedConstructorTemplates.State Symbol Guard)
    (state : SourceRecursiveIntersectionThunks.State width Symbol Guard)
    (stored : SourceCurrentConstrainedCapNativeCache.Stored annotation source state) :
    SourceCurrentHereditaryNativeCache.Stored annotation source state :=
  ⟨fun handle request result found => node_hereditary annotation source request result (stored.nodes handle request result found),
    fun handle request result found => edge_hereditary annotation source request result (stored.edges handle request result found)⟩

/-- A closed self branch constructs its result, installs its law, and produces an exact warm hit. -/
theorem self_query [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (annotation : Guard → Prop) (source : InternedConstructorTemplates.State Symbol Guard)
    (emptyGuard : Guard) (conjoin : Guard → Guard → Guard)
    (machine : Machine Symbol Guard) (valid : SourceRecursiveIntersectionKernel.Valid machine)
    (request : NodeRequest Symbol Guard) (ready : NodeReady machine request)
    (safe : SourceRecursiveIntersectionMemo.KeySafe width request.domain request.left request.right)
    (key : IntersectionFlatMemoKeyDomain.Triple width)
    (requested : SourceRecursiveIntersectionMemo.requestKey width request.domain request.left request.right = some key)
    (branch : SourceRecursiveIntersectionControl.decision request.domain.key request.left request.right = .self) :
    ∃ after,
      SourceRecursiveIntersectionNative.execute emptyGuard conjoin 3
        (requestNode request.domain request.left request.right) (initial width machine) = .done request.left after ∧
      SourceCurrentAllocatedNativePhysicalCache.Valid after ∧
      SourceCurrentConstrainedCapNativeCache.Stored annotation source after ∧
      lookupNode width request after = (.memoized 0, after) ∧
      demandNode 0 after = (.ready request.left, after) := by
  let before := initial width machine
  let chosen := (lookupNode width request before).2
  let running := (demandNode 0 chosen).2
  let after := finishNode 0 request.left running
  have selected : lookupNode width request before = (.memoized 0, chosen) := by
    simp [chosen, before, initial, lookupNode, requested, FlatMemoThunk.lookupOrInsert, FlatMemoThunk.empty]
  have demanded : demandNode 0 chosen = (.evaluate request, running) := by
    simp [running, chosen, before, initial, lookupNode, requested, demandNode,
      FlatMemoThunk.lookupOrInsert, FlatMemoThunk.empty, FlatMemoThunk.demand, Cache.put]
  have started := SourceCurrentConstrainedCapNativeCache.node_started annotation source request request
    before chosen running 0 (SourceCurrentAllocatedNativePhysicalCache.initial_valid machine valid)
    (SourceCurrentConstrainedCapNativeCache.initial_stored annotation source width machine)
    ready safe selected demanded
  have available := (started.2.1.nodes.checked 0 _ started.2.2.2).1.2.1
  have afterValid := SourceCurrentAllocatedNativePhysicalCache.finishNode_valid running started.2.1
    0 request request.left started.2.2.2 available
  have afterStored := SourceCurrentConstrainedCapNativeCache.finishNode_stored annotation source running
    0 request request.left started.2.1 started.2.2.1 started.2.2.2 (fun _ _ left _ => left)
  have cell : after.nodes.cells 0 = some ⟨request, .returned request.left⟩ := by
    simp [after, finishNode, FlatMemoThunk.finish, started.2.2.2, FlatMemoThunk.setStatus, Cache.put]
  have published : after.nodes.table key = some 0 := by
    simp [after, running, chosen, before, initial, lookupNode, requested, demandNode, finishNode,
      FlatMemoThunk.lookupOrInsert, FlatMemoThunk.empty, FlatMemoThunk.demand, FlatMemoThunk.finish,
      FlatMemoThunk.setStatus, Cache.put]
  have afterReady : NodeReady after.machine request :=
    (afterValid.nodes.checked 0 _ cell).1
  have hit := SourceCurrentAllocatedNativePhysicalCache.node_ready_receipt after afterValid request request afterReady
    key ⟨requested, safe⟩ 0 published request.left cell
  refine ⟨after, ?_, afterValid, afterStored, hit.2.1, hit.2.2.1⟩
  have compiled : compileNode request = .pure request.left := by
    simp only [compileNode, branch]
  have first : SourceRecursiveIntersectionNative.step emptyGuard conjoin (.node request .pure) before =
      .yielded (.finishNode 0 request.left (.pure request.left)) running := by
    simp only [SourceRecursiveIntersectionNative.step, selected, demanded, compiled, Code.bind]
  change SourceRecursiveIntersectionNative.execute emptyGuard conjoin 3 (.node request .pure) before = _
  rw [SourceRecursiveIntersectionNative.execute, first]
  rfl

/-- A constrained leaf constructs both its cold return and its next warm query from initial facts. -/
theorem constrained_self_query [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (annotation : Guard → Prop) (source : InternedConstructorTemplates.State Symbol Guard)
    (emptyGuard : Guard) (conjoin : Guard → Guard → Guard)
    (machine : Machine Symbol Guard) (valid : SourceRecursiveIntersectionKernel.Valid machine)
    (entry : Cache.Interned InternedBinderProtocol.NodeKey) (edge : EdgeValue Symbol Guard) (level : Nat)
    (children : edge.children = []) (outside : ¬ annotation edge.entry.key.constraint)
    (ready : NodeReady machine ⟨IntersectionEmptyDomain.emptyDomain, .node entry [edge] level [], .node entry [edge] level []⟩)
    (safe : SourceRecursiveIntersectionMemo.KeySafe width IntersectionEmptyDomain.emptyDomain
      (.node entry [edge] level []) (.node entry [edge] level []))
    (key : IntersectionFlatMemoKeyDomain.Triple width)
    (requested : SourceRecursiveIntersectionMemo.requestKey width IntersectionEmptyDomain.emptyDomain
      (.node entry [edge] level []) (.node entry [edge] level []) = some key) :
    let value := Value.node entry [edge] level []
    ∃ after,
      SourceRecursiveIntersectionNative.execute emptyGuard conjoin 3
        (requestNode IntersectionEmptyDomain.emptyDomain value value) (initial width machine) = .done value after ∧
      SourceRecursiveIntersectionNative.execute emptyGuard conjoin 2
        (requestNode IntersectionEmptyDomain.emptyDomain value value) after = .done value after ∧
      SourceCurrentAllocatedNativePhysicalCache.Valid after ∧
      SourceCurrentConstrainedCapNativeCache.Stored annotation source after ∧
      Cap annotation 1 value ∧ ¬ SourceEqualityAnnotationLanguage.Annotated annotation value := by
  let value := Value.node entry [edge] level []
  let request : NodeRequest Symbol Guard := ⟨IntersectionEmptyDomain.emptyDomain, value, value⟩
  have branch : SourceRecursiveIntersectionControl.decision request.domain.key request.left request.right = .self := by
    simp [request, value, SourceRecursiveIntersectionControl.decision, SourceRecursiveIntersectionControl.hasEmpty,
      SourceRecursiveIntersectionControl.reset, SourceRecursiveIntersectionControl.closedSelf, Value.referenceOf, Value.free,
      IntersectionEmptyDomain.emptyDomain, IntersectionEmptyDomain.emptyKey]
  obtain ⟨after, cold, physical, stored, selected, demanded⟩ :=
    self_query annotation source emptyGuard conjoin machine valid request ready safe key requested branch
  have warm : SourceRecursiveIntersectionNative.execute emptyGuard conjoin 2 (.node request .pure) after = .done value after := by
    simp only [SourceRecursiveIntersectionNative.execute, SourceRecursiveIntersectionNative.step, selected, demanded]
  have bounded : Cap annotation 1 value := by
    apply Cap.node 0
    intro child member
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, children, List.not_mem_nil] at member
  have notHereditary : ¬ SourceEqualityAnnotationLanguage.Annotated annotation value := by
    intro annotated
    exact outside (SourceCurrentHereditaryConstructors.node_edge annotated edge List.mem_cons_self).1
  exact ⟨after, cold, warm, physical, stored, bounded, notHereditary⟩

#print axioms node_hereditary
#check @node_hereditary
#print axioms edge_hereditary
#check @edge_hereditary
#print axioms store_hereditary
#check @store_hereditary
#print axioms self_query
#check @self_query
#print axioms constrained_self_query
#check @constrained_self_query
end MicroCFTA.CapCacheIntegration
