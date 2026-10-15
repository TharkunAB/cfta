import MicroCFTA.SourceRecursiveIntersectionNativeAnnotationHeap

/-!
# Constraint closure through actual compiled native intersection

Each emitted conjunction uses its two resident original row constraints.
The actual returned child heap supplies their checks. Native graph induction
retains closure through cold bodies, warm hits, optional binders, completion
frames, and continuations. No final constraint invariant is an input.
-/
namespace MicroCFTA.SourceRecursiveIntersectionAnnotationCode
open Cache InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
open InternedBinderProtocol IntersectionFlatMemoKeyDomain SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode

/-- Compiled edges need conjunction closure only at the two actual resident operands. -/
theorem compileEdge_constraint_closed (annotation : Guard → Prop) [DecidableEq (EdgeKey Symbol Guard)] (emptyGuard : Guard) (conjoin : Guard → Guard → Guard)
    (emptyValid : annotation emptyGuard) (conjoinedValid : ∀ first second, annotation first → annotation second → annotation (conjoin first second))
    (request : EdgeRequest Symbol Guard) (state : Machine Symbol Guard) (valid : SourceRecursiveIntersectionKernel.Valid state)
    (ready : EdgeReady state request) : Certified annotation (compileEdge emptyGuard conjoin request) state := by
  unfold compileEdge
  split
  · let input := fun (current : Machine Symbol Guard) (pair : Value Symbol Guard × Value Symbol Guard) =>
      Domain current request.domain ∧ Available current.heap pair.1 ∧ Available current.heap pair.2
    have stable : Stable input := by
      intro before after growth pair known
      exact ⟨known.1.grows _ growth, growth.available _ known.2.1, growth.available _ known.2.2⟩
    have children := safe_walk (fun pair => requestNode request.domain pair.1 pair.2)
      (request.left.children.zip request.right.children) input _ stable available_stable
      (fun pair _ current currentValid known => safe_requestNode request.domain pair.1 pair.2 current known)
      state valid (by
        intro pair member
        have contained := List.of_mem_zip member
        exact ⟨ready.1, valid.1.cached.edges request.left.entry.key request.left ready.2.1 pair.1 contained.1,
          valid.1.cached.edges request.right.entry.key request.right ready.2.2 pair.2 contained.2⟩)
    have childrenSemantic := annotation_walk annotation (fun pair => requestNode request.domain pair.1 pair.2)
      (request.left.children.zip request.right.children) input _ stable available_stable
      (fun pair _ current currentValid known => safe_requestNode request.domain pair.1 pair.2 current known)
      (fun pair _ current currentValid known => annotation_requestNode annotation request.domain pair.1 pair.2 current known)
      state valid (by
        intro pair member
        have contained := List.of_mem_zip member
        exact ⟨ready.1, valid.1.cached.edges request.left.entry.key request.left ready.2.1 pair.1 contained.1,
          valid.1.cached.edges request.right.entry.key request.right ready.2.2 pair.2 contained.2⟩)
    apply annotation_bind annotation _ _ state valid _ children childrenSemantic
    intro values after afterValid growth available
    refine ⟨?_, fun _ _ _ => trivial⟩
    intro heap
    have left := heap request.left.entry.key request.left (edge_grows _ _ growth.heap request.left ready.2.1)
    have right := heap request.right.entry.key request.right (edge_grows _ _ growth.heap request.right ready.2.2)
    exact SourceEqualityAnnotationHeap.run annotation _
      (SourceEqualityAnnotationHeap.makeEdge annotation _ _ values (conjoinedValid _ _ left right)) after.heap heap
  · exact annotation_edge annotation _ _ [.empty] state emptyValid

end MicroCFTA.SourceRecursiveIntersectionAnnotationCode

namespace MicroCFTA.SourceRecursiveIntersectionNative
open Cache InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
open InternedBinderProtocol IntersectionFlatMemoKeyDomain SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceEqualityAnnotationHeap (Heap)
open SourceRecursiveIntersectionAnnotationCode

/-- Actual checked native execution retains every operand-closed constraint property at its returned heap. -/
theorem Bounds.constraint_heap (annotation : Guard → Prop) [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {emptyGuard : Guard} {conjoin : Guard → Guard → Guard}
    {code : Code Symbol Guard A} {state after : SourceRecursiveIntersectionThunks.State width Symbol Guard} {value : A}
    {evaluated : Evaluation width Symbol Guard emptyGuard conjoin code state value after} (bounds : Bounds evaluated)
    (emptyValid : annotation emptyGuard) (conjoinedValid : ∀ first second, annotation first → annotation second → annotation (conjoin first second))
    (post : Machine Symbol Guard → A → Prop) : BodyCode code → SourceRecursiveIntersectionCode.Safe code state.machine post →
      SourceRecursiveIntersectionThunks.Valid width emptyGuard conjoin state → Certified annotation code state.machine →
      Heap annotation state.machine.heap → Heap annotation after.machine.heap := by
  induction bounds with
  | pure =>
    intro clean safe valid semantic heap
    exact heap
  | @work X A job next state final result tail bounded ih =>
    intro clean safe valid semantic heap
    let actual := InternedConstructorTemplates.run job state.machine.heap
    let current : Machine Symbol Guard := {state.machine with heap := actual.2}
    have currentValid := advance_valid width emptyGuard conjoin state valid current safe.1 safe.2.1
    have later := ih post (clean actual.1) (safe.2.2 actual.1 current rfl) currentValid
      (semantic.2 actual.1 current rfl) (semantic.1 heap)
    exact later
  | @enter A domain left right first second next state final result tail bounded ih =>
    intro clean safe valid semantic heap
    let actual := SourceRecursiveIntersectionEnvironment.enter state.machine.domains domain.key left right first second
    let current : Machine Symbol Guard := {state.machine with domains := actual.2}
    have currentValid := advance_valid width emptyGuard conjoin state valid current safe.1 safe.2.1
    have later := ih post (clean actual.1) safe.2.2 currentValid semantic heap
    exact later
  | @read A name next state final result tail bounded ih =>
    intro clean safe valid semantic heap
    have later := ih post (clean _) safe valid semantic heap
    exact later
  | @optionalBinder A key body value next state final heapState result done tail bounded ih =>
    intro clean safe valid semantic heap
    let current : Machine Symbol Guard := {state.machine with heap := heapState}
    have currentValid : SourceRecursiveIntersectionKernel.Valid current := by
      simpa only [done, construction, Result.state] using safe.1
    have growth : Extension state.machine current := by simpa only [done, construction, Result.state] using safe.2.1
    have continued := safe.2.2 value current (by simp only [done, construction]; rfl)
    have retained := SourceEqualityAnnotationStoredSyntax.optionalBinder annotation key body state.machine.heap heap valid.machine.1 semantic.1
    have afterHeap : Heap annotation current.heap := by simpa only [done, InternedNestedConstruction.Outcome.state] using retained
    have later := ih post (clean value) continued (advance_valid width emptyGuard conjoin state valid current currentValid growth)
      (semantic.2 value current (by simp only [done, construction]; rfl)) afterHeap
    exact later
  | @nodeDirect A request actual next state selected middle final value result lookup body tail bodyBound tailBound bodyIH tailIH =>
    intro clean safe valid semantic heap
    obtain ⟨same, retained⟩ := lookupNode_direct request actual state selected lookup
    subst actual
    subst selected
    have built := bodyBound.correct (fun after value => Available after.heap value) (compileNode_bodyCode request)
      (compileNode_safe request state.machine valid.machine safe.1) valid
    have bodyHeap := bodyIH (fun after value => Available after.heap value) (compileNode_bodyCode request)
      (compileNode_safe request state.machine valid.machine safe.1) valid
      (compileNode_annotation annotation request state.machine valid.machine semantic.1) heap
    have later := tailIH post (clean value) (safe.2 value middle.machine built.valid.machine built.growth built.result) built.valid
      (semantic.2 value middle.machine built.valid.machine built.growth built.result) bodyHeap
    exact later
  | @nodeReady A request next state selected current final handle value result lookup demand tail safeWord tailBound ih =>
    intro clean safe valid semantic heap
    have called := node_ready_source emptyGuard conjoin state selected current valid request safe.1 safeWord handle value lookup demand
    have growth : Extension state.machine current.machine := by rw [called.2.1]; exact .refl _
    have retained : Heap annotation current.machine.heap := by rw [called.2.1]; exact heap
    have later := ih post (clean value) (safe.2 value current.machine called.1.machine growth called.2.2.1) called.1
      (semantic.2 value current.machine called.1.machine growth called.2.2.1) retained
    exact later
  | @edgeReady A request next state selected current final handle value result lookup demand tail safeWord tailBound ih =>
    intro clean safe valid semantic heap
    have called := edge_ready_source emptyGuard conjoin state selected current valid request safe.1 safeWord handle value lookup demand
    have growth : Extension state.machine current.machine := by rw [called.2.1]; exact .refl _
    have retained : Heap annotation current.machine.heap := by rw [called.2.1]; exact heap
    have later := ih post (clean value) (safe.2 value current.machine called.1.machine growth called.2.2.1) called.1
      (semantic.2 value current.machine called.1.machine growth called.2.2.1) retained
    exact later
  | @nodeStarted A request actual next state selected current middle final handle value result lookup demand body tail safeWord bodyBound tailBound bodyIH tailIH =>
    intro clean safe valid semantic heap
    have started := node_started_source emptyGuard conjoin state selected current valid request actual safe.1 safeWord handle lookup demand
    have same := started.2.1
    subst actual
    have ready : NodeReady current.machine request := by rw [started.2.2.1]; exact safe.1
    have built := bodyBound.correct (fun after value => Available after.heap value) (compileNode_bodyCode request)
      (compileNode_safe request current.machine started.1.machine ready) started.1
    have initialHeap : Heap annotation current.machine.heap := by rw [started.2.2.1]; exact heap
    have bodyHeap := bodyIH (fun after value => Available after.heap value) (compileNode_bodyCode request)
      (compileNode_safe request current.machine started.1.machine ready) started.1
      (compileNode_annotation annotation request current.machine started.1.machine ready) initialHeap
    obtain ⟨fuel, repeated⟩ := built.meaning.node_body
    have done : SourceRecursiveIntersectionKernel.execute emptyGuard conjoin fuel request.domain request.left request.right current.machine = .done value middle.machine := by
      simpa only [Nat.add_zero] using repeated 0
    have produced := SourceRecursiveIntersectionMemo.produced_here emptyGuard conjoin fuel request.domain request.left request.right
      current.machine middle.machine started.1.machine ready.1 ready.2.1 ready.2.2 value done
    have cells := node_body_cell emptyGuard conjoin handle request current middle value
      (shape_of_valid emptyGuard conjoin current started.1) started.2.2.2 body
    have completed := finishNode_valid width emptyGuard conjoin middle built.valid handle request value cells.1 produced
    have growth : Extension state.machine middle.machine := by rw [← started.2.2.1]; exact built.growth
    have later := tailIH post (clean value) (safe.2 value middle.machine built.valid.machine growth built.result) completed
      (semantic.2 value middle.machine built.valid.machine growth built.result) bodyHeap
    exact later
  | @edgeStarted A request actual next state selected current middle final handle value result lookup demand body tail safeWord bodyBound tailBound bodyIH tailIH =>
    intro clean safe valid semantic heap
    have started := edge_started_source emptyGuard conjoin state selected current valid request actual safe.1 safeWord handle lookup demand
    have same := started.2.1
    subst actual
    have ready : EdgeReady current.machine request := by rw [started.2.2.1]; exact safe.1
    have built := bodyBound.correct (fun after value => EdgeResident after.heap value) (compileEdge_bodyCode emptyGuard conjoin request)
      (compileEdge_safe emptyGuard conjoin request current.machine started.1.machine ready) started.1
    have initialHeap : Heap annotation current.machine.heap := by rw [started.2.2.1]; exact heap
    have bodyHeap := bodyIH (fun after value => EdgeResident after.heap value) (compileEdge_bodyCode emptyGuard conjoin request)
      (compileEdge_safe emptyGuard conjoin request current.machine started.1.machine ready) started.1
      (compileEdge_constraint_closed annotation emptyGuard conjoin emptyValid conjoinedValid request current.machine started.1.machine ready) initialHeap
    obtain ⟨fuel, repeated⟩ := built.meaning.edge_body
    have done : SourceRecursiveIntersectionKernel.edge emptyGuard conjoin
        (SourceRecursiveIntersectionKernel.execute emptyGuard conjoin fuel request.domain) request.left request.right current.machine = .done value middle.machine := by
      simpa only [Nat.add_zero] using repeated 0
    have produced := SourceRecursiveIntersectionEdgeMemo.produced_here emptyGuard conjoin fuel request.domain request.left request.right
      current.machine middle.machine started.1.machine ready.1 ready.2.1 ready.2.2 value done
    have cells := edge_body_cell emptyGuard conjoin handle request current middle value
      (shape_of_valid emptyGuard conjoin current started.1) started.2.2.2 body
    have completed := finishEdge_valid width emptyGuard conjoin middle built.valid handle request value cells.1 produced
    have growth : Extension state.machine middle.machine := by rw [← started.2.2.1]; exact built.growth
    have later := tailIH post (clean value) (safe.2 value middle.machine built.valid.machine growth built.result) completed
      (semantic.2 value middle.machine built.valid.machine growth built.result) bodyHeap
    exact later
  | finishNode | finishEdge => intro clean; cases clean


end MicroCFTA.SourceRecursiveIntersectionNative
