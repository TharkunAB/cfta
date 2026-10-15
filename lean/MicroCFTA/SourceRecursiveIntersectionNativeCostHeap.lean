import MicroCFTA.SourceRecursiveIntersectionNativeSemantic
import MicroCFTA.SourceRecursiveIntersectionOrdinaryWork
import MicroCFTA.SourceRecursiveIntersectionCostEffects
import MicroCFTA.SourceRecursiveIntersectionNativeRangeCertificate

/-!
# Cost heaps through actual native evaluation

The induction follows nested native evaluations, checked memo lookups,
original source bodies, and completion frames. Ordinary jobs retain Mu
records. Explicit optional binders use the actual source compilation proof.
-/
namespace MicroCFTA.SourceRecursiveIntersectionNative
open Cache InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
open InternedBinderProtocol IntersectionFlatMemoKeyDomain SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceRecursiveIntersectionSemanticHeap (SemanticHeap)

/-- Actual completed native evaluation retains both decoded and cost heaps through compiled calls. -/
theorem Bounds.cost_heaps [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {emptyGuard : Guard} {conjoin : Guard → Guard → Guard}
    {code : Code Symbol Guard A} {state after : SourceRecursiveIntersectionThunks.State width Symbol Guard} {value : A}
    {evaluated : Evaluation width Symbol Guard emptyGuard conjoin code state value after} (bounds : Bounds evaluated)
    (post : Machine Symbol Guard → A → Prop) : BodyCode code → SourceRecursiveIntersectionCode.Safe code state.machine post →
      SourceRecursiveIntersectionThunks.Valid width emptyGuard conjoin state → Semantic code state.machine →
      SemanticHeap state.machine.heap → OrdinaryWork code → InternedFreshOrdinaryCostHeap.Heap state.machine.heap →
      SemanticHeap after.machine.heap ∧ InternedFreshOrdinaryCostHeap.Heap after.machine.heap := by
  induction bounds with
  | pure =>
    intro clean safe valid semantic heap ordinary costHeap
    exact ⟨heap, costHeap⟩
  | @work X A job next state final result tail bounded ih =>
    intro clean safe valid semantic heap ordinary costHeap
    let actual := InternedConstructorTemplates.run job state.machine.heap
    let current : Machine Symbol Guard := {state.machine with heap := actual.2}
    have currentValid := advance_valid width emptyGuard conjoin state valid current safe.1 safe.2.1
    have later := ih post (clean actual.1) (safe.2.2 actual.1 current rfl) currentValid
      (semantic.2 actual.1 current rfl) (semantic.1 heap) (ordinary.2 actual.1)
      (InternedFreshOrdinaryCostHeap.preserve state.machine.heap actual.2 costHeap (ordinary.1 state.machine.heap))
    exact later
  | @enter A domain left right first second next state final result tail bounded ih =>
    intro clean safe valid semantic heap ordinary costHeap
    let actual := SourceRecursiveIntersectionEnvironment.enter state.machine.domains domain.key left right first second
    let current : Machine Symbol Guard := {state.machine with domains := actual.2}
    have currentValid := advance_valid width emptyGuard conjoin state valid current safe.1 safe.2.1
    have later := ih post (clean actual.1) safe.2.2 currentValid semantic heap (ordinary actual.1) costHeap
    exact later
  | @read A name next state final result tail bounded ih =>
    intro clean safe valid semantic heap ordinary costHeap
    have later := ih post (clean _) safe valid semantic heap (ordinary _) costHeap
    exact later
  | @optionalBinder A key body value next state final heapState result done tail bounded ih =>
    intro clean safe valid semantic heap ordinary costHeap
    let current : Machine Symbol Guard := {state.machine with heap := heapState}
    have currentValid : SourceRecursiveIntersectionKernel.Valid current := by
      simpa only [done, construction, Result.state] using safe.1
    have growth : Extension state.machine current := by simpa only [done, construction, Result.state] using safe.2.1
    have continued := safe.2.2 value current (by simp only [done, construction]; rfl)
    have retained := SourceRecursiveIntersectionSemanticHeap.optionalBinder key body state.machine.heap heap semantic.1
    have afterHeap : SemanticHeap current.heap := by simpa only [done, InternedNestedConstruction.Outcome.state] using retained
    have retainedCosts := SourceRecursiveIntersectionCostEffects.optionalBinder key body state.machine.heap heap costHeap semantic.1
    have afterCosts : InternedFreshOrdinaryCostHeap.Heap current.heap := by
      simpa only [done, InternedNestedConstruction.Outcome.state] using retainedCosts
    have later := ih post (clean value) continued (advance_valid width emptyGuard conjoin state valid current currentValid growth)
      (semantic.2 value current (by simp only [done, construction]; rfl)) afterHeap (ordinary value) afterCosts
    exact later
  | @nodeDirect A request actual next state selected middle final value result lookup body tail bodyBound tailBound bodyIH tailIH =>
    intro clean safe valid semantic heap ordinary costHeap
    obtain ⟨same, retained⟩ := lookupNode_direct request actual state selected lookup
    subst actual
    subst selected
    have built := bodyBound.correct (fun after value => Available after.heap value) (compileNode_bodyCode request)
      (compileNode_safe request state.machine valid.machine safe.1) valid
    have bodyHeap := bodyIH (fun after value => Available after.heap value) (compileNode_bodyCode request)
      (compileNode_safe request state.machine valid.machine safe.1) valid
      (compileNode_semantic request state.machine valid.machine semantic.1) heap (compileNode_ordinaryWork request) costHeap
    have later := tailIH post (clean value) (safe.2 value middle.machine built.valid.machine built.growth built.result) built.valid
      (semantic.2 value middle.machine built.valid.machine built.growth built.result) bodyHeap.1 (ordinary value) bodyHeap.2
    exact later
  | @nodeReady A request next state selected current final handle value result lookup demand tail safeWord tailBound ih =>
    intro clean safe valid semantic heap ordinary costHeap
    have called := node_ready_source emptyGuard conjoin state selected current valid request safe.1 safeWord handle value lookup demand
    have growth : Extension state.machine current.machine := by rw [called.2.1]; exact .refl _
    have retained : SemanticHeap current.machine.heap := by rw [called.2.1]; exact heap
    have retainedCosts : InternedFreshOrdinaryCostHeap.Heap current.machine.heap := by rw [called.2.1]; exact costHeap
    have later := ih post (clean value) (safe.2 value current.machine called.1.machine growth called.2.2.1) called.1
      (semantic.2 value current.machine called.1.machine growth called.2.2.1) retained (ordinary value) retainedCosts
    exact later
  | @edgeReady A request next state selected current final handle value result lookup demand tail safeWord tailBound ih =>
    intro clean safe valid semantic heap ordinary costHeap
    have called := edge_ready_source emptyGuard conjoin state selected current valid request safe.1 safeWord handle value lookup demand
    have growth : Extension state.machine current.machine := by rw [called.2.1]; exact .refl _
    have retained : SemanticHeap current.machine.heap := by rw [called.2.1]; exact heap
    have retainedCosts : InternedFreshOrdinaryCostHeap.Heap current.machine.heap := by rw [called.2.1]; exact costHeap
    have later := ih post (clean value) (safe.2 value current.machine called.1.machine growth called.2.2.1) called.1
      (semantic.2 value current.machine called.1.machine growth called.2.2.1) retained (ordinary value) retainedCosts
    exact later
  | @nodeStarted A request actual next state selected current middle final handle value result lookup demand body tail safeWord bodyBound tailBound bodyIH tailIH =>
    intro clean safe valid semantic heap ordinary costHeap
    have started := node_started_source emptyGuard conjoin state selected current valid request actual safe.1 safeWord handle lookup demand
    have same := started.2.1
    subst actual
    have ready : NodeReady current.machine request := by rw [started.2.2.1]; exact safe.1
    have built := bodyBound.correct (fun after value => Available after.heap value) (compileNode_bodyCode request)
      (compileNode_safe request current.machine started.1.machine ready) started.1
    have initialHeap : SemanticHeap current.machine.heap := by rw [started.2.2.1]; exact heap
    have initialCosts : InternedFreshOrdinaryCostHeap.Heap current.machine.heap := by rw [started.2.2.1]; exact costHeap
    have bodyHeap := bodyIH (fun after value => Available after.heap value) (compileNode_bodyCode request)
      (compileNode_safe request current.machine started.1.machine ready) started.1
      (compileNode_semantic request current.machine started.1.machine ready) initialHeap (compileNode_ordinaryWork request) initialCosts
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
      (semantic.2 value middle.machine built.valid.machine growth built.result) bodyHeap.1 (ordinary value) bodyHeap.2
    exact later
  | @edgeStarted A request actual next state selected current middle final handle value result lookup demand body tail safeWord bodyBound tailBound bodyIH tailIH =>
    intro clean safe valid semantic heap ordinary costHeap
    have started := edge_started_source emptyGuard conjoin state selected current valid request actual safe.1 safeWord handle lookup demand
    have same := started.2.1
    subst actual
    have ready : EdgeReady current.machine request := by rw [started.2.2.1]; exact safe.1
    have built := bodyBound.correct (fun after value => EdgeResident after.heap value) (compileEdge_bodyCode emptyGuard conjoin request)
      (compileEdge_safe emptyGuard conjoin request current.machine started.1.machine ready) started.1
    have initialHeap : SemanticHeap current.machine.heap := by rw [started.2.2.1]; exact heap
    have initialCosts : InternedFreshOrdinaryCostHeap.Heap current.machine.heap := by rw [started.2.2.1]; exact costHeap
    have bodyHeap := bodyIH (fun after value => EdgeResident after.heap value) (compileEdge_bodyCode emptyGuard conjoin request)
      (compileEdge_safe emptyGuard conjoin request current.machine started.1.machine ready) started.1
      (compileEdge_semantic emptyGuard conjoin request current.machine started.1.machine ready) initialHeap
      (compileEdge_ordinaryWork emptyGuard conjoin request) initialCosts
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
      (semantic.2 value middle.machine built.valid.machine growth built.result) bodyHeap.1 (ordinary value) bodyHeap.2
    exact later
  | finishNode | finishEdge => intro clean; cases clean

/-- Actual completed evaluation retains the cost heap through compiled source calls. -/
theorem Bounds.cost_heap [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {emptyGuard : Guard} {conjoin : Guard → Guard → Guard}
    {code : Code Symbol Guard A} {state after : SourceRecursiveIntersectionThunks.State width Symbol Guard} {value : A}
    {evaluated : Evaluation width Symbol Guard emptyGuard conjoin code state value after} (bounds : Bounds evaluated)
    (post : Machine Symbol Guard → A → Prop) (clean : BodyCode code) (safe : SourceRecursiveIntersectionCode.Safe code state.machine post)
    (valid : SourceRecursiveIntersectionThunks.Valid width emptyGuard conjoin state) (semantic : Semantic code state.machine)
    (heap : SemanticHeap state.machine.heap) (ordinary : OrdinaryWork code)
    (costHeap : InternedFreshOrdinaryCostHeap.Heap state.machine.heap) :
    InternedFreshOrdinaryCostHeap.Heap after.machine.heap :=
  (bounds.cost_heaps post clean safe valid semantic heap ordinary costHeap).2

/-- Actual checked completion derives semantic and cost heaps from current input invariants. -/
theorem done_cost_heaps_of_ranges [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (emptyGuard : Guard) (conjoin : Guard → Guard → Guard) (code : Code Symbol Guard A)
    (state after : SourceRecursiveIntersectionThunks.State width Symbol Guard) (value : A)
    (post : Machine Symbol Guard → A → Prop) (clean : BodyCode code) (safe : SourceRecursiveIntersectionCode.Safe code state.machine post)
    (valid : SourceRecursiveIntersectionThunks.Valid width emptyGuard conjoin state) (semantic : Semantic code state.machine)
    (heap : SemanticHeap state.machine.heap) (ordinary : OrdinaryWork code)
    (costHeap : InternedFreshOrdinaryCostHeap.Heap state.machine.heap)
    (ranges : WordRanges emptyGuard conjoin code state) (fuel : Nat)
    (done : execute emptyGuard conjoin fuel code state = .done value after) :
    SemanticHeap after.machine.heap ∧ InternedFreshOrdinaryCostHeap.Heap after.machine.heap :=
  ((evaluation_of_done emptyGuard conjoin fuel code state after value done).bounds_of_ranges ranges).cost_heaps
    post clean safe valid semantic heap ordinary costHeap

/-- Actual checked completion retains the cost heap without a supplied final-heap premise. -/
theorem done_cost_heap_of_ranges [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (emptyGuard : Guard) (conjoin : Guard → Guard → Guard) (code : Code Symbol Guard A)
    (state after : SourceRecursiveIntersectionThunks.State width Symbol Guard) (value : A)
    (post : Machine Symbol Guard → A → Prop) (clean : BodyCode code) (safe : SourceRecursiveIntersectionCode.Safe code state.machine post)
    (valid : SourceRecursiveIntersectionThunks.Valid width emptyGuard conjoin state) (semantic : Semantic code state.machine)
    (heap : SemanticHeap state.machine.heap) (ordinary : OrdinaryWork code)
    (costHeap : InternedFreshOrdinaryCostHeap.Heap state.machine.heap)
    (ranges : WordRanges emptyGuard conjoin code state) (fuel : Nat)
    (done : execute emptyGuard conjoin fuel code state = .done value after) :
    InternedFreshOrdinaryCostHeap.Heap after.machine.heap :=
  (done_cost_heaps_of_ranges emptyGuard conjoin code state after value post clean safe valid semantic heap ordinary costHeap ranges fuel done).2

end MicroCFTA.SourceRecursiveIntersectionNative
