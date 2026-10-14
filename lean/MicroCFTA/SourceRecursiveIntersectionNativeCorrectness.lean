import MicroCFTA.SourceRecursiveIntersectionNativeBounds

/-!
# Completed native execution agrees with the guarded source kernel

Induction over the actual range-checked native evaluation derives physical
facts, exact growth, available results, concrete kernel execution, and every
new completed memo entry. Completion provenance comes from the original
compiled body. It is not a premise at completion frames.
-/
namespace MicroCFTA.SourceRecursiveIntersectionNative
open Cache InternedConstructorTemplates InternedProbeProvenance InternedEdgeResidency
open InternedBinderProtocol IntersectionFlatMemoKeyDomain SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode

/-- Completed native correspondence retains strong memo provenance and exact physical source meaning. -/
structure Correct [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] (emptyGuard : Guard) (conjoin : Guard → Guard → Guard)
    (code : Code Symbol Guard A) (state : SourceRecursiveIntersectionThunks.State width Symbol Guard) (value : A)
    (after : SourceRecursiveIntersectionThunks.State width Symbol Guard) (post : Machine Symbol Guard → A → Prop) : Prop where
  valid : SourceRecursiveIntersectionThunks.Valid width emptyGuard conjoin after
  growth : Extension state.machine after.machine
  result : post after.machine value
  meaning : Meaning emptyGuard conjoin code state.machine value after.machine

/-- Actual completed native source evaluation derives guarded kernel meaning and completed memo provenance. -/
theorem Bounds.correct [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {emptyGuard : Guard} {conjoin : Guard → Guard → Guard}
    {code : Code Symbol Guard A} {state after : SourceRecursiveIntersectionThunks.State width Symbol Guard} {value : A}
    {evaluated : Evaluation width Symbol Guard emptyGuard conjoin code state value after} (bounds : Bounds evaluated)
    (post : Machine Symbol Guard → A → Prop) : BodyCode code → SourceRecursiveIntersectionCode.Safe code state.machine post →
      SourceRecursiveIntersectionThunks.Valid width emptyGuard conjoin state → Correct emptyGuard conjoin code state value after post := by
  induction bounds with
  | pure =>
    intro clean safe valid
    exact ⟨valid, .refl _, safe, 0, fun _ => rfl⟩
  | @work X A job next state final result tail bounded ih =>
    intro clean safe valid
    let actual := InternedConstructorTemplates.run job state.machine.heap
    let current : Machine Symbol Guard := {state.machine with heap := actual.2}
    have currentValid := advance_valid width emptyGuard conjoin state valid current safe.1 safe.2.1
    have later := ih post (clean actual.1) (safe.2.2 actual.1 current rfl) currentValid
    exact ⟨later.valid, safe.2.1.trans later.growth, later.result, later.meaning⟩
  | @enter A domain left right first second next state final result tail bounded ih =>
    intro clean safe valid
    let actual := SourceRecursiveIntersectionEnvironment.enter state.machine.domains domain.key left right first second
    let current : Machine Symbol Guard := {state.machine with domains := actual.2}
    have currentValid := advance_valid width emptyGuard conjoin state valid current safe.1 safe.2.1
    have later := ih post (clean actual.1) safe.2.2 currentValid
    exact ⟨later.valid, safe.2.1.trans later.growth, later.result, later.meaning⟩
  | @read A name next state final result tail bounded ih =>
    intro clean safe valid
    have later := ih post (clean _) safe valid
    exact ⟨later.valid, later.growth, later.result, later.meaning⟩
  | @optionalBinder A key body value next state final heap result done tail bounded ih =>
    intro clean safe valid
    let current : Machine Symbol Guard := {state.machine with heap := heap}
    have currentValid : SourceRecursiveIntersectionKernel.Valid current := by
      simpa only [done, construction, Result.state] using safe.1
    have growth : Extension state.machine current := by simpa only [done, construction, Result.state] using safe.2.1
    have continued := safe.2.2 value current (by simp only [done, construction]; rfl)
    have later := ih post (clean value) continued (advance_valid width emptyGuard conjoin state valid current currentValid growth)
    refine ⟨later.valid, growth.trans later.growth, later.result, ?_⟩
    obtain ⟨fuel, repeated⟩ := later.meaning
    refine ⟨fuel, ?_⟩
    intro extra
    change (construction (SourceRecursiveIntersectionMaybeMu.maybeMu key body state.machine.heap) state.machine).bind
      (fun value after => meaning emptyGuard conjoin (fuel + extra) (next value) after) = .done result final.machine
    rw [done]
    exact repeated extra
  | @nodeDirect A request actual next state selected middle final value result lookup body tail bodyBound tailBound bodyIH tailIH =>
    intro clean safe valid
    obtain ⟨same, retained⟩ := lookupNode_direct request actual state selected lookup
    subst actual
    subst selected
    have built := bodyIH (fun after value => Available after.heap value) (compileNode_bodyCode request)
      (compileNode_safe request state.machine valid.machine safe.1) valid
    have later := tailIH post (clean value) (safe.2 value middle.machine built.valid.machine built.growth built.result) built.valid
    exact ⟨later.valid, built.growth.trans later.growth, later.result, Meaning.node built.meaning.node_body later.meaning⟩
  | @nodeReady A request next state selected current final handle value result lookup demand tail safeWord tailBound ih =>
    intro clean safe valid
    have called := node_ready_source emptyGuard conjoin state selected current valid request safe.1 safeWord handle value lookup demand
    have growth : Extension state.machine current.machine := by rw [called.2.1]; exact .refl _
    have later := ih post (clean value) (safe.2 value current.machine called.1.machine growth called.2.2.1) called.1
    exact ⟨later.valid, growth.trans later.growth, later.result, Meaning.node called.2.2.2 later.meaning⟩
  | @edgeReady A request next state selected current final handle value result lookup demand tail safeWord tailBound ih =>
    intro clean safe valid
    have called := edge_ready_source emptyGuard conjoin state selected current valid request safe.1 safeWord handle value lookup demand
    have growth : Extension state.machine current.machine := by rw [called.2.1]; exact .refl _
    have later := ih post (clean value) (safe.2 value current.machine called.1.machine growth called.2.2.1) called.1
    exact ⟨later.valid, growth.trans later.growth, later.result, Meaning.edge called.2.2.2 later.meaning⟩
  | @nodeStarted A request actual next state selected current middle final handle value result lookup demand body tail safeWord bodyBound tailBound bodyIH tailIH =>
    intro clean safe valid
    have started := node_started_source emptyGuard conjoin state selected current valid request actual safe.1 safeWord handle lookup demand
    have same := started.2.1
    subst actual
    have ready : NodeReady current.machine request := by rw [started.2.2.1]; exact safe.1
    have built := bodyIH (fun after value => Available after.heap value) (compileNode_bodyCode request)
      (compileNode_safe request current.machine started.1.machine ready) started.1
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
    refine ⟨later.valid, growth.trans later.growth, later.result, Meaning.node ?_ later.meaning⟩
    refine ⟨fuel, ?_⟩
    intro extra
    simpa only [started.2.2.1, SourceRecursiveIntersectionThunks.finishNode] using repeated extra
  | @edgeStarted A request actual next state selected current middle final handle value result lookup demand body tail safeWord bodyBound tailBound bodyIH tailIH =>
    intro clean safe valid
    have started := edge_started_source emptyGuard conjoin state selected current valid request actual safe.1 safeWord handle lookup demand
    have same := started.2.1
    subst actual
    have ready : EdgeReady current.machine request := by rw [started.2.2.1]; exact safe.1
    have built := bodyIH (fun after value => EdgeResident after.heap value) (compileEdge_bodyCode emptyGuard conjoin request)
      (compileEdge_safe emptyGuard conjoin request current.machine started.1.machine ready) started.1
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
    refine ⟨later.valid, growth.trans later.growth, later.result, Meaning.edge ?_ later.meaning⟩
    refine ⟨fuel, ?_⟩
    intro extra
    simpa only [started.2.2.1, SourceRecursiveIntersectionThunks.finishEdge] using repeated extra
  | finishNode | finishEdge => intro clean; cases clean

end MicroCFTA.SourceRecursiveIntersectionNative
