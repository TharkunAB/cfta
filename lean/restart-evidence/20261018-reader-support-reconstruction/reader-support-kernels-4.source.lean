import MicroCFTA.SourceCurrentObservationReaderSupport

set_option linter.all true
set_option maxRecDepth 30000
set_option maxHeartbeats 5000000
set_option cbv.maxSteps 100000000

namespace MicroCFTA.ReaderSupportKernels
open Cache Language InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedNestedConstruction (Syntax Outcome)
open InternedFreshOrdinaryConstruction (build)
open InternedFreshOrdinaryStoredSubstitution (unfold)
open InternedBinderProtocol (Reference NodeKey)
open SourceEqualityRequiredCache (Ready Keeps)
open SourceCurrentReaderObservations (Related)
open SourceCurrentOpenObservations (Same)
open SourceCurrentObservationReaderSupport (Preparation WarmSupport)
open InternedFreshMuUnfoldBudget (Settled)

private def value (outcome : Outcome Nat Bool (Value Nat Bool)) : Value Nat Bool :=
  match outcome with | .done result _ => result | .pending .. => .empty
private def unary (symbol : Nat) (child : Syntax Nat Bool) : Syntax Nat Bool :=
  .node [.mk symbol false [child]]
private def first : Syntax Nat Bool := .binder true (unary 0 (.var 0))
private def second : Syntax Nat Bool := .binder true (unary 1 (.var 0))
private def source : Syntax Nat Bool := .node [.mk 2 false [first,unary 0 first,second]]
private def built := build source [] empty
private def root := value built
private def before := built.state
private def left := (children root)[0]?.getD .empty
private def layer := (children root)[1]?.getD .empty
private def cold := (children root)[2]?.getD .empty
private def coldRun := unfold cold before
private def coldResult := value coldRun
private def coldAfter := coldRun.state
private def fields : Value Nat Bool → Interned NodeKey × Value Nat Bool × Value Nat Bool × Value Nat Bool
  | .mu entry body depth ordinary => (entry,body,depth,ordinary)
  | _ => (⟨0,.node []⟩,.empty,.empty,.empty)
private theorem actual : build source [] empty = .done root before := by cbv
private theorem initial_ready : Ready before := SourceEqualityRequiredCache.constructed source root before actual
private theorem root_available : Available before root :=
  (InternedFreshOrdinaryFacts.build_verified source [] empty InternedNestedFacts.empty_facts
    (by intro value member; cases member)).result root before actual
private theorem left_available : Available before left := root_available.children left
  (List.mem_of_getElem? (show (children root)[0]? = some left by cbv))
private theorem layer_available : Available before layer := root_available.children layer
  (List.mem_of_getElem? (show (children root)[1]? = some layer by cbv))
private theorem cold_available : Available before cold := root_available.children cold
  (List.mem_of_getElem? (show (children root)[2]? = some cold by cbv))
private theorem closed : left.free = [] ∧ layer.free = [] ∧ cold.free = [] := by
  constructor
  · cbv
  · constructor <;> cbv
private theorem left_shape : left = .mu (fields left).1 (fields left).2.1 (fields left).2.2.1 (fields left).2.2.2 := by cbv
private theorem warm_left : unfold left before = .done layer before := by cbv
private theorem cold_actual : unfold cold before = .done coldResult coldAfter := by cbv
private theorem cold_changed : coldAfter.edges.next ≠ before.edges.next := by cbv
private theorem cold_unsettled : ¬ Settled before cold := by
  rintro ⟨result,finished⟩
  have same := (Outcome.done.inj (cold_actual.symm.trans finished)).2
  exact cold_changed (congrArg (fun state : State Nat Bool => state.edges.next) same)
private theorem distinct : left ≠ layer := by
  intro same
  have shape := congrArg Value.referenceOf same
  cbv at shape
  cases shape
private theorem empty_parity : left.referenceOf = .empty ↔ layer.referenceOf = .empty := by
  cbv
  constructor <;> intro impossible <;> cases impossible

private def shifted := (run (makeEdge 77 true []) before).2
private def shiftedRun := unfold cold shifted
private def shiftedResult := value shiftedRun
private def shiftedAfter := shiftedRun.state
private def coldRow : EdgeValue Nat Bool :=
  (InternedEdgeResidency.nodeEdges coldResult)[0]?.getD (.mk ⟨0,⟨0,[],false⟩⟩ [])
private theorem cold_shape : cold = .mu (fields cold).1 (fields cold).2.1 (fields cold).2.2.1 (fields cold).2.2.2 := by cbv
private theorem shifted_actual : unfold cold shifted = .done shiftedResult shiftedAfter := by cbv
private theorem shifted_keeps : Keeps before shifted :=
  (SourceEqualityRequiredCache.edge 77 true [] before initial_ready (by intro input member; cases member)).1
private theorem old_origin : MergedFreshOrdinaryGraph.Origin before [cold] coldRow := by
  have called := cold_actual
  rw [cold_shape] at called ⊢
  apply (MergedFreshOrdinaryGraph.origin_unfold before _ _ _ _ coldResult coldAfter called coldRow).mpr
  exact ⟨coldResult,.seed List.mem_cons_self,
    List.mem_of_getElem? (show (InternedEdgeResidency.nodeEdges coldResult)[0]? = some coldRow by cbv)⟩
private theorem shifted_loses_row : ¬ MergedFreshOrdinaryGraph.Origin shifted [cold] coldRow := by
  intro origin
  have called := shifted_actual
  rw [cold_shape] at called origin
  have exposed := (MergedFreshOrdinaryGraph.origin_unfold shifted _ _ _ _ shiftedResult shiftedAfter called coldRow).mp origin
  have physical := MergedFreshOrdinaryExposureCoverage.origin_terminal shifted shiftedResult (by cbv) coldRow exposed
  have identity : coldRow.entry.identity ∈ (InternedEdgeResidency.nodeEdges shiftedResult).map (fun row => row.entry.identity) :=
    List.mem_map.mpr ⟨coldRow,physical,rfl⟩
  cbv at identity
  simp at identity

/-- Actual closed source data produces new support and transports a nontrivial recursive observation pair. -/
theorem prepared_recursive_pair :
    build source [] empty = .done root before ∧ left ≠ layer ∧
    unfold left before = .done layer before ∧ ¬ Settled before cold ∧
    ∃ prepared later, Preparation before prepared ∧ Keeps before prepared ∧
      WarmSupport prepared (fun input => Available prepared input ∧ input.free = []) ∧
      prepared ≠ before ∧ later = (run (makeEdge 77 true []) prepared).2 ∧ Keeps prepared later ∧
      Related prepared left layer ∧ Related later left layer ∧
      ∀ depth, Same depth prepared [left] [layer] ↔ Same depth later [left] [layer] := by
  refine ⟨actual,distinct,warm_left,cold_unsettled,?_⟩
  obtain ⟨prepared,history,keeps,support⟩ := SourceCurrentObservationReaderSupport.prepare before initial_ready
  have leftSupport : Available prepared left ∧ left.free = [] := ⟨keeps.available left left_available,closed.1⟩
  have layerSupport : Available prepared layer ∧ layer.free = [] := ⟨keeps.available layer layer_available,closed.2.1⟩
  have changed : prepared ≠ before := by
    intro same
    subst prepared
    exact cold_unsettled (support.2.2 cold ⟨cold_available,closed.2.2⟩)
  have warm : unfold left prepared = .done layer prepared :=
    InternedFreshOrdinaryStoredSubstitution.unfold_replay left before prepared layer before
      initial_ready.semantic.1.normal.facts.coherent.valid warm_left keeps.growth
  have paired : Related prepared left layer := by
    refine ⟨empty_parity,?_⟩
    intro depth
    rw [left_shape] at warm ⊢
    exact SourceCurrentOpenObservations.unfold depth prepared _ _ _ _ layer prepared warm
  let later := (run (makeEdge 77 true []) prepared).2
  have advanced : Keeps prepared later := (SourceEqualityRequiredCache.edge 77 true [] prepared keeps.ready
    (by intro input member; cases member)).1
  refine ⟨prepared,later,history,keeps,support,changed,rfl,advanced,paired,?_,?_⟩
  · exact SourceCurrentObservationReaderSupport.related prepared later
      keeps.ready.semantic.1.normal.facts.coherent.valid advanced.growth _ support left layer
      leftSupport layerSupport paired
  · intro depth
    exact SourceCurrentObservationReaderSupport.same_iff prepared later
      keeps.ready.semantic.1.normal.facts.coherent.valid advanced.growth _ support depth [left] [layer]
      (by intro input member; exact List.mem_singleton.mp member ▸ leftSupport)
      (by intro input member; exact List.mem_singleton.mp member ▸ layerSupport)

/-- Actual supported growth can change a cold unfold's exact physical row identity. -/
theorem cold_origin_boundary :
    Ready before ∧ Ready shifted ∧ Keeps before shifted ∧ Available before cold ∧ cold.free = [] ∧
      unfold cold before = .done coldResult coldAfter ∧
      unfold cold shifted = .done shiftedResult shiftedAfter ∧
      MergedFreshOrdinaryGraph.Origin before [cold] coldRow ∧
      ¬ MergedFreshOrdinaryGraph.Origin shifted [cold] coldRow :=
  ⟨initial_ready,shifted_keeps.ready,shifted_keeps,cold_available,closed.2.2,
    cold_actual,shifted_actual,old_origin,shifted_loses_row⟩

end MicroCFTA.ReaderSupportKernels
