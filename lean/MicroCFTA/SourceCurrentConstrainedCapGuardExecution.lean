import MicroCFTA.SourceCurrentConstrainedCapSourceHistory
import MicroCFTA.SourceCurrentConstrainedCapGuardHeap
import MicroCFTA.SourceCurrentConstrainedCapGuardSemantics
import MicroCFTA.SourceCurrentConstrainedCapGuardNormalization
import MicroCFTA.SourceCurrentConstrainedCapGuardReadback

/-!
# Guard observations through actual source construction

The syntax induction retains the causal guard heap at every stopping state.
Each actual earlier callback supplies its own observation before the next
callback starts. Fresh publication derives the body-to-probe equality.
Warm readback uses the earlier writer's retained certificate.
-/
namespace MicroCFTA.SourceCurrentConstrainedCapGuardExecution
open Cache InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance InternedNestedFacts
open InternedNestedConstruction (Syntax EdgeSyntax Outcome work request finish)
open InternedNestedProvenance (Values Edges depth_available ordinary_available)
open InternedFreshOrdinaryConstruction InternedFreshOrdinaryFacts
open InternedBinderProtocol (Reference NodeKey)
open SourceCurrentConstrainedCapGuardHeap (Heap Checked done_checked bind_checked preserve)
open SourceCurrentConstrainedCapGuardDepth (profile)
open SourceCurrentConstrainedCapGuardSemantics (decode evaluate evaluateMany evaluateEdges)
local notation "Context" => SourceCurrentConstrainedCapSourceHistory.Context
local notation "GShape" => SourceCurrentConstrainedCapGuardSemantics.Shape
variable {Symbol Guard : Type}

/-- Each original child position retains its actual structural and guard observation. -/
def Observation (valid : Guard → Prop) (value : Value Symbol Guard) (shape : GShape Reference) : Prop :=
  InternedFreshOrdinaryDepthComposition.Observed value shape.shape ∧ profile valid value = shape.guardDepth

/-- Ordered source children retain both observations at every literal position. -/
abbrev Matches (valid : Guard → Prop) (values : List (Value Symbol Guard)) (shapes : List (GShape Reference)) :=
  InternedOccurrenceObservations.Paired (Observation valid) values shapes

private theorem matches_shape {valid : Guard → Prop} {values : List (Value Symbol Guard)} {shapes : List (GShape Reference)}
    (matched : Matches valid values shapes) :
    InternedFreshOrdinaryDepthComposition.Matches values (shapes.map SourceCurrentConstrainedCapGuardSemantics.Shape.shape) := by
  induction matched with
  | nil => exact .nil
  | cons first rest ih => exact .cons first.1 ih

private theorem matches_guard {valid : Guard → Prop} {values : List (Value Symbol Guard)} {shapes : List (GShape Reference)}
    (matched : Matches valid values shapes) :
    SourceCurrentConstrainedCapGuardDepth.children valid values =
      (SourceCurrentConstrainedCapGuardSemantics.combineMany shapes).guardDepth := by
  induction matched with
  | nil => simp [SourceCurrentConstrainedCapGuardDepth.children, SourceCurrentConstrainedCapGuardSemantics.combineMany]
  | cons first rest ih => simp only [SourceCurrentConstrainedCapGuardDepth.children,
      SourceCurrentConstrainedCapGuardSemantics.combineMany, SourceCurrentConstrainedCapGuardSemantics.combine,
      first.2, ih]

private theorem bind_heap (valid : Guard → Prop) (outcome : Outcome Symbol Guard A)
    (next : A → State Symbol Guard → Outcome Symbol Guard B) (heap : Heap valid outcome.state)
    (later : ∀ value after, outcome = .done value after → Heap valid after → Heap valid (next value after).state) :
    Heap valid (outcome.bind next).state := by
  cases outcome with
  | pending => exact heap
  | done value after => exact later value after rfl heap

private theorem request_heap [DecidableEq (EdgeKey Symbol Guard)] (valid : Guard → Prop) (smart : Bool)
    (expression : Syntax Symbol Guard) (environment : List (Value Symbol Guard))
    (depth ordinary : Value Symbol Guard) (state : State Symbol Guard)
    (context : Context state environment) (heap : Heap valid state) (expected : Option Nat)
    (ordinarySame : profile valid ordinary = expected)
    (recurse : ∀ name current, Context current environment → Available current (.reference name) → Heap valid current →
      Checked valid (callback expression environment name current) (fun value => profile valid value = expected)) :
    Heap valid (request smart depth ordinary (callback expression environment) state).state := by
  cases installed : state.nodes.table (muKey depth ordinary) with
  | some entry =>
      cases present : state.nodeRecords (muKey depth ordinary) <;>
        simpa only [request, installed, present, Outcome.state] using heap
  | none =>
      let key := muKey depth ordinary
      let entry := Cache.intern state.nodes key
      let allocated := {state with nodes := entry.2}
      have reserved : Context allocated environment := context.reserve key
      have argument : Available allocated (.reference (.interned entry.1.identity)) :=
        (InternedConstructionProvenance.reserve_available key state context.base.normal.facts.coherent
          context.base.normal.facts.cached).2
      have actual := recurse (.interned entry.1.identity) allocated reserved argument heap
      simp only [request, installed]
      change Heap valid ((callback expression environment (.interned entry.1.identity) allocated).bind
        (fun value after => InternedNestedRequestFacts.complete smart entry.1 value depth ordinary after)).state
      apply bind_heap valid _ _ actual.heap
      intro value after done afterHeap
      exact SourceCurrentConstrainedCapGuardHeap.complete_heap valid smart entry.1 value depth ordinary after afterHeap
        ((actual.result value after done).trans ordinarySame.symm)

private theorem request_profile [DecidableEq (EdgeKey Symbol Guard)] (valid : Guard → Prop) (smart : Bool)
    (depth ordinary : Value Symbol Guard) (call : Reference → State Symbol Guard → Outcome Symbol Guard (Value Symbol Guard))
    (state : State Symbol Guard) (value : Value Symbol Guard) (after : State Symbol Guard)
    (actual : request smart depth ordinary call state = .done value after)
    (facts : Facts after) (depthAvailable : Available after depth) (ordinaryAvailable : Available after ordinary)
    (depthHeap : InternedFreshOrdinaryDepthHeap.Heap after) (guardHeap : Heap valid after) :
    profile valid value = SourceCurrentConstrainedCapGuardReadback.decoded valid smart depth ordinary := by
  cases installed : state.nodes.table (muKey depth ordinary) with
  | some entry =>
      cases present : state.nodeRecords (muKey depth ordinary) with
      | none => simp only [request, installed, present] at actual; cases actual
      | some result =>
          simp only [request, installed, present] at actual
          cases actual
          exact SourceCurrentConstrainedCapGuardReadback.hit_profile valid smart depth ordinary result state
            facts depthAvailable ordinaryAvailable depthHeap guardHeap present
  | none =>
      let entry := Cache.intern state.nodes (muKey depth ordinary)
      let allocated := {state with nodes := entry.2}
      simp only [request, installed] at actual
      change (call (.interned entry.1.identity) allocated).bind _ = .done value after at actual
      cases called : call (.interned entry.1.identity) allocated with
      | pending key stopped => simp only [called, Outcome.bind] at actual; cases actual
      | done body middle =>
          simp only [called, Outcome.bind] at actual
          obtain ⟨winner, present⟩ := keepFirst_present middle.nodeRecords (muKey depth ordinary) (.mu entry.1 body depth ordinary)
          dsimp only [entry] at present
          simp only [present, Option.getD_some] at actual
          cases actual
          exact SourceCurrentConstrainedCapGuardReadback.hit_profile valid smart depth ordinary winner _
            facts depthAvailable ordinaryAvailable depthHeap guardHeap present

mutual
/-- Actual full source construction derives its guard observation and retains every earlier writer. -/
theorem build_profile [DecidableEq (EdgeKey Symbol Guard)] (valid : Guard → Prop)
    (expression : Syntax Symbol Guard) (environment : List (Value Symbol Guard)) (state : State Symbol Guard)
    (context : Context state environment) (heap : Heap valid state) :
    Checked valid (build expression environment state)
      (fun value => profile valid value = (evaluate valid expression (environment.map (decode valid))).guardDepth) := by
  cases expression with
  | empty =>
      rw [build]
      apply done_checked valid _ _ _ heap
      simp [profile, evaluate]
  | var index =>
      rw [build]
      apply done_checked valid _ _ _ heap
      cases found : environment[index]? <;> simp [evaluate, List.getElem?_map, found, decode, profile]
  | node edges =>
      have verified := buildEdges_verified edges environment state context.base.normal.facts context.base.inputs
      rw [build]
      apply bind_checked valid _ _ _ _ (buildEdges_profile valid edges environment state context heap)
      intro values after returned afterHeap same
      have afterContext : Context after environment := by simpa only [returned, Outcome.state] using context.edges edges
      have resident := verified.result values after returned
      apply done_checked
      · exact preserve valid after _ afterHeap (InternedShallowHeap.makeNode_noNewMu values after)
      · rw [SourceCurrentConstrainedCapGuardNormalization.makeNode_profile valid values after
          afterContext.base.normal.facts.coherent afterContext.base.normal.facts.linked resident, same]
        simp only [evaluate]
  | union members =>
      have verified := buildMany_verified members environment state context.base.normal.facts context.base.inputs
      rw [build]
      apply bind_checked valid _ _ _ _ (buildMany_profile valid members environment state context heap)
      intro values after returned afterHeap matched
      have afterContext : Context after environment := by simpa only [returned, Outcome.state] using context.many members
      have available := verified.result values after returned
      apply done_checked
      · exact preserve valid after _ afterHeap (InternedShallowHeap.makeUnion_noNewMu values after)
      · rw [SourceCurrentConstrainedCapGuardNormalization.makeUnion_profile valid values after
          afterContext.base.normal.facts afterContext.base.normal.live available, matches_guard matched]
        simp only [evaluate]
  | binder smart body =>
      have checked : ∀ name current, Context current environment → Available current (.reference name) → Heap valid current →
          Checked valid (callback body environment name current)
            (fun value => profile valid value =
              (evaluate valid body (SourceCurrentConstrainedCapGuardSemantics.reference name :: environment.map (decode valid))).guardDepth) := by
        intro name current currentContext argument currentHeap
        have localContext := currentContext.local name argument
        have physical := build_verified body _ current localContext.base.normal.facts localContext.base.inputs
        unfold callback
        apply bind_checked valid _ _ _ _ (build_profile valid body _ current localContext currentHeap)
        intro value after done afterHeap same
        have afterContext : Context after (.reference name :: environment) := by
          simpa only [done, Outcome.state] using localContext.build body
        have available := physical.result value after done
        apply done_checked
        · exact preserve valid after _ afterHeap (InternedStoredMuOrigins.filter_noNewMu name value after)
        · rw [SourceCurrentConstrainedCapGuardNormalization.filter_profile valid name value after afterContext.base.normal available]
          simpa only [List.map_cons, decode, InternedRecordDepthShape.shape, profile,
            SourceCurrentConstrainedCapGuardSemantics.reference] using same
      rw [build]
      change Checked valid ((callback body environment .depth state).bind fun depth afterDepth =>
        (callback body environment (.uninterned (ordinaryLevel depth)) afterDepth).bind fun ordinary afterOrdinary =>
          request smart depth ordinary (callback body environment) afterOrdinary) _
      apply bind_checked valid _ _ _ _ (checked .depth state context (depth_available state) heap)
      intro depth afterDepth depthDone depthHeap depthSame
      have depthContext : Context afterDepth environment := by
        simpa only [depthDone, Outcome.state] using context.callback body .depth (depth_available state)
      have depthPhysical := callback_verified body environment .depth state context.base.normal.facts
        (context.local .depth (depth_available state)).base.inputs
      have depthAvailable := depthPhysical.result depth afterDepth depthDone
      apply bind_checked valid _ _ _ _ (checked (.uninterned (ordinaryLevel depth)) afterDepth depthContext
        (ordinary_available afterDepth _) depthHeap)
      intro ordinary afterOrdinary ordinaryDone ordinaryHeap ordinarySame
      have finalContext : Context afterOrdinary environment := by
        simpa only [ordinaryDone, Outcome.state] using depthContext.callback body (.uninterned (ordinaryLevel depth)) (ordinary_available afterDepth _)
      have ordinaryPhysical := callback_verified body environment (.uninterned (ordinaryLevel depth)) afterDepth
        depthContext.base.normal.facts (depthContext.local _ (ordinary_available afterDepth _)).base.inputs
      have finalDepth : Available afterOrdinary depth := by
        simpa only [ordinaryDone, Outcome.state] using ordinaryPhysical.available depth depthAvailable
      have finalOrdinary := ordinaryPhysical.result ordinary afterOrdinary ordinaryDone
      have whole : build (.binder smart body) environment state =
          request smart depth ordinary (callback body environment) afterOrdinary := by
        rw [build]
        change ((callback body environment .depth state).bind _) = _
        rw [depthDone]
        change ((callback body environment (.uninterned (ordinaryLevel depth)) afterDepth).bind _) = _
        rw [ordinaryDone]
        rfl
      have retained := request_heap valid smart body environment depth ordinary afterOrdinary finalContext ordinaryHeap
        (evaluate valid body (SourceCurrentConstrainedCapGuardSemantics.reference (.uninterned (ordinaryLevel depth)) :: environment.map (decode valid))).guardDepth ordinarySame (by
          intro name current currentContext argument currentHeap
          have actual := checked name current currentContext argument currentHeap
          exact ⟨actual.heap, fun value after done => (actual.result value after done).trans
            (SourceCurrentConstrainedCapGuardSemantics.arguments_guardDepth valid body _ name _)⟩)
      refine ⟨retained, ?_⟩
      intro value after returned
      have afterContext : Context after environment := by
        simpa only [whole, returned, Outcome.state] using context.build (.binder smart body)
      have afterGuard : Heap valid after := by simpa only [returned, Outcome.state] using retained
      have afterDepthAvailable : Available after depth := by
        have requestedPhysical := InternedNestedRequestFacts.request_verified smart depth ordinary
          (callback body environment) afterOrdinary finalContext.base.normal.facts finalDepth finalOrdinary
          (by
            intro name current growth history currentFacts argument
            exact callback_verified body environment name current currentFacts (by
              intro input member
              rcases List.mem_cons.mp member with rfl | member
              · exact argument
              · exact (finalContext.base.inputs input member).grows afterOrdinary current growth history))
        simpa only [returned, Outcome.state] using requestedPhysical.available depth finalDepth
      have afterOrdinaryAvailable : Available after ordinary := by
        have requestedPhysical := InternedNestedRequestFacts.request_verified smart depth ordinary
          (callback body environment) afterOrdinary finalContext.base.normal.facts finalDepth finalOrdinary
          (by
            intro name current growth history currentFacts argument
            exact callback_verified body environment name current currentFacts (by
              intro input member
              rcases List.mem_cons.mp member with rfl | member
              · exact argument
              · exact (finalContext.base.inputs input member).grows afterOrdinary current growth history))
        simpa only [returned, Outcome.state] using requestedPhysical.available ordinary finalOrdinary
      have readback := request_profile valid smart depth ordinary _ afterOrdinary value after returned
        afterContext.base.normal.facts afterDepthAvailable afterOrdinaryAvailable afterContext.depth afterGuard
      have depthObserved := (InternedRecordDepthExecution.callback_depth body environment .depth state context.base
        (depth_available state) context.depth).result depth afterDepth depthDone
      have ordinaryObserved := (InternedRecordDepthExecution.callback_depth body environment (.uninterned (ordinaryLevel depth)) afterDepth depthContext.base
        (ordinary_available afterDepth _) depthContext.depth).result ordinary afterOrdinary ordinaryDone
      have fresh : .uninterned (ordinaryLevel depth) ∉ InternedRecordDepthCallback.captured body environment := by
        intro member
        have present := (InternedFreshOrdinaryDepthHeap.observed_other _ _ .depth depth depthObserved.2
          (.uninterned (ordinaryLevel depth)) (by intro impossible; cases impossible)).mpr member
        exact ordinary_fresh depth (InternedDeepFreeNormalization.deep_free depth afterDepth
          depthContext.base.normal.facts.coherent depthAvailable _ present)
      have own := InternedFreshOrdinaryDepthHeap.observed_own _ _ (.uninterned (ordinaryLevel depth)) ordinary ordinaryObserved.2 fresh
      have useExact : InternedFreshOrdinaryDepthHeap.usesLocal depth ordinary =
          InternedDepthSemantics.hasLocal (InternedRecordDepthCallback.symbolic body environment).deep := by
        rw [InternedFreshOrdinaryDepthComposition.hasLocal_uses]
        apply Bool.eq_iff_iff.mpr
        simpa only [InternedFreshOrdinaryDepthHeap.usesLocal, decide_eq_true_eq, InternedRecordDepthCallback.uses] using own
      have shapeExact : (evaluate valid body (SourceCurrentConstrainedCapGuardSemantics.reference (.inl ()) ::
          (environment.map (decode valid)).map (SourceCurrentConstrainedCapGuardSemantics.Shape.map Sum.inr))).shape =
          InternedRecordDepthCallback.symbolic body environment := by
        rw [SourceCurrentConstrainedCapGuardSemantics.evaluate_shape]
        simp [InternedRecordDepthCallback.symbolic, decode, SourceCurrentConstrainedCapGuardSemantics.reference,
          SourceCurrentConstrainedCapGuardSemantics.Shape.map, List.map_map, Function.comp_def]
      rw [readback]
      have ordinaryExpected : profile valid ordinary =
          (evaluate valid body (SourceCurrentConstrainedCapGuardSemantics.reference (.inl ()) ::
            (environment.map (decode valid)).map (SourceCurrentConstrainedCapGuardSemantics.Shape.map Sum.inr))).guardDepth := by
        rw [ordinarySame, SourceCurrentConstrainedCapGuardSemantics.evaluate_supplied]
        rfl
      simp only [SourceCurrentConstrainedCapGuardReadback.decoded, useExact, ordinaryExpected,
        evaluate, SourceCurrentConstrainedCapGuardSemantics.binder, shapeExact]
termination_by sizeOf expression

/-- Actual ordered source children retain both observations and the causal guard heap. -/
theorem buildMany_profile [DecidableEq (EdgeKey Symbol Guard)] (valid : Guard → Prop)
    (expressions : List (Syntax Symbol Guard)) (environment : List (Value Symbol Guard)) (state : State Symbol Guard)
    (context : Context state environment) (heap : Heap valid state) :
    Checked valid (buildMany expressions environment state)
      (fun values => Matches valid values (evaluateMany valid expressions (environment.map (decode valid)))) := by
  cases expressions with
  | nil => rw [buildMany]; apply done_checked valid _ _ _ heap; simpa only [evaluateMany] using (InternedOccurrenceObservations.Paired.nil : Matches valid [] [])
  | cons first rest =>
      have physical := build_verified first environment state context.base.normal.facts context.base.inputs
      have shapeChecked := InternedRecordDepthExecution.build_depth first environment state context.base context.depth
      rw [buildMany]
      apply bind_checked valid _ _ _ _ (build_profile valid first environment state context heap)
      intro value after returned afterHeap same
      have afterContext : Context after environment := by simpa only [returned, Outcome.state] using context.build first
      have observed : InternedFreshOrdinaryDepthComposition.Observed value
          (evaluate valid first (environment.map (decode valid))).shape := by
        rw [SourceCurrentConstrainedCapGuardSemantics.evaluate_shape]
        simpa only [List.map_map, decode, Function.comp_def] using shapeChecked.result value after returned
      apply bind_checked valid _ _ _ _ (buildMany_profile valid rest environment after afterContext afterHeap)
      intro values final completed finalHeap matched
      apply done_checked valid _ _ _ finalHeap
      simpa only [evaluateMany] using InternedOccurrenceObservations.Paired.cons ⟨observed, same⟩ matched
termination_by sizeOf expressions

/-- Actual surviving rows retain the exact guard profile computed from their original source children. -/
theorem buildEdges_profile [DecidableEq (EdgeKey Symbol Guard)] (valid : Guard → Prop)
    (expressions : List (EdgeSyntax Symbol Guard)) (environment : List (Value Symbol Guard)) (state : State Symbol Guard)
    (context : Context state environment) (heap : Heap valid state) :
    Checked valid (buildEdges expressions environment state)
      (fun edges => SourceCurrentConstrainedCapGuardDepth.rows valid (surviving edges) =
        (evaluateEdges valid expressions (environment.map (decode valid))).guardDepth) := by
  cases expressions with
  | nil => rw [buildEdges]; apply done_checked valid _ _ _ heap; simp [surviving, SourceCurrentConstrainedCapGuardDepth.rows, evaluateEdges]
  | cons first rest =>
      cases first with
      | mk symbol guard children =>
          have physical := buildMany_verified children environment state context.base.normal.facts context.base.inputs
          rw [buildEdges]
          apply bind_checked valid _ _ _ _ (buildMany_profile valid children environment state context heap)
          intro values after returned afterHeap matched
          have afterContext : Context after environment := by simpa only [returned, Outcome.state] using context.many children
          have available := physical.result values after returned
          let edge := run (makeEdge symbol guard values) after
          have edgeContext : Context edge.2 environment := afterContext.edge symbol guard values available
          have edgeHeap : Heap valid edge.2 := afterHeap
          have childrenSame : edge.1.children = values := InternedShallowValues.makeEdge_children symbol guard values after
            afterContext.base.normal.facts.coherent afterContext.base.normal.facts.cached available
          simp only [work, Outcome.bind]
          change Checked valid ((buildEdges rest environment edge.2).bind _) _
          apply bind_checked valid _ _ _ _ (buildEdges_profile valid rest environment edge.2 edgeContext edgeHeap)
          intro edges final completed finalHeap same
          apply done_checked valid _ _ _ finalHeap
          rw [SourceCurrentConstrainedCapGuardNormalization.surviving_cons, childrenSame,
            InternedFreshOrdinaryDepthComposition.children_empty (matches_shape matched)]
          have exactEdge := SourceCurrentConstrainedCapGuardNormalization.makeEdge_profile valid symbol guard values after
            afterContext.base.normal.facts.coherent afterContext.base.normal.facts.cached available
          change SourceCurrentConstrainedCapGuardDepth.rows valid [edge.1] = _ at exactEdge
          rw [exactEdge, matches_guard matched, same]
          simp only [evaluateEdges, SourceCurrentConstrainedCapGuardSemantics.combine, SourceCurrentConstrainedCapGuardSemantics.edge]
termination_by sizeOf expressions
end

/-- Empty source caches derive the full causal guard heap at every actual stopping outcome. -/
theorem closed_heap [DecidableEq (EdgeKey Symbol Guard)] (valid : Guard → Prop) (expression : Syntax Symbol Guard) :
    Heap valid (build expression [] empty).state :=
  (build_profile valid expression [] empty SourceCurrentConstrainedCapSourceHistory.empty_context
    (SourceCurrentConstrainedCapGuardHeap.empty_heap valid)).heap

end MicroCFTA.SourceCurrentConstrainedCapGuardExecution
