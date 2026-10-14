import MicroCFTA.InternedRecordDepthExecution

/-!
# Actual nested source execution has the pure cached depth

The source induction retains the decoded depth heap through every outcome.
Completed results have the pure interpreter's depth and deep names. The
callback comparison uses actual probes and the fresh ordinary policy.
-/
namespace MicroCFTA.InternedFreshOrdinarySourceDepth
open Cache InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedNestedConstruction (Syntax EdgeSyntax Outcome work request)
open InternedNestedProvenance (depth_available ordinary_available)
open InternedFreshOrdinaryConstruction InternedFreshOrdinaryFacts
open InternedFreshOrdinaryContext InternedFreshOrdinaryDepthComposition
open InternedFreshOrdinaryDepthRequest (Checked done_checked bind_checked)
open InternedDepthSemantics
open InternedDepthFreeProjectionSource (literal)
open InternedBinderProtocol (Reference)

/-- Decoding literal inputs gives the original literal shapes. -/
private theorem literal_inputs (names : List Reference) :
    ((names.map (Value.reference (Symbol := Symbol) (Guard := Guard))).map InternedRecordDepthShape.shape) = names.map literal := by
  simp only [List.map_map, Function.comp_def, InternedRecordDepthShape.shape]
  change names.map (fun name => literal name) = names.map literal
  rfl

/-- Full repaired source execution preserves the depth heap and derives each returned shape observation. -/
theorem build_depth [DecidableEq (EdgeKey Symbol Guard)] (expression : Syntax Symbol Guard)
    (names : List Reference) (state : State Symbol Guard) (context : Context state (names.map Value.reference))
    (heap : InternedFreshOrdinaryDepthHeap.Heap state) :
    Checked (build expression (names.map Value.reference) state)
      (fun value => Observed value (evaluate expression (names.map literal))) := by
  simpa only [literal_inputs] using
    InternedRecordDepthExecution.build_depth expression (names.map Value.reference) state context heap

/-- Ordered source children retain their pure shape observations at every position. -/
theorem buildMany_depth [DecidableEq (EdgeKey Symbol Guard)] (expressions : List (Syntax Symbol Guard))
    (names : List Reference) (state : State Symbol Guard) (context : Context state (names.map Value.reference))
    (heap : InternedFreshOrdinaryDepthHeap.Heap state) :
    Checked (buildMany expressions (names.map Value.reference) state)
      (fun values => Matches values (evaluateMany expressions (names.map literal))) := by
  simpa only [literal_inputs] using
    InternedRecordDepthExecution.buildMany_depth expressions (names.map Value.reference) state context heap

/-- Actual surviving source edges have exactly the pure edge interpreter's maximum child depth. -/
theorem buildEdges_depth [DecidableEq (EdgeKey Symbol Guard)] (expressions : List (EdgeSyntax Symbol Guard))
    (names : List Reference) (state : State Symbol Guard) (context : Context state (names.map Value.reference))
    (heap : InternedFreshOrdinaryDepthHeap.Heap state) :
    Checked (buildEdges expressions (names.map Value.reference) state)
      (fun edges => maximumDepth ((surviving edges).flatMap EdgeValue.children) = (evaluateEdges expressions (names.map literal)).depth) := by
  simpa only [literal_inputs] using
    InternedRecordDepthExecution.buildEdges_depth expressions (names.map Value.reference) state context heap

/-- Every actual normalized callback has its syntax-derived depth and complete deep-name response. -/
theorem callback_depth [DecidableEq (EdgeKey Symbol Guard)] (body : Syntax Symbol Guard)
    (names : List Reference) (argument : Reference) (state : State Symbol Guard)
    (context : Context state (names.map Value.reference)) (available : Available state (.reference argument))
    (heap : InternedFreshOrdinaryDepthHeap.Heap state) :
    Checked (callback body (names.map Value.reference) argument state)
      (fun value => value.depth = (InternedDepthFreeProjectionCallback.symbolic body names).depth ∧
        InternedFreshOrdinaryDepthHeap.Observed (InternedDepthFreeProjectionCallback.captured body names)
          (InternedDepthFreeProjectionCallback.uses body names) argument value) :=
  InternedFreshOrdinaryDepthComposition.callback_checked body names argument state context available
    (build_depth body (argument :: names) state (by simpa only [List.map_cons] using context.local argument available) heap)

/-- Two actual completed callbacks with the same literal captures have identical cached depth for any supplied names. -/
theorem arguments_depth [DecidableEq (EdgeKey Symbol Guard)] (body : Syntax Symbol Guard)
    (names : List Reference) (firstName secondName : Reference) (firstState secondState : State Symbol Guard)
    (firstContext : Context firstState (names.map Value.reference)) (secondContext : Context secondState (names.map Value.reference))
    (firstAvailable : Available firstState (.reference firstName)) (secondAvailable : Available secondState (.reference secondName))
    (firstHeap : InternedFreshOrdinaryDepthHeap.Heap firstState) (secondHeap : InternedFreshOrdinaryDepthHeap.Heap secondState)
    (first second : Value Symbol Guard) (afterFirst afterSecond : State Symbol Guard)
    (firstDone : callback body (names.map Value.reference) firstName firstState = .done first afterFirst)
    (secondDone : callback body (names.map Value.reference) secondName secondState = .done second afterSecond) : first.depth = second.depth :=
  ((callback_depth body names firstName firstState firstContext firstAvailable firstHeap).result _ _ firstDone).1.trans
    ((callback_depth body names secondName secondState secondContext secondAvailable secondHeap).result _ _ secondDone).1.symm

/-- Every closed source execution derives the decoded heap, including when its outcome is pending. -/
theorem closed_heap [DecidableEq (EdgeKey Symbol Guard)] (expression : Syntax Symbol Guard) :
    InternedFreshOrdinaryDepthHeap.Heap (build expression [] empty).state :=
  (build_depth expression [] empty InternedFreshOrdinaryContext.empty_context InternedFreshOrdinaryDepthHeap.empty_heap).heap

/-- A completed closed source expression has exactly the independent pure depth and deep names. -/
theorem closed_observed [DecidableEq (EdgeKey Symbol Guard)] (expression : Syntax Symbol Guard)
    (value : Value Symbol Guard) (state : State Symbol Guard) (done : build expression [] empty = .done value state) :
    Observed value (evaluate expression []) :=
  (build_depth expression [] empty InternedFreshOrdinaryContext.empty_context InternedFreshOrdinaryDepthHeap.empty_heap).result value state done

end MicroCFTA.InternedFreshOrdinarySourceDepth
