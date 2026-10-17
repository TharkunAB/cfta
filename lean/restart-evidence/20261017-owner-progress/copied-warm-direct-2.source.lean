import MicroCFTA.SourceEqualityNormalizationReceipt
import MicroCFTA.SourceCurrentParentNumeric
import MicroCFTA.SourceCurrentAllocatedPartialInitialization
import MicroCFTA.SourceCurrentAllocatedPartialWorker

/-!
# A copied constrained child reaches its existing returned cell

The prefix relation follows the literal worker branches. A suffix starts
only after the preceding child has returned at its exact full caller.
The source-built example reaches the copied finite child before either
its root owner or its ordinary wrapper owner has completed.
This result describes one finite prefix. It does not prove general progress.
-/
set_option linter.all true
set_option maxHeartbeats 5000000
set_option maxRecDepth 30000
set_option cbv.maxSteps 30000000

namespace MicroCFTA.SourceCurrentOuterCopiedWarmHit
open Cache InternedConstructorTemplates InternedProbeProvenance SourceRecursiveIntersectionKernel InternedEdgeResidency
open InternedNestedConstruction (Syntax)
open SourceCurrentAllocatedPartialState
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "Edge" => EdgeValue Symbol Guard
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "EqValue" => SourceEqualityConstraintAllocation.Value
private instance : DecidableEq FullSyntax.Formula :=
  fun first second => decidable_of_iff (FormulaOrder.compareFormula first second = .eq)
    (FormulaOrder.formula_eq first second)
private instance : DecidableEq (SourceGuards.Guard FullSyntax.Formula) := SourceEqualityPCSNativeEdge.guardDecidableEq
private instance : DecidableEq Guard := fun first second =>
  decidable_of_iff (first.equalities = second.equalities ∧ first.guard = second.guard)
    (by cases first; cases second; simp)
private noncomputable instance : DecidableEq (Value Symbol Guard) := by classical exact inferInstance

private theorem array_small (classes : EqualityNormalize.Constraints) :
    SourceCompactGuards.arrayNormalize classes = SourceEqualityNormalizationReceipt.observed 16 classes :=
  SourceEqualityNormalizationReceipt.observed_eq 16 classes
attribute [local cbv_eval] array_small


/-- A phase retains its literal remaining outer fuel and complete caller. -/
inductive Phase (width : Nat) : Type 1 where
  /-- The node result table has not yet been demanded. -/
  | node (fuel : Nat) (request : NodeRequest) (before : Caller width)
  /-- The demanded node owner is already evaluating. -/
  | body (fuel : Nat) (request : NodeRequest) (before : Caller width)
  /-- Original rows run in source order. -/
  | rows (fuel : Nat) (inherited : EqValue) (values : List Edge) (before : Caller width)
  /-- The completed parent edge supplies the descendant field and children. -/
  | descendants (fuel : Nat) (inherited : EqValue) (edge : Edge) (before : Caller width)
  /-- The inherited prefix has completed at its exact operation state. -/
  | children (fuel : Nat) (combined : EqValue) (values : List Node) (before : Caller width)
  /-- The indexed walk retains the current caller after all earlier children. -/
  | walk (fuel : Nat) (combined : EqValue) (index : Nat) (values : List Node) (before : Caller width)

/-- Each transition is a literal branch or an actual completed prefix of the worker. -/
inductive Step (g s r e p h m c n budget : Nat) : Phase width → Phase width → Prop where
  /-- Demand enters only the stored evaluating request. -/
  | node_evaluate (actual : beginNode request before = (handle, .evaluate original, running)) :
      Step g s r e p h m c n budget (.node fuel request before) (.body fuel original running)
  /-- An ordinary body enters its original row list. -/
  | body_rows (actual : request.value = .node entry originals depth free) :
      Step g s r e p h m c n budget (.body (fuel + 1) request before)
        (.rows fuel request.inherited originals before)
  /-- Descendants start at the complete returned edge caller. -/
  | rows_edge (actual : SourceCurrentAllocatedPartialWorker.edgeCall fuel g s r e p h m c n budget
        ⟨inherited, original⟩ before = .done narrowed middle) :
      Step g s r e p h m c n budget (.rows (fuel + 1) inherited (original :: rest) before)
        (.descendants fuel inherited narrowed middle)
  /-- A successful inherited prefix enters the returned edge children. -/
  | descendants_children {edge : Edge}
      (actual : (SourceCurrentAllocatedInheritedPrefix.run edge.entry.key.constraint inherited
        before.checked.operations).1 = .ok (some combined)) :
      Step g s r e p h m c n budget (.descendants fuel inherited edge before)
        (.children fuel combined edge.children (SourceCurrentAllocatedPartialGraph.prefixState before edge inherited))
  /-- A live inherited value enters the indexed walk at zero. -/
  | children_walk :
      Step g s r e p h m c n budget (.children fuel (.live identity records) values before)
        (.walk fuel (.live identity records) 0 values before)
  /-- The head request uses the actual descent at the current operation state. -/
  | walk_head :
      Step g s r e p h m c n budget (.walk (fuel + 1) combined index (value :: rest) before)
        (.node fuel ⟨(SourceCurrentAllocatedPartialGraph.descend before combined index).1, value⟩
          (SourceCurrentAllocatedPartialGraph.descend before combined index).2)
  /-- A suffix starts only after the head request has actually completed. -/
  | walk_tail (actual : SourceCurrentAllocatedPartialWorker.nodeCall fuel g s r e p h m c n budget
        ⟨(SourceCurrentAllocatedPartialGraph.descend before combined index).1, value⟩
        (SourceCurrentAllocatedPartialGraph.descend before combined index).2 = .done result middle) :
      Step g s r e p h m c n budget (.walk (fuel + 1) combined index (value :: rest) before)
        (.walk fuel combined (index + 1) rest middle)

/-- A reached phase has a finite chain of exact literal prefix transitions. -/
inductive Reached (g s r e p h m c n budget : Nat) : Phase width → Phase width → Prop where
  /-- The initial phase is reached without execution. -/
  | refl : Reached g s r e p h m c n budget phase phase
  /-- An exact prefix transition precedes the remaining reached prefix. -/
  | step (first : Step g s r e p h m c n budget before middle)
      (rest : Reached g s r e p h m c n budget middle after) :
      Reached g s r e p h m c n budget before after

private def plain : Guard := ⟨some [], .top⟩
private def inner : Guard := ⟨some [[[0], [1]]], .top⟩
private def outer : Guard := ⟨some [[[0], [1, 0]]], .top⟩
private def leaf : Syntax Symbol Guard := .node [.mk ("leaf", .top) plain []]
private def finite : Syntax Symbol Guard := .node [.mk ("pair", .top) inner [leaf, leaf]]
private def recursive : Syntax Symbol Guard :=
  .binder false (.node [.mk ("leaf", .top) plain [], .mk ("pair", .top) plain [.var 0, .var 0]])
private def expression : Syntax Symbol Guard := .node [.mk ("roots", .top) outer [finite, recursive]]
private def built := InternedFreshOrdinaryConstruction.build expression [] empty
private def original : Value Symbol Guard := match built with | .done value _ => value | .pending .. => .empty
private def heap := built.state
private def b := ((children original)[0]?).getD (Value.empty : Value Symbol Guard)
private def tau := ((children original)[1]?).getD (Value.empty : Value Symbol Guard)
private def first := SourceEqualityConstraintAllocation.construct outer.equalities Cache.emptyState
private def second := SourceEqualityConstraintAllocation.construct inner.equalities first.2
private def third := SourceEqualityConstraintAllocation.construct plain.equalities second.2
private def outerValue : SourceEqualityConstraintAllocation.Value := match first.1 with | .ok value => value | _ => .contradiction
private def innerValue : SourceEqualityConstraintAllocation.Value := match second.1 with | .ok value => value | _ => .contradiction
private def plainValue : SourceEqualityConstraintAllocation.Value := match third.1 with | .ok value => value | _ => .contradiction
private def before := SourceCurrentAllocatedPartialInitialization.caller 8 third.2 heap
private def sourceEdge : EdgeValue Symbol Guard :=
  ((nodeEdges original)[0]?).getD (run (makeEdge ("roots", .top) outer [b,tau]) heap).1

private theorem cached_inner : SourceEqualityGuardReadback.Cached inner.equalities := by
  have normal : EqualityNormalize.mkEqConstraints 2 [[[0], [1]]] = .normalized [[[0], [1]]] := by cbv
  intro classes same
  cases same
  exact SourceEqualityGuardReadback.normalized normal
private theorem cached_outer : SourceEqualityGuardReadback.Cached outer.equalities := by
  have normal : EqualityNormalize.mkEqConstraints 2 [[[0], [1, 0]]] = .normalized [[[0], [1, 0]]] := by cbv
  intro classes same
  cases same
  exact SourceEqualityGuardReadback.normalized normal
private theorem history : SourceEqualityOriginalAllocationHistory.History Cache.emptyState third.2 [outer,inner,plain] := by
  have one : SourceEqualityOriginalAllocationHistory.History Cache.emptyState first.2 [outer] := by
    simpa only [List.nil_append] using SourceEqualityOriginalAllocationHistory.History.construct
      (.start Cache.emptyState) cached_outer (show first = (.ok outerValue,first.2) by cbv)
  have two : SourceEqualityOriginalAllocationHistory.History Cache.emptyState second.2 [outer,inner] :=
    SourceEqualityOriginalAllocationHistory.History.construct one cached_inner (show second = (.ok innerValue,second.2) by cbv)
  exact SourceEqualityOriginalAllocationHistory.History.construct two SourceEqualityGuardReadback.empty_cached
    (show third = (.ok plainValue,third.2) by cbv)
private theorem built_done : built = .done original heap := by cbv
private theorem source_ready : SourceCurrentConjunctionClassScan.Ready before.checked ∧
    Available heap original ∧ original.free = [] ∧ SourceRecursiveIntersectionInputView.Original original := by
  have initial := SourceCurrentConjunctionClassHistoryEntry.constructed 8 history Cache.empty_valid expression
    (fun guard member => by
      simp only [expression,finite,leaf,recursive,SourceEqualityConstraintOrigins.guards,
        SourceEqualityConstraintOrigins.edgeGuards,SourceEqualityConstraintOrigins.childGuards,
        List.mem_cons,List.mem_append,List.not_mem_nil,or_false,or_assoc,false_or] at member
      rcases member with rfl | rfl | rfl | rfl | rfl | rfl <;> simp) original heap built_done
  have allocated := SourceEqualityMkEdgeAllocation.emptyField_correct _ initial.1.good.operations
  exact ⟨⟨⟨initial.1.good.native,initial.1.good.heap,allocated.1,initial.1.good.fields.grows allocated.2.1⟩,
    initial.1.semantic,initial.1.costs,initial.1.scopedCache,initial.1.idle⟩,initial.2⟩


private def rootRequest : NodeRequest := ⟨plainValue, original⟩
private def rootRunning := (beginNode rootRequest before).2.2
private noncomputable def rootEdgeCall := SourceCurrentAllocatedPartialWorker.edgeCall
  22 16 16 16 16 16 16 16 16 128 0 ⟨plainValue, sourceEdge⟩ rootRunning
private noncomputable def narrowed : Edge := match rootEdgeCall with
  | .done value _ => value | .failed .. => sourceEdge
private noncomputable def rootAfter := rootEdgeCall.state
private noncomputable def rootCombined : EqValue :=
  match (SourceCurrentAllocatedInheritedPrefix.run narrowed.entry.key.constraint plainValue rootAfter.checked.operations).1 with
  | .ok (some value) => value | _ => .contradiction
private noncomputable def rootPrefix := SourceCurrentAllocatedPartialGraph.prefixState rootAfter narrowed plainValue
private noncomputable def firstDescent := SourceCurrentAllocatedPartialGraph.descend rootPrefix rootCombined 0
private noncomputable def firstRequest : NodeRequest := ⟨firstDescent.1, b⟩
private noncomputable def firstCall := SourceCurrentAllocatedPartialWorker.nodeCall
  21 16 16 16 16 16 16 16 16 128 0 firstRequest firstDescent.2
private noncomputable def afterB := firstCall.state
private noncomputable def wrapper : Node := (narrowed.children[1]?).getD (Value.empty : Node)
private noncomputable def secondDescent := SourceCurrentAllocatedPartialGraph.descend afterB rootCombined 1
private noncomputable def wrapperRequest : NodeRequest := ⟨secondDescent.1, wrapper⟩
private noncomputable def wrapperRunning := (beginNode wrapperRequest secondDescent.2).2.2
private noncomputable def wrapperEdge : Edge :=
  ((nodeEdges wrapper)[0]?).getD sourceEdge
private noncomputable def wrapperEdgeCall := SourceCurrentAllocatedPartialWorker.edgeCall
  18 16 16 16 16 16 16 16 16 128 0 ⟨wrapperRequest.inherited, wrapperEdge⟩ wrapperRunning
private noncomputable def wrapperNarrowed : Edge := match wrapperEdgeCall with
  | .done value _ => value | .failed .. => wrapperEdge
private noncomputable def wrapperAfter := wrapperEdgeCall.state
private noncomputable def innerCombined : EqValue :=
  match (SourceCurrentAllocatedInheritedPrefix.run wrapperNarrowed.entry.key.constraint wrapperRequest.inherited
    wrapperAfter.checked.operations).1 with
  | .ok (some value) => value | _ => .contradiction
private noncomputable def innerPrefix :=
  SourceCurrentAllocatedPartialGraph.prefixState wrapperAfter wrapperNarrowed wrapperRequest.inherited
private noncomputable def copied : Node := (wrapperNarrowed.children[0]?).getD (Value.empty : Node)
private noncomputable def hitDescent := SourceCurrentAllocatedPartialGraph.descend innerPrefix innerCombined 0
private noncomputable def hitRequest : NodeRequest := ⟨hitDescent.1, copied⟩
private noncomputable def atHit := hitDescent.2

private theorem prefix_facts :
    beginNode rootRequest before = (0, .evaluate rootRequest, rootRunning) ∧
    nodeEdges original = [sourceEdge] ∧
    rootEdgeCall = .done narrowed rootAfter ∧
    rootCombined = outerValue ∧
    narrowed.children = [b, wrapper] ∧
    firstCall = .done b afterB ∧
    beginNode firstRequest firstDescent.2 = (1, .evaluate firstRequest, (beginNode firstRequest firstDescent.2).2.2) ∧
    beginNode wrapperRequest secondDescent.2 = (3, .evaluate wrapperRequest, wrapperRunning) ∧
    nodeEdges wrapper = [wrapperEdge] ∧
    wrapperEdgeCall = .done wrapperNarrowed wrapperAfter ∧
    innerCombined = plainValue ∧
    wrapperNarrowed.children = [copied, tau] ∧
    copied = b ∧ firstRequest.key = hitRequest.key ∧
    atHit.nodeResults.table hitRequest.key = some 1 ∧
    atHit.nodeResults.cells 1 = some ⟨firstRequest, .returned b⟩ ∧
    atHit.nodeResults.cells 0 = some ⟨rootRequest, .evaluating⟩ ∧
    atHit.nodeResults.cells 3 = some ⟨wrapperRequest, .evaluating⟩ := by cbv

private theorem original_shape : ∃ entry depth free, original = .node entry [sourceEdge] depth free := by
  exact ⟨_, _, _, rfl⟩
private theorem wrapper_shape : ∃ entry depth free, wrapper = .node entry [wrapperEdge] depth free := by
  exact ⟨_, _, _, rfl⟩

private theorem reached : Reached 16 16 16 16 16 16 16 16 128 0
    (.node 24 rootRequest before) (.node 17 hitRequest atHit) := by
  obtain ⟨entry, depth, free, shape⟩ := original_shape
  obtain ⟨wrapperEntry, wrapperDepth, wrapperFree, wrapperShape⟩ := wrapper_shape
  have facts := prefix_facts
  rcases facts with ⟨rootStarted, originalRows, rootDone, rootLive, rootChildren,
    firstDone, firstStarted, wrapperStarted, wrapperRows, wrapperDone, innerLive,
    wrapperChildren, copiedB, sameKey, published, returned, rootActive, wrapperActive⟩
  have rootPrefixDone : (SourceCurrentAllocatedInheritedPrefix.run narrowed.entry.key.constraint plainValue
      rootAfter.checked.operations).1 = .ok (some outerValue) := by cbv
  have innerPrefixDone : (SourceCurrentAllocatedInheritedPrefix.run wrapperNarrowed.entry.key.constraint
      wrapperRequest.inherited wrapperAfter.checked.operations).1 = .ok (some plainValue) := by cbv
  refine .step (.node_evaluate rootStarted) ?_
  refine .step (.body_rows shape) ?_
  refine .step (.rows_edge rootDone) ?_
  refine .step (.descendants_children rootPrefixDone) ?_
  have liveOuter : ∃ identity records, outerValue = .live identity records := by exact ⟨_, _, rfl⟩
  obtain ⟨outerIdentity, outerRecords, liveOuter⟩ := liveOuter
  rw [liveOuter]
  refine .step .children_walk ?_
  rw [← liveOuter, ← rootLive, rootChildren]
  refine .step (.walk_tail firstDone) ?_
  refine .step .walk_head ?_
  refine .step (.node_evaluate wrapperStarted) ?_
  refine .step (.body_rows wrapperShape) ?_
  refine .step (.rows_edge wrapperDone) ?_
  refine .step (.descendants_children innerPrefixDone) ?_
  have livePlain : ∃ identity records, plainValue = .live identity records := by exact ⟨_, _, rfl⟩
  obtain ⟨plainIdentity, plainRecords, livePlain⟩ := livePlain
  rw [livePlain]
  refine .step .children_walk ?_
  rw [← livePlain, ← innerLive, wrapperChildren]
  exact .step .walk_head .refl

end MicroCFTA.SourceCurrentOuterCopiedWarmHit
