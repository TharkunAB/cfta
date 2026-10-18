import MicroCFTA.SourceCurrentReaderReplacementSlots
import MicroCFTA.SourceEqualityRequiredCache
import MicroCFTA.SourceCurrentOpenObservationConstructors

set_option linter.all true
set_option maxRecDepth 30000
set_option maxHeartbeats 5000000
set_option cbv.maxSteps 100000000

namespace MicroCFTA.ReaderReplacementKernels
open Cache Language InternedConstructorTemplates InternedProbeProvenance InternedRecordCoherence
open InternedNestedConstruction (Syntax Outcome)
open InternedFreshOrdinaryConstruction InternedFreshOrdinaryFacts
open InternedBinderProtocol (NodeKey Reference)
open SourceEqualityRequiredCache (Ready)
open SourceCurrentNativeMuPublication (Publication)
open SourceCurrentReaderObservations (Related)
open SourceCurrentOpenObservations (Same RowMatch ReferenceOrigin)
open SourceCurrentReaderReplacementSlots (Paired)
open SourceCurrentStoredMuBinderChildLineage (bind)
open InternedStoredSubstitution (Environment)
open InternedFreshOrdinaryStoredSubstitution (execute unfold)

private def value (outcome : Outcome Nat Bool (Value Nat Bool)) :=
  match outcome with | .done result _ => result | .pending .. => .empty
private def unary (child : Syntax Nat Bool) : Syntax Nat Bool := .node [.mk 0 false [child]]
private def firstBody : Syntax Nat Bool := unary (.var 0)
private def secondBody : Syntax Nat Bool := unary (unary (.var 0))
private def firstSource : Syntax Nat Bool := .binder false firstBody
private def secondSource : Syntax Nat Bool := .binder false secondBody
private def firstDepth := callback firstBody [] .depth (empty (Symbol := Nat) (Guard := Bool))
private def firstOrdinary := callback firstBody [] (.uninterned (ordinaryLevel (value firstDepth))) firstDepth.state
private def firstKey := muKey (value firstDepth) (value firstOrdinary)
private def firstReserved := Cache.intern firstOrdinary.state.nodes firstKey
private def firstAllocated := {firstOrdinary.state with nodes := firstReserved.2}
private def firstCallback := callback firstBody [] (.interned firstReserved.1.identity) firstAllocated
private def firstEvent : Publication (Symbol := Nat) (Guard := Bool) where
  smart := false
  expression := firstBody
  environment := []
  before := empty
  afterDepth := firstDepth.state
  cut := firstOrdinary.state
  afterBody := firstCallback.state
  depth := value firstDepth
  ordinary := value firstOrdinary
  body := value firstCallback
  context := SourceCurrentConstrainedCapSourceHistory.empty_context
  depthDone := by cbv
  ordinaryDone := by cbv
  missing := by cbv
  bodyDone := by cbv
private theorem first_actual : build firstSource [] empty = .done firstEvent.result firstEvent.after := firstEvent.build_done
private def secondDepth := callback secondBody [] .depth firstEvent.after
private def secondOrdinary := callback secondBody [] (.uninterned (ordinaryLevel (value secondDepth))) secondDepth.state
private def secondKey := muKey (value secondDepth) (value secondOrdinary)
private def secondReserved := Cache.intern secondOrdinary.state.nodes secondKey
private def secondAllocated := {secondOrdinary.state with nodes := secondReserved.2}
private def secondCallback := callback secondBody [] (.interned secondReserved.1.identity) secondAllocated
private def secondEvent : Publication (Symbol := Nat) (Guard := Bool) where
  smart := false
  expression := secondBody
  environment := []
  before := firstEvent.after
  afterDepth := secondDepth.state
  cut := secondOrdinary.state
  afterBody := secondCallback.state
  depth := value secondDepth
  ordinary := value secondOrdinary
  body := value secondCallback
  context := by
    have retained := SourceCurrentConstrainedCapSourceHistory.empty_context.build firstSource
    simpa only [first_actual,Outcome.state] using retained
  depthDone := by cbv
  ordinaryDone := by cbv
  missing := by cbv
  bodyDone := by cbv
private def source : Syntax Nat Bool := .node [.mk 9 true [firstSource,secondSource,
  unary firstSource,unary secondSource,unary (unary secondSource)]]
private def built := build source [] empty
private def root : Value Nat Bool := value built
private def reader := built.state
private def left : Value Nat Bool := firstEvent.candidate
private def right : Value Nat Bool := secondEvent.candidate
private def firstLayer : Value Nat Bool := (children root)[2]?.getD .empty
private def rightLayer : Value Nat Bool := (children root)[3]?.getD .empty
private def secondLayer : Value Nat Bool := (children root)[4]?.getD .empty
private theorem actual : build source [] empty = .done root reader := by cbv
private theorem ready : Ready reader := SourceEqualityRequiredCache.constructed source root reader actual
private theorem present_left : reader.nodeRecords firstEvent.key = some left := by cbv
private theorem present_right : reader.nodeRecords secondEvent.key = some right := by cbv
private theorem available_left : Available reader left := ready.semantic.1.normal.facts.cached.nodes _ _ present_left
private theorem available_right : Available reader right := ready.semantic.1.normal.facts.cached.nodes _ _ present_right
private theorem unfold_left : unfold left reader = .done firstLayer reader := by cbv
private theorem unfold_right : unfold right reader = .done secondLayer reader := by cbv
private theorem used : InternedFreshOrdinaryDepthHeap.usesLocal firstEvent.depth firstEvent.ordinary = true ∧
    InternedFreshOrdinaryDepthHeap.usesLocal secondEvent.depth secondEvent.ordinary = true := by
  constructor <;> cbv
private theorem distinct : left ≠ right := by
  intro same
  have ids := congrArg Value.referenceOf same
  cbv at ids
  cases ids
private theorem distinct_keys : firstEvent.key ≠ secondEvent.key := by
  intro same
  cbv at same
  cases same

private def Layer (child parent : Value Nat Bool) : Prop :=
  ∃ (entry : Interned NodeKey) (edge : Interned (EdgeKey Nat Bool)) depth free,
    parent = .node entry [.mk edge [child]] depth free ∧ edge.key.symbol = 0 ∧ edge.key.constraint = false
private def nodeFields : Value Nat Bool → Interned NodeKey × List (EdgeValue Nat Bool) × Nat × List Reference
  | .node entry rows depth free => (entry,rows,depth,free)
  | _ => (⟨0,.node []⟩,[],0,[])
private def row (parent : Value Nat Bool) : EdgeValue Nat Bool :=
  match InternedEdgeResidency.nodeEdges parent with
  | first :: _ => first
  | [] => .mk ⟨0,⟨0,[],false⟩⟩ []
private theorem first_layer : Layer left firstLayer := by
  refine ⟨(nodeFields firstLayer).1,(row firstLayer).entry,firstLayer.depth,firstLayer.free,?_,?_,?_⟩ <;> cbv
private theorem right_layer : Layer right rightLayer := by
  refine ⟨(nodeFields rightLayer).1,(row rightLayer).entry,rightLayer.depth,rightLayer.free,?_,?_,?_⟩ <;> cbv
private theorem second_layer : Layer rightLayer secondLayer := by
  refine ⟨(nodeFields secondLayer).1,(row secondLayer).entry,secondLayer.depth,secondLayer.free,?_,?_,?_⟩ <;> cbv

end MicroCFTA.ReaderReplacementKernels
