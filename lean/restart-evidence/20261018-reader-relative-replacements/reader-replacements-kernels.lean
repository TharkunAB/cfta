import MicroCFTA.SourceCurrentReaderReplacementSlots
import MicroCFTA.SourceCurrentReaderObservations
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
private theorem source_positions : (children root)[0]? = some left ∧ (children root)[1]? = some right := by
  constructor <;> cbv
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
  ∃ (entry : Interned NodeKey) (edge : Interned (EdgeKey Nat Bool)) (depth : Nat) (free : List Reference),
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

private theorem no_reference {child parent : Value Nat Bool} (layer : Layer child parent) (name : Reference) :
    ¬ ReferenceOrigin reader [parent] name := by
  obtain ⟨entry,edge,depth,free,shape,_symbol,_guard⟩ := layer
  rw [shape,SourceCurrentOpenObservations.reference_expand reader _ (fun _ impossible => by cases impossible) name]
  change ¬ ReferenceOrigin reader [] name
  rw [SourceCurrentOpenObservations.reference_seeds]
  rintro ⟨_,impossible,_⟩
  cases impossible

private theorem layer_zero {a b first second : Value Nat Bool} (one : Layer a first) (two : Layer b second) :
    Same 0 reader [first] [second] :=
  fun name => iff_of_false (no_reference one name) (no_reference two name)

private theorem layer_same (depth : Nat) {a b first second : Value Nat Bool}
    (one : Layer a first) (two : Layer b second) (related : Same depth reader [a] [b]) :
    Same (depth + 1) reader [first] [second] := by
  obtain ⟨entry,edge,level,free,shape,symbol,guard⟩ := one
  obtain ⟨other,paired,otherLevel,otherFree,otherShape,otherSymbol,otherGuard⟩ := two
  rw [shape,otherShape]
  apply SourceCurrentOpenObservationConstructors.node depth reader
  · intro selected member
    obtain rfl := List.mem_singleton.mp member
    exact ⟨.mk paired [b],List.mem_singleton_self _,symbol.trans otherSymbol.symm,
      guard.trans otherGuard.symm,.cons related .nil⟩
  · intro selected member
    obtain rfl := List.mem_singleton.mp member
    exact ⟨.mk edge [a],List.mem_singleton_self _,otherSymbol.trans symbol.symm,
      otherGuard.trans guard.symm,.cons related.symm .nil⟩

private theorem left_observations (depth : Nat) : Same depth reader [left] [firstLayer] :=
  SourceCurrentOpenObservations.unfold depth reader firstEvent.entry firstEvent.body firstEvent.depth
    firstEvent.ordinary firstLayer reader unfold_left
private theorem right_observations (depth : Nat) : Same depth reader [right] [secondLayer] :=
  SourceCurrentOpenObservations.unfold depth reader secondEvent.entry secondEvent.body secondEvent.depth
    secondEvent.ordinary secondLayer reader unfold_right

private theorem finite (depth : Nat) :
    Same depth reader [left] [right] ∧ Same depth reader [left] [rightLayer] := by
  induction depth with
  | zero =>
      exact ⟨(left_observations 0).trans ((layer_zero first_layer second_layer).trans (right_observations 0).symm),
        (left_observations 0).trans (layer_zero first_layer right_layer)⟩
  | succ depth ih =>
      exact ⟨(left_observations (depth + 1)).trans
          ((layer_same depth first_layer second_layer ih.2).trans (right_observations (depth + 1)).symm),
        (left_observations (depth + 1)).trans (layer_same depth first_layer right_layer ih.1)⟩

private theorem related : Related reader left right := by
  refine ⟨?_,fun depth => (finite depth).1⟩
  change ((InternedBinderProtocol.NodeRef.mu firstEvent.entry.identity = .empty) ↔
    (InternedBinderProtocol.NodeRef.mu secondEvent.entry.identity = .empty))
  constructor <;> intro impossible <;> cases impossible

private def firstMap : Environment Nat Bool := bind (.interned firstEvent.entry.identity) left (fun _ => none)
private def secondMap : Environment Nat Bool := bind (.interned secondEvent.entry.identity) right (fun _ => none)
private theorem reference_execute (name : Reference) (environment : Environment Nat Bool) (state : State Nat Bool) :
    execute (.reference name) environment state = .done ((environment name).getD (.reference name)) state := by
  simp [execute,InternedStoredSubstitution.leaves,Value.free,InternedStoredSubstitution.encode,
    InternedStoredSubstitution.slot,build,InternedStoredSubstitution.input]
private theorem first_variable :
    (build (.var 0) [.reference (.interned firstEvent.entry.identity)] reader).bind
      (fun value current => execute value firstMap current) = .done left reader := by
  simp only [build,List.getElem?_cons_zero,Option.getD_some,Outcome.bind]
  rw [reference_execute]
  simp only [firstMap,SourceCurrentStoredMuBinderChildLineage.bind,ite_true,Option.getD_some]
private theorem second_variable :
    (build (.var 0) [.reference (.interned secondEvent.entry.identity)] reader).bind
      (fun value current => execute value secondMap current) = .done right reader := by
  simp only [build,List.getElem?_cons_zero,Option.getD_some,Outcome.bind]
  rw [reference_execute]
  simp only [secondMap,SourceCurrentStoredMuBinderChildLineage.bind,ite_true,Option.getD_some]
private theorem first_reference_available : Available reader (.reference (.interned firstEvent.entry.identity)) := by
  apply reference_available
  intro identity member
  have same : identity = firstEvent.entry.identity := by
    simpa only [Value.free,List.mem_singleton,Reference.interned.injEq] using member
  subst identity
  exact ⟨firstEvent.key,by cbv⟩

private theorem witness :
    build source [] empty = .done root reader ∧ Ready reader ∧
    (children root)[0]? = some left ∧ (children root)[1]? = some right ∧
    reader.nodeRecords firstEvent.key = some left ∧ reader.nodeRecords secondEvent.key = some right ∧
    Available reader left ∧ Available reader right ∧ left ≠ right ∧ firstEvent.key ≠ secondEvent.key ∧
    InternedFreshOrdinaryDepthHeap.usesLocal firstEvent.depth firstEvent.ordinary = true ∧
    InternedFreshOrdinaryDepthHeap.usesLocal secondEvent.depth secondEvent.ordinary = true ∧
    unfold left reader = .done firstLayer reader ∧ unfold right reader = .done secondLayer reader ∧
    Related reader left right ∧
    Paired (Related reader) firstMap secondMap
      [.reference (.interned firstEvent.entry.identity)] [.reference (.interned secondEvent.entry.identity)] ∧
    (build (.var 0) [.reference (.interned firstEvent.entry.identity)] reader).bind
      (fun value current => execute value firstMap current) = .done left reader ∧
    (build (.var 0) [.reference (.interned secondEvent.entry.identity)] reader).bind
      (fun value current => execute value secondMap current) = .done right reader ∧
    ∃ rawFirst afterFirst rawSecond afterSecond,
      build firstEvent.expression [.reference (.interned firstEvent.entry.identity)] firstEvent.allocated = .done rawFirst afterFirst ∧
      run (withoutSelfReference (.interned firstEvent.entry.identity) rawFirst) afterFirst = (firstEvent.body,firstEvent.afterBody) ∧
      build secondEvent.expression [.reference (.interned secondEvent.entry.identity)] secondEvent.allocated = .done rawSecond afterSecond ∧
      run (withoutSelfReference (.interned secondEvent.entry.identity) rawSecond) afterSecond = (secondEvent.body,secondEvent.afterBody) ∧
      Grows afterFirst firstEvent.afterBody ∧ Grows afterSecond secondEvent.afterBody := by
  have paired : Paired (Related reader) (fun _ => none) (fun _ => none) firstEvent.environment secondEvent.environment := .nil
  obtain ⟨_firstFresh,_secondFresh,extended,raws⟩ :=
    SourceCurrentReaderReplacementSlots.publication_extend (Related reader) firstEvent secondEvent
      (fun _ => none) (fun _ => none) paired left right related
  have observed := SourceCurrentReaderReplacementSlots.reference (Related reader)
    (SourceCurrentReaderObservations.Related.refl reader) reader ready.semantic.1.normal.facts.coherent
    firstMap secondMap [.reference (.interned firstEvent.entry.identity)] [.reference (.interned secondEvent.entry.identity)]
    extended (by
      intro value member
      obtain rfl := List.mem_singleton.mp member
      exact first_reference_available)
    0 left right reader reader first_variable second_variable
  exact ⟨actual,ready,source_positions.1,source_positions.2,present_left,present_right,available_left,available_right,distinct,distinct_keys,used.1,used.2,
    unfold_left,unfold_right,observed.1,extended,first_variable,second_variable,raws⟩

/-- Distinct source-built used Mu values supply related replacements at one reader and both actual publication bindings. -/
theorem distinct_used_replacements :
    build source [] empty = .done root reader ∧ Ready reader ∧
    (children root)[0]? = some left ∧ (children root)[1]? = some right ∧
    reader.nodeRecords firstEvent.key = some left ∧ reader.nodeRecords secondEvent.key = some right ∧
    Available reader left ∧ Available reader right ∧ left ≠ right ∧ firstEvent.key ≠ secondEvent.key ∧
    InternedFreshOrdinaryDepthHeap.usesLocal firstEvent.depth firstEvent.ordinary = true ∧
    InternedFreshOrdinaryDepthHeap.usesLocal secondEvent.depth secondEvent.ordinary = true ∧
    unfold left reader = .done firstLayer reader ∧ unfold right reader = .done secondLayer reader ∧
    Related reader left right ∧
    Paired (Related reader) firstMap secondMap
      [.reference (.interned firstEvent.entry.identity)] [.reference (.interned secondEvent.entry.identity)] ∧
    (build (.var 0) [.reference (.interned firstEvent.entry.identity)] reader).bind
      (fun value current => execute value firstMap current) = .done left reader ∧
    (build (.var 0) [.reference (.interned secondEvent.entry.identity)] reader).bind
      (fun value current => execute value secondMap current) = .done right reader ∧
    ∃ rawFirst afterFirst rawSecond afterSecond,
      build firstEvent.expression [.reference (.interned firstEvent.entry.identity)] firstEvent.allocated = .done rawFirst afterFirst ∧
      run (withoutSelfReference (.interned firstEvent.entry.identity) rawFirst) afterFirst = (firstEvent.body,firstEvent.afterBody) ∧
      build secondEvent.expression [.reference (.interned secondEvent.entry.identity)] secondEvent.allocated = .done rawSecond afterSecond ∧
      run (withoutSelfReference (.interned secondEvent.entry.identity) rawSecond) afterSecond = (secondEvent.body,secondEvent.afterBody) ∧
      Grows afterFirst firstEvent.afterBody ∧ Grows afterSecond secondEvent.afterBody := witness

end MicroCFTA.ReaderReplacementKernels
