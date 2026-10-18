import MicroCFTA.SourceCurrentStoredLiteralExecutionParts
import MicroCFTA.SourceCurrentPublicationSharedReplacements
import MicroCFTA.SourceCurrentRetainedMuWriterAlignment
import MicroCFTA.SourceCurrentReaderFiniteOrdinaryStep

set_option linter.all true
set_option maxHeartbeats 5000000
set_option maxRecDepth 30000

namespace MicroCFTA.FilteredRootReview
open Cache Language InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedNestedConstruction (Syntax EdgeSyntax Outcome work)
open InternedFreshOrdinaryConstruction InternedFreshOrdinaryFacts
open InternedFreshOrdinaryStoredSubstitution (execute unfold)
open InternedBinderProtocol (Reference NodeKey)
open SourceEqualityRequiredCache (Ready Keeps)
open SourceCurrentNativeMuPublication (Publication History)
open SourceCurrentRetainedMuWriterAlignment (Writer)
open SourceCurrentReaderFiniteOrdinaryStep (RelatedAt)

private def value (outcome : Outcome Nat Bool (Value Nat Bool)) :=
  match outcome with | .done result _ => result | .pending .. => .empty
private def leaf : Syntax Nat Bool := .node [.mk 5 true []]
private def prefixSource : Syntax Nat Bool := .node [.mk 99 true [.binder false leaf,leaf]]
private def prefix := build prefixSource [] empty
private def prefixValue := value prefix
private def prefixState := prefix.state
private def first : Value Nat Bool := (children prefixValue)[0]?.getD .empty
private def second : Value Nat Bool := (children prefixValue)[1]?.getD .empty
private def nested : Syntax Nat Bool :=
  .binder true (.node [.mk 2 true [],.mk 3 false [.var 0,.var 2]])
private def rows : List (EdgeSyntax Nat Bool) := [.mk 8 false [.var 0]]
private def expression : Syntax Nat Bool := .union [.var 0,.node rows,nested]
private def requester : Syntax Nat Bool :=
  .union [.var 0,.node [.mk 8 false [.var 0],.mk 8 false [.var 0]],nested,.empty]
private def captures : List (Value Nat Bool) := [.reference .depth]
private def depthCall := callback expression captures .depth prefixState
private def ordinaryCall := callback expression captures (.uninterned (ordinaryLevel (value depthCall))) depthCall.state
private def key := muKey (value depthCall) (value ordinaryCall)
private def reserved := Cache.intern ordinaryCall.state.nodes key
private def allocated := {ordinaryCall.state with nodes := reserved.2}
private def bodyCall := callback expression captures (.interned reserved.1.identity) allocated
private def event : Publication (Symbol := Nat) (Guard := Bool) where
  smart := false
  expression := expression
  environment := captures
  before := prefixState
  afterDepth := depthCall.state
  cut := ordinaryCall.state
  afterBody := bodyCall.state
  depth := value depthCall
  ordinary := value ordinaryCall
  body := value bodyCall
  context := (SourceCurrentConstrainedCapSourceHistory.empty_context.build prefixSource).local
    .depth (InternedNestedProvenance.depth_available _)
  depthDone := by cbv
  ordinaryDone := by cbv
  missing := by cbv
  bodyDone := by cbv
private def reader := event.after
private theorem prefix_actual : build prefixSource [] empty = .done prefixValue prefixState := by cbv
private theorem actual : build (.binder false expression) captures prefixState = .done event.result reader := event.build_done
private theorem source_keeps (expression : Syntax Nat Bool) (inputs : List (Value Nat Bool))
    (before after : State Nat Bool) (ready : Ready before) (available : InternedNestedProvenance.Values before inputs)
    (value : Value Nat Bool) (actual : build expression inputs before = .done value after) : Keeps before after := by
  have context := SourceRecursiveIntersectionSemanticHeap.context before ready.semantic inputs available
  have checked := build_verified expression inputs before ready.semantic.1.normal.facts available
  refine ⟨⟨?_,?_,?_⟩,?_,?_⟩
  · simpa only [actual,Outcome.state] using SourceRecursiveIntersectionSemanticHeap.source expression inputs before ready.semantic available
  · exact InternedFreshOrdinaryCoverage.build_covered expression inputs before
      ready.semantic.1.normal.facts.coherent.valid ready.covered value after actual
  · simpa only [actual,Outcome.state] using
      (InternedOpenDepthExecution.build_depth expression inputs before context ready.semantic.2 ready.depth).heap
  · simpa only [actual,Outcome.state] using checked.growth
  · simpa only [actual,Outcome.state] using checked.history
private theorem kept : Keeps prefixState reader :=
  source_keeps (.binder false expression) captures prefixState reader
    (SourceEqualityRequiredCache.constructed prefixSource prefixValue prefixState prefix_actual)
    (by intro value member; obtain rfl := List.mem_singleton.mp member; exact InternedNestedProvenance.depth_available _)
    event.result actual
private theorem ready : Ready reader := kept.ready
private theorem replacements_available : Available reader first ∧ Available reader second := by
  have root := (InternedFreshOrdinaryFacts.closed_verified prefixSource).result prefixValue prefixState prefix_actual
  constructor
  · exact kept.available first (root.children first (by cbv; exact List.mem_cons_self))
  · exact kept.available second (root.children second (by cbv; exact List.mem_cons_of_mem _ List.mem_cons_self))

private theorem distinct : first ≠ second := by
  intro same
  have refs := congrArg Value.referenceOf same
  cbv at refs
  cases refs
private def firstEntry : Interned NodeKey := (entryOf first).getD ⟨0,.node []⟩
private def firstDepth : Value Nat Bool := match first with | .mu _ _ depth _ => depth | _ => .empty
private def firstOrdinary : Value Nat Bool := match first with | .mu _ _ _ ordinary => ordinary | _ => .empty
private theorem related (depth : Nat) (view : State Nat Bool) : RelatedAt depth view first second := by
  have shape : first = .mu firstEntry second firstDepth firstOrdinary := by cbv
  have closed : second.free = [] := by cbv
  have done : unfold (.mu firstEntry second firstDepth firstOrdinary) view = .done second view :=
    SourceCurrentStoredUnionObservations.closed second _ view closed
  refine ⟨?_,?_⟩
  · rw [shape]
    change ((InternedBinderProtocol.NodeRef.mu firstEntry.identity = .empty) ↔ second.referenceOf = .empty)
    have secondNotEmpty : second.referenceOf ≠ .empty := by cbv; intro impossible; cases impossible
    constructor
    · intro impossible; cases impossible
    · intro impossible; exact False.elim (secondNotEmpty impossible)
  · rw [shape]
    exact SourceCurrentOpenObservations.unfold depth view firstEntry second firstDepth firstOrdinary second view done

private theorem nested_raw (firstName secondName : Reference) (current : State Nat Bool) :
    build nested (.reference firstName :: captures) current = build nested (.reference secondName :: captures) current := by
  apply InternedFreshOrdinaryDependencies.build_congr
  intro index member
  have support : InternedNestedDependencies.inputs nested = [1] := by cbv
  rw [support] at member
  obtain rfl := List.mem_singleton.mp member
  rfl

end MicroCFTA.FilteredRootReview
