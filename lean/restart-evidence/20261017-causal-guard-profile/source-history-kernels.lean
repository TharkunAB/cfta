import MicroCFTA.SourceCurrentConstrainedCapSourceHistory
import MicroCFTA.InternedFreshOrdinaryClosedCompletion

set_option linter.all true
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.proofs true
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000

namespace MicroCFTA.SourceHistoryKernels
open Cache InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance InternedNestedFacts
open InternedNestedConstruction (Syntax Outcome work request finish)
open InternedFreshOrdinaryConstruction InternedFreshOrdinaryFacts
open SourceCurrentConstrainedCapSourceHistory
variable {Symbol Guard : Type}

private theorem callback_empty [DecidableEq (EdgeKey Symbol Guard)]
    (environment : List (Value Symbol Guard)) (name : InternedBinderProtocol.Reference) (state : State Symbol Guard) :
    callback .empty environment name state = .done .empty state := by
  simp [callback, build, Outcome.bind, work, withoutSelfReference, run]

/-- A raw Mu constructs its own actual body and retains the earlier joint observation heap. -/
theorem raw_empty_origin [DecidableEq (EdgeKey Symbol Guard)] :
    ∃ (entry : Interned InternedBinderProtocol.NodeKey) (after : State Symbol Guard),
      build (.binder false .empty) [] empty = .done (.mu entry .empty .empty .empty) after ∧
      after.nodeRecords (muKey (.empty : Value Symbol Guard) .empty) = some (.mu entry .empty .empty .empty) ∧
      Heap after ∧ Origin entry (.empty : Value Symbol Guard) .empty .empty := by
  let state := empty (Symbol := Symbol) (Guard := Guard)
  let key := muKey (.empty : Value Symbol Guard) .empty
  let entry := Cache.intern state.nodes key
  let allocated := {state with nodes := entry.2}
  let after := {allocated with nodeRecords := keepFirst allocated.nodeRecords key (.mu entry.1 .empty .empty .empty)}
  have actual : build (.binder false .empty) [] state = .done (.mu entry.1 .empty .empty .empty) after := by
    simp [build, Outcome.bind, work, withoutSelfReference, run, request, state, empty, key, entry, allocated, after, Cache.intern, Cache.emptyState, reserve, install,
      keepFirst, Cache.put, finish]
  have present : after.nodeRecords key = some (.mu entry.1 .empty .empty .empty) := by
    simp [after, allocated, state, empty, keepFirst, Cache.put]
  have history : Heap after := by
    change build (.binder false .empty) [] empty = _ at actual
    simpa only [actual, Outcome.state] using closed_origins (.binder false .empty : Syntax Symbol Guard)
  exact ⟨entry.1, after, actual, present, history, history key entry.1 .empty .empty .empty present⟩

/-- A pre-existing unfinished reservation produces a literal pending stop and retains all earlier histories. -/
theorem pending_reserved [DecidableEq (EdgeKey Symbol Guard)] :
    ∃ (state : State Symbol Guard) (key : InternedBinderProtocol.NodeKey),
      build (.binder false .empty) [] state = .pending key state ∧
      Heap (build (.binder false .empty) [] state).state ∧ Context state [] := by
  let original := empty (Symbol := Symbol) (Guard := Guard)
  let key := muKey (.empty : Value Symbol Guard) .empty
  let state := {original with nodes := (Cache.intern original.nodes key).2}
  have actual : build (.binder false .empty) [] state = .pending key state := by
    simp only [build, Outcome.bind, work, withoutSelfReference, run]
    change request false (.empty : Value Symbol Guard) .empty _ state = _
    simp only [request, state]
    rfl
  have context : Context state [] := empty_context.reserve key
  have heap : Heap state := empty_heap
  exact ⟨state, key, actual, build_origins _ _ _ context heap, context⟩

/-- A closed nested Mu run constructs its own result and carries each stored writer's historical depth heap. -/
theorem nested_constructed [DecidableEq (EdgeKey Symbol Guard)] (body : Syntax Symbol Guard) :
    ∃ (value : Value Symbol Guard) (after : State Symbol Guard),
      build (.binder false (.binder true body)) [] empty = .done value after ∧
      Heap after ∧ InternedFreshOrdinaryDepthHeap.Heap after := by
  obtain ⟨value, after, actual⟩ := InternedFreshOrdinaryClosedCompletion.closed_complete (.binder false (.binder true body))
  have history : Heap after := by simpa only [actual, Outcome.state] using closed_origins (.binder false (.binder true body))
  have joint : Context after [] := by simpa only [actual, Outcome.state] using empty_context.build (.binder false (.binder true body))
  exact ⟨value, after, actual, history, joint.depth⟩

#print axioms raw_empty_origin
#check @raw_empty_origin
#print axioms pending_reserved
#check @pending_reserved
#print axioms nested_constructed
#check @nested_constructed
end MicroCFTA.SourceHistoryKernels
