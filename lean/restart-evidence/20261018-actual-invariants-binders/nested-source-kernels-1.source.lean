import MicroCFTA.SourceCurrentNestedSourceInertBinder

set_option linter.all true
set_option maxHeartbeats 3000000
set_option maxRecDepth 30000

namespace MicroCFTA.NestedSourceKernels
open Cache InternedConstructorTemplates InternedProbeProvenance InternedRecordCoherence
open InternedNestedConstruction (Syntax Outcome)
open InternedFreshOrdinaryConstruction InternedFreshOrdinaryFacts
open InternedBinderProtocol (Reference)
open SourceEqualityRequiredCache (Ready Keeps)
open SourceCurrentNativeMuPublication (Publication History)
open SourceCurrentNestedSourceInertBinder (Inert)

private def output (outcome : Outcome Nat Bool (Value Nat Bool)) :=
  match outcome with | .done value _ => value | .pending .. => .empty
private def captureSource : Syntax Nat Bool := .binder false (.node [.mk 3 true [.var 0]])
private def captureCall := build captureSource [] (empty (Symbol := Nat) (Guard := Bool))
private def capture := output captureCall
private def base := captureCall.state
private theorem captureDone : build captureSource [] empty = .done capture base := by cbv
private theorem baseReady : Ready base := SourceEqualityRequiredCache.constructed captureSource capture base captureDone
private theorem captureAvailable : Available base capture :=
  (build_verified captureSource [] empty InternedStoredMuOrigins.empty_normal.facts (by simp [Values])).result capture base captureDone
private theorem baseHistory : History empty base := by
  simpa only [base] using SourceCurrentNativeMuPublication.closed_history captureSource

private def expression : Syntax Nat Bool := .union [
  .binder false (.node [.mk 7 false [.var 0,.var 2]]),
  .node [.mk 9 true [.empty,.var 0]]]
private def captures := [capture]
private def depthCall := callback expression captures .depth base
private def ordinaryCall := callback expression captures (.uninterned (ordinaryLevel (output depthCall))) depthCall.state
private def key := muKey (output depthCall) (output ordinaryCall)
private def reserved := Cache.intern ordinaryCall.state.nodes key
private def allocated := {ordinaryCall.state with nodes := reserved.2}
private def bodyCall := callback expression captures (.interned reserved.1.identity) allocated
private def event : Publication (Symbol := Nat) (Guard := Bool) where
  smart := false
  expression := expression
  environment := captures
  before := base
  afterDepth := depthCall.state
  cut := ordinaryCall.state
  afterBody := bodyCall.state
  depth := output depthCall
  ordinary := output ordinaryCall
  body := output bodyCall
  context := ⟨SourceRecursiveIntersectionSemanticHeap.context base baseReady.semantic captures (by
    intro value member
    rcases List.mem_singleton.mp member with rfl
    exact captureAvailable),baseReady.semantic.2⟩
  depthDone := by cbv
  ordinaryDone := by cbv
  missing := by cbv
  bodyDone := by cbv
private def reader := event.after
private theorem actual : build (.binder false expression) captures base = .done event.result reader := event.build_done

private theorem sourceKeeps (source : Syntax Nat Bool) (inputs : List (Value Nat Bool))
    (before after : State Nat Bool) (ready : Ready before) (available : Values before inputs)
    (value : Value Nat Bool) (actual : build source inputs before = .done value after) : Keeps before after := by
  have context := SourceRecursiveIntersectionSemanticHeap.context before ready.semantic inputs available
  have checked := build_verified source inputs before ready.semantic.1.normal.facts available
  refine ⟨⟨?_,?_,?_⟩,?_,?_⟩
  · simpa only [actual,Outcome.state] using SourceRecursiveIntersectionSemanticHeap.source source inputs before ready.semantic available
  · exact InternedFreshOrdinaryCoverage.build_covered source inputs before ready.semantic.1.normal.facts.coherent.valid
      ready.covered value after actual
  · simpa only [actual,Outcome.state] using
      (InternedOpenDepthExecution.build_depth source inputs before context ready.semantic.2 ready.depth).heap
  · simpa only [actual,Outcome.state] using checked.growth
  · simpa only [actual,Outcome.state] using checked.history
private theorem capturesAvailable : Values base captures := by
  intro value member
  rcases List.mem_singleton.mp member with rfl
  exact captureAvailable
private theorem kept : Keeps base reader := sourceKeeps (.binder false expression) captures base reader baseReady capturesAvailable event.result actual
private theorem current : Keeps event.afterBody reader :=
  ⟨kept.ready,⟨extends_refl _,extends_refl _,extends_refl _,keepFirst_extends _ _ _⟩,extends_refl _⟩
private theorem readerHistory : History empty reader := by
  obtain ⟨history⟩ := SourceCurrentNativeMuPublication.build_history (.binder false expression) captures base
    ⟨SourceRecursiveIntersectionSemanticHeap.context base baseReady.semantic captures capturesAvailable,baseReady.semantic.2⟩
  exact .trans baseHistory (by simpa only [actual,Outcome.state] using history)
private theorem inert : Inert event.expression event.environment := by cbv
private theorem notFree : ¬ InternedStoredShallowCompletion.BinderFree event.expression := by
  simp [event,expression,InternedStoredShallowCompletion.BinderFree,InternedStoredShallowCompletion.ManyBinderFree]
private theorem nestedUsed : ∃ entry body depth ordinary, event.body = .mu entry body depth ordinary ∧
    InternedFreshOrdinaryDepthHeap.usesLocal depth ordinary = true := by
  refine ⟨_,_,_,_,?_,?_⟩ <;> cbv

private theorem publication_proof :
    build captureSource [] empty = .done capture base ∧
    build (.binder false expression) captures base = .done event.result reader ∧
    Inert event.expression event.environment ∧
    ¬ InternedStoredShallowCompletion.BinderFree event.expression ∧
    (∃ entry body depth ordinary, event.body = .mu entry body depth ordinary ∧
      InternedFreshOrdinaryDepthHeap.usesLocal depth ordinary = true) ∧
    event.body = event.ordinary ∧
    ∃ result after,
      InternedFreshOrdinaryStoredSubstitution.execute event.body
        (fun name => if name = .interned event.entry.identity then some capture else none) reader = .done result after ∧
      InternedFreshOrdinaryStoredSubstitution.execute event.ordinary
        (fun name => if name = .uninterned (ordinaryLevel event.depth) then some capture else none) after = .done result after ∧
      InternedFreshOrdinaryStoredSubstitution.execute event.body
        (fun name => if name = .interned event.entry.identity then some capture else none) after = .done result after ∧
      Keeps reader after ∧ Available after result ∧ Nonempty (History reader after) := by
  obtain ⟨same,result,after,first,second,warm,keeps,available,history⟩ :=
    SourceCurrentNestedSourceInertBinder.publication_inert event inert reader current capture
      (kept.available capture captureAvailable)
  exact ⟨captureDone,actual,inert,notFree,nestedUsed,same,result,after,first,second,warm,keeps,available,history⟩

/-- A used nested source binder and recursive capture satisfy the inert outer publication producer. -/
theorem publication :
    build captureSource [] empty = .done capture base ∧
    build (.binder false expression) captures base = .done event.result reader ∧
    Inert event.expression event.environment ∧
    ¬ InternedStoredShallowCompletion.BinderFree event.expression ∧
    (∃ entry body depth ordinary, event.body = .mu entry body depth ordinary ∧
      InternedFreshOrdinaryDepthHeap.usesLocal depth ordinary = true) ∧
    event.body = event.ordinary ∧
    ∃ result after,
      InternedFreshOrdinaryStoredSubstitution.execute event.body
        (fun name => if name = .interned event.entry.identity then some capture else none) reader = .done result after ∧
      InternedFreshOrdinaryStoredSubstitution.execute event.ordinary
        (fun name => if name = .uninterned (ordinaryLevel event.depth) then some capture else none) after = .done result after ∧
      InternedFreshOrdinaryStoredSubstitution.execute event.body
        (fun name => if name = .interned event.entry.identity then some capture else none) after = .done result after ∧
      Keeps reader after ∧ Available after result ∧ Nonempty (History reader after) := publication_proof

private theorem warm_proof :
    build (.binder true expression) captures reader = .done event.body reader ∧
    ∃ depth afterDepth raw afterRaw after,
      callback expression captures .depth reader = .done depth afterDepth ∧
      build expression (.reference (.uninterned (ordinaryLevel depth)) :: captures) afterDepth = .done raw afterRaw ∧
      run (withoutSelfReference (.uninterned (ordinaryLevel depth)) raw) afterRaw = (raw,afterRaw) ∧
      callback expression captures (.uninterned (ordinaryLevel depth)) afterDepth = .done raw afterRaw ∧
      build (.binder true expression) captures reader = .done raw after ∧
      InternedNestedConstruction.request true depth raw (callback expression captures) afterRaw = .done raw after ∧
      .uninterned (ordinaryLevel depth) ∉ raw.free ∧
      InternedFreshOrdinaryDepthHeap.usesLocal depth raw = false ∧
      Keeps reader after ∧ Available after raw ∧
      Nonempty (History reader after) ∧ Nonempty (History empty after) := by
  constructor
  · cbv
  · exact SourceCurrentNestedSourceInertBinder.complete expression captures reader kept.ready
      (fun value member => kept.available value (capturesAvailable value member)) readerHistory inert

/-- The smart warm call selects the earlier raw winner and constructs its raw ordinary result. -/
theorem warm :
    build (.binder true expression) captures reader = .done event.body reader ∧
    ∃ depth afterDepth raw afterRaw after,
      callback expression captures .depth reader = .done depth afterDepth ∧
      build expression (.reference (.uninterned (ordinaryLevel depth)) :: captures) afterDepth = .done raw afterRaw ∧
      run (withoutSelfReference (.uninterned (ordinaryLevel depth)) raw) afterRaw = (raw,afterRaw) ∧
      callback expression captures (.uninterned (ordinaryLevel depth)) afterDepth = .done raw afterRaw ∧
      build (.binder true expression) captures reader = .done raw after ∧
      InternedNestedConstruction.request true depth raw (callback expression captures) afterRaw = .done raw after ∧
      .uninterned (ordinaryLevel depth) ∉ raw.free ∧
      InternedFreshOrdinaryDepthHeap.usesLocal depth raw = false ∧
      Keeps reader after ∧ Available after raw ∧
      Nonempty (History reader after) ∧ Nonempty (History empty after) := warm_proof

end MicroCFTA.NestedSourceKernels
