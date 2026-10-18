import MicroCFTA.SourceCurrentNativeUnusedRootDeletion
import MicroCFTA.SourceRecursiveIntersectionSemanticHeap

set_option linter.all true
set_option maxRecDepth 30000
set_option maxHeartbeats 5000000
set_option cbv.maxSteps 100000000

namespace MicroCFTA.UnusedRootDeletionIntegration
open Cache InternedConstructorTemplates InternedProbeProvenance
open InternedNestedConstruction (Syntax Outcome)
open InternedFreshOrdinaryConstruction (build ordinaryLevel)
open InternedFreshOrdinaryFacts (callback)
open InternedBinderProtocol (Reference)
open InternedRootProfile (Profile Equivalent)
open InternedFreshOrdinaryDepthHeap (usesLocal)
open SourceCurrentConstrainedCapSourceHistory (Context)
open SourceCurrentNativeMuPublication (History)
open SourceCurrentStoredRootDeletion (deleted)

private def expression (kind : Option (Option Bool)) : Syntax Nat Bool :=
  match kind with
  | none => .var 0
  | some none => .node [.mk 7 false []]
  | some (some false) => .var 1
  | some (some true) => .union [.var 0,.var 1]
private def captures : List (Value Nat Bool) := [.reference (.uninterned 10)]
private def result (call : Outcome Nat Bool (Value Nat Bool)) : Value Nat Bool :=
  match call with | .done value _ => value | .pending .. => .empty
private def cold (kind : Option (Option Bool)) := build (.binder true (expression kind)) captures empty
private def output (kind : Option (Option Bool)) := result (cold kind)
private def reader (kind : Option (Option Bool)) := (cold kind).state
private def before (kind : Option (Option Bool)) (warm : Bool) := if warm then reader kind else empty
private def depthCall (kind : Option (Option Bool)) (warm : Bool) :=
  callback (expression kind) captures .depth (before kind warm)
private def depthValue (kind : Option (Option Bool)) (warm : Bool) := result (depthCall kind warm)
private def ordinaryCall (kind : Option (Option Bool)) (warm : Bool) :=
  callback (expression kind) captures (.uninterned (ordinaryLevel (depthValue kind warm))) (depthCall kind warm).state
private def ordinaryValue (kind : Option (Option Bool)) (warm : Bool) := result (ordinaryCall kind warm)

private theorem done (kind : Option (Option Bool)) (warm : Bool) :
    build (.binder true (expression kind)) captures (before kind warm) = .done (output kind) (reader kind) := by
  cases kind with
  | none => cases warm <;> cbv
  | some mode =>
      cases mode with
      | none => cases warm <;> cbv
      | some flag => cases flag <;> cases warm <;> cbv
private theorem depth_done (kind : Option (Option Bool)) (warm : Bool) :
    callback (expression kind) captures .depth (before kind warm) =
      .done (depthValue kind warm) (depthCall kind warm).state := by
  cases kind with
  | none => cases warm <;> cbv
  | some mode =>
      cases mode with
      | none => cases warm <;> cbv
      | some flag => cases flag <;> cases warm <;> cbv
private theorem ordinary_done (kind : Option (Option Bool)) (warm : Bool) :
    callback (expression kind) captures (.uninterned (ordinaryLevel (depthValue kind warm))) (depthCall kind warm).state =
      .done (ordinaryValue kind warm) (ordinaryCall kind warm).state := by
  cases kind with
  | none => cases warm <;> cbv
  | some mode =>
      cases mode with
      | none => cases warm <;> cbv
      | some flag => cases flag <;> cases warm <;> cbv
private theorem unused (kind : Option (Option Bool)) (warm : Bool) :
    usesLocal (depthValue kind warm) (ordinaryValue kind warm) = false := by
  cases kind with
  | none => cases warm <;> cbv
  | some mode =>
      cases mode with
      | none => cases warm <;> cbv
      | some flag => cases flag <;> cases warm <;> cbv

private theorem captures_available (state : State Nat Bool) : InternedNestedProvenance.Values state captures := by
  intro value member
  have same : value = .reference (.uninterned 10) := by simpa only [captures,List.mem_singleton] using member
  cases same
  exact InternedNestedProvenance.ordinary_available state _
private theorem initial_context : Context empty captures :=
  ⟨SourceRecursiveIntersectionSemanticHeap.context empty SourceRecursiveIntersectionSemanticHeap.empty_heap captures
    (captures_available empty),InternedFreshOrdinaryDepthHeap.empty_heap⟩
private theorem current_context (kind : Option (Option Bool)) (warm : Bool) : Context (before kind warm) captures := by
  cases warm with
  | false => exact initial_context
  | true => exact initial_context.build (.binder true (expression kind))
private theorem current_history (kind : Option (Option Bool)) (warm : Bool) : Nonempty (History empty (before kind warm)) := by
  cases warm with
  | false => exact ⟨.refl empty⟩
  | true => exact SourceCurrentNativeMuPublication.build_history (.binder true (expression kind)) captures empty initial_context

private theorem checked (kind : Option (Option Bool)) (warm : Bool) :
    ∃ (expression : Syntax Nat Bool) (captures : List (Value Nat Bool))
      (initial value : Value Nat Bool) (reader before : State Nat Bool)
      (depth : Value Nat Bool) (afterDepth : State Nat Bool)
      (ordinary : Value Nat Bool) (cut : State Nat Bool)
      (raw : Value Nat Bool) (afterRaw : State Nat Bool),
      expression = (match kind with
        | none => .var 0 | some none => .node [.mk 7 false []]
        | some (some false) => .var 1 | some (some true) => .union [.var 0,.var 1]) ∧
      captures = [.reference (.uninterned 10)] ∧
      build (.binder true expression) captures empty = .done initial reader ∧
      before = (if warm then reader else empty) ∧ value = initial ∧
      Context before captures ∧ Nonempty (History empty before) ∧
      build (.binder true expression) captures before = .done value reader ∧
      callback expression captures .depth before = .done depth afterDepth ∧
      callback expression captures (.uninterned (ordinaryLevel depth)) afterDepth = .done ordinary cut ∧
      build expression (.reference (.uninterned (ordinaryLevel depth)) :: captures) afterDepth = .done raw afterRaw ∧
      run (withoutSelfReference (.uninterned (ordinaryLevel depth)) raw) afterRaw = (ordinary,cut) ∧
      Grows afterRaw reader ∧ Extends afterRaw.nodes.issued reader.nodes.issued ∧
      usesLocal depth ordinary = false ∧
      ∀ (cuts : Reference → Bool) (assignment : Reference → Profile),
        Equivalent (deleted cuts value assignment)
          (deleted (fun name => cuts name || (name == .uninterned (ordinaryLevel depth))) raw assignment) := by
  obtain ⟨history⟩ := current_history kind warm
  obtain ⟨depth,afterDepth,ordinary,cut,raw,afterRaw,depthDone,ordinaryDone,rawDone,filterDone,growth,issued,reduced⟩ :=
    SourceCurrentNativeUnusedRootDeletion.build (expression kind) captures (before kind warm)
      (current_context kind warm) history (output kind) (reader kind) (done kind warm)
  have sameDepth := Outcome.done.inj ((depth_done kind warm).symm.trans depthDone)
  cases sameDepth.1
  cases sameDepth.2
  have sameOrdinary := Outcome.done.inj ((ordinary_done kind warm).symm.trans ordinaryDone)
  cases sameOrdinary.1
  cases sameOrdinary.2
  exact ⟨expression kind,captures,output kind,output kind,reader kind,before kind warm,
    depthValue kind warm,(depthCall kind warm).state,ordinaryValue kind warm,(ordinaryCall kind warm).state,
    raw,afterRaw,rfl,rfl,done kind false,rfl,rfl,current_context kind warm,⟨history⟩,done kind warm,
    depthDone,ordinaryDone,rawDone,filterDone,growth,issued,unused kind warm,reduced (unused kind warm)⟩

/-- Actual unused calls reduce root deletion to their exact strict source calls, both cold and warm. -/
theorem actual_unused (kind : Option (Option Bool)) (warm : Bool) :
    ∃ (expression : Syntax Nat Bool) (captures : List (Value Nat Bool))
      (initial value : Value Nat Bool) (reader before : State Nat Bool)
      (depth : Value Nat Bool) (afterDepth : State Nat Bool)
      (ordinary : Value Nat Bool) (cut : State Nat Bool)
      (raw : Value Nat Bool) (afterRaw : State Nat Bool),
      expression = (match kind with
        | none => .var 0 | some none => .node [.mk 7 false []]
        | some (some false) => .var 1 | some (some true) => .union [.var 0,.var 1]) ∧
      captures = [.reference (.uninterned 10)] ∧
      build (.binder true expression) captures empty = .done initial reader ∧
      before = (if warm then reader else empty) ∧ value = initial ∧
      Context before captures ∧ Nonempty (History empty before) ∧
      build (.binder true expression) captures before = .done value reader ∧
      callback expression captures .depth before = .done depth afterDepth ∧
      callback expression captures (.uninterned (ordinaryLevel depth)) afterDepth = .done ordinary cut ∧
      build expression (.reference (.uninterned (ordinaryLevel depth)) :: captures) afterDepth = .done raw afterRaw ∧
      run (withoutSelfReference (.uninterned (ordinaryLevel depth)) raw) afterRaw = (ordinary,cut) ∧
      Grows afterRaw reader ∧ Extends afterRaw.nodes.issued reader.nodes.issued ∧
      usesLocal depth ordinary = false ∧
      ∀ (cuts : Reference → Bool) (assignment : Reference → Profile),
        Equivalent (deleted cuts value assignment)
          (deleted (fun name => cuts name || (name == .uninterned (ordinaryLevel depth))) raw assignment) := checked kind warm

end MicroCFTA.UnusedRootDeletionIntegration

set_option linter.all true
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.proofs true
set_option pp.proofs.threshold 254
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000

#check @MicroCFTA.UnusedRootDeletionIntegration.actual_unused
#print MicroCFTA.UnusedRootDeletionIntegration.actual_unused
#print axioms MicroCFTA.UnusedRootDeletionIntegration.actual_unused
