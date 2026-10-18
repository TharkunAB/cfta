import MicroCFTA.SourceCurrentNativeUnusedRootShadow
import MicroCFTA.SourceRecursiveIntersectionSemanticHeap

set_option linter.all true
set_option maxRecDepth 30000
set_option maxHeartbeats 5000000
set_option cbv.maxSteps 100000000

namespace MicroCFTA.UnusedRootShadowIntegration
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
open SourceCurrentStoredMuProfileContract (shadow)

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

private def extension : Syntax Nat Bool := .node [.mk 99 false []]
private def extendedCall (kind : Option (Option Bool)) := build extension [] (reader kind)
private def common (kind : Option (Option Bool)) := (extendedCall kind).state
private theorem extension_context (kind : Option (Option Bool)) : Context (reader kind) [] :=
  ⟨⟨(current_context kind true).base.normal,(by intro value member; cases member),
    (current_context kind true).base.profiles,(current_context kind true).base.freeNames⟩,
    (current_context kind true).depth⟩
private theorem extension_done (kind : Option (Option Bool)) :
    build extension [] (reader kind) = .done (result (extendedCall kind)) (common kind) := by
  cases kind with
  | none => cbv
  | some mode =>
      cases mode with
      | none => cbv
      | some flag => cases flag <;> cbv
private theorem later (kind : Option (Option Bool)) : Grows (reader kind) (common kind) :=
  (InternedFreshOrdinaryFacts.build_verified extension [] (reader kind) (extension_context kind).base.normal.facts
    (by intro value member; cases member)).growth
private theorem common_history (kind : Option (Option Bool)) : Nonempty (History empty (common kind)) := by
  obtain ⟨first⟩ := current_history kind true
  obtain ⟨last⟩ := SourceCurrentNativeMuPublication.build_history extension [] (reader kind) (extension_context kind)
  exact ⟨.trans first last⟩
private theorem allocation (kind : Option (Option Bool)) : (common kind).nodes.next = (reader kind).nodes.next + 1 := by
  cases kind with
  | none => cbv
  | some mode =>
      cases mode with
      | none => cbv
      | some flag => cases flag <;> cbv

private theorem checked (kind : Option (Option Bool)) (warm : Bool) :
    ∃ (expression : Syntax Nat Bool) (captures : List (Value Nat Bool))
      (initial value extensionValue : Value Nat Bool) (reader before common : State Nat Bool)
      (depth : Value Nat Bool) (afterDepth : State Nat Bool)
      (ordinary : Value Nat Bool) (cut : State Nat Bool)
      (raw : Value Nat Bool) (afterRaw : State Nat Bool),
      expression = (match kind with
        | none => .var 0 | some none => .node [.mk 7 false []]
        | some (some false) => .var 1 | some (some true) => .union [.var 0,.var 1]) ∧
      captures = [.reference (.uninterned 10)] ∧
      build (.binder true expression) captures empty = .done initial reader ∧
      before = (if warm then reader else empty) ∧ value = initial ∧
      Context before captures ∧
      build (.binder true expression) captures before = .done value reader ∧
      build (.node [.mk 99 false []]) [] reader = .done extensionValue common ∧
      common.nodes.next = reader.nodes.next + 1 ∧ Grows reader common ∧ Nonempty (History empty common) ∧
      callback expression captures .depth before = .done depth afterDepth ∧
      callback expression captures (.uninterned (ordinaryLevel depth)) afterDepth = .done ordinary cut ∧
      build expression (.reference (.uninterned (ordinaryLevel depth)) :: captures) afterDepth = .done raw afterRaw ∧
      run (withoutSelfReference (.uninterned (ordinaryLevel depth)) raw) afterRaw = (ordinary,cut) ∧
      Grows afterRaw reader ∧ Extends afterRaw.nodes.issued reader.nodes.issued ∧
      usesLocal depth ordinary = false ∧ .uninterned (ordinaryLevel depth) ∉ value.free ∧
      (∀ (cuts : Reference → Bool) (assignment : Reference → Profile) (replacement : Profile),
        deleted cuts value assignment = deleted cuts value (shadow (.uninterned (ordinaryLevel depth)) replacement assignment)) ∧
      ∀ (cuts : Reference → Bool) (assignment : Reference → Profile),
        Equivalent (deleted cuts value assignment)
          (deleted (fun name => cuts name || (name == .uninterned (ordinaryLevel depth))) raw
            (shadow (.uninterned (ordinaryLevel depth)) (some []) assignment)) := by
  obtain ⟨history⟩ := common_history kind
  obtain ⟨depth,afterDepth,ordinary,cut,raw,afterRaw,depthDone,ordinaryDone,rawDone,filterDone,growth,issued,reduced⟩ :=
    SourceCurrentNativeUnusedRootShadow.build (expression kind) captures (before kind warm)
      (current_context kind warm) (output kind) (reader kind) (done kind warm) (common kind) (later kind) history
  have sameDepth := Outcome.done.inj ((depth_done kind warm).symm.trans depthDone)
  cases sameDepth.1
  cases sameDepth.2
  have sameOrdinary := Outcome.done.inj ((ordinary_done kind warm).symm.trans ordinaryDone)
  cases sameOrdinary.1
  cases sameOrdinary.2
  obtain ⟨missing,shadowed,reduced⟩ := reduced (unused kind warm)
  exact ⟨expression kind,captures,output kind,output kind,result (extendedCall kind),reader kind,before kind warm,
    common kind,depthValue kind warm,(depthCall kind warm).state,ordinaryValue kind warm,(ordinaryCall kind warm).state,
    raw,afterRaw,rfl,rfl,done kind false,rfl,rfl,current_context kind warm,done kind warm,
    extension_done kind,allocation kind,later kind,⟨history⟩,depthDone,ordinaryDone,rawDone,filterDone,
    growth,issued,unused kind warm,missing,shadowed,reduced⟩

/-- Actual cold and warm unused binders share any local profile at a strictly later source reader. -/
theorem actual_unused_shadow (kind : Option (Option Bool)) (warm : Bool) :
    ∃ (expression : Syntax Nat Bool) (captures : List (Value Nat Bool))
      (initial value extensionValue : Value Nat Bool) (reader before common : State Nat Bool)
      (depth : Value Nat Bool) (afterDepth : State Nat Bool)
      (ordinary : Value Nat Bool) (cut : State Nat Bool)
      (raw : Value Nat Bool) (afterRaw : State Nat Bool),
      expression = (match kind with
        | none => .var 0 | some none => .node [.mk 7 false []]
        | some (some false) => .var 1 | some (some true) => .union [.var 0,.var 1]) ∧
      captures = [.reference (.uninterned 10)] ∧
      build (.binder true expression) captures empty = .done initial reader ∧
      before = (if warm then reader else empty) ∧ value = initial ∧
      Context before captures ∧
      build (.binder true expression) captures before = .done value reader ∧
      build (.node [.mk 99 false []]) [] reader = .done extensionValue common ∧
      common.nodes.next = reader.nodes.next + 1 ∧ Grows reader common ∧ Nonempty (History empty common) ∧
      callback expression captures .depth before = .done depth afterDepth ∧
      callback expression captures (.uninterned (ordinaryLevel depth)) afterDepth = .done ordinary cut ∧
      build expression (.reference (.uninterned (ordinaryLevel depth)) :: captures) afterDepth = .done raw afterRaw ∧
      run (withoutSelfReference (.uninterned (ordinaryLevel depth)) raw) afterRaw = (ordinary,cut) ∧
      Grows afterRaw reader ∧ Extends afterRaw.nodes.issued reader.nodes.issued ∧
      usesLocal depth ordinary = false ∧ .uninterned (ordinaryLevel depth) ∉ value.free ∧
      (∀ (cuts : Reference → Bool) (assignment : Reference → Profile) (replacement : Profile),
        deleted cuts value assignment = deleted cuts value (shadow (.uninterned (ordinaryLevel depth)) replacement assignment)) ∧
      ∀ (cuts : Reference → Bool) (assignment : Reference → Profile),
        Equivalent (deleted cuts value assignment)
          (deleted (fun name => cuts name || (name == .uninterned (ordinaryLevel depth))) raw
            (shadow (.uninterned (ordinaryLevel depth)) (some []) assignment)) := checked kind warm

end MicroCFTA.UnusedRootShadowIntegration

set_option linter.all true
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.proofs true
set_option pp.proofs.threshold 254
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000

#check @MicroCFTA.UnusedRootShadowIntegration.actual_unused_shadow
#print MicroCFTA.UnusedRootShadowIntegration.actual_unused_shadow
#print axioms MicroCFTA.UnusedRootShadowIntegration.actual_unused_shadow
