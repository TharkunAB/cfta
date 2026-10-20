import MicroCFTA.SourceCurrentNativePublicationTrace

/-!
# Actual native optional-binder sites for selected Mu cells

The physically admitted trace locates the optional-binder instruction that
first installs an arbitrary selected full Mu cell. The exact checked
prefix, yielded step and suffix remain in one witness. Initial cells stay
explicit. This result does not attach a compiler owner or source writer.
-/
namespace MicroCFTA.SourceCurrentNativeMuOptionalSite
open Cache InternedConstructorTemplates InternedProbeProvenance
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceEqualityNativeDemand
open SourceCurrentAllocatedNativePhysicalTraceCompletion (Trace)
open SourceRecursiveIntersectionSemanticHeap (SemanticHeap)
open InternedShallowHeap (NoNewMu noNewMu_refl)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Heap" => InternedConstructorTemplates.State Symbol Guard
local notation "HeapInputs" => SourceEqualityNativeDemandHeap.Inputs
local instance : DecidableEq (SourceGuards.Guard FullSyntax.Formula) := SourceEqualityPCSNativeEdge.guardDecidableEq
variable {A : Type} {width : Nat}

private theorem lift_heap (operations : SourceEqualityConstraintMemoAllocation.State)
    (outcome : SourceRecursiveIntersectionNative.Outcome width Symbol Guard A) :
    (lift operations outcome).state.native.machine.heap = outcome.state.machine.heap := by
  cases outcome <;> rfl

private theorem prior_or_none {before after : Heap} {key : InternedBinderProtocol.NodeKey} {target : Value Symbol Guard}
    (growth : Grows before after) (present : after.nodeRecords key = some target) :
    before.nodeRecords key = some target ∨ before.nodeRecords key = none := by
  cases old : before.nodeRecords key with
  | none => exact .inr rfl
  | some value =>
    have retained := growth.nodeRecords key value old
    have same : value = target := Option.some.inj (retained.symm.trans present)
    cases same
    exact .inl rfl

variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]

private theorem step_effects (control : Control A) (before : Checked width)
    (semantic : SemanticHeap before.native.machine.heap) (inputs : HeapInputs control before) :
    SemanticHeap (step control before).state.native.machine.heap ∧
    Grows before.native.machine.heap (step control before).state.native.machine.heap ∧
    Extends before.native.machine.heap.nodes.issued (step control before).state.native.machine.heap.nodes.issued := by
  refine ⟨(SourceCurrentNativePublicationTrace.step control before semantic inputs).1,?_⟩
  cases control with
  | edgeBody request next =>
    rw [step,SourceEqualityNativeDemandOperations.body_native]
    exact ⟨grows_refl _,extends_refl _⟩
  | code code =>
    cases code with
    | pure | fail | enter | read | finishNode | finishEdge => exact ⟨grows_refl _,extends_refl _⟩
    | work job next =>
      change Grows before.native.machine.heap
        (lift before.operations (SourceRecursiveIntersectionNative.step SourceEqualityConstraintConstructors.top
          SourceEqualityPCSNativeEdge.conjoin (.work job next) before.native)).state.native.machine.heap ∧ _
      rw [lift_heap]
      exact ⟨(run_correct job before.native.machine.heap semantic.1.normal.facts.coherent.valid).2,
        run_issued_extends job before.native.machine.heap semantic.1.normal.facts.coherent.valid⟩
    | optionalBinder pair body next =>
      have verified := SourceRecursiveIntersectionMaybeMu.verified pair body before.native.machine.heap
        semantic.1.normal.facts inputs
      cases called : SourceRecursiveIntersectionMaybeMu.maybeMu pair body before.native.machine.heap with
      | done value heap | pending key heap =>
        simpa only [step,SourceRecursiveIntersectionNative.step,called,lift,Outcome.state,advance,
          InternedNestedConstruction.Outcome.state] using And.intro verified.growth verified.history
    | node request next =>
      have same : (step (.code (.node request next)) before).state.native.machine.heap = before.native.machine.heap := by
        change (lift before.operations (SourceRecursiveIntersectionNative.step SourceEqualityConstraintConstructors.top
          SourceEqualityPCSNativeEdge.conjoin (.node request next) before.native)).state.native.machine.heap = _
        rw [lift_heap,SourceRecursiveIntersectionNative.node_step_machine]
      rw [same]
      exact ⟨grows_refl _,extends_refl _⟩
    | edge request next =>
      rw [SourceEqualityNativeDemandHeap.step_edge_heap]
      exact ⟨grows_refl _,extends_refl _⟩

private theorem trace_effects {fuel : Nat} {control rest : Control A} {before after : Checked width}
    (actual : Trace fuel control before rest after) (semantic : SemanticHeap before.native.machine.heap) :
    SemanticHeap after.native.machine.heap ∧ Grows before.native.machine.heap after.native.machine.heap ∧
      Extends before.native.machine.heap.nodes.issued after.native.machine.heap.nodes.issued := by
  induction actual with
  | refl => exact ⟨semantic,grows_refl _,extends_refl _⟩
  | cons control before next current rest after count inputs one tail ih =>
    have checked := step_effects control before semantic
      (SourceCurrentAllocatedNativePhysicalExecution.inputs_heap control before inputs)
    have reached : SemanticHeap current.native.machine.heap ∧
        Grows before.native.machine.heap current.native.machine.heap ∧
        Extends before.native.machine.heap.nodes.issued current.native.machine.heap.nodes.issued := by
      simpa only [one,Outcome.state] using checked
    have later := ih reached.1
    exact ⟨later.1,grows_trans reached.2.1 later.2.1,extends_trans reached.2.2 later.2.2⟩

private theorem step_kind (control : Control A) (before : Checked width) (inputs : HeapInputs control before) :
    NoNewMu before.native.machine.heap (step control before).state.native.machine.heap ∨
      ∃ pair body next, control = .code (.optionalBinder pair body next) := by
  cases control with
  | edgeBody request next =>
    apply Or.inl
    rw [step,SourceEqualityNativeDemandOperations.body_native]
    exact noNewMu_refl _
  | code code =>
    cases code with
    | pure | fail | enter | read | finishNode | finishEdge => exact .inl (noNewMu_refl _)
    | work job next =>
      apply Or.inl
      change NoNewMu before.native.machine.heap
        (lift before.operations (SourceRecursiveIntersectionNative.step SourceEqualityConstraintConstructors.top
          SourceEqualityPCSNativeEdge.conjoin (.work job next) before.native)).state.native.machine.heap
      rw [lift_heap]
      exact SourceCurrentNativePublicationTrace.work_noNewMu job before.native.machine.heap inputs
    | optionalBinder pair body next => exact .inr ⟨pair,body,next,rfl⟩
    | node request next =>
      apply Or.inl
      change NoNewMu before.native.machine.heap
        (lift before.operations (SourceRecursiveIntersectionNative.step SourceEqualityConstraintConstructors.top
          SourceEqualityPCSNativeEdge.conjoin (.node request next) before.native)).state.native.machine.heap
      rw [lift_heap,SourceRecursiveIntersectionNative.node_step_machine]
      exact noNewMu_refl _
    | edge request next =>
      apply Or.inl
      rw [SourceEqualityNativeDemandHeap.step_edge_heap]
      exact noNewMu_refl _

private def Site (fuel : Nat) (control : Control A) (before : Checked width)
    (rest : Control A) (after : Checked width) (key : InternedBinderProtocol.NodeKey)
    (target : Value Symbol Guard) : Prop :=
  ∃ prefixFuel suffixFuel pair body next siteBefore siteAfter result heap,
    fuel = prefixFuel + 1 + suffixFuel ∧
    Trace prefixFuel control before (.code (.optionalBinder pair body next)) siteBefore ∧
    SemanticHeap siteBefore.native.machine.heap ∧ Available siteBefore.native.machine.heap body ∧
    SourceRecursiveIntersectionMaybeMu.maybeMu pair body siteBefore.native.machine.heap = .done result heap ∧
    siteAfter = ⟨advance siteBefore.native {siteBefore.native.machine with heap := heap},siteBefore.operations⟩ ∧
    step (.code (.optionalBinder pair body next)) siteBefore = .yielded (.code (next result)) siteAfter ∧
    Trace suffixFuel (.code (next result)) siteAfter rest after ∧
    siteBefore.native.machine.heap.nodeRecords key = none ∧ heap.nodeRecords key = some target ∧
    Grows before.native.machine.heap siteBefore.native.machine.heap ∧
    Extends before.native.machine.heap.nodes.issued siteBefore.native.machine.heap.nodes.issued ∧
    Grows heap after.native.machine.heap ∧ Extends heap.nodes.issued after.native.machine.heap.nodes.issued

/-- A selected physical Mu is initial or has an exact optional-binder occurrence in the same admitted trace. -/
theorem trace {fuel : Nat} {control rest : Control A} {before after : Checked width}
    (actual : Trace fuel control before rest after) (semantic : SemanticHeap before.native.machine.heap)
    (key : InternedBinderProtocol.NodeKey) (entry : Interned InternedBinderProtocol.NodeKey)
    (body depth ordinary : Value Symbol Guard)
    (selected : after.native.machine.heap.nodeRecords key = some (.mu entry body depth ordinary)) :
    before.native.machine.heap.nodeRecords key = some (.mu entry body depth ordinary) ∨
    ∃ prefixFuel suffixFuel pair siteBody next siteBefore siteAfter result heap,
      fuel = prefixFuel + 1 + suffixFuel ∧
      Trace prefixFuel control before (.code (.optionalBinder pair siteBody next)) siteBefore ∧
      SemanticHeap siteBefore.native.machine.heap ∧ Available siteBefore.native.machine.heap siteBody ∧
      SourceRecursiveIntersectionMaybeMu.maybeMu pair siteBody siteBefore.native.machine.heap = .done result heap ∧
      siteAfter = ⟨advance siteBefore.native {siteBefore.native.machine with heap := heap},siteBefore.operations⟩ ∧
      step (.code (.optionalBinder pair siteBody next)) siteBefore = .yielded (.code (next result)) siteAfter ∧
      Trace suffixFuel (.code (next result)) siteAfter rest after ∧
      siteBefore.native.machine.heap.nodeRecords key = none ∧ heap.nodeRecords key = some (.mu entry body depth ordinary) ∧
      Grows before.native.machine.heap siteBefore.native.machine.heap ∧
      Extends before.native.machine.heap.nodes.issued siteBefore.native.machine.heap.nodes.issued ∧
      Grows heap after.native.machine.heap ∧ Extends heap.nodes.issued after.native.machine.heap.nodes.issued := by
  have recover {count : Nat} {start finish : Control A} {first last : Checked width}
      (part : Trace count start first finish last) :
      SemanticHeap first.native.machine.heap →
      last.native.machine.heap.nodeRecords key = some (.mu entry body depth ordinary) →
      first.native.machine.heap.nodeRecords key = some (.mu entry body depth ordinary) ∨
        Site count start first finish last key (.mu entry body depth ordinary) := by
    induction part with
    | refl => intro _ present; exact .inl present
    | cons start first middle current finish last count inputs one tail ih =>
      intro firstSemantic present
      have heapInputs := SourceCurrentAllocatedNativePhysicalExecution.inputs_heap start first inputs
      have checked := step_effects start first firstSemantic heapInputs
      have reached : SemanticHeap current.native.machine.heap ∧
          Grows first.native.machine.heap current.native.machine.heap ∧
          Extends first.native.machine.heap.nodes.issued current.native.machine.heap.nodes.issued := by
        simpa only [one,Outcome.state] using checked
      rcases ih reached.1 present with currentPresent | laterSite
      · rcases step_kind start first heapInputs with old | ⟨pair,siteBody,next,sameControl⟩
        · have prior : first.native.machine.heap.nodeRecords key = some (.mu entry body depth ordinary) := by
            apply old key entry body depth ordinary
            simpa only [one,Outcome.state] using currentPresent
          exact .inl prior
        · rcases prior_or_none reached.2.1 currentPresent with prior | missing
          · exact .inl prior
          · subst start
            cases called : SourceRecursiveIntersectionMaybeMu.maybeMu pair siteBody first.native.machine.heap with
            | pending pending heap =>
              simp only [step,SourceRecursiveIntersectionNative.step,called,lift] at one
              cases one
            | done result heap =>
              have yielded : step (.code (.optionalBinder pair siteBody next)) first =
                  .yielded (.code (next result))
                    ⟨advance first.native {first.native.machine with heap := heap},first.operations⟩ := by
                simp only [step,SourceRecursiveIntersectionNative.step,called,lift]
              have same := Outcome.yielded.inj (yielded.symm.trans one)
              have sameMiddle : middle = .code (next result) := same.1.symm
              have sameCurrent : current =
                  (⟨advance first.native {first.native.machine with heap := heap},first.operations⟩ : Checked width) := same.2.symm
              have sitePresent : heap.nodeRecords key = some (.mu entry body depth ordinary) := by
                rw [sameCurrent] at currentPresent
                exact currentPresent
              have later := trace_effects tail reached.1
              have suffixGrowth : Grows heap last.native.machine.heap := by
                rw [sameCurrent] at later
                exact later.2.1
              have suffixIssued : Extends heap.nodes.issued last.native.machine.heap.nodes.issued := by
                rw [sameCurrent] at later
                exact later.2.2
              have suffix : Trace count (.code (next result)) current finish last := by
                rw [sameMiddle] at tail
                exact tail
              have yieldedCurrent : step (.code (.optionalBinder pair siteBody next)) first =
                  .yielded (.code (next result)) current := by
                rw [←sameMiddle]
                exact one
              exact .inr ⟨0,count,pair,siteBody,next,first,current,result,heap,by omega,.refl _ _,firstSemantic,
                heapInputs,called,sameCurrent,yieldedCurrent,suffix,missing,sitePresent,
                grows_refl _,extends_refl _,suffixGrowth,suffixIssued⟩
      · obtain ⟨prefixFuel,suffixFuel,pair,siteBody,next,siteBefore,siteAfter,result,heap,
          fuelEq,earlierTrace,siteSemantic,siteAvailable,called,advanced,yielded,suffix,missing,sitePresent,
          earlierGrowth,earlierIssued,laterGrowth,laterIssued⟩ := laterSite
        exact .inr ⟨prefixFuel + 1,suffixFuel,pair,siteBody,next,siteBefore,siteAfter,result,heap,
          by omega,.cons start first middle current _ siteBefore prefixFuel inputs one earlierTrace,
          siteSemantic,siteAvailable,called,advanced,yielded,suffix,missing,sitePresent,
          grows_trans reached.2.1 earlierGrowth,extends_trans reached.2.2 earlierIssued,laterGrowth,laterIssued⟩
  exact recover actual semantic selected

end MicroCFTA.SourceCurrentNativeMuOptionalSite

set_option linter.all true
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.proofs true
set_option pp.proofs.threshold 254
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000

#check @MicroCFTA.SourceCurrentNativeMuOptionalSite.trace
#print MicroCFTA.SourceCurrentNativeMuOptionalSite.trace
#print axioms MicroCFTA.SourceCurrentNativeMuOptionalSite.trace
