import MicroCFTA.SourceCurrentNativePublicationTrace

/-!
# Native optional-binder sites through bounded stopping execution

The actual physical input plan locates the operation that first installs a
selected full Mu cell. The result retains the literal nested outcome and
checked step. Terminal blocked operations keep their actual heap effects.
This result does not attach a compiler owner or original source binding.
-/
namespace MicroCFTA.SourceCurrentNativeMuStoppingSite
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

private theorem execute_effects (count : Nat) (control : Control A) (before : Checked width)
    (semantic : SemanticHeap before.native.machine.heap)
    (inputs : SourceCurrentAllocatedNativePhysicalExecution.InputsThrough count control before) :
    SemanticHeap (SourceEqualityNativeDemand.execute count control before).state.native.machine.heap ∧
    Grows before.native.machine.heap (SourceEqualityNativeDemand.execute count control before).state.native.machine.heap ∧
    Extends before.native.machine.heap.nodes.issued (SourceEqualityNativeDemand.execute count control before).state.native.machine.heap.nodes.issued := by
  induction count generalizing control before with
  | zero => exact ⟨semantic,grows_refl _,extends_refl _⟩
  | succ count ih =>
    have checked := step_effects control before semantic
      (SourceCurrentAllocatedNativePhysicalExecution.inputs_heap control before inputs.1)
    cases observed : step control before with
    | yielded next after =>
      have reached : SemanticHeap after.native.machine.heap ∧
          Grows before.native.machine.heap after.native.machine.heap ∧
          Extends before.native.machine.heap.nodes.issued after.native.machine.heap.nodes.issued := by
        simpa only [observed,Outcome.state] using checked
      have remaining : SourceCurrentAllocatedNativePhysicalExecution.InputsThrough count next after := by
        simpa only [SourceCurrentAllocatedNativePhysicalExecution.InputsThrough,observed] using inputs.2
      have later := ih next after reached.1 remaining
      simpa only [SourceEqualityNativeDemand.execute,observed] using And.intro later.1
        (And.intro (grows_trans reached.2.1 later.2.1) (extends_trans reached.2.2 later.2.2))
    | done | failed | constraintError | blocked =>
      simpa only [SourceEqualityNativeDemand.execute,observed,Outcome.state] using checked

private theorem step_suffix (remaining : Nat) (control : Control A) (before : Checked width)
    (semantic : SemanticHeap before.native.machine.heap)
    (inputs : SourceCurrentAllocatedNativePhysicalExecution.InputsThrough (remaining + 1) control before) :
    Grows (step control before).state.native.machine.heap
      (SourceEqualityNativeDemand.execute (remaining + 1) control before).state.native.machine.heap ∧
    Extends (step control before).state.native.machine.heap.nodes.issued
      (SourceEqualityNativeDemand.execute (remaining + 1) control before).state.native.machine.heap.nodes.issued := by
  have checked := step_effects control before semantic
    (SourceCurrentAllocatedNativePhysicalExecution.inputs_heap control before inputs.1)
  cases observed : step control before with
  | yielded next after =>
    have reached : SemanticHeap after.native.machine.heap := by
      simpa only [observed,Outcome.state] using checked.1
    have laterInputs : SourceCurrentAllocatedNativePhysicalExecution.InputsThrough remaining next after := by
      simpa only [SourceCurrentAllocatedNativePhysicalExecution.InputsThrough,observed] using inputs.2
    have later := execute_effects remaining next after reached laterInputs
    simpa only [SourceEqualityNativeDemand.execute,observed,Outcome.state] using later.2
  | done | failed | constraintError | blocked =>
    simp only [SourceEqualityNativeDemand.execute,observed,Outcome.state]
    exact ⟨grows_refl _,extends_refl _⟩

private def Site (count : Nat) (control : Control A) (before : Checked width)
    (key : InternedBinderProtocol.NodeKey) (target : Value Symbol Guard) : Prop :=
  ∃ prefixFuel remainingFuel pair siteBody next siteBefore call siteStep,
    count = prefixFuel + 1 + remainingFuel ∧
    Trace prefixFuel control before (.code (.optionalBinder pair siteBody next)) siteBefore ∧
    SourceCurrentAllocatedNativePhysicalExecution.Inputs (.code (.optionalBinder pair siteBody next)) siteBefore ∧
    SemanticHeap siteBefore.native.machine.heap ∧ Available siteBefore.native.machine.heap siteBody ∧
    SourceRecursiveIntersectionMaybeMu.maybeMu pair siteBody siteBefore.native.machine.heap = call ∧
    siteStep = (match call with
      | .done result heap => .yielded (.code (next result))
          ⟨advance siteBefore.native {siteBefore.native.machine with heap := heap},siteBefore.operations⟩
      | .pending pending heap => .blocked (.native (.constructor pending))
          (.code (.optionalBinder pair siteBody next))
          ⟨advance siteBefore.native {siteBefore.native.machine with heap := heap},siteBefore.operations⟩) ∧
    step (.code (.optionalBinder pair siteBody next)) siteBefore = siteStep ∧
    SourceEqualityNativeDemand.execute count control before = resume remainingFuel siteStep ∧
    siteBefore.native.machine.heap.nodeRecords key = none ∧ call.state.nodeRecords key = some target ∧
    Grows before.native.machine.heap siteBefore.native.machine.heap ∧
    Extends before.native.machine.heap.nodes.issued siteBefore.native.machine.heap.nodes.issued ∧
    Grows call.state (SourceEqualityNativeDemand.execute count control before).state.native.machine.heap ∧
    Extends call.state.nodes.issued (SourceEqualityNativeDemand.execute count control before).state.native.machine.heap.nodes.issued

private theorem at_step (remaining : Nat) (control : Control A) (before : Checked width)
    (semantic : SemanticHeap before.native.machine.heap)
    (inputs : SourceCurrentAllocatedNativePhysicalExecution.InputsThrough (remaining + 1) control before)
    (key : InternedBinderProtocol.NodeKey) (entry : Interned InternedBinderProtocol.NodeKey)
    (body depth ordinary : Value Symbol Guard)
    (present : (step control before).state.native.machine.heap.nodeRecords key = some (.mu entry body depth ordinary)) :
    before.native.machine.heap.nodeRecords key = some (.mu entry body depth ordinary) ∨
      Site (remaining + 1) control before key (.mu entry body depth ordinary) := by
  have heapInputs := SourceCurrentAllocatedNativePhysicalExecution.inputs_heap control before inputs.1
  have checked := step_effects control before semantic heapInputs
  rcases step_kind control before heapInputs with unchanged | ⟨pair,siteBody,next,sameControl⟩
  · exact .inl (unchanged key entry body depth ordinary present)
  · rcases prior_or_none checked.2.1 present with prior | missing
    · exact .inl prior
    · subst control
      let call := SourceRecursiveIntersectionMaybeMu.maybeMu pair siteBody before.native.machine.heap
      let siteStep : Outcome width A := step (.code (.optionalBinder pair siteBody next)) before
      have mapped : siteStep = (match call with
          | .done result heap => .yielded (.code (next result))
              ⟨advance before.native {before.native.machine with heap := heap},before.operations⟩
          | .pending pending heap => .blocked (.native (.constructor pending))
              (.code (.optionalBinder pair siteBody next))
              ⟨advance before.native {before.native.machine with heap := heap},before.operations⟩) := by
        dsimp [siteStep,call]
        cases called : SourceRecursiveIntersectionMaybeMu.maybeMu pair siteBody before.native.machine.heap <;>
          simp only [step,SourceRecursiveIntersectionNative.step,called,lift]
      have sameHeap : siteStep.state.native.machine.heap = call.state := by
        rw [mapped]
        cases call <;> rfl
      have sitePresent : call.state.nodeRecords key = some (.mu entry body depth ordinary) := by
        rw [←sameHeap]
        exact present
      have suffix := step_suffix remaining (.code (.optionalBinder pair siteBody next)) before semantic inputs
      have resumed : SourceEqualityNativeDemand.execute (remaining + 1) (.code (.optionalBinder pair siteBody next)) before =
          resume remaining siteStep := by
        dsimp [siteStep]
        cases observed : step (.code (.optionalBinder pair siteBody next)) before <;>
          simp only [SourceEqualityNativeDemand.execute,observed,resume]
      have suffixGrowth : Grows call.state
          (SourceEqualityNativeDemand.execute (remaining + 1) (.code (.optionalBinder pair siteBody next)) before).state.native.machine.heap := by
        rw [←sameHeap]
        exact suffix.1
      have suffixIssued : Extends call.state.nodes.issued
          (SourceEqualityNativeDemand.execute (remaining + 1) (.code (.optionalBinder pair siteBody next)) before).state.native.machine.heap.nodes.issued := by
        rw [←sameHeap]
        exact suffix.2
      exact .inr ⟨0,remaining,pair,siteBody,next,before,call,siteStep,by omega,.refl _ _,inputs.1,
        semantic,heapInputs,rfl,mapped,rfl,resumed,missing,sitePresent,grows_refl _,extends_refl _,
        suffixGrowth,suffixIssued⟩

/-- Every bounded outcome has an exact initial cell or an actual optional-binder site, including terminal blocking. -/
theorem execute {count : Nat} {control : Control A} {before : Checked width}
    (inputs : SourceCurrentAllocatedNativePhysicalExecution.InputsThrough count control before)
    (semantic : SemanticHeap before.native.machine.heap)
    (key : InternedBinderProtocol.NodeKey) (entry : Interned InternedBinderProtocol.NodeKey)
    (body depth ordinary : Value Symbol Guard)
    (selected : (SourceEqualityNativeDemand.execute count control before).state.native.machine.heap.nodeRecords key =
      some (.mu entry body depth ordinary)) :
    before.native.machine.heap.nodeRecords key = some (.mu entry body depth ordinary) ∨
    ∃ prefixFuel remainingFuel pair siteBody next siteBefore call siteStep,
      count = prefixFuel + 1 + remainingFuel ∧
      Trace prefixFuel control before (.code (.optionalBinder pair siteBody next)) siteBefore ∧
      SourceCurrentAllocatedNativePhysicalExecution.Inputs (.code (.optionalBinder pair siteBody next)) siteBefore ∧
      SemanticHeap siteBefore.native.machine.heap ∧ Available siteBefore.native.machine.heap siteBody ∧
      SourceRecursiveIntersectionMaybeMu.maybeMu pair siteBody siteBefore.native.machine.heap = call ∧
      siteStep = (match call with
        | .done result heap => .yielded (.code (next result))
            ⟨advance siteBefore.native {siteBefore.native.machine with heap := heap},siteBefore.operations⟩
        | .pending pending heap => .blocked (.native (.constructor pending))
            (.code (.optionalBinder pair siteBody next))
            ⟨advance siteBefore.native {siteBefore.native.machine with heap := heap},siteBefore.operations⟩) ∧
      step (.code (.optionalBinder pair siteBody next)) siteBefore = siteStep ∧
      SourceEqualityNativeDemand.execute count control before = resume remainingFuel siteStep ∧
      siteBefore.native.machine.heap.nodeRecords key = none ∧
      call.state.nodeRecords key = some (.mu entry body depth ordinary) ∧
      Grows before.native.machine.heap siteBefore.native.machine.heap ∧
      Extends before.native.machine.heap.nodes.issued siteBefore.native.machine.heap.nodes.issued ∧
      Grows call.state (SourceEqualityNativeDemand.execute count control before).state.native.machine.heap ∧
      Extends call.state.nodes.issued (SourceEqualityNativeDemand.execute count control before).state.native.machine.heap.nodes.issued := by
  have recover (count : Nat) (control : Control A) (before : Checked width)
      (inputs : SourceCurrentAllocatedNativePhysicalExecution.InputsThrough count control before)
      (semantic : SemanticHeap before.native.machine.heap)
      (present : (SourceEqualityNativeDemand.execute count control before).state.native.machine.heap.nodeRecords key =
        some (.mu entry body depth ordinary)) :
      before.native.machine.heap.nodeRecords key = some (.mu entry body depth ordinary) ∨
        Site count control before key (.mu entry body depth ordinary) := by
    induction count generalizing control before with
    | zero => exact .inl present
    | succ count ih =>
      have checked := step_effects control before semantic
        (SourceCurrentAllocatedNativePhysicalExecution.inputs_heap control before inputs.1)
      cases observed : step control before with
      | yielded next after =>
        have reached : SemanticHeap after.native.machine.heap ∧
            Grows before.native.machine.heap after.native.machine.heap ∧
            Extends before.native.machine.heap.nodes.issued after.native.machine.heap.nodes.issued := by
          simpa only [observed,Outcome.state] using checked
        have remaining : SourceCurrentAllocatedNativePhysicalExecution.InputsThrough count next after := by
          simpa only [SourceCurrentAllocatedNativePhysicalExecution.InputsThrough,observed] using inputs.2
        have laterPresent : (SourceEqualityNativeDemand.execute count next after).state.native.machine.heap.nodeRecords key =
            some (.mu entry body depth ordinary) := by
          simpa only [SourceEqualityNativeDemand.execute,observed] using present
        rcases ih next after remaining reached.1 laterPresent with atCurrent | laterSite
        · apply at_step count control before semantic inputs key entry body depth ordinary
          simpa only [observed,Outcome.state] using atCurrent
        · obtain ⟨prefixFuel,remainingFuel,pair,siteBody,continuation,siteBefore,call,siteStep,
            fuelEq,prefixTrace,siteInputs,siteSemantic,siteAvailable,called,mapped,siteObserved,
            resumed,missing,sitePresent,prefixGrowth,prefixIssued,suffixGrowth,suffixIssued⟩ := laterSite
          have whole : SourceEqualityNativeDemand.execute (count + 1) control before =
              resume remainingFuel siteStep := by
            simpa only [SourceEqualityNativeDemand.execute,observed] using resumed
          have finalGrowth : Grows call.state
              (SourceEqualityNativeDemand.execute (count + 1) control before).state.native.machine.heap := by
            simpa only [SourceEqualityNativeDemand.execute,observed] using suffixGrowth
          have finalIssued : Extends call.state.nodes.issued
              (SourceEqualityNativeDemand.execute (count + 1) control before).state.native.machine.heap.nodes.issued := by
            simpa only [SourceEqualityNativeDemand.execute,observed] using suffixIssued
          exact .inr ⟨prefixFuel + 1,remainingFuel,pair,siteBody,continuation,siteBefore,call,siteStep,by omega,
            .cons control before next after _ siteBefore prefixFuel inputs.1 observed prefixTrace,
            siteInputs,siteSemantic,siteAvailable,called,mapped,siteObserved,whole,missing,sitePresent,
            grows_trans reached.2.1 prefixGrowth,extends_trans reached.2.2 prefixIssued,finalGrowth,finalIssued⟩
      | done | failed | constraintError | blocked =>
        apply at_step count control before semantic inputs key entry body depth ordinary
        simpa only [SourceEqualityNativeDemand.execute,observed,Outcome.state] using present
  exact recover count control before inputs semantic selected

end MicroCFTA.SourceCurrentNativeMuStoppingSite
