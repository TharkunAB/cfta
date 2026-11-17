import MicroCFTA.SourceSynthesisCurrentUniverseNativeAllocation
import MicroCFTA.SourceCurrentNativePublicationTrace

namespace MicroCFTA.SourceSynthesisCurrentUniverseNativeAllocation
open Cache InternedConstructorTemplates InternedProbeProvenance
open InternedBinderProtocol (NodeKey)
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceEqualityNativeDemand
open SourceCurrentAllocatedNativePhysicalTraceCompletion (Trace)
open SourceCurrentAllocatedNativePhysicalExecution (InputsThrough)
open SourceEqualityNativeDemandOperations (FieldsThrough)
open SourceSynthesisTypeSyntax (Library Query)
open SourceSynthesisFirstOrderConstruction (Expression)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSynthesisGeneralizeSyntax.Guard
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Profile" => SourceCurrentAllocatedNativeClosedResetProfile.Profile
local notation "ordinarySymbols" => SourceSynthesisUniverseCallerBoundary.ordinarySymbols
set_option autoImplicit false

/- Note [Cold query heap writers]
Each nonoptional physical instruction preserves every complete Mu record.
The source-qualified optional-prefix theorem supplies the remaining writer.
The proof retains one literal rooted prefix at each step. It applies the
optional theorem at that prefix and uses the original total fuel bound.
Terminal outcomes retain the actual step heap, including blocked effects.
The helper's optional rule is internal. The public source theorem derives it
from the original source and the actual prefix.
-/

private theorem cold_lift_heap {width : Nat} {A : Type}
    (operations : SourceEqualityConstraintMemoAllocation.State)
    (outcome : SourceRecursiveIntersectionNative.Outcome width Symbol Guard A) :
    (lift operations outcome).state.native.machine.heap = outcome.state.machine.heap := by
  cases outcome <;> rfl

private theorem cold_step_no_new_mu
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat} {A : Type}
    (control : Control A) (before : Checked width)
    (currentInputs : SourceCurrentAllocatedNativePhysicalExecution.Inputs control before)
    (optional : ∀ (binder : Nat × Nat) (body : Value Symbol Guard)
      (resume : Value Symbol Guard → Code Symbol Guard A),
      control = .code (.optionalBinder binder body resume) →
      InternedShallowHeap.NoNewMu before.native.machine.heap
        (SourceRecursiveIntersectionMaybeMu.maybeMu binder body before.native.machine.heap).state) :
    InternedShallowHeap.NoNewMu before.native.machine.heap
      (step control before).state.native.machine.heap := by
  cases control with
  | edgeBody request resume =>
      rw [step, SourceEqualityNativeDemandOperations.body_native]
      exact InternedShallowHeap.noNewMu_refl _
  | code code =>
      cases code with
      | pure | fail | enter | read | finishNode | finishEdge =>
          exact InternedShallowHeap.noNewMu_refl _
      | work job resume =>
          change InternedShallowHeap.NoNewMu before.native.machine.heap
            (lift before.operations (SourceRecursiveIntersectionNative.step SourceEqualityConstraintConstructors.top
              SourceEqualityPCSNativeEdge.conjoin (.work job resume) before.native)).state.native.machine.heap
          rw [cold_lift_heap]
          exact SourceCurrentNativePublicationTrace.work_noNewMu job before.native.machine.heap currentInputs
      | optionalBinder binder body resume =>
          have kept := optional binder body resume rfl
          cases called : SourceRecursiveIntersectionMaybeMu.maybeMu binder body before.native.machine.heap with
          | done value heap | pending key heap =>
              simpa only [step, SourceRecursiveIntersectionNative.step, called, lift, Outcome.state,
                advance, InternedNestedConstruction.Outcome.state] using kept
      | node request resume =>
          change InternedShallowHeap.NoNewMu before.native.machine.heap
            (lift before.operations (SourceRecursiveIntersectionNative.step SourceEqualityConstraintConstructors.top
              SourceEqualityPCSNativeEdge.conjoin (.node request resume) before.native)).state.native.machine.heap
          rw [cold_lift_heap, SourceRecursiveIntersectionNative.node_step_machine]
          exact InternedShallowHeap.noNewMu_refl _
      | edge request resume =>
          rw [SourceEqualityNativeDemandHeap.step_edge_heap]
          exact InternedShallowHeap.noNewMu_refl _

theorem original_universe_cold_query_no_new_mu
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat}
    (lib : Library) (query : Query) (signed : Int) (whole : Expression)
    (accepted : SourceSynthesisCurrentConstruction.firstOrderRaw lib query signed = .ok whole)
    (rootValue : Value Symbol Guard) (sourceHeap : InternedConstructorTemplates.State Symbol Guard)
    (built : InternedFreshOrdinaryConstruction.build (ordinarySymbols whole) [] empty =
      .done rootValue sourceHeap)
    (key : NodeKey) (entry : Interned NodeKey) (body depth ordinary : Value Symbol Guard)
    (stored : sourceHeap.nodeRecords key = some (.mu entry body depth ordinary))
    (rootRequest : NodeRequest Symbol Guard) (machine : Machine Symbol Guard)
    (machineValid : SourceRecursiveIntersectionKernel.Valid machine)
    (sourceGrowth : Grows sourceHeap machine.heap)
    (rootDomain : rootRequest.domain = IntersectionEmptyDomain.emptyDomain)
    (leftProfile : Profile entry.identity rootRequest.left)
    (rightProfile : Profile entry.identity rootRequest.right)
    (operations : SourceEqualityConstraintMemoAllocation.State)
    (operationsValid : SourceEqualityConstraintMemoAllocation.Valid operations)
    (fuel : Nat)
    (inputs : InputsThrough fuel (.code (.node rootRequest .pure))
      (⟨initial width machine, operations⟩ : Checked width))
    (fields : FieldsThrough fuel (.code (.node rootRequest .pure))
      (⟨initial width machine, operations⟩ : Checked width)) :
    InternedShallowHeap.NoNewMu machine.heap
      (SourceEqualityNativeDemand.execute fuel (.code (.node rootRequest .pure))
        (⟨initial width machine, operations⟩ : Checked width)).state.native.machine.heap ∧
    ∀ (used : Nat) (rest : Control (Value Symbol Guard)) (current : Checked width),
      used ≤ fuel →
      Trace used (.code (.node rootRequest .pure))
        (⟨initial width machine, operations⟩ : Checked width) rest current →
      InternedShallowHeap.NoNewMu machine.heap current.native.machine.heap
 := by
  let initialState : Checked width := ⟨initial width machine, operations⟩
  let rootControl : Control (Value Symbol Guard) := .code (.node rootRequest .pure)
  have sourceStep (used : Nat) (control : Control (Value Symbol Guard)) (current : Checked width)
      (past : Trace used rootControl initialState control current)
      (room : used + 1 ≤ fuel)
      (currentInputs : SourceCurrentAllocatedNativePhysicalExecution.Inputs control current) :
      InternedShallowHeap.NoNewMu current.native.machine.heap
        (step control current).state.native.machine.heap := by
    apply cold_step_no_new_mu control current currentInputs
    intro binder siteBody resume same
    subst control
    exact original_universe_optional_prefix_no_new_mu
      lib query signed whole accepted rootValue sourceHeap built key entry body depth ordinary stored
      rootRequest machine machineValid sourceGrowth rootDomain leftProfile rightProfile operations operationsValid
      fuel used current binder siteBody resume room inputs fields past
  have traceOld (count : Nat) (control : Control (Value Symbol Guard)) (before : Checked width)
      (rest : Control (Value Symbol Guard)) (after : Checked width)
      (suffix : Trace count control before rest after) :
      ∀ (used : Nat), Trace used rootControl initialState control before → used + count ≤ fuel →
        InternedShallowHeap.NoNewMu before.native.machine.heap after.native.machine.heap := by
    induction suffix with
    | refl control before =>
        intro _used _past _room
        exact InternedShallowHeap.noNewMu_refl _
    | cons control before next middle final after remaining currentInputs one tail ih =>
        intro used past room
        have oneTrace : Trace 1 control before next middle :=
          .cons _ _ _ _ _ _ 0 currentInputs one (.refl _ _)
        have nextPrefix := past.trans oneTrace
        have kept := sourceStep used control before past (by omega) currentInputs
        have keptAt : InternedShallowHeap.NoNewMu before.native.machine.heap middle.native.machine.heap := by
          simpa only [one, Outcome.state] using kept
        have later := ih (used + 1) nextPrefix (by omega)
        exact InternedShallowHeap.noNewMu_trans keptAt later
  have executeOld : ∀ (remaining : Nat) (control : Control (Value Symbol Guard)) (before : Checked width)
      (used : Nat), used + remaining ≤ fuel → Trace used rootControl initialState control before →
      InputsThrough remaining control before →
      InternedShallowHeap.NoNewMu before.native.machine.heap
        (SourceEqualityNativeDemand.execute remaining control before).state.native.machine.heap := by
    intro remaining
    induction remaining with
    | zero =>
        intro control before _used _room _past _remainingInputs
        exact InternedShallowHeap.noNewMu_refl _
    | succ remaining ih =>
        intro control before used room past remainingInputs
        have kept := sourceStep used control before past (by omega) remainingInputs.1
        cases one : step control before with
        | yielded next after =>
            have oneTrace : Trace 1 control before next after :=
              .cons _ _ _ _ _ _ 0 remainingInputs.1 one (.refl _ _)
            have nextPrefix := past.trans oneTrace
            have nextInputs : InputsThrough remaining next after := by
              simpa only [one] using remainingInputs.2
            have keptAt : InternedShallowHeap.NoNewMu before.native.machine.heap after.native.machine.heap := by
              simpa only [one, Outcome.state] using kept
            have later := ih next after (used + 1) (by omega) nextPrefix nextInputs
            simpa only [SourceEqualityNativeDemand.execute, one] using
              InternedShallowHeap.noNewMu_trans keptAt later
        | done | failed | constraintError | blocked =>
            simpa only [SourceEqualityNativeDemand.execute, one, Outcome.state] using kept
  constructor
  · exact executeOld fuel rootControl initialState 0 (by omega) (.refl _ _) inputs
  · intro used rest current bounded actual
    exact traceOld used rootControl initialState rest current actual 0 (.refl _ _)
      (by simpa only [Nat.zero_add] using bounded)

end MicroCFTA.SourceSynthesisCurrentUniverseNativeAllocation

#print axioms MicroCFTA.SourceSynthesisCurrentUniverseNativeAllocation.cold_lift_heap
#print axioms MicroCFTA.SourceSynthesisCurrentUniverseNativeAllocation.cold_step_no_new_mu
#print axioms MicroCFTA.SourceSynthesisCurrentUniverseNativeAllocation.original_universe_cold_query_no_new_mu
