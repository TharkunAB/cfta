import MicroCFTA.SourceCurrentAllocatedNativeContextCache
import MicroCFTA.SourceCurrentAllocatedNativeCompileDispatchOrigin
import MicroCFTA.SourceCurrentAllocatedNativeEdgeCompileDispatchOrigin

/-!
# Both memo laws on one actual initial-query history

Each finish uses its actual original prefix and compiled producer. The
induction supplies both existing laws at that same before-finish state.
Local body rules remain explicit semantic proof obligations.
-/
namespace MicroCFTA.SourceCurrentAllocatedNativeActualPrefixReturnedInduction
open InternedConstructorTemplates SourceRecursiveIntersectionCode SourceRecursiveIntersectionThunks
open SourceEqualityNativeDemand
open SourceCurrentAllocatedNativeContextCache (Returned)
open SourceCurrentAllocatedNativePhysicalTraceCompletion (Trace)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Native" => SourceRecursiveIntersectionThunks.State
local notation "Inputs" => SourceCurrentAllocatedNativePhysicalExecution.Inputs
variable {width : Nat}

set_option autoImplicit false

private theorem lookup_nodes
    (nodeLaw : NodeRequest Symbol Guard → Value Symbol Guard → Prop)
    (edgeLaw : EdgeRequest Symbol Guard → EdgeValue Symbol Guard → Prop)
    (request : NodeRequest Symbol Guard) (state : Native width Symbol Guard)
    (nodes : Returned nodeLaw state.nodes) (edges : Returned edgeLaw state.edges) :
    Returned nodeLaw (lookupNode width request state).2.nodes ∧
      Returned edgeLaw (lookupNode width request state).2.edges := by
  cases key : SourceRecursiveIntersectionMemo.requestKey width request.domain request.left request.right with
  | none => simpa only [lookupNode, key] using And.intro nodes edges
  | some value =>
      constructor
      · simpa only [lookupNode, key] using
          SourceCurrentAllocatedNativeContextCache.returned_lookup nodeLaw value request state.nodes nodes
      · simpa only [lookupNode, key] using edges

private theorem step_returned
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (nodeLaw : NodeRequest Symbol Guard → Value Symbol Guard → Prop)
    (edgeLaw : EdgeRequest Symbol Guard → EdgeValue Symbol Guard → Prop)
    (control next : Control (Value Symbol Guard)) (before after : Checked width)
    (nodes : Returned nodeLaw before.native.nodes) (edges : Returned edgeLaw before.native.edges)
    (inputs : Inputs control before)
    (one : SourceEqualityNativeDemand.step control before = .yielded next after)
    (nodeFinish : ∀ (handle : Nat) (value : Value Symbol Guard)
      (resume : Code Symbol Guard (Value Symbol Guard)) (request : NodeRequest Symbol Guard),
      control = .code (.finishNode handle value resume) →
      before.native.nodes.cells handle = some ⟨request, .evaluating⟩ → nodeLaw request value)
    (edgeFinish : ∀ (handle : Nat) (value : EdgeValue Symbol Guard)
      (resume : Code Symbol Guard (Value Symbol Guard)) (request : EdgeRequest Symbol Guard),
      control = .code (.finishEdge handle value resume) →
      before.native.edges.cells handle = some ⟨request, .evaluating⟩ → edgeLaw request value) :
    Returned nodeLaw after.native.nodes ∧ Returned edgeLaw after.native.edges := by
  cases control with
  | edgeBody request resume =>
      have same : after.native = before.native := by
        simpa only [show SourceEqualityNativeDemand.body request resume before = .yielded next after from one,
          Outcome.state] using SourceEqualityNativeDemandOperations.body_native request resume before
      rw [same]
      exact ⟨nodes, edges⟩
  | code code =>
    cases code with
    | pure | fail => cases one
    | work job resume | enter domain left right first second resume | read name resume =>
        obtain ⟨rfl, rfl⟩ := Outcome.yielded.inj one
        exact ⟨nodes, edges⟩
    | optionalBinder key body resume =>
        cases chosen : SourceRecursiveIntersectionMaybeMu.maybeMu key body before.native.machine.heap with
        | pending =>
            simp only [SourceEqualityNativeDemand.step, SourceRecursiveIntersectionNative.step, chosen, lift] at one
            cases one
        | done value heap =>
            simp only [SourceEqualityNativeDemand.step, SourceRecursiveIntersectionNative.step, chosen, lift] at one
            obtain ⟨rfl, rfl⟩ := Outcome.yielded.inj one
            exact ⟨nodes, edges⟩
    | node request resume =>
        have published := lookup_nodes nodeLaw edgeLaw request before.native nodes edges
        cases selected : lookupNode width request before.native with
        | mk selection chosen =>
          simp only [selected] at published
          cases selection with
          | direct emitted =>
              have same := Outcome.yielded.inj (by
                simpa only [SourceEqualityNativeDemand.step, SourceRecursiveIntersectionNative.step, selected, lift] using one)
              obtain ⟨rfl, rfl⟩ := same
              exact published
          | memoized handle =>
            have demandedLaws : Returned nodeLaw (demandNode handle chosen).2.nodes ∧
                Returned edgeLaw (demandNode handle chosen).2.edges :=
              ⟨SourceCurrentAllocatedNativeContextCache.returned_demand nodeLaw handle chosen.nodes published.1, published.2⟩
            cases demanded : demandNode handle chosen with
            | mk observation running =>
              simp only [demanded] at demandedLaws
              cases observation with
              | absent | busy =>
                  simp only [SourceEqualityNativeDemand.step, SourceRecursiveIntersectionNative.step, selected, demanded, lift] at one
                  cases one
              | ready value | evaluate emitted =>
                  have same := Outcome.yielded.inj (by
                    simpa only [SourceEqualityNativeDemand.step, SourceRecursiveIntersectionNative.step, selected, demanded, lift] using one)
                  obtain ⟨rfl, rfl⟩ := same
                  exact demandedLaws
    | edge request resume =>
        have published : Returned nodeLaw (lookupEdge width request before.native).2.nodes ∧
            Returned edgeLaw (lookupEdge width request before.native).2.edges :=
          ⟨nodes, SourceCurrentAllocatedNativeContextCache.returned_lookup edgeLaw _ request before.native.edges edges⟩
        cases selected : lookupEdge width request before.native with
        | mk handle chosen =>
          simp only [selected] at published
          have demandedLaws : Returned nodeLaw (demandEdge handle chosen).2.nodes ∧
              Returned edgeLaw (demandEdge handle chosen).2.edges :=
            ⟨published.1, SourceCurrentAllocatedNativeContextCache.returned_demand edgeLaw handle chosen.edges published.2⟩
          cases demanded : demandEdge handle chosen with
          | mk observation running =>
            simp only [demanded] at demandedLaws
            cases observation with
            | absent | busy =>
                simp only [SourceEqualityNativeDemand.step, selected, demanded] at one
                cases one
            | ready value | evaluate emitted =>
                have same := Outcome.yielded.inj (by
                  simpa only [SourceEqualityNativeDemand.step, selected, demanded] using one)
                obtain ⟨rfl, rfl⟩ := same
                exact demandedLaws
    | finishNode handle value resume =>
        obtain ⟨request, running, _available⟩ := inputs
        have localLaw := nodeFinish handle value resume request rfl running
        obtain ⟨rfl, rfl⟩ := Outcome.yielded.inj one
        exact ⟨SourceCurrentAllocatedNativeContextCache.returned_finish
          nodeLaw handle request value before.native.nodes nodes running localLaw, edges⟩
    | finishEdge handle value resume =>
        obtain ⟨request, running, _resident⟩ := inputs
        have localLaw := edgeFinish handle value resume request rfl running
        obtain ⟨rfl, rfl⟩ := Outcome.yielded.inj one
        exact ⟨nodes, SourceCurrentAllocatedNativeContextCache.returned_finish
          edgeLaw handle request value before.native.edges edges running localLaw⟩

theorem returned_at_every_actual_prefix
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat}
    (nodeLaw : NodeRequest Symbol Guard → Value Symbol Guard → Prop)
    (edgeLaw : EdgeRequest Symbol Guard → EdgeValue Symbol Guard → Prop)
    (rootRequest : NodeRequest Symbol Guard)
    (machine : SourceRecursiveIntersectionKernel.Machine Symbol Guard)
    (machineValid : SourceRecursiveIntersectionKernel.Valid machine)
    (operations : SourceEqualityConstraintMemoAllocation.State)
    (fuel count : Nat) (rest : Control (Value Symbol Guard)) (after : Checked width)
    (bounded : count ≤ fuel)
    (actual : Trace count (.code (.node rootRequest .pure))
      (⟨initial width machine, operations⟩ : Checked width) rest after)
    (nodeBodies : ∀ (finishUsed dispatchUsed bodyCount handle : Nat)
      (request : NodeRequest Symbol Guard) (value : Value Symbol Guard)
      (beforeBody beforeFinish : Checked width)
      (resume : Value Symbol Guard → Code Symbol Guard (Value Symbol Guard)),
      finishUsed < count → dispatchUsed + bodyCount = finishUsed → 0 < dispatchUsed →
      Trace finishUsed (.code (.node rootRequest .pure))
        (⟨initial width machine, operations⟩ : Checked width)
        (.code (.finishNode handle value (resume value))) beforeFinish →
      Steps dispatchUsed (.code (.node rootRequest .pure))
        (⟨initial width machine, operations⟩ : Checked width)
        (.code ((compileNode request).bind
          (fun result => .finishNode handle result (resume result)))) beforeBody →
      beforeBody.native.nodes.cells handle = some ⟨request, .evaluating⟩ →
      Steps bodyCount (.code (compileNode request)) beforeBody (.code (.pure value)) beforeFinish →
      beforeFinish.native.nodes.cells handle = some ⟨request, .evaluating⟩ →
      Returned nodeLaw beforeFinish.native.nodes → Returned edgeLaw beforeFinish.native.edges →
      nodeLaw request value)
    (edgeBodies : ∀ (finishUsed dispatchUsed bodyCount handle : Nat)
      (request : EdgeRequest Symbol Guard) (value : EdgeValue Symbol Guard)
      (beforeBody beforeFinish : Checked width)
      (resume : EdgeValue Symbol Guard → Code Symbol Guard (Value Symbol Guard)),
      finishUsed < count → dispatchUsed + bodyCount = finishUsed → 0 < dispatchUsed →
      Trace finishUsed (.code (.node rootRequest .pure))
        (⟨initial width machine, operations⟩ : Checked width)
        (.code (.finishEdge handle value (resume value))) beforeFinish →
      Steps dispatchUsed (.code (.node rootRequest .pure))
        (⟨initial width machine, operations⟩ : Checked width)
        (.edgeBody request (fun result => .finishEdge handle result (resume result))) beforeBody →
      beforeBody.native.edges.cells handle = some ⟨request, .evaluating⟩ →
      Steps bodyCount (.edgeBody request .pure) beforeBody (.code (.pure value)) beforeFinish →
      beforeFinish.native.edges.cells handle = some ⟨request, .evaluating⟩ →
      Returned nodeLaw beforeFinish.native.nodes → Returned edgeLaw beforeFinish.native.edges →
      edgeLaw request value) :
    (Returned nodeLaw after.native.nodes ∧ Returned edgeLaw after.native.edges) ∧
      ∀ (used : Nat) (currentControl : Control (Value Symbol Guard)) (current : Checked width),
        used ≤ count →
        Trace used (.code (.node rootRequest .pure))
          (⟨initial width machine, operations⟩ : Checked width) currentControl current →
        Returned nodeLaw current.native.nodes ∧ Returned edgeLaw current.native.edges := by
  have stepAt (used : Nat) (control next : Control (Value Symbol Guard))
      (before current : Checked width) (smaller : used < count)
      (origin : Trace used (.code (.node rootRequest .pure))
        (⟨initial width machine, operations⟩ : Checked width) control before)
      (nodes : Returned nodeLaw before.native.nodes) (edges : Returned edgeLaw before.native.edges)
      (inputs : Inputs control before)
      (one : SourceEqualityNativeDemand.step control before = .yielded next current) :
      Returned nodeLaw current.native.nodes ∧ Returned edgeLaw current.native.edges := by
    apply step_returned nodeLaw edgeLaw control next before current nodes edges inputs one
    · intro handle value next request same owner
      subst control
      obtain ⟨dispatchUsed, bodyCount, beforeBody, resume, total, positive, _dispatchBound,
          entered, running, bodyTrace, last⟩ :=
        SourceCurrentAllocatedNativeCompileDispatchOrigin.compiled_node_origin_from_initial_query_finish
          rootRequest machine machineValid operations fuel used handle request value next before
          (by omega) origin owner
      apply nodeBodies used dispatchUsed bodyCount handle request value beforeBody before resume
        smaller total positive ?_ entered running bodyTrace owner nodes edges
      simpa only [last] using origin
    · intro handle value next request same owner
      subst control
      obtain ⟨dispatchUsed, bodyCount, beforeBody, resume, total, positive, _dispatchBound,
          entered, running, bodyTrace, last⟩ :=
        SourceCurrentAllocatedNativeEdgeCompileDispatchOrigin.checked_edge_body_origin_from_initial_query_finish
          rootRequest machine machineValid operations fuel used handle request value next before
          (by omega) origin owner
      apply edgeBodies used dispatchUsed bodyCount handle request value beforeBody before resume
        smaller total positive ?_ entered running bodyTrace owner nodes edges
      simpa only [last] using origin
  have advance (remaining : Nat) :
      ∀ (used : Nat) (control final : Control (Value Symbol Guard)) (before last : Checked width),
        used + remaining ≤ count →
        Trace used (.code (.node rootRequest .pure))
          (⟨initial width machine, operations⟩ : Checked width) control before →
        (Returned nodeLaw before.native.nodes ∧ Returned edgeLaw before.native.edges) →
        Trace remaining control before final last →
        Returned nodeLaw last.native.nodes ∧ Returned edgeLaw last.native.edges := by
    induction remaining with
    | zero =>
        intro used control final before last _within _origin known tail
        cases tail
        exact known
    | succ remaining ih =>
        intro used control final before last within origin known tail
        cases tail with
        | cons _ _ next middle _ _ _ inputs one later =>
            have currentLaws := stepAt used control next before middle (by omega)
              origin known.1 known.2 inputs one
            have oneTrace : Trace 1 control before next middle :=
              .cons _ _ _ _ _ _ 0 inputs one (.refl _ _)
            have nextOrigin : Trace (used + 1) (.code (.node rootRequest .pure))
                (⟨initial width machine, operations⟩ : Checked width) next middle :=
              origin.trans oneTrace
            exact ih (used + 1) next final middle last (by omega) nextOrigin currentLaws later
  have allPrefixes (used : Nat) (currentControl : Control (Value Symbol Guard)) (current : Checked width)
      (within : used ≤ count)
      (origin : Trace used (.code (.node rootRequest .pure))
        (⟨initial width machine, operations⟩ : Checked width) currentControl current) :
      Returned nodeLaw current.native.nodes ∧ Returned edgeLaw current.native.edges := by
    exact advance used 0 (.code (.node rootRequest .pure)) currentControl
      ⟨initial width machine, operations⟩ current (by omega) (.refl _ _)
      ⟨SourceCurrentAllocatedNativeContextCache.returned_empty nodeLaw,
        SourceCurrentAllocatedNativeContextCache.returned_empty edgeLaw⟩ origin
  exact ⟨allPrefixes count rest after (by omega) actual, allPrefixes⟩

end MicroCFTA.SourceCurrentAllocatedNativeActualPrefixReturnedInduction
