import MicroCFTA.SourceCurrentAllocatedNativeEdgeBodyReturned
import MicroCFTA.SourceCurrentAllocatedNativePhysicalCache
import MicroCFTA.SourceEqualityNativeDemandRunning

/-!
# Returned laws through one actual checked node query

The body hypothesis uses a strict smaller budget at the real emitted body.
The actual clean body trace retains the captured evaluating cell.
The finish frame stores the same producer result and retains both memo laws.
-/
namespace MicroCFTA.SourceCurrentAllocatedNativeNodeQueryReturned
open InternedConstructorTemplates SourceRecursiveIntersectionCode SourceRecursiveIntersectionThunks
open SourceEqualityNativeDemand
open SourceCurrentAllocatedNativeContextCache (Returned)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Native" => SourceRecursiveIntersectionThunks.State
variable {width : Nat}

set_option autoImplicit false

/-- A pure control retains its exact full state at every budget. -/
private theorem pure_endpoint_state
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (fuel : Nat) (value : Value Symbol Guard) (state : Checked width) :
    (SourceEqualityNativeDemand.execute fuel (.code (.pure value)) state).state = state := by
  cases fuel <;> rfl

/-- Actual node publication retains both existing returned laws. -/
private theorem lookup_returned
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

/-- The captured node finish retains both laws at every actual endpoint. -/
private theorem finish_endpoint_returned
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (nodeLaw : NodeRequest Symbol Guard → Value Symbol Guard → Prop)
    (edgeLaw : EdgeRequest Symbol Guard → EdgeValue Symbol Guard → Prop)
    (request : NodeRequest Symbol Guard) (handle : Nat) (value : Value Symbol Guard) (state : Checked width)
    (nodes : Returned nodeLaw state.native.nodes) (edges : Returned edgeLaw state.native.edges)
    (running : state.native.nodes.cells handle = some ⟨request, .evaluating⟩)
    (localLaw : nodeLaw request value) (fuel : Nat) :
    Returned nodeLaw (SourceEqualityNativeDemand.execute fuel
      (.code (.finishNode handle value (.pure value))) state).state.native.nodes ∧
    Returned edgeLaw (SourceEqualityNativeDemand.execute fuel
      (.code (.finishNode handle value (.pure value))) state).state.native.edges := by
  cases fuel with
  | zero => exact ⟨nodes, edges⟩
  | succ fuel =>
      have finished := SourceCurrentAllocatedNativeContextCache.returned_finish
        nodeLaw handle request value state.native.nodes nodes running localLaw
      change Returned nodeLaw
          (SourceEqualityNativeDemand.execute fuel (.code (.pure value))
            ⟨finishNode handle value state.native, state.operations⟩).state.native.nodes ∧
        Returned edgeLaw
          (SourceEqualityNativeDemand.execute fuel (.code (.pure value))
            ⟨finishNode handle value state.native, state.operations⟩).state.native.edges
      rw [pure_endpoint_state]
      exact ⟨finished, edges⟩

/-- Actual node query endpoints retain both laws through the same strict smaller emitted body. -/
theorem node_query_returned_of_body_induction
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (nodeLaw : NodeRequest Symbol Guard → Value Symbol Guard → Prop)
    (edgeLaw : EdgeRequest Symbol Guard → EdgeValue Symbol Guard → Prop)
    (request : NodeRequest Symbol Guard) (state : Checked width) (fuel : Nat)
    (physical : SourceCurrentAllocatedNativePhysicalCache.Valid state.native)
    (ready : NodeReady state.native.machine request)
    (safe : ∀ key, SourceRecursiveIntersectionMemo.requestKey width request.domain request.left request.right = some key →
      SourceRecursiveIntersectionMemo.KeySafe width request.domain request.left request.right)
    (nodes : Returned nodeLaw state.native.nodes) (edges : Returned edgeLaw state.native.edges)
    (bodyIH : ∀ bodyFuel, bodyFuel < fuel →
      ∀ (next : Value Symbol Guard → Code Symbol Guard (Value Symbol Guard)) (first : Checked width),
      Steps 1 (.code (.node request .pure)) state
        (.code ((compileNode request).bind next)) first →
      Returned nodeLaw first.native.nodes → Returned edgeLaw first.native.edges →
      Returned nodeLaw (SourceEqualityNativeDemand.execute bodyFuel
        (.code (compileNode request)) first).state.native.nodes ∧
      Returned edgeLaw (SourceEqualityNativeDemand.execute bodyFuel
        (.code (compileNode request)) first).state.native.edges ∧
      (∀ (value : Value Symbol Guard) (middle : Checked width),
        Steps bodyFuel (.code (compileNode request)) first (.code (.pure value)) middle →
        nodeLaw request value)) :
    Returned nodeLaw (SourceEqualityNativeDemand.execute fuel
      (.code (.node request .pure)) state).state.native.nodes ∧
    Returned edgeLaw (SourceEqualityNativeDemand.execute fuel
      (.code (.node request .pure)) state).state.native.edges := by
  cases fuel with
  | zero => exact ⟨nodes, edges⟩
  | succ fuel =>
      have publishedLaws := lookup_returned nodeLaw edgeLaw request state.native nodes edges
      cases selected : lookupNode width request state.native with
      | mk selection chosen =>
          cases selection with
          | direct actual =>
              obtain ⟨same, unchanged⟩ :=
                SourceRecursiveIntersectionNative.lookupNode_direct request actual state.native chosen selected
              subst actual
              subst chosen
              have one : SourceEqualityNativeDemand.step (.code (.node request .pure)) state =
                  .yielded (.code ((compileNode request).bind .pure)) state := by
                simp only [SourceEqualityNativeDemand.step, SourceRecursiveIntersectionNative.step,
                  selected, SourceEqualityNativeDemand.lift]
              have prefixObserved : Steps 1 (.code (.node request .pure)) state
                  (.code ((compileNode request).bind .pure)) state :=
                .cons _ _ _ _ _ _ _ one (.refl _ _)
              have built := bodyIH fuel (by omega) .pure state prefixObserved nodes edges
              simpa only [SourceEqualityNativeDemand.execute, one, code_bind_pure] using
                And.intro built.1 built.2.1
          | memoized handle =>
              have chosenNodes : Returned nodeLaw chosen.nodes := by
                simpa only [selected] using publishedLaws.1
              have chosenEdges : Returned edgeLaw chosen.edges := by
                simpa only [selected] using publishedLaws.2
              obtain ⟨key, keyed, _published, _machine⟩ :=
                SourceRecursiveIntersectionNative.lookupNode_memoized request state.native chosen handle selected
              have keySafe := safe key keyed
              have chosenPhysical : SourceCurrentAllocatedNativePhysicalCache.Valid chosen := by
                simpa only [selected] using
                  SourceCurrentAllocatedNativePhysicalCache.lookupNode_valid state.native physical request ready keySafe
              have demandedNodes : Returned nodeLaw (demandNode handle chosen).2.nodes :=
                SourceCurrentAllocatedNativeContextCache.returned_demand nodeLaw handle chosen.nodes chosenNodes
              have demandedEdges : Returned edgeLaw (demandNode handle chosen).2.edges := chosenEdges
              cases demanded : demandNode handle chosen with
              | mk observation current =>
                  have currentNodes : Returned nodeLaw current.nodes := by
                    simpa only [demanded] using demandedNodes
                  have currentEdges : Returned edgeLaw current.edges := by
                    simpa only [demanded] using demandedEdges
                  cases observation with
                  | absent | busy =>
                      simpa only [SourceEqualityNativeDemand.execute, SourceEqualityNativeDemand.step,
                        SourceRecursiveIntersectionNative.step, selected, demanded,
                        SourceEqualityNativeDemand.lift, SourceEqualityNativeDemand.Outcome.state] using
                        And.intro currentNodes currentEdges
                  | ready value =>
                      have one : SourceEqualityNativeDemand.step (.code (.node request .pure)) state =
                          .yielded (.code (.pure value)) ⟨current, state.operations⟩ := by
                        simp only [SourceEqualityNativeDemand.step, SourceRecursiveIntersectionNative.step,
                          selected, demanded, SourceEqualityNativeDemand.lift]
                      simpa only [SourceEqualityNativeDemand.execute, one, pure_endpoint_state] using
                        And.intro currentNodes currentEdges
                  | evaluate actual =>
                      have same := SourceCurrentAllocatedNativePhysicalCache.node_started request actual
                        state.native chosen current handle physical ready keySafe selected demanded
                      subst actual
                      let first : Checked width := ⟨current, state.operations⟩
                      let next : Value Symbol Guard → Code Symbol Guard (Value Symbol Guard) :=
                        fun value => .finishNode handle value (.pure value)
                      have one : SourceEqualityNativeDemand.step (.code (.node request .pure)) state =
                          .yielded (.code ((compileNode request).bind next)) first := by
                        simp only [SourceEqualityNativeDemand.step, SourceRecursiveIntersectionNative.step,
                          selected, demanded, SourceEqualityNativeDemand.lift, first, next]
                      have prefixObserved : Steps 1 (.code (.node request .pure)) state
                          (.code ((compileNode request).bind next)) first :=
                        .cons _ _ _ _ _ _ _ one (.refl _ _)
                      have currentPhysical : SourceCurrentAllocatedNativePhysicalCache.Valid current := by
                        simpa only [demanded] using
                          SourceCurrentAllocatedNativePhysicalCache.demandNode_valid chosen chosenPhysical handle
                      have running :=
                        (SourceRecursiveIntersectionNative.demandNode_evaluate handle chosen current request demanded).2
                      have endpoint : (SourceEqualityNativeDemand.execute (fuel + 1)
                            (.code (.node request .pure)) state).state =
                          (SourceEqualityNativeDemand.execute fuel
                            ((Control.code (compileNode request)).bind next) first).state := by
                        simp only [SourceEqualityNativeDemand.execute, one, Control.bind]
                      rw [endpoint]
                      rcases SourceCurrentAllocatedNativeEdgeBodyReturned.bind_endpoint_state_cases
                          fuel (.code (compileNode request)) next first with sameEndpoint |
                          ⟨steps, value, middle, shorter, actualBody, sameEndpoint⟩
                      · rw [sameEndpoint]
                        have built := bodyIH fuel (by omega) next first prefixObserved currentNodes currentEdges
                        exact ⟨built.1, built.2.1⟩
                      · rw [sameEndpoint]
                        have built := bodyIH steps (by omega) next first prefixObserved currentNodes currentEdges
                        have middleNodes : Returned nodeLaw middle.native.nodes := by
                          simpa only [actualBody.execute, Outcome.state] using built.1
                        have middleEdges : Returned edgeLaw middle.native.edges := by
                          simpa only [actualBody.execute, Outcome.state] using built.2.1
                        have localLaw := built.2.2 value middle actualBody
                        have retained := SourceEqualityNativeDemandRunning.trace_retains steps
                          (.code (compileNode request)) first middle value actualBody
                          (compileNode_bodyCode request) currentPhysical.shape
                        have middleRunning := retained.2.1 handle request running
                        exact finish_endpoint_returned nodeLaw edgeLaw request handle value middle
                          middleNodes middleEdges middleRunning localLaw (fuel - steps)

end MicroCFTA.SourceCurrentAllocatedNativeNodeQueryReturned

#print axioms MicroCFTA.SourceCurrentAllocatedNativeNodeQueryReturned.node_query_returned_of_body_induction
