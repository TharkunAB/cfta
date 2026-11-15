import MicroCFTA.SourceCurrentAllocatedNativeEdgeBodyReturned
import MicroCFTA.SourceCurrentAllocatedNativePhysicalCache
import MicroCFTA.SourceEqualityNativeDemandRunning

/-!
# Returned laws through one actual checked edge query

The body hypothesis uses a strict smaller budget at the actual checked body.
The actual clean body trace retains the captured evaluating edge cell.
The finish frame stores the same producer row and retains both memo laws.
-/
namespace MicroCFTA.SourceCurrentAllocatedNativeEdgeQueryReturned
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
    (fuel : Nat) (value : EdgeValue Symbol Guard) (state : Checked width) :
    (SourceEqualityNativeDemand.execute fuel (.code (.pure value)) state).state = state := by
  cases fuel <;> rfl

/-- Actual edge publication retains both existing returned laws. -/
private theorem lookup_returned
    (nodeLaw : NodeRequest Symbol Guard → Value Symbol Guard → Prop)
    (edgeLaw : EdgeRequest Symbol Guard → EdgeValue Symbol Guard → Prop)
    (request : EdgeRequest Symbol Guard) (state : Native width Symbol Guard)
    (nodes : Returned nodeLaw state.nodes) (edges : Returned edgeLaw state.edges) :
    Returned nodeLaw (lookupEdge width request state).2.nodes ∧
      Returned edgeLaw (lookupEdge width request state).2.edges := by
  constructor
  · simpa only [lookupEdge] using nodes
  · simpa only [lookupEdge] using
      SourceCurrentAllocatedNativeContextCache.returned_lookup edgeLaw
        (SourceRecursiveIntersectionEdgeMemo.requestKey width request.domain request.left request.right)
        request state.edges edges

/-- The captured edge finish retains both laws at every actual endpoint. -/
private theorem finish_endpoint_returned
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (nodeLaw : NodeRequest Symbol Guard → Value Symbol Guard → Prop)
    (edgeLaw : EdgeRequest Symbol Guard → EdgeValue Symbol Guard → Prop)
    (request : EdgeRequest Symbol Guard) (handle : Nat) (value : EdgeValue Symbol Guard) (state : Checked width)
    (nodes : Returned nodeLaw state.native.nodes) (edges : Returned edgeLaw state.native.edges)
    (running : state.native.edges.cells handle = some ⟨request, .evaluating⟩)
    (localLaw : edgeLaw request value) (fuel : Nat) :
    Returned nodeLaw (SourceEqualityNativeDemand.execute fuel
      (.code (.finishEdge handle value (.pure value))) state).state.native.nodes ∧
    Returned edgeLaw (SourceEqualityNativeDemand.execute fuel
      (.code (.finishEdge handle value (.pure value))) state).state.native.edges := by
  cases fuel with
  | zero => exact ⟨nodes, edges⟩
  | succ fuel =>
      have finished := SourceCurrentAllocatedNativeContextCache.returned_finish
        edgeLaw handle request value state.native.edges edges running localLaw
      change Returned nodeLaw
          (SourceEqualityNativeDemand.execute fuel (.code (.pure value))
            ⟨finishEdge handle value state.native, state.operations⟩).state.native.nodes ∧
        Returned edgeLaw
          (SourceEqualityNativeDemand.execute fuel (.code (.pure value))
            ⟨finishEdge handle value state.native, state.operations⟩).state.native.edges
      rw [pure_endpoint_state]
      exact ⟨nodes, finished⟩

/-- Actual edge query endpoints retain both laws through the same strict smaller checked body. -/
theorem edge_query_returned_of_body_induction
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (nodeLaw : NodeRequest Symbol Guard → Value Symbol Guard → Prop)
    (edgeLaw : EdgeRequest Symbol Guard → EdgeValue Symbol Guard → Prop)
    (request : EdgeRequest Symbol Guard) (state : Checked width) (fuel : Nat)
    (physical : SourceCurrentAllocatedNativePhysicalCache.Valid state.native)
    (ready : EdgeReady state.native.machine request)
    (safe : SourceRecursiveIntersectionEdgeMemo.KeySafe width request.domain request.left request.right)
    (nodes : Returned nodeLaw state.native.nodes) (edges : Returned edgeLaw state.native.edges)
    (bodyIH : ∀ bodyFuel, bodyFuel < fuel →
      ∀ (next : EdgeValue Symbol Guard → Code Symbol Guard (EdgeValue Symbol Guard)) (first : Checked width),
      Steps 1 (.code (.edge request .pure)) state (.edgeBody request next) first →
      Returned nodeLaw first.native.nodes → Returned edgeLaw first.native.edges →
      Returned nodeLaw (SourceEqualityNativeDemand.execute bodyFuel
        (.edgeBody request .pure) first).state.native.nodes ∧
      Returned edgeLaw (SourceEqualityNativeDemand.execute bodyFuel
        (.edgeBody request .pure) first).state.native.edges ∧
      (∀ (value : EdgeValue Symbol Guard) (middle : Checked width),
        Steps bodyFuel (.edgeBody request .pure) first (.code (.pure value)) middle →
        edgeLaw request value)) :
    Returned nodeLaw (SourceEqualityNativeDemand.execute fuel
      (.code (.edge request .pure)) state).state.native.nodes ∧
    Returned edgeLaw (SourceEqualityNativeDemand.execute fuel
      (.code (.edge request .pure)) state).state.native.edges := by
  cases fuel with
  | zero => exact ⟨nodes, edges⟩
  | succ fuel =>
      have publishedLaws := lookup_returned nodeLaw edgeLaw request state.native nodes edges
      cases selected : lookupEdge width request state.native with
      | mk handle chosen =>
          have chosenNodes : Returned nodeLaw chosen.nodes := by
            simpa only [selected] using publishedLaws.1
          have chosenEdges : Returned edgeLaw chosen.edges := by
            simpa only [selected] using publishedLaws.2
          have chosenPhysical : SourceCurrentAllocatedNativePhysicalCache.Valid chosen := by
            simpa only [selected] using
              SourceCurrentAllocatedNativePhysicalCache.lookupEdge_valid state.native physical request ready safe
          have demandedNodes : Returned nodeLaw (demandEdge handle chosen).2.nodes := chosenNodes
          have demandedEdges : Returned edgeLaw (demandEdge handle chosen).2.edges :=
            SourceCurrentAllocatedNativeContextCache.returned_demand edgeLaw handle chosen.edges chosenEdges
          cases demanded : demandEdge handle chosen with
          | mk observation current =>
              have currentNodes : Returned nodeLaw current.nodes := by
                simpa only [demanded] using demandedNodes
              have currentEdges : Returned edgeLaw current.edges := by
                simpa only [demanded] using demandedEdges
              cases observation with
              | absent | busy =>
                  simpa only [SourceEqualityNativeDemand.execute, SourceEqualityNativeDemand.step,
                    selected, demanded, SourceEqualityNativeDemand.Outcome.state] using
                    And.intro currentNodes currentEdges
              | ready value =>
                  have one : SourceEqualityNativeDemand.step (.code (.edge request .pure)) state =
                      .yielded (.code (.pure value)) ⟨current, state.operations⟩ := by
                    simp only [SourceEqualityNativeDemand.step, selected, demanded]
                  simpa only [SourceEqualityNativeDemand.execute, one, pure_endpoint_state] using
                    And.intro currentNodes currentEdges
              | evaluate actual =>
                  have same := SourceCurrentAllocatedNativePhysicalCache.edge_started request actual
                    state.native chosen current handle physical ready safe selected demanded
                  subst actual
                  let first : Checked width := ⟨current, state.operations⟩
                  let next : EdgeValue Symbol Guard → Code Symbol Guard (EdgeValue Symbol Guard) :=
                    fun value => .finishEdge handle value (.pure value)
                  have one : SourceEqualityNativeDemand.step (.code (.edge request .pure)) state =
                      .yielded (.edgeBody request next) first := by
                    simp only [SourceEqualityNativeDemand.step, selected, demanded, first, next]
                  have prefixObserved : Steps 1 (.code (.edge request .pure)) state
                      (.edgeBody request next) first :=
                    .cons _ _ _ _ _ _ _ one (.refl _ _)
                  have currentPhysical : SourceCurrentAllocatedNativePhysicalCache.Valid current := by
                    simpa only [demanded] using
                      SourceCurrentAllocatedNativePhysicalCache.demandEdge_valid chosen chosenPhysical handle
                  have running :=
                    (SourceRecursiveIntersectionNative.demandEdge_evaluate handle chosen current request demanded).2
                  have endpoint : (SourceEqualityNativeDemand.execute (fuel + 1)
                        (.code (.edge request .pure)) state).state =
                      (SourceEqualityNativeDemand.execute fuel
                        ((Control.edgeBody request .pure).bind next) first).state := by
                    simp only [SourceEqualityNativeDemand.execute, one, Control.bind, Code.bind]
                  rw [endpoint]
                  rcases SourceCurrentAllocatedNativeEdgeBodyReturned.bind_endpoint_state_cases
                      fuel (.edgeBody request .pure) next first with sameEndpoint |
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
                      (.edgeBody request .pure) first middle value actualBody
                      (by intro value; trivial) currentPhysical.shape
                    have middleRunning := retained.2.2 handle request running
                    exact finish_endpoint_returned nodeLaw edgeLaw request handle value middle
                      middleNodes middleEdges middleRunning localLaw (fuel - steps)

end MicroCFTA.SourceCurrentAllocatedNativeEdgeQueryReturned
