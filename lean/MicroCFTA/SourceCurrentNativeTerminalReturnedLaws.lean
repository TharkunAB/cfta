import MicroCFTA.SourceCurrentAllocatedNativeContextCache
import MicroCFTA.SourceEqualityNativeDemandOperations

/-!
# Returned laws at an actual terminal native step

Note [Terminal memo laws]
A terminal step can publish or demand memo cells before it blocks.
The lookup and demand laws preserve every existing returned-cell law.
Checked edge bodies retain the whole native state, including all tables.
A finish instruction always yields. The terminal observation excludes it.
This module proves no source meaning, native inhabitance, or model existence.
-/
namespace MicroCFTA.SourceCurrentNativeTerminalReturnedLaws
open InternedConstructorTemplates SourceRecursiveIntersectionCode SourceRecursiveIntersectionThunks
open SourceEqualityNativeDemand
open SourceCurrentAllocatedNativeContextCache (Returned)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Native" => SourceRecursiveIntersectionThunks.State

set_option autoImplicit false
variable {width : Nat} {Output : Type}

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

theorem terminal_step_preserves_returned
    [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (nodeLaw : NodeRequest Symbol Guard → Value Symbol Guard → Prop)
    (edgeLaw : EdgeRequest Symbol Guard → EdgeValue Symbol Guard → Prop)
    (control : Control Output) (before : Checked width)
    (nodes : Returned nodeLaw before.native.nodes)
    (edges : Returned edgeLaw before.native.edges)
    (terminal : ∀ (next : Control Output) (after : Checked width),
      SourceEqualityNativeDemand.step control before ≠ .yielded next after) :
    Returned nodeLaw (SourceEqualityNativeDemand.step control before).state.native.nodes ∧
      Returned edgeLaw (SourceEqualityNativeDemand.step control before).state.native.edges := by
  cases control with
  | edgeBody request resume =>
      change Returned nodeLaw (SourceEqualityNativeDemand.body request resume before).state.native.nodes ∧
        Returned edgeLaw (SourceEqualityNativeDemand.body request resume before).state.native.edges
      rw [SourceEqualityNativeDemandOperations.body_native]
      exact ⟨nodes, edges⟩
  | code code =>
    cases code with
    | pure value => exact ⟨nodes, edges⟩
    | fail failure => exact ⟨nodes, edges⟩
    | work job resume => exact ⟨nodes, edges⟩
    | enter domain left right first second resume => exact ⟨nodes, edges⟩
    | read name resume => exact ⟨nodes, edges⟩
    | optionalBinder key body resume =>
        cases chosen : SourceRecursiveIntersectionMaybeMu.maybeMu key body before.native.machine.heap with
        | pending pendingKey heap =>
            simpa only [SourceEqualityNativeDemand.step, SourceRecursiveIntersectionNative.step,
              chosen, lift, Outcome.state, advance] using And.intro nodes edges
        | done value heap =>
            simpa only [SourceEqualityNativeDemand.step, SourceRecursiveIntersectionNative.step,
              chosen, lift, Outcome.state, advance] using And.intro nodes edges
    | node request resume =>
        have published := lookup_nodes nodeLaw edgeLaw request before.native nodes edges
        cases selected : lookupNode width request before.native with
        | mk selection chosen =>
          simp only [selected] at published
          cases selection with
          | direct emitted =>
              simpa only [SourceEqualityNativeDemand.step, SourceRecursiveIntersectionNative.step,
                selected, lift, Outcome.state] using published
          | memoized handle =>
            have demandedLaws : Returned nodeLaw (demandNode handle chosen).2.nodes ∧
                Returned edgeLaw (demandNode handle chosen).2.edges :=
              ⟨SourceCurrentAllocatedNativeContextCache.returned_demand nodeLaw handle chosen.nodes published.1,
                published.2⟩
            cases demanded : demandNode handle chosen with
            | mk observation running =>
              simp only [demanded] at demandedLaws
              cases observation <;>
                simpa only [SourceEqualityNativeDemand.step, SourceRecursiveIntersectionNative.step,
                  selected, demanded, lift, Outcome.state] using demandedLaws
    | edge request resume =>
        have published : Returned nodeLaw (lookupEdge width request before.native).2.nodes ∧
            Returned edgeLaw (lookupEdge width request before.native).2.edges :=
          ⟨nodes, SourceCurrentAllocatedNativeContextCache.returned_lookup
            edgeLaw _ request before.native.edges edges⟩
        cases selected : lookupEdge width request before.native with
        | mk handle chosen =>
          simp only [selected] at published
          have demandedLaws : Returned nodeLaw (demandEdge handle chosen).2.nodes ∧
              Returned edgeLaw (demandEdge handle chosen).2.edges :=
            ⟨published.1, SourceCurrentAllocatedNativeContextCache.returned_demand
              edgeLaw handle chosen.edges published.2⟩
          cases demanded : demandEdge handle chosen with
          | mk observation running =>
            simp only [demanded] at demandedLaws
            cases observation <;>
              simpa only [SourceEqualityNativeDemand.step, selected, demanded, Outcome.state] using demandedLaws
    | finishNode handle value resume =>
        exact False.elim (terminal _ _ rfl)
    | finishEdge handle value resume =>
        exact False.elim (terminal _ _ rfl)

end MicroCFTA.SourceCurrentNativeTerminalReturnedLaws
