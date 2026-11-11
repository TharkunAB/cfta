import MicroCFTA.SourcePruningEnumerationSharedTraversalProper
import MicroCFTA.SourcePruningEnumerationOwnInputShape
import MicroCFTA.SourcePruningEnumerationSelectedEdgeProper

/-!
# Proper paths at actual shared selected and captured outcomes

The actual own prefix supplies the middle cache and child inputs.
Current guard normalization supplies valid projected tries.
Finalization retains proper paths at its actual returned cache.
-/
namespace MicroCFTA.SourcePruningEnumerationSharedSelectedContinuations.SelectedEdge
open EnumerationState EnumerationCorrectness EnumerationProgress EnumerationSchedule EnumerationSemantics
open InternedConstructorTemplates
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Queries" => SourceEndpointMemo.Memos
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
variable {width : Nat}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]

/-- Every retained selected-edge cache has proper stored pending paths. -/
theorem observed_cache_proper
    (checkEmpty : Bool) (r n p h k : Nat) (scs : List Suspended)
    (edge : EdgeValue Symbol Constraint) (caller : Caller width) (before : Cached) (queries : Queries)
    (proper : ProperState before.core) (inherited : ValidSuspended scs)
    (cached : SourceEqualityGuardReadback.Cached edge.entry.key.constraint.equalities)
    {result : Result width}
    (observed : run checkEmpty r n p h k scs edge caller before queries = result) :
    match (generalizing := false) result with
    | .complete _ _ _ after | .rejected _ _ after | .finalizeStopped _ _ _ after =>
        ProperState after.core
    | .stopped _ _ (some after) => ProperState after.core
    | _ => True := by
  cases allowed : arityAllows edge.children.length scs with
  | false =>
      simp only [run, SourcePruningEnumerationCachedOwn.prepare, allowed,
        Bool.false_eq_true, ↓reduceIte] at observed
      cases observed
      exact proper
  | true =>
      cases projected : SourcePruningEnumerationConstraint.project edge.entry.key.constraint with
      | none =>
          simp only [run, SourcePruningEnumerationCachedOwn.prepare, allowed, ↓reduceIte,
            projected] at observed
          cases observed
          trivial
      | some projection =>
          rcases projection with ⟨tries, residual⟩
          have triesValid := (SourcePruningEnumerationEdgeProjectionLanguage.projected_complete
            edge.entry.key.constraint cached tries residual projected).1
          cases suspended : SourcePruningEnumerationCachedOwn.suspendMany
              caller.checked.native.machine.heap tries before with
          | none =>
              simp only [run, SourcePruningEnumerationCachedOwn.prepare, allowed, ↓reduceIte,
                projected, suspended, Option.map_none] at observed
              cases observed
              trivial
          | some ownResult =>
              rcases ownResult with ⟨own, middle⟩
              have middleProper := SourcePruningEnumerationCachedOwn.suspendMany_proper
                caller.checked.native.machine.heap tries before middle own proper suspended
              have ownSame := SourcePruningEnumerationCachedOwn.suspendMany_vars
                caller.checked.native.machine.heap tries before own middle suspended
              let inputs := SourcePruningEnumerationEdgeInputs.children edge scs before.core.counter tries
              let staged := inputs.map (fun input => (input.1, input.2,
                SourcePruningEnumerationShallowChild.prepareChild
                  (EnumGuard := Constraint) input.2 input.1))
              have prepared : SourcePruningEnumerationCachedOwn.prepare
                  caller.checked.native.machine.heap scs edge before =
                    some [((edge.entry.key.symbol, staged, residual), middle)] := by
                simp only [SourcePruningEnumerationCachedOwn.prepare, allowed, ↓reduceIte,
                  projected, suspended, Option.map_some]
                rw [ownSame]
                simp only [staged, inputs, SourcePruningEnumerationEdgeInputs.children, List.map_map]
                rfl
              have buckets : ∀ input ∈ inputs, ProperInputs input.2 := by
                intro input member
                rcases input with ⟨incoming, bucket⟩
                exact SourcePruningEnumerationSelectedEdge.children_proper_inputs
                  edge scs before.core.counter tries inherited triesValid incoming bucket member
              have readback : staged.map (fun input => (input.1, input.2.1)) = inputs := by
                dsimp only [staged]
                simp only [List.map_map]
                exact List.map_id _
              simp only [run, prepared] at observed
              rw [readback] at observed
              cases childrenRun : ChildTraversal.run checkEmpty r n p h k inputs
                  caller middle queries with
              | complete fragments reached saved after =>
                  rw [childrenRun] at observed
                  cases observed
                  change ProperState after.core
                  exact ChildTraversal.complete_proper checkEmpty r n p h k inputs
                    caller reached middle after queries saved fragments middleProper buckets childrenRun
              | stopped completedPrefix observation candidate =>
                  rw [childrenRun] at observed
                  cases observed
                  cases candidate with
                  | none => trivial
                  | some after =>
                      exact ChildTraversal.stopped_candidate_proper checkEmpty r n p h k inputs
                        caller middle after queries completedPrefix observation middleProper buckets childrenRun

end MicroCFTA.SourcePruningEnumerationSharedSelectedContinuations.SelectedEdge

namespace MicroCFTA.SourcePruningEnumerationSharedSelectedContinuations.CapturedEdge
open EnumerationState EnumerationCorrectness EnumerationProgress EnumerationSemantics
open InternedConstructorTemplates
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Queries" => SourceEndpointMemo.Memos
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
variable {width : Nat}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]

/-- The stored payload supplies inherited validity at every retained captured cache. -/
theorem observed_cache_proper
    (checkEmpty : Bool) (r n p h k target : Nat) (scs : List Suspended)
    (edge : EdgeValue Symbol Constraint) (caller : Caller width) (before : Cached) (queries : Queries)
    (proper : ProperState before.core) {node : Option Nat}
    (stored : before.core.values[target]? = some (.unenumerated node scs))
    (cached : SourceEqualityGuardReadback.Cached edge.entry.key.constraint.equalities)
    {result : SelectedEdge.Result width}
    (observed : run checkEmpty r n p h k target scs edge caller before queries = some result) :
    match (generalizing := false) result with
    | .complete _ _ _ after | .rejected _ _ after | .finalizeStopped _ _ _ after =>
        ProperState after.core
    | .stopped _ _ (some after) => ProperState after.core
    | _ => True := by
  have payload := proper (.unenumerated node scs) (List.mem_of_getElem? stored)
  have inherited : ValidSuspended scs := by
    cases node with
    | none =>
        change scs = [] at payload
        subst scs
        intro sc member
        cases member
    | some handle =>
        intro sc member
        exact (payload sc member).1
  have retained := SelectedEdge.observed_cache_proper checkEmpty r n p h k scs edge
    caller before queries proper inherited cached rfl
  generalize selected : SelectedEdge.run checkEmpty r n p h k scs edge caller before queries =
    selectedResult at retained
  unfold run at observed
  rw [selected] at observed
  cases selectedResult with
  | unhandled =>
      cases observed
      trivial
  | rejected reached saved after =>
      cases observed
      exact retained
  | stopped completedPrefix observation candidate =>
      cases observed
      exact retained
  | finalizeStopped fragment reached saved after =>
      cases observed
      exact retained
  | complete fragment reached saved after =>
      cases finalized : SourcePruningEnumerationFinalize.run
          reached.checked.native.machine.heap k target fragment after with
      | none =>
          simp only [finalized] at observed
          cases observed
          exact retained
      | some finished =>
          simp only [finalized] at observed
          cases observed
          exact SourcePruningEnumerationFinalize.run_proper
            reached.checked.native.machine.heap k target fragment after finished retained finalized

end MicroCFTA.SourcePruningEnumerationSharedSelectedContinuations.CapturedEdge
