import MicroCFTA.SourceCurrentSecondaryTrace
import MicroCFTA.InternedFreshOrdinaryMemoGateTrace
import MicroCFTA.SourceSecondaryGateEndpointClosed

/-!
# Closed original values at current clear secondary endpoints

A constrained Mu endpoint returns false only when it is closed.
An unconstrained open Mu unfolds before the endpoint test.
Actual prepared substitution retains each external free name. Exact source
cost observations transfer that name to the returned value. A completed
false endpoint trace therefore implies that the original value is closed.
The theorem retains the existing context, depth, coverage, and cost heaps.
It does not assume closed input or transfer the graph to GHC evaluation.
-/
namespace MicroCFTA.SourceCurrentSecondaryProjectionEndpoint
open Cache InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedNestedConstruction (Outcome)
open InternedBinderProtocol (Reference NodeKey)
open InternedFreshOrdinaryMemoGateTrace (Ready)
open SourceCurrentSecondaryTrace (NodeTrace)
open InternedFreeOccurrenceRank (costs costs_free)

private def EndpointClosed (path : EqualityNormalize.Path) (value : Value Symbol Guard)
    (before : State Symbol Guard) (answer : Bool) : Prop :=
  path = [] → answer = false → Ready before → Available before value → value.free = []

private theorem node_closed [DecidableEq (EdgeKey Symbol Guard)]
    (unconstrained : Value Symbol Guard → Bool)
    {path : EqualityNormalize.Path} {value : Value Symbol Guard} {before : State Symbol Guard}
    {answer : Bool} {after : State Symbol Guard}
    (trace : NodeTrace unconstrained path value before answer after) :
    EndpointClosed path value before answer := by
  induction trace using NodeTrace.rec
      (motive_2 := fun _ _ _ _ _ _ _ => True)
      (motive_3 := fun _ _ _ _ _ _ _ => True) with
  | empty => intro _ _ _ _; rfl
  | reference => intro _ impossible; cases impossible
  | union => intro _ impossible; cases impossible
  | finite fast =>
      intro _ _ _ _
      have closed := (Bool.and_eq_true_iff.mp fast).2
      simpa only [Value.free, List.isEmpty_iff] using closed
  | @endpoint depth entry edges free state slow =>
      intro _ cleared _ _
      cases free with
      | nil => rfl
      | cons => cases cleared
  | branches slow trace ih => intro impossible; cases impossible
  | constrained blocked =>
      intro atEndpoint cleared _ _
      subst atEndpoint
      simpa only [Bool.not_eq_false', List.isEmpty_iff] using cleared
  | closed plain closed =>
      intro _ _ _ _
      exact List.isEmpty_iff.mp closed
  | @unfold entry body depth ordinary before next middle path answer final plain opened actual trace ih =>
      intro atEndpoint cleared ready available
      have openFree : (Value.mu entry body depth ordinary).free ≠ [] := by
        intro empty
        simp only [empty, List.isEmpty_nil] at opened
        cases opened
      have retained := SourceSecondaryGateEndpointClosed.unfold_retains_free entry body depth ordinary before next middle ready available openFree actual
      have nextClosed := ih atEndpoint cleared retained.1 retained.2.1
      apply Classical.byContradiction
      intro notClosed
      obtain ⟨name, member⟩ := List.exists_mem_of_ne_nil _ notClosed
      have survives := retained.2.2 name member
      simp only [nextClosed, List.not_mem_nil] at survives
  | missing => trivial
  | present => trivial
  | nil => trivial
  | stop => trivial
  | next => trivial

/-- A completed false secondary node trace at the root path implies original closedness. -/
theorem endpoint_closed [DecidableEq (EdgeKey Symbol Guard)]
    (unconstrained : Value Symbol Guard → Bool)
    {value : Value Symbol Guard} {before after : State Symbol Guard}
    (trace : NodeTrace unconstrained [] value before false after)
    (ready : Ready before) (available : Available before value) : value.free = [] :=
  node_closed unconstrained trace rfl rfl ready available

/-- The actual completed secondary endpoint worker derives the same original closedness. -/
theorem of_done [DecidableEq (EdgeKey Symbol Guard)]
    (unconstrained : Value Symbol Guard → Bool) (fuel : Nat)
    (value : Value Symbol Guard) (before after : State Symbol Guard)
    (done : SourceCurrentSecondaryTrace.nodeMeets unconstrained fuel [] value before =
      .done (some false) after)
    (ready : Ready before) (available : Available before value) : value.free = [] :=
  endpoint_closed unconstrained
    (SourceCurrentSecondaryTrace.node_trace_of_done unconstrained fuel [] value before false after done)
    ready available

end MicroCFTA.SourceCurrentSecondaryProjectionEndpoint
