import MicroCFTA.SourceEndpointGate
import MicroCFTA.EndpointGateCompletion

/-!
# Finite current-policy gate checks on source construction

Actual repaired records supply the unfolding rank and the descendant read.
Original closed construction supplies the required cache invariants. This
is a pure decision theorem. The global source predicate memo is separate.
-/
namespace MicroCFTA.SourceEndpointGateCompletion
open Cache InternedConstructorTemplates
open InternedNestedConstruction (Syntax Outcome)
open InternedFreshOrdinaryGateRank (Node fromCompleted)

/-- The current total gate reads actual metadata, stored children, and descendants. -/
def total [DecidableEq (EdgeKey Symbol Guard)] (unconstrained : Value Symbol Guard → Bool)
    (path : EqualityNormalize.Path) (node : Node Symbol Guard) : Bool :=
  EndpointGateCompletion.total (SourceEndpointGate.read unconstrained)
    (SourceEndpointGate.ranking unconstrained) path node

/-- Each certified source record has a finite completed current-policy check. -/
theorem completes [DecidableEq (EdgeKey Symbol Guard)]
    (unconstrained : Value Symbol Guard → Bool) (path : EqualityNormalize.Path)
    (node : Node Symbol Guard) :
    ∃ fuel, EndpointRecursionGate.nodeMeets (SourceEndpointGate.read unconstrained) fuel path node =
      some (total unconstrained path node) :=
  EndpointGateCompletion.completes (SourceEndpointGate.read unconstrained)
    (SourceEndpointGate.ranking unconstrained) path node

/-- Every larger fuel amount returns the same actual-record gate decision. -/
theorem eventually_exact [DecidableEq (EdgeKey Symbol Guard)]
    (unconstrained : Value Symbol Guard → Bool) (path : EqualityNormalize.Path)
    (node : Node Symbol Guard) :
    ∃ bound, ∀ extra,
      EndpointRecursionGate.nodeMeets (SourceEndpointGate.read unconstrained) (bound + extra) path node =
        some (total unconstrained path node) :=
  EndpointGateCompletion.eventually_exact (SourceEndpointGate.read unconstrained)
    (SourceEndpointGate.ranking unconstrained) path node

/-- Any completed check on a certified source record agrees with its total decision. -/
theorem completed_agrees [DecidableEq (EdgeKey Symbol Guard)]
    (unconstrained : Value Symbol Guard → Bool) (fuel : Nat) (path : EqualityNormalize.Path)
    (node : Node Symbol Guard) (result : Bool)
    (completed : EndpointRecursionGate.nodeMeets (SourceEndpointGate.read unconstrained) fuel path node = some result) :
    total unconstrained path node = result :=
  EndpointGateCompletion.completed_agrees (SourceEndpointGate.read unconstrained)
    (SourceEndpointGate.ranking unconstrained) fuel path node result completed

/-- Original source construction supplies finite current-policy checks at every path. -/
theorem source_eventually_exact [DecidableEq (EdgeKey Symbol Guard)]
    (expression : Syntax Symbol Guard) (unconstrained : Value Symbol Guard → Bool) :
    ∃ value state, ∃ done : InternedFreshOrdinaryConstruction.build expression [] empty = .done value state,
      ∀ path, ∃ bound, ∀ extra,
        EndpointRecursionGate.nodeMeets (SourceEndpointGate.read unconstrained) (bound + extra) path
          (fromCompleted expression value state done) =
        some (total unconstrained path (fromCompleted expression value state done)) := by
  obtain ⟨value, state, done⟩ := InternedFreshOrdinaryClosedCompletion.closed_complete expression
  exact ⟨value, state, done, fun path => eventually_exact unconstrained path _⟩

end MicroCFTA.SourceEndpointGateCompletion
