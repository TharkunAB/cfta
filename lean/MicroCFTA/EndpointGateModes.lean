import MicroCFTA.EndpointStatefulGate
import MicroCFTA.EndpointRecursionGate

/-!
# Primary and secondary endpoint modes from main a22b2ad4

The primary class partition enables descendant checks. The secondary scan
disables only that endpoint read. Its decisions and constructor effects are
exactly the older free-reference-only gate. This module does not model the
new class partition schedule or the emptiness query that follows the scan.
-/
namespace MicroCFTA.EndpointGateModes
open EqualityNormalize InternedConstructorTemplates InternedNestedConstruction

/-- The source mode controls only the extra endpoint descendant read. -/
def withEndpoint (belowEnd : Bool) (read : EndpointRecursionGate.Read Node) : EndpointRecursionGate.Read Node :=
  {read with reaches := fun node => belowEnd && read.reaches node}

/-- The enabled primary mode is exactly the stronger gate from 24a710a3. -/
theorem enabled (read : EndpointRecursionGate.Read Node) (fuel : Nat) (path : Path) (node : Node) :
    EndpointRecursionGate.nodeMeets (withEndpoint true read) fuel path node =
      EndpointRecursionGate.nodeMeets read fuel path node := rfl

/-- Disabling descendants restores one exact previous-policy dispatch. -/
theorem dispatch_disabled (read : EndpointRecursionGate.Read Node) (recur : Path → Node → Option Bool)
    (path : Path) (node : Node) :
    EndpointRecursionGate.dispatch (withEndpoint false read) recur path node =
      ConstrainedRecursionGate.dispatch read.previous recur path node := by
  simp only [EndpointRecursionGate.dispatch, ConstrainedRecursionGate.dispatch, withEndpoint,
    Bool.false_and, Bool.or_false]
  rfl

/-- The disabled secondary mode is exactly the older gate at every fuel amount. -/
theorem disabled (read : EndpointRecursionGate.Read Node) (fuel : Nat) (path : Path) (node : Node) :
    EndpointRecursionGate.nodeMeets (withEndpoint false read) fuel path node =
      ConstrainedRecursionGate.nodeMeets read.previous fuel path node := by
  induction fuel generalizing path node with
  | zero => rfl
  | succ fuel ih =>
      simp only [EndpointRecursionGate.nodeMeets, ConstrainedRecursionGate.nodeMeets]
      rw [dispatch_disabled]
      have same : EndpointRecursionGate.nodeMeets (withEndpoint false read) fuel =
          ConstrainedRecursionGate.nodeMeets read.previous fuel := funext fun path => funext fun node => ih path node
      rw [same]

/-- The enabled stateful mode preserves every completed or pending result and exact constructor heap. -/
theorem stateful_enabled [DecidableEq (EdgeKey Symbol Guard)]
    (unconstrained reaches : Value Symbol Guard → Bool) (fuel : Nat) (path : Path)
    (value : Value Symbol Guard) (heap : State Symbol Guard) :
    EndpointStatefulGate.nodeMeets unconstrained (fun value => true && reaches value) fuel path value heap =
      EndpointStatefulGate.nodeMeets unconstrained reaches fuel path value heap := rfl

/-- The secondary stateful dispatch retains the exact previous constructor computation. -/
theorem stateful_dispatch_disabled [DecidableEq (EdgeKey Symbol Guard)]
    (unconstrained reaches : Value Symbol Guard → Bool)
    (recur : Path → Value Symbol Guard → State Symbol Guard → Outcome Symbol Guard (Option Bool))
    (path : Path) (value : Value Symbol Guard) (heap : State Symbol Guard) :
    EndpointStatefulGate.dispatch unconstrained (fun value => false && reaches value) recur path value heap =
      InternedFreshOrdinaryStatefulGate.dispatch unconstrained recur path value heap := by
  simp only [EndpointStatefulGate.dispatch, InternedFreshOrdinaryStatefulGate.dispatch,
    Bool.false_and, Bool.or_false]
  rfl

/-- The disabled stateful mode equals the older worker, including errors, unfinished fuel, and returned heaps. -/
theorem stateful_disabled [DecidableEq (EdgeKey Symbol Guard)]
    (unconstrained reaches : Value Symbol Guard → Bool) (fuel : Nat) (path : Path)
    (value : Value Symbol Guard) (heap : State Symbol Guard) :
    EndpointStatefulGate.nodeMeets unconstrained (fun value => false && reaches value) fuel path value heap =
      InternedFreshOrdinaryStatefulGate.nodeMeets unconstrained fuel path value heap := by
  induction fuel generalizing path value heap with
  | zero => rfl
  | succ fuel ih =>
      simp only [EndpointStatefulGate.nodeMeets, InternedFreshOrdinaryStatefulGate.nodeMeets]
      rw [stateful_dispatch_disabled]
      have same : EndpointStatefulGate.nodeMeets unconstrained (fun value => false && reaches value) fuel =
          InternedFreshOrdinaryStatefulGate.nodeMeets unconstrained fuel :=
        funext fun path => funext fun value => funext fun heap => ih path value heap
      rw [same]

end MicroCFTA.EndpointGateModes
