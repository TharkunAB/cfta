import MicroCFTA.EndpointGateModes
import MicroCFTA.EndpointMemoGateClasses
import MicroCFTA.InternedFreshOrdinaryStatefulGateClasses

/-!
# Exact caller modes for forest paths and ordered classes

The primary mode enables endpoint descendant reads. The secondary mode
disables that read and uses the exact free-reference worker. These equations
retain every outcome and returned constructor heap at every fuel amount.
They make no runtime memo publication claim.
-/
namespace MicroCFTA.EndpointGateClassModes
open InternedConstructorTemplates InternedNestedConstruction EqualityNormalize

/-- The enabled forest-path worker is exactly the current primary worker. -/
theorem meets_enabled [DecidableEq (EdgeKey Symbol Guard)]
    (unconstrained reaches : Value Symbol Guard → Bool) (fuel : Nat)
    (values : List (Value Symbol Guard)) (path : Path) (heap : State Symbol Guard) :
    EndpointStatefulGate.meets unconstrained (fun value => true && reaches value) fuel values path heap =
      EndpointStatefulGate.meets unconstrained reaches fuel values path heap := rfl

/-- The enabled ordered class worker is exactly the current primary worker. -/
theorem class_enabled [DecidableEq (EdgeKey Symbol Guard)]
    (unconstrained reaches : Value Symbol Guard → Bool) (fuel : Nat)
    (values : List (Value Symbol Guard)) (paths : Class) (heap : State Symbol Guard) :
    EndpointStatefulGate.classMeets unconstrained (fun value => true && reaches value) fuel values paths heap =
      EndpointStatefulGate.classMeets unconstrained reaches fuel values paths heap := rfl

/-- The disabled forest-path worker retains every exact previous-policy outcome and heap. -/
theorem meets_disabled [DecidableEq (EdgeKey Symbol Guard)]
    (unconstrained reaches : Value Symbol Guard → Bool) (fuel : Nat)
    (values : List (Value Symbol Guard)) (path : Path) (heap : State Symbol Guard) :
    EndpointStatefulGate.meets unconstrained (fun value => false && reaches value) fuel values path heap =
      InternedFreshOrdinaryStatefulGate.meets unconstrained fuel values path heap := by
  have same : EndpointStatefulGate.nodeMeets unconstrained (fun value => false && reaches value) fuel =
      InternedFreshOrdinaryStatefulGate.nodeMeets unconstrained fuel :=
    funext fun path => funext fun value => funext fun current =>
      EndpointGateModes.stateful_disabled unconstrained reaches fuel path value current
  cases path with
  | nil => rfl
  | cons index rest =>
      simp only [EndpointStatefulGate.meets, InternedFreshOrdinaryStatefulGate.meets, same]

/-- The disabled class worker retains exact source order, short circuits, and returned heaps. -/
theorem class_disabled [DecidableEq (EdgeKey Symbol Guard)]
    (unconstrained reaches : Value Symbol Guard → Bool) (fuel : Nat)
    (values : List (Value Symbol Guard)) (paths : Class) (heap : State Symbol Guard) :
    EndpointStatefulGate.classMeets unconstrained (fun value => false && reaches value) fuel values paths heap =
      InternedFreshOrdinaryStatefulGate.classMeets unconstrained fuel values paths heap := by
  simp only [EndpointStatefulGate.classMeets, InternedFreshOrdinaryStatefulGate.classMeets, meets_disabled]

end MicroCFTA.EndpointGateClassModes
