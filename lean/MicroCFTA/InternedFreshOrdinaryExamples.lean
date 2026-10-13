import MicroCFTA.InternedFreshOrdinaryConstruction
import MicroCFTA.InternedClosedPendingBoundary
import MicroCFTA.InternedPairedPendingBoundary

/-!
# Checked examples for the fresh-ordinary repair

Both pending counterexamples complete under the repaired policy.
These finite computations do not prove general completion or semantic equivalence.
The baseline executor and all its counterexamples remain unchanged.
-/
namespace MicroCFTA.InternedFreshOrdinaryExamples
open InternedConstructorTemplates InternedNestedConstruction
open InternedFreshOrdinaryConstruction (ordinaryLevel)

/-- Run the original open counterexample under the repaired policy. -/
def openResult := InternedFreshOrdinaryConstruction.build
  (.binder false InternedPairedPendingBoundary.ancestor) InternedPairedPendingBoundary.environment empty

/-- Run the original closed counterexample under the repaired policy. -/
def closedResult := InternedFreshOrdinaryConstruction.build InternedClosedPendingBoundary.expression [] empty

/-- The open case completes and retains its original ordinary capture. -/
theorem open_complete :
    (match openResult with
      | .done value _ => some (value.depth, value.free.contains (.uninterned 1))
      | .pending .. => none) = some (1, true) := by
  set_option maxRecDepth 30000 in
  set_option cbv.maxSteps 200000000 in cbv

/-- Some repaired record uses a different ordinary name from its body's depth. -/
def readbackDiffers (state : State Nat Unit) : Bool :=
  (List.range state.nodes.next).any fun identity =>
    match state.nodes.issued identity with
    | none => false
    | some key =>
        match state.nodeRecords key with
        | some (.mu _ body depth _) => ordinaryLevel depth != body.depth
        | _ => false

/-- Inspect completion, closed free names, and the required matcher choice in one execution. -/
def closedObservation : Option (Nat × Bool × Bool) :=
  match closedResult with
  | .done value state => some (value.depth, value.free.isEmpty, readbackDiffers state)
  | .pending .. => none

set_option maxHeartbeats 2000000 in
/-- The closed case completes, and a stored body's depth cannot recover every chosen ordinary name. -/
theorem closed_complete : closedObservation = some (1, true, true) := by
  set_option maxRecDepth 30000 in
  set_option cbv.maxSteps 400000000 in cbv

end MicroCFTA.InternedFreshOrdinaryExamples
