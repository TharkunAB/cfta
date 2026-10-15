import MicroCFTA.SourceEqualityGuardedEdgeGraph

/-!
# Bounded source guarded-edge worker

Physical accessor errors and complete child errors retain their exact native
scope. Incomplete child work remains its actual stage observation. Successful
child work invokes literal makeEdge with the original full constraint.
-/
namespace MicroCFTA.SourceEqualityGuardedEdgeWorker
open InternedConstructorTemplates SourceObservations SourceSymbolicIndex
open SourceEqualityClassFoldGraph SourceEqualityNativeScoped
variable {Formula : Type}
local notation "Symbol" => Label Formula
local notation "Guard" => Constraint Formula

/-- Edge results retain checked errors or the actual incomplete child stage. -/
inductive Result (width : Nat) (Formula : Type) : Type 1 where
  | done (answer : Except String (EdgeValue (Label Formula) (Constraint Formula))) (state : NativeState width (Label Formula) (Constraint Formula))
  | children (observation : SourceEqualityOnePassWorker.Result width (Label Formula) (Constraint Formula))

/-- The source reconstruction resumes only after a complete successful child result. -/
def finish [DecidableEq (EdgeKey Symbol Guard)] (edge : EdgeValue Symbol Guard)
    (observation : SourceEqualityOnePassWorker.Result width Symbol Guard) : Result width Formula :=
  match observation with
  | .done (.ok values) middle =>
      let built := run (makeEdge edge.entry.key.symbol edge.entry.key.constraint values) middle.machine.heap
      .done (.ok built.1) (advanceHeap middle built.2)
  | .done (.error message) middle => .done (.error message) middle
  | other => .children other

/-- Execute the actual own accessor and source equality pass before original-guard reconstruction. -/
noncomputable def run [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (unconstrained : Value Symbol Guard → Bool) (emptyGuard : Guard) (conjoin : Guard → Guard → Guard) (clear : Guard → Bool) (top : Guard)
    (g e p h c n : Nat) (edge : EdgeValue Symbol Guard) (inherited : SourceEqualityPrecheck.Constraint) (before : NativeState width Symbol Guard) : Result width Formula :=
  match SourceEqualityPhysicalPayload.own edge.entry.key.constraint with
  | .error message => .done (.error message) before
  | .ok payload => finish edge (SourceEqualityOnePassWorker.run unconstrained emptyGuard conjoin clear top g e p h c n payload inherited edge.children before)

/-- Use the actual bounded parent-array precheck in the same source guarded-edge continuation. -/
noncomputable def runArray [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (unconstrained : Value Symbol Guard → Bool) (emptyGuard : Guard) (conjoin : Guard → Guard → Guard) (clear : Guard → Bool) (top : Guard)
    (work g e p h c n : Nat) (edge : EdgeValue Symbol Guard) (inherited : SourceEqualityPrecheck.Constraint) (before : NativeState width Symbol Guard) : Result width Formula :=
  match SourceEqualityPhysicalPayload.own edge.entry.key.constraint with
  | .error message => .done (.error message) before
  | .ok payload => finish edge (SourceEqualityOnePassWorker.runArray unconstrained emptyGuard conjoin clear top work g e p h c n payload inherited edge.children before)

/-- Six stable stage bounds retain the exact rebuilt edge and complete native state. -/
def StableRun (evaluation : Nat → Nat → Nat → Nat → Nat → Nat → Result width Formula)
    (answer : Except String (EdgeValue Symbol Guard)) (after : NativeState width Symbol Guard) : Prop :=
  ∃ g e p h c n, ∀ gg ee pp hh cc nn, g ≤ gg → e ≤ ee → p ≤ pp → h ≤ hh → c ≤ cc → n ≤ nn →
    evaluation gg ee pp hh cc nn = .done answer after

end MicroCFTA.SourceEqualityGuardedEdgeWorker
