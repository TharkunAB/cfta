import MicroCFTA.SourceEqualityPartialWorker

/-!
# The first required child of an ordinary one-row body

A one-level probe identifies the first live recursive request.
Any successful body with another callback must complete that request.
Native stages, physical combination, and the first child's warm state
are shared. No completed parent graph or future child result is supplied.
-/
namespace MicroCFTA.SourceEqualityPartialFirstDemand
open InternedConstructorTemplates SourceObservations SourceSymbolicIndex
open SourceEqualityClassFoldGraph SourceEqualityNativeScoped
local notation "Symbol" => Label FullSyntax.Formula
local notation "Guard" => Constraint FullSyntax.Formula
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] {width : Nat}
local notation "source" => SourceMemoGate.unconstrained
local notation "top" => SourceEqualityConstraintConstructors.top (Formula := FullSyntax.Formula)

/-- A first incomplete child remains inside its actual edge and row observations. -/
def waiting (inherited : SourceEqualityPrecheck.Constraint) (value : Value Symbol Guard)
    (state : NativeState width Symbol Guard) : SourceEqualityPartialWorker.Result width :=
  .incomplete (.rows (.incomplete (.children (.exhausted inherited value state))))

/-- Every successful one-row body must first complete the actual child identified by its one-level probe. -/
theorem first_required
    (call : SourceEqualityPrecheck.Constraint → Value Symbol Guard → NativeState width Symbol Guard → SourceEqualityPartialWorker.Result width)
    (g e p h c n : Nat) (inherited childInherited : SourceEqualityPrecheck.Constraint)
    (entry : Cache.Interned InternedBinderProtocol.NodeKey) (edge : EdgeValue Symbol Guard)
    (depth : Nat) (free : List InternedBinderProtocol.Reference)
    (child : Value Symbol Guard) (before reached : NativeState width Symbol Guard)
    (observed : SourceEqualityPartialWorker.run g e p h c n 1 inherited (.node entry [edge] depth free) before =
      waiting childInherited child reached)
    (result : Value Symbol Guard) (after : NativeState width Symbol Guard)
    (finished : SourceEqualityPartialWorker.step call g e p h c n inherited (.node entry [edge] depth free) before = .done (.ok result) after) :
    ∃ value middle, call childInherited child reached = .done (.ok value) middle := by
  simp only [SourceEqualityPartialWorker.run, SourceEqualityPartialWorker.step,
    SourceEqualityInheritedRows.walk] at observed finished
  simp only [SourceEqualityInheritedEdgeWorker.run] at observed finished
  cases native : SourceEqualityGuardedEdgeWorker.run source top SourceEqualityPCSNativeEdge.conjoin
      SourceMemoGate.plain top g e p h c n edge inherited before with
  | children observation => simp [native, waiting] at observed
  | done answer middle =>
    cases answer with
    | error message => simp [native, waiting] at observed
    | ok narrowed =>
      simp only [native, SourceEqualityInheritedEdgeWorker.descendants] at observed finished
      cases ownRead : SourceEqualityPhysicalPayload.own narrowed.entry.key.constraint with
      | error message => simp [ownRead, waiting] at observed
      | ok own =>
        simp only [ownRead] at observed finished
        cases combined : SourceEqualityInheritedPayload.combine inherited own with
        | error message => simp [combined, waiting] at observed
        | ok payload =>
          simp only [combined] at observed finished
          cases payload with
          | none => simp [SourceEqualityInheritedChildren.run, waiting] at observed
          | some records =>
            cases values : narrowed.children with
            | nil => simp [values, SourceEqualityInheritedChildren.run, SourceEqualityInheritedChildren.walk,
                waiting] at observed
            | cons head tail =>
              simp [values, SourceEqualityInheritedChildren.run, SourceEqualityInheritedChildren.walk,
                SourceEqualityInheritedChildren.Result.bind, waiting] at observed
              rcases observed with ⟨rfl, rfl, rfl⟩
              cases actual : call (SourceEqualityDescend.descend (some records) 0) head middle with
              | incomplete observation =>
                  simp [values, SourceEqualityInheritedChildren.run, SourceEqualityInheritedChildren.walk,
                    actual, SourceEqualityInheritedChildren.Result.bind] at finished
              | done answer afterChild =>
                  cases answer with
                  | error message =>
                      simp [values, SourceEqualityInheritedChildren.run, SourceEqualityInheritedChildren.walk,
                        actual, SourceEqualityInheritedChildren.Result.bind] at finished
                  | ok value => exact ⟨value, afterChild, rfl⟩
end MicroCFTA.SourceEqualityPartialFirstDemand
