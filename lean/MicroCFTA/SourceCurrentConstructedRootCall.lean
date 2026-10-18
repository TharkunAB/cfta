import MicroCFTA.SourceCurrentConstructedOuterInitial
import MicroCFTA.SourceCurrentAllocatedPartialInitialization

/-!
# Root reduction from actual closed construction

Actual construction and covered field allocation derive the initial caller
context. The actual empty inherited value imposes no equality constraint.
A completed bounded root call therefore preserves the complete input language.
Numeric capacity, guard coverage and successful execution remain premises.
The logical initial state does not assert a reset of Haskell global caches.
-/
namespace MicroCFTA.SourceCurrentConstructedRootCall
open Cache Language InternedConstructorTemplates InternedProbeProvenance
open InternedNestedConstruction (Syntax)
open InternedFreshOrdinaryConstruction (build)
open SourceCurrentConstrainedCapGeneratedQueryResources (Fits)
open SourceCurrentAllocatedNativeResourceForecast (Profile Room)
open SourceCurrentAllocatedPartialWorker (nodeCall)

local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Key" => SourceEqualityPartialConstraintKey.Key
local notation "Node" => Value Symbol Guard
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Carrier" => SourceEqualityAnnotationHeap.Heap
local notation "Seed" => List Guard × Profile

open SourceCurrentAllocatedPartialInitialization

variable [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Symbol] [DecidableEq Node]

/-- A completed root call with actual empty inheritance preserves the constructed language. -/
theorem root_call (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula)
    {initial final : Cache.State Key} {originals : List Guard}
    (history : SourceEqualityOriginalAllocationHistory.History initial final originals)
    (valid : Cache.Valid initial) (expression : Syntax Symbol Guard)
    (covered : ∀ original ∈ SourceEqualityConstraintOrigins.guards expression, original ∈ originals)
    (root : Node) (heap : State Symbol Guard)
    (constructed : build expression [] empty = .done root heap)
    (seed : Seed) (fits : Fits seed.2 (caller (bits+2) final heap).checked)
    (carrier : Carrier (fun guard => guard ∈ seed.1) heap)
    (fuel g s r e p h m c n budget : Nat)
    (room : Room bits (SourceCurrentOuterInitialActual.Schedule.node fuel budget seed).2)
    (result : Node) (after : Caller (bits+2))
    (called : nodeCall fuel g s r e p h m c n budget
      ⟨emptyValue final,root⟩ (caller (bits+2) final heap) = .done result after) :
    Available after.checked.native.machine.heap result ∧
      ∀ ambient, InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver) ambient result =
        InternedGuardedSyntax.evaluate (SourceEqualityPCSGuard.holds formulas solver) [] expression := by
  obtain ⟨context,identity,emptySame,inherited,available,_closed,_original⟩ :=
    SourceCurrentAllocatedPartialInitialization.constructed (bits+2) history valid
      expression covered root heap constructed formulas solver
  have inheritedReady : SourceEqualityConstraintAllocation.Ready
      (caller (bits+2) final heap).checked.operations.constraints (emptyValue final) := by
    rw [emptySame]
    exact inherited
  obtain ⟨resultAvailable,law⟩ := SourceCurrentConstructedOuterInitial.node_call
    formulas solver expression root ⟨heap,Cache.emptyState⟩ (operations final) constructed
    (caller (bits+2) final heap) after (inventory expression root heap constructed) globals
    rfl rfl context seed fits carrier ⟨emptyValue final,root⟩ inheritedReady available
    fuel g s r e p h m c n budget room result called
  refine ⟨resultAvailable,?_⟩
  intro ambient
  have exactInput : InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver) ambient result =
      InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver) ambient root := by
    funext term
    apply propext
    apply (law ambient term).2
    change SourceEqualityPrecheck.Sat term (emptyValue final).payload
    rw [emptySame]
    simp [SourceEqualityConstraintAllocation.Value.payload,SourceEqualityPrecheck.Sat,EqualityNormalize.Satisfies]
  exact exactInput.trans (InternedGuardedExecution.closed_language expression root heap constructed _ ambient)

end MicroCFTA.SourceCurrentConstructedRootCall
