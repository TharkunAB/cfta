import MicroCFTA.SourcePruningEnumerationOutcomeResources
import MicroCFTA.SourcePruningEnumerationRendering

/-!
# Assignments from rendering an actual recursive output

The output resources supply that output's own safe ordered cache.
Actual rendering and checked residuals construct its complete assignment.
This result does not infer acceptance at an earlier input.
-/
namespace MicroCFTA.SourcePruningEnumerationRecursive
open Language EnumerationState EnumerationCorrectness
open SourcePruningEnumerationIncomingReservation (Seed)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Core" => EnumerationState.State Symbol Constraint
variable {Typing : Type} {width : Nat}
variable [DecidableEq (InternedConstructorTemplates.EdgeKey Symbol Constraint)]

/-- Actual output resources and checked rendering construct an assignment at that output's native heap. -/
theorem OutputResources.render_assignment
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula)
    (original : Caller width) (seed : Seed) (output : Output width Typing)
    (resources : OutputResources formulas solver original seed output)
    (ambient : InternedGuardedLanguage.Env Symbol) (marker : Symbol) (fuel uv : Nat)
    (after : Core) (term : Term Symbol) (pending : List (Constraint × Term Symbol))
    (discharged : SourcePruningEnumerationRendering.Discharged output.cache.core)
    (observed : Success
      (SourcePruningEnumerationRendering.render output.caller.checked.native.machine.heap marker fuel uv)
      output.cache.core (term, pending) after)
    (checked : ∀ obligation ∈ pending,
      SourceEqualityPCSGuard.holds formulas solver obligation.1 obligation.2 = true) :
    ∃ assignment : Nat → Term Symbol,
      Satisfies
        (SourcePruningEnumerationNativeLanguage.handles (SourceEqualityPCSGuard.holds formulas solver)
          ambient output.caller.checked.native.machine.heap)
        (fun guard value => SourceEqualityPCSGuard.holds formulas solver guard value = true)
        assignment output.cache.core ∧
      term = assignment uv ∧ EnumerationCompressionFrame.Frame output.cache.core after ∧
      Satisfies
        (SourcePruningEnumerationNativeLanguage.handles (SourceEqualityPCSGuard.holds formulas solver)
          ambient output.caller.checked.native.machine.heap)
        (fun guard value => SourceEqualityPCSGuard.holds formulas solver guard value = true)
        assignment after := by
  obtain ⟨_next, _final, _metadata, _post, _queries, packet, _shape, _fits, _known⟩ := resources
  obtain ⟨level, frontier, ordered⟩ := packet.ordered
  exact SourcePruningEnumerationRendering.render_assignment
    output.caller.checked.native.machine.heap (SourceEqualityPCSGuard.holds formulas solver) ambient
    (fun guard value => SourceEqualityPCSGuard.holds formulas solver guard value = true)
    marker fuel uv output.cache.core after term pending packet.safe level frontier ordered
    discharged observed checked

end MicroCFTA.SourcePruningEnumerationRecursive
