import MicroCFTA.SourceFlatPruningRecursiveOutputResources
import MicroCFTA.SourceFlatPruningRenderingAssignment

/-!
# Assignments at actual recursive outputs

Each emitted output supplies its own native heap and safe ordered cache.
Actual rendering, discharge and residual checks construct its assignment.
The result does not assert acceptance at an earlier enumeration state.
-/
namespace MicroCFTA.SourceFlatPruningRecursive
open Language
open SourcePruningEnumerationIncomingReservation (Seed)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Core" => EnumerationFlatState.State Symbol Constraint
variable {Typing : Type} {width : Nat}
variable [DecidableEq (InternedConstructorTemplates.EdgeKey Symbol Constraint)]

/-- Checked rendering of a discharged actual output constructs an assignment at that output's heap. -/
theorem output_render_assignment
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula)
    (original : Caller width) (seed : Seed) (output : Output width Typing)
    (resources : OutputResources formulas solver original seed output)
    (holds : Constraint → Term Symbol → Bool) (ambient : InternedGuardedLanguage.Env Symbol)
    (meaning : Constraint → Term Symbol → Prop) (marker : Symbol) (fuel uv : Nat)
    (after : Core) (term : Term Symbol) (pending : List (Constraint × Term Symbol))
    (discharged : SourceFlatPruningRendering.Discharged output.cache.core)
    (observed : Except.ok ((term, pending), after) ∈
      ExceptT.run (SourceFlatPruningRendering.render
        output.caller.checked.native.machine.heap marker fuel uv output.cache.core))
    (checked : ∀ obligation ∈ pending, meaning obligation.1 obligation.2) :
    ∃ assignment : Nat → Term Symbol,
      EnumerationFlatState.Satisfies
        (SourcePruningEnumerationNativeLanguage.handles holds ambient
          output.caller.checked.native.machine.heap) meaning assignment output.cache.core ∧
      term = assignment uv ∧ after = output.cache.core ∧
      EnumerationFlatState.Satisfies
        (SourcePruningEnumerationNativeLanguage.handles holds ambient
          output.caller.checked.native.machine.heap) meaning assignment after := by
  obtain ⟨_next, _final, _metadata, earlier, _post, _queries, packet, related,
    _shape, _correct, _fits, _known⟩ := resources
  obtain ⟨level, frontier, ordered⟩ := packet.ordered
  exact SourceFlatPruningRendering.render_assignment
    output.caller.checked.native.machine.heap holds ambient meaning marker fuel uv
    output.cache.core after earlier.core term pending related.core packet.safe
    level frontier ordered discharged observed checked

end MicroCFTA.SourceFlatPruningRecursive
