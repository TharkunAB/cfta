import MicroCFTA.SourceSynthesisProgramRoleReadback
import MicroCFTA.SourceSynthesisPartialProgramDecoder

/-!
# One Program across completions of the actual finished readback

The current packet and Program slots determine the actual readback projection.
Every completion retains that same Program. The full Core frame remains.
The complete driver must still derive its Program-slot history.
-/
namespace MicroCFTA.SourceSynthesisProgramRoleCompletions
open EnumerationState EnumerationCorrectness
open SourceSynthesisProgramEnumerationRoles (ProgramSlots)
open SourceSynthesisProgramTermSize (Projection)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Core" => EnumerationState.State Symbol Constraint
local notation "literal" => SourceSynthesisLabelProgramBuildRoles.literal
variable {Typing : Type} {width : Nat}
variable [DecidableEq (InternedConstructorTemplates.EdgeKey Symbol Constraint)]
variable {formulas : SourceGuards.Formulas FullSyntax.Formula}
    {solver : SourceGuards.Entailment FullSyntax.Formula}
    {inventory : SourceCurrentAllocatedNativeInventoryState.Inventory}
    {caller : SourceCurrentAllocatedPartialState.State width}
    {memos : EndpointMemoGateTrace.Memos}
    {metadata : SourcePruningRecordTypes.Metadata Typing}
    {before : EnumerationExpandableIndex.Cached Symbol Constraint}
    {valid : Constraint → Prop}

/-- The same actual readback and every completion project to one Program. -/
theorem root_partial_completions_program
    (packet : SourcePruningEnumerationRecursive.Packet formulas solver
      inventory caller memos metadata before)
    (finished : EnumerationPureSelection.next (fun _ => none) before = .done)
    (marked : Nat → Prop)
    (roles : ProgramSlots valid literal caller.checked.native.machine.heap before.core marked)
    (root : marked 0) (fuel : Nat) (actualPartial : SourcePruningTemplates.PartialTerm) (after : Core)
    (actual : Success (SourcePruningEnumerationPartialOutput.rootPartial
      caller.checked.native.machine.heap fuel) before.core actualPartial after) :
    ∃ program, Projection literal Prod.fst (SourcePruningPositions.openProgram true actualPartial) program ∧
      EnumerationCompressionFrame.Frame before.core after ∧
      ∀ (assignment : Nat → Language.Term Symbol) (full : Language.Term Symbol),
        SourcePruningPartialMatch.Completes assignment actualPartial full →
        Projection literal Prod.fst full program := by
  classical
  obtain ⟨program, projected, frame⟩ := SourceSynthesisProgramRoleReadback.root_partial_program
    packet finished marked roles root fuel actualPartial after actual
  refine ⟨program, projected, frame, ?_⟩
  intro assignment full completed
  exact (SourceSynthesisPartialProgramDecoder.completion_decoder_of_projection
    actualPartial program projected assignment full completed).1

end MicroCFTA.SourceSynthesisProgramRoleCompletions
