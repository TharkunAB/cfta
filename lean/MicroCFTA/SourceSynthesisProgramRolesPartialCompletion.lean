import MicroCFTA.SourceSynthesisProgramRoleCompletions

/-!
# One actual partial root with its complete Program receipt

The existing producer runs once at the same current packet.
Its complete readback and conditional model observers retain their original witnesses.
One Program projection applies to the actual partial root and every completion.
This result supplies no satisfying Type assignment or completion witness.
-/
namespace MicroCFTA.SourceSynthesisProgramRolesPartialCompletion
open EnumerationState EnumerationCorrectness
open SourceSynthesisProgramEnumerationRoles (ProgramSlots)
open SourceSynthesisProgramTermSize (Projection)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Core" => EnumerationState.State Symbol Constraint
local notation "PartialTerm" => SourcePruningTemplates.PartialTerm
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

/-- One actual root producer retains its full receipt and the same Program for all completions. -/
theorem complete_program_root
    (packet : SourcePruningEnumerationRecursive.Packet formulas solver
      inventory caller memos metadata before)
    (finished : EnumerationPureSelection.next (fun _ => none) before = .done)
    (marked : Nat → Prop)
    (roles : ProgramSlots valid literal caller.checked.native.machine.heap before.core marked)
    (root : marked 0) :
    ∃ (level : Nat → Nat) (frontier : Nat),
      EnumerationOrder.Stratified before.core level frontier ∧
      ∃ (bound : Nat) (actualPartial : PartialTerm) (after : Core),
        (∀ extra,
          Success (SourcePruningEnumerationPartialOutput.rootPartial
            caller.checked.native.machine.heap (bound + extra)) before.core actualPartial after ∧
          ExceptT.run (SourcePruningEnumerationPartialOutput.rootPartial
            caller.checked.native.machine.heap (bound + extra) before.core) = [.ok (actualPartial, after)]) ∧
        EnumerationDriver.RenderStable before.core after ∧
        EnumerationCompressionFrame.Frame before.core after ∧
        EnumerationOrder.Stratified after level frontier ∧
        (∀ (language : NodeLanguage Symbol) (meaning : Constraint → Language.Term Symbol → Prop)
          (assignment : Nat → Language.Term Symbol),
          Satisfies language meaning assignment before.core →
            Satisfies language meaning assignment after ∧
            SourcePruningPartialMatch.Completes assignment actualPartial (assignment 0)) ∧
        ∃ program, Projection literal Prod.fst (SourcePruningPositions.openProgram true actualPartial) program ∧
          ∀ (assignment : Nat → Language.Term Symbol) (full : Language.Term Symbol),
            SourcePruningPartialMatch.Completes assignment actualPartial full →
              Projection literal Prod.fst full program := by
  obtain ⟨level, frontier, ordered⟩ := packet.ordered
  have inside : 0 < before.core.counter := roles.bounded 0 root
  obtain ⟨bound, actualPartial, after, runs, stable, frame, afterOrdered, models⟩ :=
    SourcePruningEnumerationPartialOutput.rootPartial_complete
      caller.checked.native.machine.heap level frontier before.core packet.safe ordered inside
  have firstRun : Success (SourcePruningEnumerationPartialOutput.rootPartial
      caller.checked.native.machine.heap bound) before.core actualPartial after := by
    simpa only [Nat.add_zero] using (runs 0).1
  obtain ⟨program, projected, _completionFrame, completions⟩ :=
    SourceSynthesisProgramRoleCompletions.root_partial_completions_program
      packet finished marked roles root bound actualPartial after firstRun
  exact ⟨level, frontier, ordered, bound, actualPartial, after, runs, stable, frame,
    afterOrdered, models, program, projected, completions⟩

end MicroCFTA.SourceSynthesisProgramRolesPartialCompletion
