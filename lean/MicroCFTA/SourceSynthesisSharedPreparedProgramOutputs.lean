import MicroCFTA.SourceSynthesisProgramRolesSharedReadback
import MicroCFTA.SourceSynthesisSharedPreparedOutputControl

/-!
# Program readback at every emitted output without a stop rule

One shared prepared driver retains its full resources and Program roles.
Actual output control derives finishedness at each emitted output.
Each output retains the same complete partial-root receipt.
This result does not assert that an output or satisfying completion exists.
-/
namespace MicroCFTA.SourceSynthesisSharedPreparedProgramOutputs
open EnumerationState EnumerationCorrectness
open InternedConstructorTemplates (EdgeKey EdgeValue Value)
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentConstrainedCapGeneratedQueryResources (Fits)
open SourcePruningEnumerationSharedIncomingReservation (Seed)
open SourcePruningEnumerationRecursive (Packet)
open SourcePruningEnumerationSharedPreparedRecursive (run OutcomeResources emitted)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Metadata" => SourcePruningRecordTypes.Metadata
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Heap" => SourceEqualityAnnotationHeap.Heap
local notation "literal" => SourceSynthesisLabelProgramBuildRoles.literal
variable {Typing Key : Type} {bits : Nat}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]

/-- Every actual output without a stop rule retains its complete Program root receipt. -/
theorem run_finite_complete_resources_program_outputs
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Constraint))
    (order : Metadata Typing → List Nat → Option Nat)
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) (recursiveFuel : Nat) (inventory : Inventory)
    (caller : Caller (bits + 2)) (memos : Memos) (before : Cached) (metadata : Metadata Typing)
    (seed : Seed) (ceiling : Nat)
    (packet : Packet formulas solver inventory caller memos metadata before)
    (bounded : Fits seed.2 caller.checked)
    (known : Heap (fun guard => guard ∈ seed.1) caller.checked.native.machine.heap)
    (selectionMembers : ∀ entry rows depth free, ∀ edge ∈ edgesOf (.node entry rows depth free), edge ∈ rows)
    (selectionLength : ∀ entry rows depth free, (edgesOf (.node entry rows depth free)).length ≤ rows.length)
    (initialMass : SourcePruningEnumerationPrefixAdmission.suspendedBound before.core ≤ ceiling)
    (reserved : SourcePruningEnumerationSharedPreparedReservation.Reserved bits recursiveFuel seed ceiling)
    (valid : Constraint → Prop) (marked : Nat → Prop)
    (slots : SourceSynthesisProgramEnumerationRoles.ProgramSlots valid literal
      caller.checked.native.machine.heap before.core marked) (root : marked 0) :
    ∃ bound outcome,
      (
      (∀ extra, run holeKey fits admits graph templates checkEmpty edgesOf none order (bound + extra) recursiveFuel
        metadata caller memos.query before = outcome) ∧
      OutcomeResources formulas solver caller
        (SourcePruningEnumerationSharedPreparedReservation.final recursiveFuel seed ceiling) outcome ) ∧
      ∀ output ∈ emitted outcome, ∃ finalMarked : Nat → Prop,
        (∀ uv, marked uv → finalMarked uv) ∧ finalMarked 0 ∧
        SourceSynthesisProgramEnumerationRoles.ProgramSlots valid literal
          output.caller.checked.native.machine.heap output.cache.core finalMarked ∧
        output.metadata = none ∧
        EnumerationPureSelection.next (fun _ => none) output.cache = .done ∧
          ∃ (next : Inventory) (final : Memos) (outputMetadata : Metadata Typing),
            SourceCurrentAllocatedPartialInvariant.Post formulas solver next caller output.caller final ∧
            final.query = output.queries ∧
            Packet formulas solver next output.caller final outputMetadata output.cache ∧
            (output.metadata = none ∨ output.metadata = some outputMetadata) ∧
            Fits (SourcePruningEnumerationSharedPreparedReservation.final recursiveFuel seed ceiling).2
              output.caller.checked ∧
            Heap (fun guard => guard ∈
              (SourcePruningEnumerationSharedPreparedReservation.final recursiveFuel seed ceiling).1)
              output.caller.checked.native.machine.heap ∧
            ∃ (level : Nat → Nat) (frontier : Nat),
              EnumerationOrder.Stratified output.cache.core level frontier ∧
              ∃ (readFuel : Nat) (actualPartial : SourcePruningTemplates.PartialTerm)
                (after : EnumerationState.State Symbol Constraint),
                (∀ extra,
                  Success (SourcePruningEnumerationPartialOutput.rootPartial
                    output.caller.checked.native.machine.heap (readFuel + extra))
                    output.cache.core actualPartial after ∧
                  ExceptT.run (SourcePruningEnumerationPartialOutput.rootPartial
                    output.caller.checked.native.machine.heap (readFuel + extra) output.cache.core) =
                    [.ok (actualPartial, after)]) ∧
                EnumerationDriver.RenderStable output.cache.core after ∧
                EnumerationCompressionFrame.Frame output.cache.core after ∧
                EnumerationOrder.Stratified after level frontier ∧
                (∀ (language : NodeLanguage Symbol) (meaning : Constraint → Language.Term Symbol → Prop)
                  (assignment : Nat → Language.Term Symbol),
                  Satisfies language meaning assignment output.cache.core →
                    Satisfies language meaning assignment after ∧
                    SourcePruningPartialMatch.Completes assignment actualPartial (assignment 0)) ∧
                ∃ program, SourceSynthesisProgramTermSize.Projection literal Prod.fst
                    (SourcePruningPositions.openProgram true actualPartial) program ∧
                  ∀ (assignment : Nat → Language.Term Symbol) (full : Language.Term Symbol),
                    SourcePruningPartialMatch.Completes assignment actualPartial full →
                      SourceSynthesisProgramTermSize.Projection literal Prod.fst full program := by
  obtain ⟨bound, outcome, retained, outputRoots⟩ :=
    SourceSynthesisProgramRolesSharedReadback.run_finite_complete_resources_program_roots
      holeKey fits admits graph templates checkEmpty edgesOf none order formulas solver recursiveFuel
      inventory caller memos before metadata seed ceiling packet bounded known selectionMembers
      selectionLength initialMass reserved valid marked slots root
  refine ⟨bound, outcome, retained, ?_⟩
  intro output member
  have sameRun : run holeKey fits admits graph templates checkEmpty edgesOf none order
      bound recursiveFuel metadata caller memos.query before = outcome := by
    simpa only [Nat.add_zero] using retained.1 0
  have actualMember : output ∈ emitted (run holeKey fits admits graph templates checkEmpty edgesOf none order
      bound recursiveFuel metadata caller memos.query before) := by
    rw [sameRun]
    exact member
  have control := SourcePruningEnumerationSharedPreparedRecursive.run_output_control
    holeKey fits admits graph templates checkEmpty edgesOf none order bound recursiveFuel
    metadata caller memos.query before output actualMember
  have noMetadata : output.metadata = none := control.2 rfl
  have finished : EnumerationPureSelection.next (fun _ => none) output.cache = .done :=
    control.1 noMetadata
  obtain ⟨finalMarked, extending, outputRoot, outputSlots, readback⟩ := outputRoots output member
  exact ⟨finalMarked, extending, outputRoot, outputSlots, noMetadata, finished, readback finished⟩

end MicroCFTA.SourceSynthesisSharedPreparedProgramOutputs
