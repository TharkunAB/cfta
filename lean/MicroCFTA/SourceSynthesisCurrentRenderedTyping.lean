import MicroCFTA.SourcePruningEnumerationPreparedHistoryRenderingSoundness
import MicroCFTA.SourceSynthesisCurrentRootTyping
import MicroCFTA.SourceSynthesisLabelProgramBuildRoles
import MicroCFTA.InternedGuardedExecution

/-!
# Current source typing of a discharged rendered history

The actual renderer constructs the assignment at the actual history output.
The history restores the original stored native root and its restrictions.
The same literal build transfers that term to the current source expression.
The receipt retains every assignment, frame, Program and annotation field.
Whole-cache discharge and checked rendered residuals remain explicit premises.
Default recursive Mu observations and the reduction/refold pipeline remain outside this result.
-/
namespace MicroCFTA.SourcePruningEnumerationPreparedRecursive
open Language EnumerationState EnumerationCorrectness InternedConstructorTemplates
open SourcePruningEnumerationRecursive (Output)
open SourcePruningEnumerationNodes
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourcePruningEnumerationIncomingReservation (Seed)
open SourceSynthesisTypeSyntax (Library Query)
open SourceSynthesisFirstOrderConstruction (Expression)
open SourceSynthesisUniverseCallerBoundary (ordinarySymbols)
open SourceSynthesisProgramBuildRolesGeneric (mapSyntax)
open SourceSynthesisProgramTermSize (Projection toProgram)
open SourceSynthesisOrdinaryTyping (Typed)
open SourceSynthesisPr210TypeReflection (candidateRigid)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Metadata" => SourcePruningRecordTypes.Metadata
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Core" => EnumerationState.State Symbol Constraint
local notation "literal" => SourceSynthesisLabelProgramBuildRoles.literal

private theorem holds_decider_eq (first second : DecidableEq FullSyntax.Formula)
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula) :
    @SourceEqualityPCSGuard.holds FullSyntax.Formula first formulas solver =
      @SourceEqualityPCSGuard.holds FullSyntax.Formula second formulas solver :=
  congrArg (fun decider : DecidableEq FullSyntax.Formula =>
    @SourceEqualityPCSGuard.holds FullSyntax.Formula decider formulas solver)
    (Subsingleton.elim first second)

variable {Typing Key : Type} {bits : Nat}
variable [DecidableEq FullSyntax.Formula]
variable [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]
variable {holeKey : Typing → Nat → Key} {fits : Key → Symbol → Bool} {admits : Key → Node → Bool}
variable {graph : Graph Symbol Constraint} {templates : List (Template.Pattern Symbol)}
variable {checkEmpty : Bool} {edgesOf : Node → List (EdgeValue Symbol Constraint)}
variable {stop : Option (Metadata Typing → Nat → Bool)}
variable {order : Metadata Typing → List Nat → Option Nat}
variable {formulas : SourceGuards.Formulas FullSyntax.Formula}
variable {solver : SourceGuards.Entailment FullSyntax.Formula}
variable {workFuel recursiveFuel : Nat} {inventory : Inventory} {caller : Caller (bits + 2)} {memos : Memos}
variable {metadata : Metadata Typing} {before : Cached} {seed : Seed} {ceiling : Nat}
variable {next : Option Next} {output : Output (bits + 2) Typing}

/-- Checked discharged rendering retains its full native receipt and the same current typed Program. -/
theorem ResourceHistory.render_current_typed
    (history : ResourceHistory holeKey fits admits graph templates checkEmpty edgesOf stop order
      formulas solver workFuel recursiveFuel inventory caller memos metadata before seed ceiling next output)
    (lib : Library) (query : Query) (signed : Int) (expression : Expression)
    (returned : SourceSynthesisCurrentConstruction.firstOrderRaw lib query signed = .ok expression)
    (value : Node) (sourceHeap : InternedConstructorTemplates.State Symbol Constraint)
    (built : InternedFreshOrdinaryConstruction.build (ordinarySymbols expression) [] empty = .done value sourceHeap)
    (actualNext : next = SourcePruningEnumerationRestart.decision stop order metadata before)
    (canonical : EnumerationValidity.Canonical before.core)
    (outputArity : SourcePruningEnumerationArityOrigins.Heap output.caller.checked.native.machine.heap)
    (discharged : SourcePruningEnumerationRendering.Discharged output.cache.core)
    (ambient : InternedGuardedLanguage.Env Symbol) (fuel : Nat) (after : Core)
    (term : Term Symbol) (pending : List (Constraint × Term Symbol))
    (observed : Success (SourcePruningEnumerationRendering.render
      output.caller.checked.native.machine.heap ("Mu", FullSyntax.Formula.top) fuel 0)
      output.cache.core (term, pending) after)
    (checked : ∀ obligation ∈ pending,
      SourceEqualityPCSGuard.holds formulas solver obligation.1 obligation.2 = true)
    (handle : Nat) (bucket : List Suspended)
    (stored : before.core.values[0]? = some (.unenumerated (some handle) bucket))
    (decoded : lookupNode caller.checked.native.machine.heap handle = some value) :
    ∃ assignment : Nat → Term Symbol,
      Satisfies
        (SourcePruningEnumerationNativeLanguage.handles (SourceEqualityPCSGuard.holds formulas solver)
          ambient caller.checked.native.machine.heap)
        (fun guard accepted => SourceEqualityPCSGuard.holds formulas solver guard accepted = true)
        assignment before.core ∧
      InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver) ambient value term ∧
      (∀ sc ∈ bucket, Suspended.Holds assignment term sc) ∧ term = assignment 0 ∧
      EnumerationCompressionFrame.Frame output.cache.core after ∧
      Satisfies
        (SourcePruningEnumerationNativeLanguage.handles (SourceEqualityPCSGuard.holds formulas solver)
          ambient output.caller.checked.native.machine.heap)
        (fun guard accepted => SourceEqualityPCSGuard.holds formulas solver guard accepted = true)
        assignment output.cache.core ∧
      Satisfies
        (SourcePruningEnumerationNativeLanguage.handles (SourceEqualityPCSGuard.holds formulas solver)
          ambient output.caller.checked.native.machine.heap)
        (fun guard accepted => SourceEqualityPCSGuard.holds formulas solver guard accepted = true)
        assignment after ∧
      ∃ program body,
        term = .node (literal "filter") [candidateRigid query.queryGoal, body] ∧
        Typed lib query program query.queryGoal ∧
        term.atPath [0] = some (candidateRigid query.queryGoal) ∧
        body.atPath [0] = some (candidateRigid query.queryGoal) ∧
        Projection literal Prod.fst term program ∧
        toProgram literal Prod.fst term = program ∧
        program.components = signed.toNat := by
  have guardEq :
      @SourceEqualityPCSGuard.holds FullSyntax.Formula FormulaExecutable.formulaDecidableEq formulas solver =
        SourceEqualityPCSGuard.holds formulas solver := holds_decider_eq _ _ formulas solver
  have oldChecked : ∀ obligation ∈ pending,
      @SourceEqualityPCSGuard.holds FullSyntax.Formula FormulaExecutable.formulaDecidableEq
        formulas solver obligation.1 obligation.2 = true := by
    simpa only [guardEq] using checked
  obtain ⟨assignment, original, nativeAccepted, restrictions, termSame, frame,
      outputSatisfied, afterSatisfied⟩ :=
    history.render_sound actualNext canonical outputArity discharged ambient
      ("Mu", FullSyntax.Formula.top) fuel 0 after term pending observed oldChecked
      handle bucket value stored decoded
  simp only [guardEq] at original nativeAccepted outputSatisfied afterSatisfied
  have mappedBuilt : InternedFreshOrdinaryConstruction.build (mapSyntax literal expression)
      [] empty = .done value sourceHeap := by
    simpa only [SourceSynthesisLabelProgramBuildRoles.mapSyntax_ordinarySymbols] using built
  have sourceAccepted : InternedGuardedSyntax.evaluate (SourceEqualityPCSGuard.holds formulas solver)
      [] (mapSyntax literal expression) term := by
    rw [← InternedGuardedExecution.closed_language (mapSyntax literal expression) value sourceHeap
      mappedBuilt (SourceEqualityPCSGuard.holds formulas solver) ambient]
    exact nativeAccepted
  obtain ⟨program, body, shape, typed, annotation, bodyAnnotation, projected, sourceDecoded, counted⟩ :=
    SourceSynthesisCurrentRootTyping.firstOrderRaw_typed formulas solver lib query signed expression
      returned term sourceAccepted
  exact ⟨assignment, original, nativeAccepted, restrictions, termSame, frame,
    outputSatisfied, afterSatisfied, program, body, shape, typed, annotation,
    bodyAnnotation, projected, sourceDecoded, counted⟩

end MicroCFTA.SourcePruningEnumerationPreparedRecursive
