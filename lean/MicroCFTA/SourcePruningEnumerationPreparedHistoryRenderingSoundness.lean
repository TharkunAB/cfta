import MicroCFTA.SourcePruningEnumerationPreparedResourceHistoryLanguage
import MicroCFTA.SourcePruningEnumerationPreparedOutputRendering

/-!
# Original native acceptance from an actual rendered prepared output

The actual renderer constructs the final assignment.
The actual prepared history restores original assignment restrictions.
The local observer uses the same output arity heap as the finite producer.
The original stored root then supplies its original native language.
Whole-cache discharge and checked PCS residuals remain explicit observer premises.
-/
namespace MicroCFTA.SourcePruningEnumerationPreparedRecursive
open Language EnumerationState EnumerationCorrectness InternedConstructorTemplates
open SourcePruningEnumerationRecursive (Packet Output)
open SourcePruningEnumerationNodes
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourcePruningEnumerationIncomingReservation (Seed)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Metadata" => SourcePruningRecordTypes.Metadata
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Core" => EnumerationState.State Symbol Constraint
variable {Typing Key : Type} {bits : Nat}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]
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

/-- Checked actual rendering at a discharged history output satisfies the original stored native root. -/
theorem ResourceHistory.render_sound
    (history : ResourceHistory holeKey fits admits graph templates checkEmpty edgesOf stop order
      formulas solver workFuel recursiveFuel inventory caller memos metadata before seed ceiling next output)
    (actualNext : next = SourcePruningEnumerationRestart.decision stop order metadata before)
    (canonical : EnumerationValidity.Canonical before.core)
    (outputArity : SourcePruningEnumerationArityOrigins.Heap output.caller.checked.native.machine.heap)
    (discharged : SourcePruningEnumerationRendering.Discharged output.cache.core)
    (ambient : InternedGuardedLanguage.Env Symbol) (marker : Symbol) (fuel uv : Nat)
    (after : Core) (term : Term Symbol) (pending : List (Constraint × Term Symbol))
    (observed : Success
      (SourcePruningEnumerationRendering.render output.caller.checked.native.machine.heap marker fuel uv)
      output.cache.core (term, pending) after)
    (checked : ∀ obligation ∈ pending,
      SourceEqualityPCSGuard.holds formulas solver obligation.1 obligation.2 = true)
    (handle : Nat) (bucket : List Suspended) (value : Node)
    (stored : before.core.values[uv]? = some (.unenumerated (some handle) bucket))
    (decoded : lookupNode caller.checked.native.machine.heap handle = some value) :
    ∃ assignment : Nat → Term Symbol,
      Satisfies
        (SourcePruningEnumerationNativeLanguage.handles (SourceEqualityPCSGuard.holds formulas solver)
          ambient caller.checked.native.machine.heap)
        (fun guard accepted => SourceEqualityPCSGuard.holds formulas solver guard accepted = true)
        assignment before.core ∧
      InternedGuardedLanguage.meaning (SourceEqualityPCSGuard.holds formulas solver) ambient value term ∧
      (∀ sc ∈ bucket, Suspended.Holds assignment term sc) ∧ term = assignment uv ∧
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
        assignment after := by
  obtain ⟨assignment, satisfied, termSame, frame, renderedSatisfied⟩ :=
    history.render_assignment ambient marker fuel uv after term pending discharged observed checked
  have original := history.sound actualNext canonical outputArity discharged ambient assignment satisfied
  have atRoot := original.1.2 uv
  have restrictions :
      SourcePruningEnumerationNativeLanguage.handles (SourceEqualityPCSGuard.holds formulas solver)
        ambient caller.checked.native.machine.heap handle (assignment uv) ∧
      ∀ sc ∈ bucket, Suspended.Holds assignment (assignment uv) sc := by
    simpa [heap, stored, slot, Fragments.slotSatisfies, Fragments.permits] using atRoot
  have accepted := (SourcePruningEnumerationNativeLanguage.handles_lookup
    (SourceEqualityPCSGuard.holds formulas solver) ambient caller.checked.native.machine.heap
    handle value (assignment uv) decoded).mp restrictions.1
  refine ⟨assignment, original, ?_, ?_, termSame, frame, satisfied, renderedSatisfied⟩
  · simpa only [termSame] using accepted
  · simpa only [termSame] using restrictions.2

end MicroCFTA.SourcePruningEnumerationPreparedRecursive
