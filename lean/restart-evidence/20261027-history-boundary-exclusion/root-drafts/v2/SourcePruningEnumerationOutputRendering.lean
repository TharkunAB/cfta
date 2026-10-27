import MicroCFTA.SourcePruningEnumerationFiniteHistoryContract
import MicroCFTA.SourcePruningEnumerationRendering

/-!
# Assignments from rendering an actual resource-history output

The final history tag supplies its own complete packet.
Actual rendering and checked residuals construct the output assignment.
No separate final resource or safety premise is required.
-/
namespace MicroCFTA.SourcePruningEnumerationRecursive
open Language EnumerationState EnumerationCorrectness InternedConstructorTemplates
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

/-- The final actual history tag retains its own full packet. -/
theorem ResourceHistory.output_packet
    (history : ResourceHistory holeKey fits admits graph templates checkEmpty edgesOf stop order formulas solver
      workFuel recursiveFuel inventory caller memos metadata before seed ceiling next output) :
    ∃ finalInventory finalMemos finalMetadata,
      Packet formulas solver finalInventory output.caller finalMemos finalMetadata output.cache := by
  induction history with
  | stopped admission => exact ⟨_, _, _, admission.1⟩
  | done admission => exact ⟨_, _, _, admission.1⟩
  | parked _admission _valid _observed _tail ih => exact ih
  | ordinary _admission _valid _observed _post _invocation _receipt _callbackAdmission _callback _tail ih =>
      exact ih

/-- Actual rendering constructs a complete assignment at the same history output's native heap. -/
theorem ResourceHistory.render_assignment
    (history : ResourceHistory holeKey fits admits graph templates checkEmpty edgesOf stop order formulas solver
      workFuel recursiveFuel inventory caller memos metadata before seed ceiling next output)
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
  obtain ⟨_finalInventory, _finalMemos, _finalMetadata, packet⟩ := history.output_packet
  obtain ⟨level, frontier, ordered⟩ := packet.ordered
  exact SourcePruningEnumerationRendering.render_assignment
    output.caller.checked.native.machine.heap (SourceEqualityPCSGuard.holds formulas solver) ambient
    (fun guard value => SourceEqualityPCSGuard.holds formulas solver guard value = true)
    marker fuel uv output.cache.core after term pending packet.safe level frontier ordered
    discharged observed checked

end MicroCFTA.SourcePruningEnumerationRecursive
