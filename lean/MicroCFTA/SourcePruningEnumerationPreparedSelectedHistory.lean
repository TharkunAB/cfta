import MicroCFTA.SourcePruningEnumerationPreparedFiniteReceiptHistory

/-!
# Admitted selected paths to one emitted output

The certificate retains one actual preparation, a complete local receipt,
its false recording and the same smaller-depth resource history.
It is a producer result. It is not an original admission condition.
-/
namespace MicroCFTA.SourcePruningEnumerationPreparedRecursive
open EnumerationState InternedConstructorTemplates
open SourcePruningEnumerationRecursive (Output)
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourcePruningEnumerationIncomingReservation (Seed)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
variable {Typing Key : Type} {bits : Nat}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]

/-- An actual selected output retains full local resources and its admitted callback tail. -/
def SelectedOutputHistoryAt
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Constraint))
    (stop : Option (SourcePruningRecordTypes.Metadata Typing → Nat → Bool))
    (order : SourcePruningRecordTypes.Metadata Typing → List Nat → Option Nat)
    (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)
    (workFuel recursiveFuel : Nat) (inventory : Inventory) (caller : Caller (bits + 2)) (memos : Memos)
    (metadata : SourcePruningRecordTypes.Metadata Typing) (before : Cached) (uv : Nat)
    (output : Output (bits + 2) Typing) : Prop :=
  ∃ (fragment : Fragments.Fragment Symbol) (reached : Caller (bits + 2)) (after : Cached)
    (returnedInventory : Inventory) (returnedMemos : Memos) (callbackSeed : Seed) (callbackCeiling : Nat),
    SourcePruningEnumerationSelectedContinuations.Invocation
      (continueWith (resume holeKey fits admits graph templates checkEmpty edgesOf stop order workFuel recursiveFuel)
        graph templates stop order workFuel metadata uv)
      checkEmpty workFuel workFuel workFuel workFuel workFuel workFuel workFuel uv edgesOf caller before memos.query
        fragment reached returnedMemos.query after ∧
    SelectedHistoryReceipt formulas solver metadata checkEmpty workFuel uv inventory caller memos before
      fragment reached after returnedInventory returnedMemos ∧
    CallbackOutputHistoryAt holeKey fits admits graph templates checkEmpty edgesOf stop order formulas solver
      workFuel recursiveFuel returnedInventory reached returnedMemos metadata after uv fragment
      callbackSeed callbackCeiling output

end MicroCFTA.SourcePruningEnumerationPreparedRecursive
