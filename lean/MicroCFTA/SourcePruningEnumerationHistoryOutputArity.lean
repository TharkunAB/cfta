import MicroCFTA.SourcePruningEnumerationHistoryPost
import MicroCFTA.SourcePruningEnumerationOrdinaryReceiptArity

/-!
# Projected arity on the same actual resource history

Every earlier selected edge remains in the actual output heap.
The output heap supplies arity for these retained edge records.
The proof keeps every original history field and full memo state.
It does not require arity heaps at intermediate inputs.
-/
namespace MicroCFTA.SourcePruningEnumerationRecursive
open EnumerationState InternedConstructorTemplates
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourcePruningEnumerationIncomingReservation (Seed)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Metadata" => SourcePruningRecordTypes.Metadata
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "ArityHeap" => SourcePruningEnumerationArityOrigins.Heap
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

/-- The same output heap derives all projected-arity annotations on its actual resource history. -/
theorem ResourceHistory.with_arity_of_output_heap
    (history : ResourceHistory holeKey fits admits graph templates checkEmpty edgesOf stop order formulas solver
      workFuel recursiveFuel inventory caller memos metadata before seed ceiling next output)
    (outputHeap : ArityHeap output.caller.checked.native.machine.heap) :
    ResourceHistoryWithArity holeKey fits admits graph templates checkEmpty edgesOf stop order formulas solver
      workFuel recursiveFuel inventory caller memos metadata before seed ceiling next output := by
  revert outputHeap
  induction history with
  | stopped admission =>
      intro _outputHeap
      exact .stopped admission
  | done admission =>
      intro _outputHeap
      exact .done admission
  | parked admission valid observed _tail ih =>
      intro outputHeap
      exact .parked admission valid observed (ih outputHeap)
  | ordinary admission valid observed prefixPost invocation receipt callbackAdmission callback tail ih =>
      intro outputHeap
      obtain ⟨_next, _final, tailPost, _query⟩ := tail.native_post
      refine .ordinary admission valid observed prefixPost invocation ?_ callbackAdmission callback (ih outputHeap)
      apply OrdinaryHistoryReceipt.with_arity_from_scan_heap receipt
      obtain ⟨_entered, _handle, _scs, _decoded, _edge, _headSeed, _inherited, _headInventory,
        _headCaller, _headMemos, _headBound, _original, _entry, _enteredPacket, headPost,
        _captured, completed⟩ := receipt
      have kept := (headPost.effects.keeps.trans completed.post.effects.keeps).trans tailPost.effects.keeps
      intro key edge stored
      exact outputHeap key edge (kept.growth.edgeRecords key edge stored)

end MicroCFTA.SourcePruningEnumerationRecursive
