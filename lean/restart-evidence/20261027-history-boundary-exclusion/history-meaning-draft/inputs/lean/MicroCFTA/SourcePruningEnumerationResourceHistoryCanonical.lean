import MicroCFTA.SourcePruningEnumerationHistoryReceiptCanonical
import MicroCFTA.SourcePruningEnumerationPrefixCanonicalHistory

/-!
# Initial canonical storage through the full actual resource history

Each retained prefix preserves canonical storage.
Actual ordinary entry, head completion and callback preserve the same invariant.
Each emitted output uses its own final cache.
-/
namespace MicroCFTA.SourcePruningEnumerationRecursive
open EnumerationState EnumerationCorrectness EnumerationValidity InternedConstructorTemplates
open SourceCurrentAllocatedNativeInventoryState (Inventory)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Metadata" => SourcePruningRecordTypes.Metadata
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
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
variable {metadata : Metadata Typing} {before : Cached}
variable {seed : SourcePruningEnumerationIncomingReservation.Seed} {ceiling : Nat}
variable {next : Option Next} {output : Output (bits + 2) Typing}

/-- Initial canonical storage reaches the same output's own cache through every actual operation. -/
theorem ResourceHistory.canonical_output
    (history : ResourceHistory holeKey fits admits graph templates checkEmpty edgesOf stop order formulas solver workFuel
      recursiveFuel inventory caller memos metadata before seed ceiling next output)
    (canonical : Canonical before.core) : Canonical output.cache.core := by
  induction history with
  | stopped _ => exact canonical
  | done _ => exact canonical
  | @parked fuel inventory caller memos metadata before seed ceiling uv checked parked updated next core
      tailSeed tailCeiling output _admission valid observed _tail ih =>
      have prefixCanonical := SourcePruningEnumerationSelectedStep.prefix_canonical
        holeKey fits admits graph templates checkEmpty edgesOf stop order metadata formulas solver inventory
        workFuel uv caller before memos canonical valid
      rw [observed] at prefixCanonical
      have full := valid.2.1
      rw [observed] at full
      obtain ⟨_oldHandle, _scs, _readAfter, _reading, _checking, cached, same, coreSame,
        _cacheValid, _safe, _pending, _counter, _ordered, rawSame⟩ := full
      have cacheSame : parked = cached := Option.some.inj same
      subst cached
      have rows : ExceptT.run (SourcePruningEnumerationRestart.run stop order metadata parked checked) =
          [.ok ((updated, next), core)] := (Option.some.inj rawSame).symm
      have returnedCore : core = parked.core := by
        change (if SourcePruningEnumerationRestart.decision stop order metadata parked = some .stuck then []
          else [Except.ok ((metadata, SourcePruningEnumerationRestart.decision stop order metadata parked), checked)]) =
            [Except.ok ((updated, next), core)] at rows
        split at rows
        · cases rows
        · have sameCore : checked = core := congrArg Prod.snd (Except.ok.inj (List.cons.inj rows).1)
          exact sameCore.symm.trans coreSame.symm
      apply ih
      change Canonical core
      rw [returnedCore]
      exact prefixCanonical
  | @ordinary fuel inventory caller memos metadata before seed ceiling uv checked prepared ordinaryInventory
      ordinaryCaller ordinaryMemos action narrowed updated rightCore fragment returnedInventory headCaller
      returnedMemos headCache recorded callbackCore callbackSeed callbackCeiling output
      _admission valid observed _prefixPost _invocation receipt _callbackAdmission callback _tail ih =>
      have prefixCanonical := SourcePruningEnumerationSelectedStep.prefix_canonical
        holeKey fits admits graph templates checkEmpty edgesOf stop order metadata formulas solver inventory
        workFuel uv caller before memos canonical valid
      rw [observed] at prefixCanonical
      have recorded : Success (SourcePruningRecordTypes.recordTypes graph templates workFuel updated uv
          (.inl fragment)) headCache.core (false, recorded) callbackCore := by
        rw [Success, callback]
        exact List.mem_singleton_self _
      exact ih (receipt.canonical_after_callback graph templates workFuel (false, _) callbackCore
        prefixCanonical recorded)

end MicroCFTA.SourcePruningEnumerationRecursive
