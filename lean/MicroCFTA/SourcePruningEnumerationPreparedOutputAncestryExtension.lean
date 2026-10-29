import MicroCFTA.SourcePruningEnumerationPreparedReceiptAncestryExtension
import MicroCFTA.SourcePruningEnumerationPrefixAncestryExtension
import MicroCFTA.SourcePruningEnumerationPreparedFiniteHistoryResources

/-!
# Per-slot ancestry retained by actual prepared outputs

Each admitted output history retains every original recursion key at its slot.
The original finite producer supplies these histories at its own work bound.
This result concerns emitted outputs, including outputs before a stop.
It does not concern caches attached to the final stopped diagnostic.
-/
namespace MicroCFTA.SourcePruningEnumerationPreparedRecursive
open EnumerationState EnumerationCorrectness InternedConstructorTemplates
open SourcePruningEnumerationAncestryExtension
open SourcePruningEnumerationRecursive (Packet Output)
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentConstrainedCapGeneratedQueryResources (Fits)
open SourcePruningEnumerationIncomingReservation (Seed)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Metadata" => SourcePruningRecordTypes.Metadata
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Heap" => SourceEqualityAnnotationHeap.Heap
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

/-- Every actual admitted output retains each original key at the same raw slot. -/
theorem ResourceHistory.ancestry_extension
    (history : ResourceHistory holeKey fits admits graph templates checkEmpty edgesOf stop order formulas solver workFuel
      recursiveFuel inventory caller memos metadata before seed ceiling next output) :
    Extends before.core output.cache.core := by
  induction history with
  | stopped _ => exact Extends.refl _
  | done _ => exact Extends.refl _
  | @parked fuel inventory caller memos metadata before seed ceiling uv checked parked updated next core
      tailSeed tailCeiling output admission valid observed _tail ih =>
      have prefixHistories := SourcePruningEnumerationSelectedStep.prefix_recursion_ancestry
        holeKey fits admits graph templates checkEmpty edgesOf stop order metadata formulas solver inventory
        workFuel uv caller before memos admission.1.safe.1.total valid
      rw [observed] at prefixHistories
      have beforeToParked : Extends before.core parked.core := by
        intro slot key member
        simpa only [prefixHistories] using member
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
      have tailExtends : Extends core output.cache.core := ih
      rw [returnedCore] at tailExtends
      exact beforeToParked.trans tailExtends
  | @selected fuel inventory caller memos metadata before seed ceiling uv checked prepared ordinaryInventory
      ordinaryCaller ordinaryMemos action narrowed updated rightCore fragment returnedInventory headCaller
      returnedMemos headCache recorded callbackCore callbackSeed callbackCeiling output
      admission valid observed _prefixPost _invocation receipt _callbackAdmission callback _tail ih =>
      have prefixHistories := SourcePruningEnumerationSelectedStep.prefix_recursion_ancestry
        holeKey fits admits graph templates checkEmpty edgesOf stop order metadata formulas solver inventory
        workFuel uv caller before memos admission.1.safe.1.total valid
      rw [observed] at prefixHistories
      have beforeToNarrowed : Extends before.core narrowed.core := by
        intro slot key member
        simpa only [prefixHistories] using member
      have recordedSuccess : Success (SourcePruningRecordTypes.recordTypes graph templates workFuel updated uv
          (.inl fragment)) headCache.core (false, recorded) callbackCore := by
        rw [Success, callback]
        exact List.mem_singleton_self _
      have callbackExtends := receipt.ancestry_extension_after_callback graph templates workFuel
        (false, recorded) callbackCore recordedSuccess
      have tailExtends : Extends callbackCore output.cache.core := ih
      exact beforeToNarrowed.trans (callbackExtends.trans tailExtends)

/-- Original finite resources retain all histories and extend ancestry at every emitted output. -/
theorem run_finite_complete_resources_with_ancestry
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Constraint))
    (stop : Option (Metadata Typing → Nat → Bool)) (order : Metadata Typing → List Nat → Option Nat)
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
    (reserved : SourcePruningEnumerationPreparedReservation.Reserved bits recursiveFuel seed ceiling) :
    ∃ bound outcome,
      (∀ extra, run holeKey fits admits graph templates checkEmpty edgesOf stop order (bound + extra) recursiveFuel
        metadata caller memos.query before = outcome) ∧
      OutcomeResources formulas solver caller
        (SourcePruningEnumerationPreparedReservation.final recursiveFuel seed ceiling) outcome ∧
      (∀ extra output, output ∈ SourcePruningEnumerationHookInvocation.hookOutputs outcome →
        ResourceHistory holeKey fits admits graph templates checkEmpty edgesOf stop order formulas solver
          (bound + extra) recursiveFuel inventory caller memos metadata before seed ceiling
          (SourcePruningEnumerationRestart.decision stop order metadata before) output) ∧
      ∀ output ∈ SourcePruningEnumerationHookInvocation.hookOutputs outcome,
        Extends before.core output.cache.core := by
  obtain ⟨bound, outcome, running, resources, histories⟩ := run_finite_complete_resources_with_history
    holeKey fits admits graph templates checkEmpty edgesOf stop order formulas solver recursiveFuel
    inventory caller memos before metadata seed ceiling packet bounded known
    selectionMembers selectionLength initialMass reserved
  refine ⟨bound, outcome, running, resources, histories, ?_⟩
  intro output member
  exact (histories 0 output member).ancestry_extension

end MicroCFTA.SourcePruningEnumerationPreparedRecursive
