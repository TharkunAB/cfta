import MicroCFTA.SourcePruningEnumerationSelectedStep
import MicroCFTA.SourcePruningEnumerationSelectedOrdinary

namespace MicroCFTA.SourcePruningEnumerationSelectedStep
open EnumerationState EnumerationCorrectness EnumerationSchedule EnumerationCompressionFrame
open InternedConstructorTemplates InternedProbeProvenance
open SourcePruningEnumerationNodes SourcePruningEnumerationObservation
open SourceCurrentAllocatedQueryMemo (advancePhysical)
open SourceCurrentAllocatedNativeInventoryState (Inventory)
open SourceCurrentAllocatedPartialInvariant (Context Post)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Core" => EnumerationState.State Symbol Constraint
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Queries" => SourceEndpointMemo.Memos
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Metadata" => SourcePruningRecordTypes.Metadata

variable {Typing Key : Type} {width : Nat}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]
variable (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
variable (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
variable (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Constraint))
variable (stop : Option (Metadata Typing → Nat → Bool))
variable (order : Metadata Typing → List Nat → Option Nat) (metadata : Metadata Typing)

attribute [local instance] SourcePruningEnumerationAction.actionMonadList

/-- The actual nonempty preparation fixes its pure or representative-and-write action. -/
theorem prepared_action
    (nativeFuel representativeFuel uv oldHandle newHandle : Nat) (scs : List Suspended)
    (oldValue value : Node) (heap nextHeap : InternedConstructorTemplates.State Symbol Constraint)
    (narrowed : SourcePruningOuterNarrow.narrow holeKey fits admits metadata nativeFuel uv oldValue heap =
      .done value nextHeap)
    (nonempty : value ≠ .empty) (encoded : encodeNode value = some newHandle) :
    SourcePruningEnumerationAction.prepare holeKey fits admits metadata nativeFuel representativeFuel
      uv oldHandle scs oldValue heap =
      .done (value, some (if newHandle = oldHandle then (pure () : EnumerateM Symbol Constraint Unit)
        else representative representativeFuel uv >>= fun selected =>
          setValue selected (.unenumerated (some newHandle) scs))) nextHeap := by
  cases value with
  | empty => exact False.elim (nonempty rfl)
  | reference name => simp [encodeNode] at encoded
  | node entry edges depth free => simp only [SourcePruningEnumerationAction.prepare, narrowed, encoded]
  | union entry members depth free => simp only [SourcePruningEnumerationAction.prepare, narrowed, encoded]
  | mu entry body depth ordinary => simp only [SourcePruningEnumerationAction.prepare, narrowed, encoded]

/-- Successful preparation has one raw row at its actual reached core. -/
theorem prepared_singleton
    (nativeFuel representativeFuel uv oldHandle newHandle : Nat) (scs : List Suspended)
    (oldValue value : Node) (heap nextHeap : InternedConstructorTemplates.State Symbol Constraint)
    (action : EnumerateM Symbol Constraint Unit) (checked after : Core)
    (narrowed : SourcePruningOuterNarrow.narrow holeKey fits admits metadata nativeFuel uv oldValue heap =
      .done value nextHeap)
    (nonempty : value ≠ .empty) (encoded : encodeNode value = some newHandle)
    (prepared : SourcePruningEnumerationAction.prepare holeKey fits admits metadata nativeFuel representativeFuel
      uv oldHandle scs oldValue heap = .done (value, some action) nextHeap)
    (observed : Success action checked () after) :
    ExceptT.run (action checked) = [.ok ((), after)] := by
  have actual := prepared_action holeKey fits admits metadata nativeFuel representativeFuel uv oldHandle newHandle
    scs oldValue value heap nextHeap narrowed nonempty encoded
  rw [prepared] at actual
  have actionSame : action =
      (if newHandle = oldHandle then (pure () : EnumerateM Symbol Constraint Unit)
        else representative representativeFuel uv >>= fun selected =>
          setValue selected (.unenumerated (some newHandle) scs)) :=
    Option.some.inj (Prod.mk.inj (MergedSourceComparison.Result.done.inj actual).1).2
  rw [actionSame] at observed ⊢
  by_cases same : newHandle = oldHandle
  · rw [if_pos same] at observed ⊢
    obtain ⟨_unit, rfl⟩ := (success_pure () () checked after).mp observed
    rfl
  · rw [if_neg same] at observed ⊢
    obtain ⟨selected, resolved, reading, writing⟩ := (success_bind _ _ checked () after).mp observed
    obtain ⟨found, lookup, selectedSame, resolvedSame⟩ :=
      (representative_success representativeFuel uv checked resolved selected).mp reading
    have raw : representative representativeFuel uv checked = [.ok (selected, resolved)] := by
      rw [selectedSame, resolvedSame]
      exact representative_exact representativeFuel uv checked found lookup
    rw [bind_single _ _ checked resolved selected raw]
    have afterSame := (EnumerationDriver.modify_success _ resolved after).mp writing
    rw [afterSame]
    rfl

/-- The actual repeated check executes only the indexed parked restart. -/
theorem run_parked
    (readFuel checkFuel nativeFuel representativeFuel indexFuel callbackFuel r n p h k uv oldHandle : Nat)
    (scs : List Suspended) (caller : Caller width) (before parked : Cached) (queries : Queries)
    (readAfter checked : Core)
    (read : ExceptT.run (getValue readFuel uv before.core) =
      [.ok (.unenumerated (some oldHandle) scs, readAfter)])
    (check : ExceptT.run (SourcePruningEnumerationRecursion.checkRepeated caller.checked.native.machine.heap
      checkFuel uv oldHandle scs readAfter) = [.ok (true, checked)])
    (adapted : SourcePruningEnumerationParkedRestart.adapt caller.checked.native.machine.heap
      indexFuel uv oldHandle scs before checked = some parked) :
    run holeKey fits admits graph templates checkEmpty edgesOf stop order metadata
      readFuel checkFuel nativeFuel representativeFuel indexFuel callbackFuel r n p h k uv caller before queries =
      .parked checked (some parked)
        (some (ExceptT.run (SourcePruningEnumerationRestart.run stop order metadata parked checked))) := by
  simp only [run, read, check, adapted, Option.map_some]

/-- Empty narrowing retains the reached caller and rejects before later callbacks. -/
theorem run_empty
    (readFuel checkFuel nativeFuel representativeFuel indexFuel callbackFuel r n p h k uv oldHandle : Nat)
    (scs : List Suspended) (oldValue : Node) (caller : Caller width) (before : Cached) (queries : Queries)
    (readAfter checked : Core) (heap : InternedConstructorTemplates.State Symbol Constraint)
    (read : ExceptT.run (getValue readFuel uv before.core) =
      [.ok (.unenumerated (some oldHandle) scs, readAfter)])
    (check : ExceptT.run (SourcePruningEnumerationRecursion.checkRepeated caller.checked.native.machine.heap
      checkFuel uv oldHandle scs readAfter) = [.ok (false, checked)])
    (decoded : lookupNode caller.checked.native.machine.heap oldHandle = some oldValue)
    (prepared : SourcePruningEnumerationAction.prepare holeKey fits admits metadata nativeFuel representativeFuel
      uv oldHandle scs oldValue caller.checked.native.machine.heap =
      .done (.empty, some (reject : EnumerateM Symbol Constraint Unit)) heap) :
    run holeKey fits admits graph templates checkEmpty edgesOf stop order metadata
      readFuel checkFuel nativeFuel representativeFuel indexFuel callbackFuel r n p h k uv caller before queries =
      .narrowed checked (.done (.empty, some (reject : EnumerateM Symbol Constraint Unit)) heap)
        (SourceCurrentAllocatedPartialState.advance caller
          (advancePhysical caller.checked ⟨heap, caller.checked.operations⟩) caller.fourth caller.merge)
        queries (some []) none none none := by
  simp only [run, read, check, decoded, prepared]
  rfl

/-- A successful actual action and attached cache reach the concrete Right callback and ordinary worker. -/
theorem run_narrowed
    (readFuel checkFuel nativeFuel representativeFuel indexFuel callbackFuel r n p h k uv oldHandle newHandle : Nat)
    (scs : List Suspended) (oldValue value : Node) (caller : Caller width) (before after : Cached)
    (queries : Queries) (readAfter checked : Core)
    (heap : InternedConstructorTemplates.State Symbol Constraint) (action : EnumerateM Symbol Constraint Unit)
    (read : ExceptT.run (getValue readFuel uv before.core) =
      [.ok (.unenumerated (some oldHandle) scs, readAfter)])
    (check : ExceptT.run (SourcePruningEnumerationRecursion.checkRepeated caller.checked.native.machine.heap
      checkFuel uv oldHandle scs readAfter) = [.ok (false, checked)])
    (decoded : lookupNode caller.checked.native.machine.heap oldHandle = some oldValue)
    (prepared : SourcePruningEnumerationAction.prepare holeKey fits admits metadata nativeFuel representativeFuel
      uv oldHandle scs oldValue caller.checked.native.machine.heap = .done (value, some action) heap)
    (raw : ExceptT.run (action checked) = [.ok ((), after.core)])
    (encoded : encodeNode value = some newHandle)
    (adapted : SourcePruningEnumerationNarrowAdapter.adapt heap indexFuel uv oldHandle newHandle scs
      before after.core = some after) :
    run holeKey fits admits graph templates checkEmpty edgesOf stop order metadata
      readFuel checkFuel nativeFuel representativeFuel indexFuel callbackFuel r n p h k uv caller before queries =
      .narrowed checked (.done (value, some action) heap)
        (SourceCurrentAllocatedPartialState.advance caller
          (advancePhysical caller.checked ⟨heap, caller.checked.operations⟩) caller.fourth caller.merge)
        queries (some [.ok ((), after.core)]) (some after)
        (some [.ok ((false, metadata), after.core)])
        (some (SourcePruningEnumerationNativeOrdinary.run checkEmpty r n p h k uv edgesOf
          (SourceCurrentAllocatedPartialState.advance caller
            (advancePhysical caller.checked ⟨heap, caller.checked.operations⟩) caller.fourth caller.merge)
          after queries)) := by
  have right : ExceptT.run (SourcePruningRecordTypes.recordTypes graph templates callbackFuel metadata uv
      (.inr newHandle) after.core) = [.ok ((false, metadata), after.core)] := by
    rw [SourcePruningRecordTypes.recordTypes_inr]
    rfl
  simp only [run, read, check, decoded, prepared, raw, encoded, adapted, right]
  rfl

end MicroCFTA.SourcePruningEnumerationSelectedStep
