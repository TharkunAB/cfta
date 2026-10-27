import MicroCFTA.SourceFlatPruningRecursion
import MicroCFTA.SourceFlatPruningAction
import MicroCFTA.SourceFlatPruningIndexAdapters
import MicroCFTA.SourceFlatPruningOracle
import MicroCFTA.SourceFlatPruningRestart
import MicroCFTA.SourcePruningEnumerationSelectedStep

/-!
# Actual selected prefixes with direct-parent forests

The prefix retains all reached observations. It does not scan ordinary siblings.
The native caller advances at the same preparation endpoint, including failures.
-/

namespace MicroCFTA.SourceFlatPruningSelectedPrefix

open EnumerationState InternedConstructorTemplates
open SourcePruningEnumerationNodes
open SourceCurrentAllocatedQueryMemo (advancePhysical)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Core" => EnumerationFlatState.State Symbol Constraint
local notation "Cached" => EnumerationFlatCached.Cached Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Queries" => SourceEndpointMemo.Memos
local notation "Metadata" => SourcePruningRecordTypes.Metadata
local notation "ReadRaw" => List (Except Error (UVarValue Symbol × Core))
local notation "CheckRaw" => List (Except Error (Bool × Core))
local notation "ActionRaw" => List (Except Error (Unit × Core))
local notation "Prepared" => MergedSourceComparison.Result Symbol Constraint
  (Node × Option (EnumerationFlatState.Action Symbol Constraint Unit))

/-- Retain each actual prefix observation before any ordinary continuation. -/
inductive Result (width : Nat) (Typing : Type) where
  /-- Entry or recursion checking does not supply the supported singleton. -/
  | stopped (read : ReadRaw) (checked : Option CheckRaw)
  /-- Retain the cleared core, optional indexed cache and actual restart rows. -/
  | parked (checked : Core) (candidate : Option Cached)
      (raw : Option (List (Except Error ((Metadata Typing × Option Next) × Core))))
  /-- Retain the exact preparation, native effects and all reached core observations. -/
  | narrowed (checked : Core) (prepared : Prepared) (caller : Caller width) (queries : Queries)
      (action : Option ActionRaw) (candidate : Option Cached)
      (right : Option (List (Except Error ((Bool × Metadata Typing) × Core))))

variable {Typing Key α : Type} {width : Nat}
variable [DecidableEq (EdgeKey Symbol Constraint)]

/-- Execute the whole selected prefix through its actual Right callback. -/
noncomputable def run
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (stop : Option (Metadata Typing → Nat → Bool))
    (order : Metadata Typing → List Nat → Option Nat) (metadata : Metadata Typing)
    (nativeFuel callbackFuel uv : Nat) (caller : Caller width) (before : Cached)
    (queries : Queries) : Result width Typing :=
  let read := ExceptT.run (EnumerationFlatState.getValue uv before.core)
  match read with
  | [.ok (.unenumerated (some oldHandle) scs, readAfter)] =>
      let check := ExceptT.run (SourceFlatPruningRecursion.checkRepeated
        caller.checked.native.machine.heap uv oldHandle scs readAfter)
      match check with
      | [.ok (true, checked)] =>
          let candidate := SourceFlatPruningIndexAdapters.parked
            caller.checked.native.machine.heap uv oldHandle scs before checked
          .parked checked candidate (candidate.map fun parked =>
            ExceptT.run (SourceFlatPruningRestart.run stop order metadata parked checked))
      | [.ok (false, checked)] =>
          match lookupNode caller.checked.native.machine.heap oldHandle with
          | none => .stopped read (some check)
          | some oldValue =>
              let prepared := SourceFlatPruningAction.prepare holeKey fits admits metadata nativeFuel
                uv oldHandle scs oldValue caller.checked.native.machine.heap
              let reached := SourceCurrentAllocatedPartialState.advance caller
                (advancePhysical caller.checked ⟨prepared.state, caller.checked.operations⟩) caller.fourth caller.merge
              match prepared with
              | .failed _fault _heap => .narrowed checked prepared reached queries none none none
              | .done (_value, none) _heap => .narrowed checked prepared reached queries none none none
              | .done (value, some action) heap =>
                  let raw := ExceptT.run (action checked)
                  match raw with
                  | [.ok ((), observed)] =>
                      match encodeNode value with
                      | none => .narrowed checked prepared reached queries (some raw) none none
                      | some newHandle =>
                          let candidate := SourceFlatPruningIndexAdapters.narrowed heap
                            uv oldHandle newHandle scs before observed
                          match candidate with
                          | none => .narrowed checked prepared reached queries (some raw) none none
                          | some attached =>
                              let right := ExceptT.run (SourceFlatPruningOracle.recordTypes
                                graph templates callbackFuel metadata uv (.inr newHandle) attached.core)
                              match right with
                              | [.ok ((false, _updated), callbackCore)] =>
                                  let after := EnumerationFlatCached.frame callbackCore attached
                                  .narrowed checked prepared reached queries (some raw) (some after) (some right)
                              | _ => .narrowed checked prepared reached queries (some raw) (some attached) (some right)
                  | _ => .narrowed checked prepared reached queries (some raw) none none
      | _ => .stopped read (some check)
  | _ => .stopped read none

/-- Optional raw observations retain absence separately from every ordered result. -/
def OptionalRows
    (flat : Option (List (Except Error (α × Core))))
    (earlier : Option (List (Except Error (α × EnumerationState.State Symbol Constraint)))) : Prop :=
  match flat, earlier with
  | none, none => True
  | some first, some second => EnumerationResultRelation.Results EnumerationFlatState.Related first second
  | _, _ => False

/-- Relate the complete prefix and require its old ordinary continuation to remain absent. -/
def ResultRelated (flat : Result width Typing)
    (earlier : SourcePruningEnumerationSelectedStep.Result width Typing) : Prop :=
  match flat, earlier with
  | .stopped read checked, .stopped oldRead oldChecked =>
      EnumerationResultRelation.Results EnumerationFlatState.Related read oldRead ∧ OptionalRows checked oldChecked
  | .parked checked candidate raw, .parked oldChecked oldCandidate oldRaw =>
      EnumerationFlatState.Related checked oldChecked ∧
        EnumerationFlatNativeIndex.WritesRelated candidate oldCandidate ∧ OptionalRows raw oldRaw
  | .narrowed checked prepared caller queries action candidate right,
      .narrowed oldChecked oldPrepared oldCaller oldQueries oldAction oldCandidate oldRight ordinary =>
      EnumerationFlatState.Related checked oldChecked ∧
        SourceFlatPruningAction.PreparedRelated checked oldChecked prepared oldPrepared ∧
        caller = oldCaller ∧ queries = oldQueries ∧ OptionalRows action oldAction ∧
        EnumerationFlatNativeIndex.WritesRelated candidate oldCandidate ∧ OptionalRows right oldRight ∧ ordinary = none
  | _, _ => False

end MicroCFTA.SourceFlatPruningSelectedPrefix
