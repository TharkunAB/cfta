import MicroCFTA.SourcePruningEnumerationParkedRestart
import MicroCFTA.SourcePruningEnumerationNarrowAdapter
import MicroCFTA.SourcePruningEnumerationNativeOrdinary
import MicroCFTA.SourcePruningEnumerationAction
import MicroCFTA.SourcePruningRecordTypes

namespace MicroCFTA.SourcePruningEnumerationSelectedStep
open EnumerationState InternedConstructorTemplates
open SourcePruningEnumerationNodes
open SourceCurrentAllocatedQueryMemo (advancePhysical)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Core" => EnumerationState.State Symbol Constraint
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Queries" => SourceEndpointMemo.Memos
local notation "Metadata" => SourcePruningRecordTypes.Metadata
local notation "ReadRaw" => List (Except EnumerationState.Error (UVarValue Symbol × Core))
local notation "CheckRaw" => List (Except EnumerationState.Error (Bool × Core))
local notation "ActionRaw" => List (Except EnumerationState.Error (Unit × Core))
local notation "Prepared" => MergedSourceComparison.Result Symbol Constraint (Node × Option (EnumerateM Symbol Constraint Unit))
local notation "OrdinaryRaw" => List (Except EnumerationState.Error ((Nat × Nat × List Suspended × Node) × Core))

/-- Retain the actual observations of a selected source step without asserting recursive completion. -/
inductive Result (width : Nat) (Typing : Type) where
  /-- Entry or recursion checking does not supply the supported pending singleton. -/
  | stopped (read : ReadRaw) (checked : Option CheckRaw)
  /-- Repeated recursion retains its checked core and optional indexed restart observation. -/
  | parked (checked : Core) (candidate : Option Cached)
      (raw : Option (List (Except EnumerationState.Error ((Metadata Typing × Option Next) × Core))))
  /-- Narrowing retains its actual caller, action and each reached continuation stage. -/
  | narrowed (checked : Core) (prepared : Prepared) (caller : Caller width) (queries : Queries)
      (action : Option ActionRaw) (candidate : Option Cached)
      (right : Option (List (Except EnumerationState.Error ((Bool × Metadata Typing) × Core))))
      (ordinary : Option (OrdinaryRaw × Option (SourcePruningEnumerationNativeBranches.Result width)))

variable {Typing Key : Type} {width : Nat}
section Prefix
variable [DecidableEq (EdgeKey Symbol Constraint)]

/-- Observe the selected prefix through Right recording without scanning ordinary siblings. -/
noncomputable def runPrefix
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (stop : Option (Metadata Typing → Nat → Bool))
    (order : Metadata Typing → List Nat → Option Nat) (metadata : Metadata Typing)
    (readFuel checkFuel nativeFuel representativeFuel indexFuel callbackFuel uv : Nat)
    (caller : Caller width) (before : Cached) (queries : Queries) : Result width Typing :=
  let read := ExceptT.run (getValue readFuel uv before.core)
  match read with
  | [.ok (.unenumerated (some oldHandle) scs, readAfter)] =>
      let check := ExceptT.run (SourcePruningEnumerationRecursion.checkRepeated
        caller.checked.native.machine.heap checkFuel uv oldHandle scs readAfter)
      match check with
      | [.ok (true, checked)] =>
          let candidate := SourcePruningEnumerationParkedRestart.adapt
            caller.checked.native.machine.heap indexFuel uv oldHandle scs before checked
          .parked checked candidate (candidate.map fun parked =>
            ExceptT.run (SourcePruningEnumerationRestart.run stop order metadata parked checked))
      | [.ok (false, checked)] =>
          match lookupNode caller.checked.native.machine.heap oldHandle with
          | none => .stopped read (some check)
          | some oldValue =>
              let prepared := SourcePruningEnumerationAction.prepare holeKey fits admits metadata nativeFuel
                representativeFuel uv oldHandle scs oldValue caller.checked.native.machine.heap
              let reached := SourceCurrentAllocatedPartialState.advance caller
                (advancePhysical caller.checked ⟨prepared.state, caller.checked.operations⟩) caller.fourth caller.merge
              match prepared with
              | .failed _fault _heap => .narrowed checked prepared reached queries none none none none
              | .done (_value, none) _heap => .narrowed checked prepared reached queries none none none none
              | .done (value, some action) heap =>
                  let raw := ExceptT.run (action checked)
                  match raw with
                  | [.ok ((), observed)] =>
                      match encodeNode value with
                      | none => .narrowed checked prepared reached queries (some raw) none none none
                      | some newHandle =>
                          let candidate := SourcePruningEnumerationNarrowAdapter.adapt heap indexFuel
                            uv oldHandle newHandle scs before observed
                          match candidate with
                          | none => .narrowed checked prepared reached queries (some raw) none none none
                          | some attached =>
                              let right := ExceptT.run (SourcePruningRecordTypes.recordTypes
                                graph templates callbackFuel metadata uv (.inr newHandle) attached.core)
                              match right with
                              | [.ok ((false, _updated), callbackCore)] =>
                                  let after := EnumerationExpandableIndex.frame callbackCore attached
                                  .narrowed checked prepared reached queries (some raw) (some after) (some right)
                                    none
                              | _ => .narrowed checked prepared reached queries (some raw) (some attached) (some right) none
                  | _ => .narrowed checked prepared reached queries (some raw) none none none
      | _ => .stopped read (some check)
  | _ => .stopped read none

/-- Every prefix observation leaves the ordinary continuation unexecuted. -/
theorem prefix_no_ordinary
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (stop : Option (Metadata Typing → Nat → Bool))
    (order : Metadata Typing → List Nat → Option Nat) (metadata : Metadata Typing)
    (readFuel checkFuel nativeFuel representativeFuel indexFuel callbackFuel uv : Nat)
    (caller : Caller width) (before : Cached) (queries : Queries) :
    match runPrefix holeKey fits admits graph templates stop order metadata readFuel checkFuel nativeFuel
      representativeFuel indexFuel callbackFuel uv caller before queries with
    | .narrowed _ _ _ _ _ _ _ ordinary => ordinary = none
    | _ => True := by
  unfold runPrefix
  dsimp only
  generalize ExceptT.run (getValue readFuel uv before.core) = read
  cases read with
  | nil => trivial
  | cons first rest =>
      cases rest with
      | cons _ _ => trivial
      | nil =>
          cases first with
          | error _ => trivial
          | ok pair =>
              obtain ⟨value, readAfter⟩ := pair
              cases value with
              | eliminated | enumerated _ => trivial
              | unenumerated handle scs =>
                  cases handle with
                  | none => trivial
                  | some oldHandle =>
                      dsimp only
                      generalize ExceptT.run (SourcePruningEnumerationRecursion.checkRepeated
                        caller.checked.native.machine.heap checkFuel uv oldHandle scs readAfter) = check
                      cases check with
                      | nil => trivial
                      | cons first rest =>
                          cases rest with
                          | cons _ _ => trivial
                          | nil =>
                              cases first with
                              | error _ => trivial
                              | ok pair =>
                                  obtain ⟨repeated, checked⟩ := pair
                                  cases repeated with
                                  | true => trivial
                                  | false =>
                                      cases lookupNode caller.checked.native.machine.heap oldHandle with
                                      | none => trivial
                                      | some oldValue =>
                                          dsimp only
                                          generalize SourcePruningEnumerationAction.prepare holeKey fits admits metadata
                                            nativeFuel representativeFuel uv oldHandle scs oldValue
                                            caller.checked.native.machine.heap = prepared
                                          cases prepared with
                                          | failed _ _ => rfl
                                          | done pair heap =>
                                              obtain ⟨value, action⟩ := pair
                                              cases action with
                                              | none => rfl
                                              | some action =>
                                                  dsimp only
                                                  generalize ExceptT.run (action checked) = raw
                                                  cases raw with
                                                  | nil => rfl
                                                  | cons first rest =>
                                                      cases rest with
                                                      | cons _ _ => rfl
                                                      | nil =>
                                                          cases first with
                                                          | error _ => rfl
                                                          | ok pair =>
                                                              obtain ⟨(), observed⟩ := pair
                                                              cases encodeNode value with
                                                              | none => rfl
                                                              | some newHandle =>
                                                                  cases SourcePruningEnumerationNarrowAdapter.adapt heap
                                                                    indexFuel uv oldHandle newHandle scs before observed with
                                                                  | none => rfl
                                                                  | some attached =>
                                                                      rw [SourcePruningRecordTypes.recordTypes_inr]
                                                                      rfl

end Prefix

variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]

/-- Add the legacy ordinary scan only after an attached cache and accepted singleton Right event. -/
noncomputable def finish
    (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Constraint))
    (r n p h k uv : Nat) : Result width Typing → Result width Typing
  | .narrowed checked prepared caller queries action (some after)
      (some [.ok ((false, updated), callbackCore)]) none =>
      .narrowed checked prepared caller queries action (some after)
        (some [.ok ((false, updated), callbackCore)])
        (some (SourcePruningEnumerationNativeOrdinary.run checkEmpty r n p h k uv edgesOf caller after queries))
  | observed => observed

/-- Retain the original selected-step observation with its legacy ordinary continuation. -/
noncomputable def run
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (checkEmpty : Bool) (edgesOf : Node → List (EdgeValue Symbol Constraint))
    (stop : Option (Metadata Typing → Nat → Bool))
    (order : Metadata Typing → List Nat → Option Nat) (metadata : Metadata Typing)
    (readFuel checkFuel nativeFuel representativeFuel indexFuel callbackFuel r n p h k uv : Nat)
    (caller : Caller width) (before : Cached) (queries : Queries) : Result width Typing :=
  finish checkEmpty edgesOf r n p h k uv
    (runPrefix holeKey fits admits graph templates stop order metadata readFuel checkFuel nativeFuel
      representativeFuel indexFuel callbackFuel uv caller before queries)

end MicroCFTA.SourcePruningEnumerationSelectedStep
