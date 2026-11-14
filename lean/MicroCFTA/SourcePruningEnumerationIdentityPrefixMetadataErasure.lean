import MicroCFTA.SourcePruningEnumerationSelectedStep

set_option autoImplicit false

/-!
# Metadata erasure in the actual identity-selected prefix

The projection preserves every field except metadata.
It covers the selected prefix at the same actual inputs and fuels.
It does not cover an eager worker or a Haskell execution.
-/
namespace MicroCFTA.SourcePruningEnumerationIdentityPrefixMetadataErasure
open EnumerationState InternedConstructorTemplates
open SourcePruningEnumerationNodes
open SourcePruningEnumerationSelectedStep (Result runPrefixWithNarrow)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "NativeHeap" => InternedConstructorTemplates.State Symbol Constraint
local notation "Core" => EnumerationState.State Symbol Constraint
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Queries" => SourceEndpointMemo.Memos
local notation "Metadata" => SourcePruningRecordTypes.Metadata
variable {width : Nat}

/-- Replace metadata with the canonical Unit record. -/
def eraseMetadata {Typing : Type} (_metadata : Metadata Typing) : Metadata Unit :=
  ⟨[], [], [], ()⟩

/-- Erase metadata in the existing prefix result and retain every other field. -/
def erasePrefix {Typing : Type} : Result width Typing → Result width Unit
  | .stopped read checked => .stopped read checked
  | .parked checked candidate raw =>
      .parked checked candidate (raw.map fun rows => rows.map fun
        | .error fault => .error fault
        | .ok ((metadata, next), after) => .ok ((eraseMetadata metadata, next), after))
  | .narrowed checked prepared caller queries action candidate right ordinary =>
      .narrowed checked prepared caller queries action candidate
        (right.map fun rows => rows.map fun
          | .error fault => .error fault
          | .ok ((flag, metadata), after) => .ok ((flag, eraseMetadata metadata), after)) ordinary

/-- Identity preparation does not inspect metadata. -/
private theorem prepare_identity_metadata {Typing : Type}
    (metadata : Metadata Typing) (unitMetadata : Metadata Unit)
    (nativeFuel representativeFuel uv oldHandle : Nat) (scs : List Suspended)
    (oldValue : Node) (heap : NativeHeap) :
    SourcePruningEnumerationAction.prepareWithNarrow (EnumGuard := Constraint)
      (fun _ _ _ value heap => .done value heap) metadata nativeFuel representativeFuel
      uv oldHandle scs oldValue heap =
    SourcePruningEnumerationAction.prepareWithNarrow (EnumGuard := Constraint)
      (fun _ _ _ value heap => .done value heap) unitMetadata nativeFuel representativeFuel
      uv oldHandle scs oldValue heap := rfl

/-- Identity prefixes have the same erased observation at the same actual inputs. -/
theorem runPrefix_identity_metadata_erasure {Typing : Type}
    [DecidableEq (EdgeKey Symbol Constraint)]
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (order : List Nat → Option Nat)
    (metadata : Metadata Typing) (unitMetadata : Metadata Unit)
    (readFuel checkFuel nativeFuel representativeFuel indexFuel callbackFuel uv : Nat)
    (caller : Caller width) (before : Cached) (queries : Queries) :
    erasePrefix (runPrefixWithNarrow (fun _ _ _ value heap => .done value heap)
      graph templates none (fun _ candidates => order candidates) metadata
      readFuel checkFuel nativeFuel representativeFuel indexFuel callbackFuel uv caller before queries) =
    erasePrefix (runPrefixWithNarrow (fun _ _ _ value heap => .done value heap)
      graph templates none (fun _ candidates => order candidates) unitMetadata
      readFuel checkFuel nativeFuel representativeFuel indexFuel callbackFuel uv caller before queries) := by
  unfold runPrefixWithNarrow
  dsimp only
  generalize ExceptT.run (getValue readFuel uv before.core) = read
  cases read with
  | nil => rfl
  | cons first rest =>
      cases rest with
      | cons _ _ =>
          cases first with
          | error _ => rfl
          | ok pair =>
              obtain ⟨value, _readAfter⟩ := pair
              cases value with
              | eliminated | enumerated _ => rfl
              | unenumerated handle _ => cases handle <;> rfl
      | nil =>
          cases first with
          | error _ => rfl
          | ok pair =>
              obtain ⟨value, readAfter⟩ := pair
              cases value with
              | eliminated | enumerated _ => rfl
              | unenumerated handle scs =>
                  cases handle with
                  | none => rfl
                  | some oldHandle =>
                      dsimp only
                      generalize ExceptT.run (SourcePruningEnumerationRecursion.checkRepeated
                        caller.checked.native.machine.heap checkFuel uv oldHandle scs readAfter) = check
                      cases check with
                      | nil => rfl
                      | cons first rest =>
                          cases rest with
                          | cons _ _ =>
                              cases first with
                              | error _ => rfl
                              | ok pair =>
                                  obtain ⟨repeated, _checked⟩ := pair
                                  cases repeated <;> rfl
                          | nil =>
                              cases first with
                              | error _ => rfl
                              | ok pair =>
                                  obtain ⟨repeated, checked⟩ := pair
                                  cases repeated with
                                  | true =>
                                      dsimp only
                                      cases SourcePruningEnumerationParkedRestart.adapt
                                          caller.checked.native.machine.heap indexFuel uv oldHandle scs before checked with
                                      | none => rfl
                                      | some parked =>
                                          simp only [erasePrefix, Option.map_some,
                                            SourcePruningEnumerationRestart.run,
                                            SourcePruningEnumerationRestart.decision]
                                          by_cases blocked : some (EnumerationPureSelection.next
                                              (fun candidates => order candidates) parked) = some Next.stuck
                                          all_goals simp [blocked, eraseMetadata, ExceptT.run]
                                  | false =>
                                      cases lookupNode caller.checked.native.machine.heap oldHandle with
                                      | none => rfl
                                      | some oldValue =>
                                          dsimp only
                                          have samePreparation := prepare_identity_metadata metadata unitMetadata
                                            nativeFuel representativeFuel uv oldHandle scs oldValue
                                            caller.checked.native.machine.heap
                                          rw [samePreparation]
                                          generalize SourcePruningEnumerationAction.prepareWithNarrow
                                            (EnumGuard := Constraint)
                                            (fun _ _ _ value heap => .done value heap) unitMetadata
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
                                                      | cons _ _ =>
                                                          cases first with
                                                          | error _ => rfl
                                                          | ok pair =>
                                                              obtain ⟨token, _observed⟩ := pair
                                                              cases token
                                                              rfl
                                                      | nil =>
                                                          cases first with
                                                          | error _ => rfl
                                                          | ok pair =>
                                                              obtain ⟨token, observed⟩ := pair
                                                              cases token
                                                              dsimp only
                                                              cases encodeNode value with
                                                              | none => rfl
                                                              | some newHandle =>
                                                                  dsimp only
                                                                  cases SourcePruningEnumerationNarrowAdapter.adapt heap
                                                                    indexFuel uv oldHandle newHandle scs before observed with
                                                                  | none => rfl
                                                                  | some attached =>
                                                                      simp only [SourcePruningRecordTypes.recordTypes_inr]
                                                                      rfl

end MicroCFTA.SourcePruningEnumerationIdentityPrefixMetadataErasure
