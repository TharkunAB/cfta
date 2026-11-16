import MicroCFTA.SourcePruningEnumerationSelectedStep
import MicroCFTA.SourceCurrentRequiredUnionNormalRead

set_option autoImplicit false

namespace MicroCFTA.SourcePruningEnumerationSelectedPrefixUnionNormal
open EnumerationState InternedConstructorTemplates
open SourcePruningEnumerationNodes
open SourceCurrentAllocatedQueryMemo (advancePhysical)
open SourceCurrentRequiredUnionNormal (UnionNormal)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Core" => EnumerationState.State Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Queries" => SourceEndpointMemo.Memos
local notation "Metadata" => SourcePruningRecordTypes.Metadata
variable {Typing Key : Type} {width : Nat}
variable [DecidableEq (EdgeKey Symbol Constraint)]

private theorem narrowAt_unionNormal
    (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (fuel : Nat) (key : Key) (value : Node)
    (heap : InternedConstructorTemplates.State Symbol Constraint) (normal : UnionNormal heap) :
    UnionNormal (SourcePruningNativeView.narrowAt fits admits fuel key value heap).state := by
  have retained := SourceCurrentRequiredUnionNormalRead.nodeEdges fuel value heap normal
  unfold SourcePruningNativeView.narrowAt
  cases exposed : MergedFreshOrdinaryExposure.nodeEdges fuel value heap with
  | done rows after =>
      have afterNormal : UnionNormal after := by
        simpa only [exposed, MergedSourceExposure.Result.state] using retained
      exact SourceCurrentRequiredUnionNormal.node
        (rows.filter (SourcePruningNativeView.keeps fits admits key)) after afterNormal
  | unresolved name after =>
      simpa only [exposed, MergedSourceExposure.Result.state, MergedSourceComparison.Result.state] using retained
  | pending key after =>
      simpa only [exposed, MergedSourceExposure.Result.state, MergedSourceComparison.Result.state] using retained
  | exhausted after =>
      simpa only [exposed, MergedSourceExposure.Result.state, MergedSourceComparison.Result.state] using retained

private theorem narrow_unionNormal
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (metadata : Metadata Typing) (fuel uv : Nat) (value : Node)
    (heap : InternedConstructorTemplates.State Symbol Constraint) (normal : UnionNormal heap) :
    UnionNormal (SourcePruningOuterNarrow.narrow holeKey fits admits metadata fuel uv value heap).state := by
  cases value with
  | mu => exact normal
  | empty | reference | node | union =>
      by_cases inTypes : metadata.types.contains uv = true
      · simpa only [SourcePruningOuterNarrow.narrow, ite_eq_left inTypes,
          MergedSourceComparison.Result.state] using normal
      · simp only [SourcePruningOuterNarrow.narrow, ite_eq_right inTypes]
        exact narrowAt_unionNormal fits admits fuel (holeKey metadata.typing uv) _ heap normal

private theorem prepare_unionNormal
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (metadata : Metadata Typing) (nativeFuel representativeFuel uv oldHandle : Nat)
    (scs : List Suspended) (value : Node)
    (heap : InternedConstructorTemplates.State Symbol Constraint) (normal : UnionNormal heap) :
    UnionNormal (SourcePruningEnumerationAction.prepare (EnumGuard := Constraint)
      holeKey fits admits metadata nativeFuel representativeFuel uv oldHandle scs value heap).state := by
  have retained := narrow_unionNormal holeKey fits admits metadata nativeFuel uv value heap normal
  unfold SourcePruningEnumerationAction.prepare SourcePruningEnumerationAction.prepareWithNarrow
  cases narrowed : SourcePruningOuterNarrow.narrow holeKey fits admits metadata nativeFuel uv value heap with
  | failed fault after =>
      simpa only [narrowed, MergedSourceComparison.Result.state] using retained
  | done result after =>
      simpa only [narrowed, MergedSourceComparison.Result.state] using retained

/-- Every actual selected prefix retains union normality at each reached native heap. -/
theorem runPrefix_unionNormal
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool) (admits : Key → Node → Bool)
    (graph : Graph Symbol Constraint) (templates : List (Template.Pattern Symbol))
    (stop : Option (Metadata Typing → Nat → Bool)) (order : Metadata Typing → List Nat → Option Nat)
    (metadata : Metadata Typing)
    (readFuel checkFuel nativeFuel representativeFuel indexFuel callbackFuel uv : Nat)
    (caller : Caller width) (before : Cached) (queries : Queries)
    (normal : UnionNormal caller.checked.native.machine.heap) :
    match SourcePruningEnumerationSelectedStep.runPrefix holeKey fits admits graph templates stop order metadata
      readFuel checkFuel nativeFuel representativeFuel indexFuel callbackFuel uv caller before queries with
    | .stopped _ _ | .parked _ _ _ => UnionNormal caller.checked.native.machine.heap
    | .narrowed _ prepared reached _ _ _ _ _ =>
        UnionNormal prepared.state ∧ UnionNormal reached.checked.native.machine.heap
 := by
  classical
  by_cases readable : ∃ (oldHandle : Nat) (scs : List Suspended) (readAfter : Core),
      ExceptT.run (getValue readFuel uv before.core) =
        [.ok (.unenumerated (some oldHandle) scs, readAfter)]
  · obtain ⟨oldHandle, scs, readAfter, reading⟩ := readable
    by_cases fresh : ∃ checked : Core,
        ExceptT.run (SourcePruningEnumerationRecursion.checkRepeated caller.checked.native.machine.heap
          checkFuel uv oldHandle scs readAfter) = [.ok (false, checked)]
    · obtain ⟨checked, checking⟩ := fresh
      cases oldDecoded : lookupNode caller.checked.native.machine.heap oldHandle with
      | none =>
          simpa only [SourcePruningEnumerationSelectedStep.runPrefix,
            SourcePruningEnumerationSelectedStep.runPrefixWithNarrow, reading, checking, oldDecoded] using normal
      | some oldValue =>
          let prepared := SourcePruningEnumerationAction.prepare (EnumGuard := Constraint) holeKey fits admits metadata
            nativeFuel representativeFuel uv oldHandle scs oldValue caller.checked.native.machine.heap
          have preparedNormal : UnionNormal prepared.state :=
            prepare_unionNormal holeKey fits admits metadata nativeFuel representativeFuel uv oldHandle scs
              oldValue caller.checked.native.machine.heap normal
          have reachedFacts : UnionNormal prepared.state ∧ UnionNormal
              (SourceCurrentAllocatedPartialState.advance caller
                (advancePhysical caller.checked ⟨prepared.state, caller.checked.operations⟩)
                caller.fourth caller.merge).checked.native.machine.heap :=
            ⟨preparedNormal, preparedNormal⟩
          unfold SourcePruningEnumerationSelectedStep.runPrefix
            SourcePruningEnumerationSelectedStep.runPrefixWithNarrow
          simp only [reading, checking, oldDecoded]
          simp only [← SourcePruningEnumerationAction.prepare_configured_eq]
          dsimp only [prepared] at reachedFacts
          generalize preparedEq : SourcePruningEnumerationAction.prepare (EnumGuard := Constraint) holeKey fits admits metadata
            nativeFuel representativeFuel uv oldHandle scs oldValue caller.checked.native.machine.heap = preparedResult
            at reachedFacts ⊢
          cases preparedResult with
          | failed fault heap => exact reachedFacts
          | done pair heap =>
              obtain ⟨value, action⟩ := pair
              cases action with
              | none => exact reachedFacts
              | some action =>
                  dsimp only
                  generalize rawEq : ExceptT.run (action checked) = rawAction
                  cases rawAction with
                  | nil => exact reachedFacts
                  | cons first rest =>
                      cases first with
                      | error fault => exact reachedFacts
                      | ok pair =>
                          obtain ⟨token, observed⟩ := pair
                          cases token
                          cases rest with
                          | cons another remaining => exact reachedFacts
                          | nil =>
                              cases encoded : encodeNode value with
                              | none => exact reachedFacts
                              | some newHandle =>
                                  dsimp only
                                  cases adapted : SourcePruningEnumerationNarrowAdapter.adapt heap indexFuel
                                      uv oldHandle newHandle scs before observed with
                                  | none => exact reachedFacts
                                  | some attached =>
                                      dsimp only
                                      have recorded : ExceptT.run (SourcePruningRecordTypes.recordTypes
                                          graph templates callbackFuel metadata uv (.inr newHandle) attached.core) =
                                          [.ok ((false, metadata), attached.core)] := by
                                        rw [SourcePruningRecordTypes.recordTypes_inr]
                                        rfl
                                      simp only [recorded]
                                      exact reachedFacts
    · unfold SourcePruningEnumerationSelectedStep.runPrefix
        SourcePruningEnumerationSelectedStep.runPrefixWithNarrow
      simp only [reading]
      generalize checkEq : ExceptT.run (SourcePruningEnumerationRecursion.checkRepeated
        caller.checked.native.machine.heap checkFuel uv oldHandle scs readAfter) = rawCheck
      cases rawCheck with
      | nil => exact normal
      | cons first rest =>
          cases first with
          | error fault => exact normal
          | ok pair =>
              obtain ⟨repeated, checked⟩ := pair
              cases rest with
              | cons another remaining => cases repeated <;> exact normal
              | nil =>
                  cases repeated with
                  | true => exact normal
                  | false => exact (fresh ⟨checked, checkEq⟩).elim
  · have stopped : SourcePruningEnumerationSelectedStep.runPrefix holeKey fits admits graph templates stop order metadata
        readFuel checkFuel nativeFuel representativeFuel indexFuel callbackFuel uv caller before queries =
        .stopped (ExceptT.run (getValue readFuel uv before.core)) none := by
      unfold SourcePruningEnumerationSelectedStep.runPrefix
        SourcePruningEnumerationSelectedStep.runPrefixWithNarrow
      dsimp only
      split
      · exact (readable ⟨_, _, _, by assumption⟩).elim
      · rfl
    rw [stopped]
    exact normal

end MicroCFTA.SourcePruningEnumerationSelectedPrefixUnionNormal
