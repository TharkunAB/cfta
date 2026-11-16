import MicroCFTA.SourcePruningEnumerationSharedEagerNoneBuckets
import MicroCFTA.SourcePruningEnumerationSelectedPreparation

namespace MicroCFTA.SourcePruningEnumerationPreparationNoneBuckets
open EnumerationState EnumerationCorrectness EnumerationSchedule
open SourcePruningEnumerationSharedEagerNoneBuckets
open SourcePruningEnumerationNodes
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => InternedConstructorTemplates.Value Symbol Constraint
local notation "Native" => InternedConstructorTemplates.State Symbol Constraint
local notation "Core" => EnumerationState.State Symbol Constraint
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
set_option autoImplicit false
variable {width : Nat}
attribute [local instance] SourcePruningEnumerationEntry.entryMonadList

/-- Actual selected entry changes ancestry and compression, but no stored value. -/
theorem entry_values (heap : Native) (fuel uv : Nat) (before after : Core)
    (result : Nat × Nat × List Suspended × Node)
    (actual : Success (SourcePruningEnumerationEntry.enter heap fuel uv) before result after) :
    after.values = before.values := by
  unfold SourcePruningEnumerationEntry.enter at actual
  obtain ⟨value, middle, reading, continued⟩ := (success_bind _ _ _ _ _).mp actual
  have readValues : middle.values = before.values := by
    obtain ⟨found, _lookup, _stored, rfl⟩ := (getValue_success fuel uv before middle value).mp reading
    rfl
  cases value with
  | eliminated | enumerated _ => simp [Success, reject, ExceptT.run] at continued
  | unenumerated node scs =>
      cases node with
      | none => simp [Success, reject, ExceptT.run] at continued
      | some handle =>
          obtain ⟨target, compressed, represented, final⟩ := (success_bind _ _ _ _ _).mp continued
          have compressedValues : compressed.values = middle.values := by
            obtain ⟨found, _lookup, _same, rfl⟩ :=
              (representative_success fuel uv middle compressed target).mp represented
            rfl
          cases decoded : lookupNode heap handle with
          | none =>
              simp only [decoded] at final
              exact (success_failure .unresolvedReference compressed after result final).elim
          | some decodedValue =>
              simp only [decoded] at final
              obtain ⟨token, written, writing, finished⟩ := (success_bind _ _ _ _ _).mp final
              cases token
              have shape := (EnumerationDriver.modify_success _ compressed written).mp writing
              have writtenValues : written.values = compressed.values := by rw [shape]
              obtain ⟨_resultSame, afterSame⟩ := (success_pure _ result written after).mp finished
              subst after
              exact writtenValues.trans (compressedValues.trans readValues)

/-- Every actual preparation enum snapshot retains empty missing-domain buckets. -/
theorem preparation_none_buckets [DecidableEq (InternedConstructorTemplates.EdgeKey Symbol Constraint)]
    (entryFuel nativeFuel uv : Nat) (caller : Caller width) (before : Cached)
    (initial : NoneBucketsEmpty before.core) :
    ∀ state ∈ rawCores (SourcePruningEnumerationSelectedPreparation.run entryFuel nativeFuel uv caller before).1,
      NoneBucketsEmpty state := by
  change ∀ state ∈ rawCores (ExceptT.run (SourcePruningEnumerationEntry.enter
    caller.checked.native.machine.heap entryFuel uv before.core)), NoneBucketsEmpty state
  intro state member
  obtain ⟨row, selected, reached⟩ := List.mem_flatMap.mp member
  cases row with
  | error message => cases reached
  | ok pair =>
      obtain ⟨result, after⟩ := pair
      have same := List.mem_singleton.mp reached
      subst state
      exact none_buckets_of_values_eq before.core after initial
        (entry_values caller.checked.native.machine.heap entryFuel uv before.core after result selected)

end MicroCFTA.SourcePruningEnumerationPreparationNoneBuckets
