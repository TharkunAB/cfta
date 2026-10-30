import MicroCFTA.SourcePruningEnumerationPathStorage
import MicroCFTA.SourcePruningEnumerationSelectedPreparation

/-!
# Stored paths at every actual Prepared entry row

Entry reads change representatives and expansion ancestry.
They do not change stored suspended buckets. The raw
entry claim does not require native normalization to complete.
-/
namespace MicroCFTA.SourcePruningEnumerationPathPreparedEntry
open EnumerationState EnumerationCorrectness InternedConstructorTemplates
open SourcePruningEnumerationPathTransport
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
variable {EnumGuard NativeGuard : Type} {P : EqualityTrie.Path → Prop}

private theorem getValue_paths (fuel uv : Nat)
    (before after : EnumerationState.State Symbol EnumGuard) (value : UVarValue Symbol)
    (paths : StatePaths P before)
    (observed : Success (getValue fuel uv) before value after) : StatePaths P after := by
  obtain ⟨_found, _lookup, _stored, rfl⟩ := (getValue_success fuel uv before after value).mp observed
  exact paths

/-- Every successful entry row retains the original stored-path predicate. -/
theorem enter_paths
    (heap : InternedConstructorTemplates.State Symbol NativeGuard) (fuel uv : Nat)
    (before after : EnumerationState.State Symbol EnumGuard)
    (result : Nat × Nat × List Suspended × Value Symbol NativeGuard)
    (paths : StatePaths P before)
    (observed : Success (SourcePruningEnumerationEntry.enter heap fuel uv) before result after) :
    StatePaths P after := by
  unfold SourcePruningEnumerationEntry.enter at observed
  obtain ⟨value, readState, read, continued⟩ := (success_bind _ _ _ _ _).mp observed
  have readPaths := getValue_paths fuel uv before readState value paths read
  cases value with
  | eliminated => simp [Success, EnumerationState.reject, ExceptT.run] at continued
  | enumerated fragment => simp [Success, EnumerationState.reject, ExceptT.run] at continued
  | unenumerated node scs =>
      cases node with
      | none => simp [Success, EnumerationState.reject, ExceptT.run] at continued
      | some handle =>
          obtain ⟨target, rootState, rooted, continued⟩ := (success_bind _ _ _ _ _).mp continued
          have rootPaths := SourcePruningEnumerationPathStorage.representative_paths
            fuel uv target readState rootState readPaths rooted
          cases decoded : SourcePruningEnumerationNodes.lookupNode heap handle with
          | none =>
              exact False.elim ((success_failure _ _ _ _)
                (by simpa only [decoded] using continued))
          | some decodedValue =>
              simp only [decoded] at continued
              obtain ⟨ignored, updated, modified, returned⟩ := (success_bind _ _ _ _ _).mp continued
              cases ignored
              have updatedSame := (EnumerationDriver.modify_success _ _ _).mp modified
              have afterSame := (success_pure (target, handle, scs, decodedValue) result updated after).mp returned
              rw [afterSame.2, updatedSame]
              exact rootPaths

/-- Every raw preparation row retains paths, including a row with an incomplete native result. -/
theorem raw_paths {width : Nat} [DecidableEq (EdgeKey Symbol Constraint)]
    (entryFuel nativeFuel uv : Nat) (caller : Caller width) (before : Cached)
    (result : Nat × Nat × List Suspended × Node) (after : EnumerationState.State Symbol Constraint)
    (paths : StatePaths P before.core)
    (observed : Except.ok (result, after) ∈
      (SourcePruningEnumerationSelectedPreparation.run entryFuel nativeFuel uv caller before).1) :
    StatePaths P after := by
  change Success (SourcePruningEnumerationEntry.enter caller.checked.native.machine.heap
    entryFuel uv) before.core result after at observed
  exact enter_paths _ entryFuel uv before.core after result paths observed

end MicroCFTA.SourcePruningEnumerationPathPreparedEntry
