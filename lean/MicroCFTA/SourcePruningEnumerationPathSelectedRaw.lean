import MicroCFTA.SourcePruningEnumerationPathStorage
import MicroCFTA.SourcePruningEnumerationPathRecordingValues
import MicroCFTA.SourcePruningEnumerationSelectedStep

/-!
# Stored paths in selected raw observations

This source-only draft has not been compiled. The path property covers each
successful raw row. It does not require a singleton or native completion.
-/
namespace MicroCFTA.SourcePruningEnumerationPathSelectedRaw
open EnumerationState EnumerationCorrectness EnumerationSchedule InternedConstructorTemplates
open SourcePruningEnumerationNodes
open SourcePruningEnumerationPathTransport SourcePruningEnumerationPathStorage
local notation "Symbol" => SourcePruningTemplates.Symbol

local instance rawMonadList : Monad List where
  pure value := [value]
  bind values continuation := values.flatMap continuation

/-- Every successful row retains the supplied stored path predicate. -/
def RawPaths {Guard α : Type} (P : EqualityTrie.Path → Prop)
    (raw : List (Except EnumerationState.Error (α × EnumerationState.State Symbol Guard))) : Prop :=
  ∀ result after, Except.ok (result, after) ∈ raw → StatePaths P after

/-- An actual value read preserves paths and exposes a bucket with the same paths. -/
theorem getValue_paths {Guard : Type} {P : EqualityTrie.Path → Prop}
    (fuel uv : Nat) (before after : EnumerationState.State Symbol Guard) (value : UVarValue Symbol)
    (paths : StatePaths P before) (success : Success (getValue fuel uv) before value after) :
    StatePaths P after ∧ BucketPaths P (references value) := by
  obtain ⟨found, _found, stored, rfl⟩ := (getValue_success fuel uv before after value).mp success
  exact ⟨paths, paths value (List.mem_of_getElem? stored)⟩

/-- A repeated-key check preserves paths even when it clears the stored bucket. -/
theorem checkRepeated_paths {EnumGuard NativeGuard : Type} {P : EqualityTrie.Path → Prop}
    (heap : InternedConstructorTemplates.State Symbol NativeGuard)
    (fuel uv handle : Nat) (scs : List Suspended)
    (before after : EnumerationState.State Symbol EnumGuard) (result : Bool)
    (paths : StatePaths P before)
    (success : Success (SourcePruningEnumerationRecursion.checkRepeated heap fuel uv handle scs)
      before result after) : StatePaths P after := by
  cases decoded : lookupNode heap handle with
  | none =>
      simp only [SourcePruningEnumerationRecursion.checkRepeated, decoded] at success
      exact False.elim (success_failure .unresolvedReference before after result success)
  | some value =>
      cases boundary : MergedOrdinaryHeight.recursiveBoundary value with
      | false =>
          simp only [SourcePruningEnumerationRecursion.checkRepeated, decoded, boundary] at success
          obtain ⟨_result, rfl⟩ := (success_pure false result before after).mp success
          exact paths
      | true =>
          simp only [SourcePruningEnumerationRecursion.checkRepeated, decoded, boundary, ↓reduceIte] at success
          obtain ⟨root, resolved, reading, continued⟩ := (success_bind _ _ _ _ _).mp success
          have resolvedPaths := representative_paths fuel uv root before resolved paths reading
          obtain ⟨snapshot, unchanged, readState, finished⟩ := (success_bind _ _ _ _ _).mp continued
          obtain ⟨snapshotSame, unchangedSame⟩ := (EnumerationDriver.get_success resolved unchanged snapshot).mp readState
          subst snapshot
          subst unchanged
          by_cases repeated : recursionKey handle scs ∈ resolved.recursionAncestry root
          · simp only [ite_eq_left repeated] at finished
            obtain ⟨⟨⟩, written, writing, final⟩ := (success_bind _ _ _ _ _).mp finished
            obtain ⟨_result, rfl⟩ := (success_pure true result written after).mp final
            exact setValue_paths root (.unenumerated (some handle) []) resolved after
              resolvedPaths (by simp [BucketPaths, references]) writing
          · simp only [ite_eq_right repeated] at finished
            obtain ⟨_result, rfl⟩ := (success_pure false result resolved after).mp finished
            exact resolvedPaths

/-- Every actual prepared action preserves paths from the unchanged inherited bucket. -/
theorem prepare_actions_paths {EnumGuard NativeGuard Typing Key : Type}
    [DecidableEq (EdgeKey Symbol NativeGuard)] {P : EqualityTrie.Path → Prop}
    (holeKey : Typing → Nat → Key) (fits : Key → Symbol → Bool)
    (admits : Key → Value Symbol NativeGuard → Bool)
    (metadata : SourcePruningRecordTypes.Metadata Typing)
    (nativeFuel representativeFuel uv oldHandle : Nat) (scs : List Suspended)
    (oldValue : Value Symbol NativeGuard) (heap : InternedConstructorTemplates.State Symbol NativeGuard)
    (inherited : BucketPaths P scs) :
    match SourcePruningEnumerationAction.prepare (EnumGuard := EnumGuard)
        holeKey fits admits metadata nativeFuel representativeFuel uv oldHandle scs oldValue heap with
    | .failed _ _ => True
    | .done (_, candidate) _ =>
        ∀ action, candidate = some action →
          ∀ before after, StatePaths P before → Success action before () after → StatePaths P after := by
  have writes (newHandle : Nat) :
      ∀ action,
        some (if newHandle = oldHandle then pure () else
          representative representativeFuel uv >>= fun selected =>
            setValue selected (.unenumerated (some newHandle) scs)) = some action →
        ∀ (before after : EnumerationState.State Symbol EnumGuard),
          StatePaths P before → Success action before () after → StatePaths P after := by
    intro action same before after paths success
    have equal := Option.some.inj same
    cases equal
    by_cases identical : newHandle = oldHandle
    · simp only [ite_eq_left identical] at success
      obtain ⟨_result, rfl⟩ := (success_pure () () before after).mp success
      exact paths
    · simp only [ite_eq_right identical] at success
      obtain ⟨selected, resolved, reading, written⟩ := (success_bind _ _ _ _ _).mp success
      exact setValue_paths selected (.unenumerated (some newHandle) scs) resolved after
        (representative_paths representativeFuel uv selected before resolved paths reading)
        inherited written
  cases narrowed : SourcePruningOuterNarrow.narrow holeKey fits admits metadata nativeFuel uv oldValue heap with
  | failed fault nextHeap =>
      simp only [SourcePruningEnumerationAction.prepare, narrowed]
  | done value nextHeap =>
      cases value with
      | empty =>
          simp only [SourcePruningEnumerationAction.prepare, narrowed]
          intro action same before after _paths success
          have equal := Option.some.inj same
          cases equal
          simp only [Success, EnumerationState.reject, ExceptT.run, List.not_mem_nil] at success
      | reference name =>
          simp only [SourcePruningEnumerationAction.prepare, narrowed, SourcePruningEnumerationNodes.encodeNode]
          intro action impossible
          cases impossible
      | node entry edges depth free =>
          simpa only [SourcePruningEnumerationAction.prepare, narrowed, SourcePruningEnumerationNodes.encodeNode]
            using writes (entry.identity + 1)
      | union entry members depth free =>
          simpa only [SourcePruningEnumerationAction.prepare, narrowed, SourcePruningEnumerationNodes.encodeNode]
            using writes (entry.identity + 1)
      | mu entry body depthShape ordinaryShape =>
          simpa only [SourcePruningEnumerationAction.prepare, narrowed, SourcePruningEnumerationNodes.encodeNode]
            using writes (entry.identity + 1)

/-- A prefix keeps paths in every retained core and successful raw row. -/
def SelectedPrefixPaths {Typing : Type} {width : Nat} (P : EqualityTrie.Path → Prop) :
    SourcePruningEnumerationSelectedStep.Result width Typing → Prop
  | .stopped read checked =>
      RawPaths P read ∧ ∀ rows, checked = some rows → RawPaths P rows
  | .parked checked candidate raw =>
      StatePaths P checked ∧
      (∀ after, candidate = some after → StatePaths P after.core) ∧
      ∀ rows, raw = some rows → RawPaths P rows
  | .narrowed checked _ _ _ action candidate right ordinary =>
      StatePaths P checked ∧
      (∀ rows, action = some rows → RawPaths P rows) ∧
      (∀ after, candidate = some after → StatePaths P after.core) ∧
      (∀ rows, right = some rows → RawPaths P rows) ∧ ordinary = none

/-- Restart keeps the supplied input core in every actual successful row. -/
theorem restart_paths {Typing : Type} {P : EqualityTrie.Path → Prop}
    (stop : Option (SourcePruningRecordTypes.Metadata Typing → Nat → Bool))
    (order : SourcePruningRecordTypes.Metadata Typing → List Nat → Option Nat)
    (metadata : SourcePruningRecordTypes.Metadata Typing)
    (cached : EnumerationExpandableIndex.Cached Symbol (SourceSymbolicIndex.Constraint FullSyntax.Formula))
    (before : EnumerationState.State Symbol (SourceSymbolicIndex.Constraint FullSyntax.Formula))
    (paths : StatePaths P before) :
    RawPaths P (ExceptT.run (SourcePruningEnumerationRestart.run stop order metadata cached before)) := by
  intro result after member
  by_cases stuck : SourcePruningEnumerationRestart.decision stop order metadata cached = some .stuck
  · simp only [SourcePruningEnumerationRestart.run, ite_eq_left stuck, ExceptT.run, List.not_mem_nil] at member
  · simp only [SourcePruningEnumerationRestart.run, ite_eq_right stuck, ExceptT.run,
      List.mem_singleton, Except.ok.injEq, Prod.mk.injEq] at member
    obtain ⟨_result, rfl⟩ := member
    exact paths

end MicroCFTA.SourcePruningEnumerationPathSelectedRaw
