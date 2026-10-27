import MicroCFTA.SourcePruningEnumerationRestart
import MicroCFTA.SourcePruningEnumerationNativeLanguage
import MicroCFTA.EnumerationProgress

/-!
# Native restart progress from actual strict pending paths

Canonical native waiting counts identify every blocking suspended reference.
Proper pending paths make each blocker a strict subtree dependency.
A finite complete assignment excludes a cycle of those dependencies.
The structural ProperState premise is separate from the recursive Packet.
-/
namespace MicroCFTA.SourcePruningEnumerationRestart
open Language Fragments EnumerationState EnumerationCorrectness EnumerationSchedule EnumerationProgress
open SourcePruningEnumerationNodes SourcePruningEnumerationObservation
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Metadata" => SourcePruningRecordTypes.Metadata
variable {Typing : Type} {width : Nat}

/-- A native model cannot leave all candidates blocked when stored references follow strict paths. -/
theorem not_stuck_of_proper
    (formulas : SourceGuards.Formulas FullSyntax.Formula)
    (solver : SourceGuards.Entailment FullSyntax.Formula)
    (stop : Option (Metadata Typing → Nat → Bool))
    (order : Metadata Typing → List Nat → Option Nat) (metadata : Metadata Typing)
    (caller : Caller width) (before : Cached)
    (valid : SourcePruningEnumerationNativeBranchCompletion.CacheValid caller before)
    (safe : Safe before.core) (proper : ProperState before.core)
    (ambient : InternedGuardedLanguage.Env Symbol)
    (residualMeaning : Constraint → Term Symbol → Prop) (assignment : Nat → Term Symbol)
    (satisfied : Satisfies
      (SourcePruningEnumerationNativeLanguage.handles (SourceEqualityPCSGuard.holds formulas solver)
        ambient caller.checked.native.machine.heap)
      residualMeaning assignment before.core) :
    decision stop order metadata before ≠ some .stuck := by
  intro stuck
  have picked : EnumerationPureSelection.next (order metadata) before = .stuck := by
    cases stop with
    | none => exact Option.some.inj stuck
    | some rule =>
        simp only [decision] at stuck
        split at stuck
        · cases stuck
        · exact Option.some.inj stuck
  have noOffered : EnumerationPureSelection.find before = some [] := by
    unfold EnumerationPureSelection.next at picked
    cases found : EnumerationPureSelection.find before with
    | none => simp only [found, pickNext] at picked
    | some offered =>
        cases offered with
        | nil => exact found
        | cons first rest =>
            cases preferred : order metadata (first :: rest) with
            | none => simp only [found, pickNext, preferred] at picked
            | some uv =>
                by_cases member : uv ∈ first :: rest <;>
                  simp only [found, pickNext, preferred, member, ↓reduceIte] at picked
  let candidates := EnumerationIndexSelection.candidates before
  have nonempty : candidates ≠ [] := by
    intro empty
    simp only [EnumerationPureSelection.find, ← show EnumerationIndexSelection.candidates before = candidates from rfl,
      empty, List.isEmpty_nil, ↓reduceIte] at noOffered
  have filtered : candidates.filter (fun uv => (before.waiting uv).isNone) = [] := by
    simpa [EnumerationPureSelection.find, candidates, nonempty] using noOffered
  obtain ⟨roots, paths, _storage, realized, counts, flags⟩ := valid
  apply strict_dependency_stuck_impossible candidates nonempty assignment
  intro target candidateMember
  have blocked : before.waiting target ≠ none := by
    intro absent
    have offered : target ∈ candidates.filter (fun uv => (before.waiting uv).isNone) :=
      List.mem_filter.mpr ⟨candidateMember, by simp [absent]⟩
    simp only [filtered, List.not_mem_nil] at offered
  obtain ⟨value, present, sc, listed, sameRoot⟩ :=
    (EnumerationCanonicalWaiting.support_exact roots before.core.values before.waiting counts target).mp blocked
  obtain ⟨source, stored⟩ := List.mem_iff_getElem?.mp present
  have payload := proper value present
  cases value with
  | eliminated | enumerated fragment => cases listed
  | unenumerated node scs =>
      cases node with
      | none =>
          have empty : scs = [] := payload
          simp only [references, empty, List.not_mem_nil] at listed
      | some handle =>
          have member : sc ∈ scs := listed
          obtain ⟨path, pathMember, strict⟩ := proper_path sc.trie (payload sc member)
          obtain ⟨native, decoded, _available, _closed⟩ := realized source handle scs stored
          have nonemptyScs : scs ≠ [] := by
            intro empty
            simp only [empty, List.not_mem_nil] at member
          have nativeCandidate : SourcePruningEnumerationNativeIndex.candidate
              caller.checked.native.machine.heap (.unenumerated (some handle) scs) = some true := by
            simp [SourcePruningEnumerationNativeIndex.candidate, decoded, nonemptyScs]
          have sourceFlag := flags source
          rw [stored, Option.getD_some] at sourceFlag
          have expandable : before.expandable source = true :=
            Option.some.inj (sourceFlag.symm.trans nativeCandidate)
          have inside : source < before.core.counter := by
            rw [safe.1.aligned]
            exact (List.getElem?_eq_some_iff.mp stored).1
          have sourceMember : source ∈ candidates := by
            exact List.mem_filter.mpr ⟨List.mem_range.mpr inside, expandable⟩
          have slotHolds := satisfied.1.2 source
          rw [heap, stored, Option.getD_some] at slotHolds
          have suspended : Suspended.Holds assignment (assignment source) sc :=
            slotHolds.2 _ (List.mem_map.mpr ⟨sc, member, rfl⟩)
          obtain ⟨size, reached⟩ := paths sc.var
          have assigned : assignment sc.var = assignment target := by
            rw [←sameRoot]
            exact satisfied.1.1 sc.var (roots sc.var) (UnionFind.sameClass_root reached)
          exact ⟨source, sourceMember, path, strict,
            by simpa only [assigned] using suspended path pathMember⟩

end MicroCFTA.SourcePruningEnumerationRestart
