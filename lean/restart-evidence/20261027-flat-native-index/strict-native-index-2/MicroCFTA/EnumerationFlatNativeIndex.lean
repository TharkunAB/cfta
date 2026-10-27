import MicroCFTA.EnumerationFlatCached
import MicroCFTA.SourcePruningEnumerationNativeIndex

/-!
# Native cached writes with direct representative reads

The write classifies the actual supplied value. It removes lost occurrences
before it adds gained occurrences. Both folds use current representatives.
No native heap intersection is repeated by this operation.
-/

namespace MicroCFTA.EnumerationFlatNativeIndex

open EnumerationFlatCached
local notation "Symbol" => SourcePruningTemplates.Symbol
variable {EnumGuard NativeGuard : Type}

/-- Count each occurrence at its direct representative in the input forest. -/
def count (forest : FlatUnionFind.Forest) (change : Int)
    (scs : List EnumerationState.Suspended) (waiting : EnumerationWaitingIndex.Waiting) :
    EnumerationWaitingIndex.Waiting :=
  EnumerationCanonicalWaiting.count (FlatUnionFind.root forest) change scs waiting

/-- Related forests supply the earlier finite paths at the exact direct roots. -/
theorem related_roots (related : FlatUnionFind.Represents flat earlier) :
    EnumerationSchedule.Roots earlier (FlatUnionFind.root flat) :=
  fun uv => ⟨_, related uv⟩

/-- One sufficient old bound counts every occurrence for every change and map. -/
theorem count_stable (related : FlatUnionFind.Represents flat earlier)
    (scs : List EnumerationState.Suspended) :
    ∃ fuel, ∀ extra change waiting,
      SourcePruningEnumerationNativeIndex.count (fuel + extra) earlier change scs waiting =
        some (count flat change scs waiting) :=
  SourcePruningEnumerationNativeIndex.count_complete earlier (FlatUnionFind.root flat)
    (related_roots related) scs

/-- Update the raw slot, its expandable flag and the two ordered count folds. -/
def write (heap : InternedConstructorTemplates.State Symbol NativeGuard)
    (target : Nat) (value : EnumerationState.UVarValue Symbol)
    (gained lost : List EnumerationState.Suspended) (before : Cached Symbol EnumGuard) :
    Option (Cached Symbol EnumGuard) :=
  (SourcePruningEnumerationNativeIndex.candidate heap value).map fun flag =>
    ⟨{before.core with values := before.core.values.set target value},
      fun other => if other = target then flag else before.expandable other,
      count before.core.representatives 1 gained
        (count before.core.representatives (-1) lost before.waiting)⟩

/-- Optional writes fail together or return related complete caches. -/
def WritesRelated (flat : Option (Cached Symbol EnumGuard))
    (earlier : Option (EnumerationExpandableIndex.Cached Symbol EnumGuard)) : Prop :=
  match flat, earlier with
  | none, none => True
  | some flat, some earlier => Related flat earlier
  | _, _ => False

/-- One shared sufficient bound preserves the actual native write and both indexes. -/
theorem write_stable (related : Related flat earlier)
    (heap : InternedConstructorTemplates.State Symbol NativeGuard)
    (target : Nat) (value : EnumerationState.UVarValue Symbol)
    (gained lost : List EnumerationState.Suspended) :
    ∃ fuel, ∀ extra, WritesRelated (write heap target value gained lost flat)
      (SourcePruningEnumerationNativeIndex.write heap (fuel + extra) target value gained lost earlier) := by
  obtain ⟨lostFuel, lostRun⟩ := count_stable related.core.representatives lost
  obtain ⟨gainedFuel, gainedRun⟩ := count_stable related.core.representatives gained
  refine ⟨lostFuel + gainedFuel, ?_⟩
  intro extra
  have removed := lostRun (gainedFuel + extra) (-1) earlier.waiting
  have saved := gainedRun (lostFuel + extra) 1
    (count flat.core.representatives (-1) lost earlier.waiting)
  rw [← Nat.add_assoc] at removed
  have order : gainedFuel + (lostFuel + extra) = lostFuel + gainedFuel + extra := by omega
  rw [order] at saved
  cases classified : SourcePruningEnumerationNativeIndex.candidate heap value with
  | none => simp [write, SourcePruningEnumerationNativeIndex.write, classified, WritesRelated]
  | some flag =>
      simp only [write, classified, Option.map_some,
        SourcePruningEnumerationNativeIndex.write, Option.bind_some, removed, saved]
      change Related _ _
      refine ⟨?_, ?_, ?_⟩
      · exact ⟨related.core.valid, related.core.representatives, related.core.counter,
          congrArg (fun values => values.set target value) related.core.values,
          related.core.obligations, related.core.recursionAncestry, related.core.expansionAncestry⟩
      · rw [related.expandable]
      · rw [related.waiting]

/-- Native flags and representative counts describe the same complete slot array. -/
structure Correct (heap : InternedConstructorTemplates.State Symbol NativeGuard)
    (state : Cached Symbol EnumGuard) : Prop where
  /-- The fresh identifier follows the last stored raw slot. -/
  aligned : state.core.counter = state.core.values.length
  /-- Every slot has its actual decoded expandable flag. -/
  expandable : ∀ uv, SourcePruningEnumerationNativeIndex.candidate heap
    ((state.core.values[uv]?).getD .eliminated) = some (state.expandable uv)
  /-- Every waiting count uses the current representative of each occurrence. -/
  waiting : EnumerationCanonicalWaiting.Correct (FlatUnionFind.root state.core.representatives)
    state.core.values state.waiting

/-- Earlier native index invariants transfer at the same supplied heap and roots. -/
theorem correct_of_related (related : Related flat earlier)
    (heap : InternedConstructorTemplates.State Symbol NativeGuard) (roots : Nat → Nat)
    (paths : EnumerationSchedule.Roots earlier.core.representatives roots)
    (aligned : earlier.core.counter = earlier.core.values.length)
    (flags : ∀ uv, SourcePruningEnumerationNativeIndex.candidate heap
      ((earlier.core.values[uv]?).getD .eliminated) = some (earlier.expandable uv))
    (waiting : EnumerationCanonicalWaiting.Correct roots earlier.core.values earlier.waiting) :
    Correct heap flat := by
  have sameRoots : FlatUnionFind.root flat.core.representatives = roots := by
    funext uv
    obtain ⟨size, path⟩ := paths uv
    exact (UnionFind.reaches_unique (related.core.representatives uv) path).1
  refine ⟨?_, ?_, ?_⟩
  · rw [related.core.counter, related.core.values]
    exact aligned
  · intro uv
    rw [related.core.values, related.expandable]
    exact flags uv
  · rw [sameRoots, related.core.values, related.waiting]
    exact waiting

/-- Replacing all old references by all new references derives both native indexes. -/
theorem write_correct (heap : InternedConstructorTemplates.State Symbol NativeGuard)
    (before after : Cached Symbol EnumGuard) (correct : Correct heap before)
    (target : Nat) (old value : EnumerationState.UVarValue Symbol)
    (stored : before.core.values[target]? = some old)
    (done : write heap target value (EnumerationSchedule.references value)
      (EnumerationSchedule.references old) before = some after) : Correct heap after := by
  cases classified : SourcePruningEnumerationNativeIndex.candidate heap value with
  | none => simp [write, classified] at done
  | some flag =>
      simp [write, classified] at done
      subst after
      refine ⟨by simpa using correct.aligned, ?_, ?_⟩
      · intro uv
        by_cases same : uv = target
        · subst uv
          have bound := (List.getElem?_eq_some_iff.mp stored).1
          simpa only [List.getElem?_set_self bound, Option.getD_some, ↓reduceIte] using classified
        · simpa only [List.getElem?_set_ne (Ne.symm same), ite_eq_right same]
            using correct.expandable uv
      · exact EnumerationCanonicalWaiting.replace_correct
          (FlatUnionFind.root before.core.representatives) before.core.values target old value
          stored before.waiting correct.waiting

end MicroCFTA.EnumerationFlatNativeIndex
