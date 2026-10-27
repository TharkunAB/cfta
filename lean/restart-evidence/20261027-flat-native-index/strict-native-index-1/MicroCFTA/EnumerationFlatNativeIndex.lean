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

end MicroCFTA.EnumerationFlatNativeIndex
