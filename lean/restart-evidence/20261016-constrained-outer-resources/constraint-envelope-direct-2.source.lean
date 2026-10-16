import MicroCFTA.SourceEqualityConjoinAllocation

/-!
# Quantitative envelopes for actual source equality operations

Normalization can append recorded suffixes to other paths.
The initial occurrence count and depth bound the resulting depth.
The initial child-index alphabet bounds each canonical path set.
Physical readback, inherited combination, and descent retain these bounds.
-/
namespace MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryConstraintEnvelope
open EqualityNormalize EqualitySaturation EqualityTermination
open SourceEqualityClassOrder

/-- The finite word count includes the empty path. -/
def wordCount (alphabet : Nat) : Nat → Nat
  | 0 => 1
  | depth + 1 => 1 + alphabet * wordCount alphabet depth

/-- Saturation depth depends on raw path occurrences, not only class count. -/
def normalizedDepth (occurrences depth : Nat) : Nat := (depth + 1) * (occurrences + 1)

/-- The input counts every literal path occurrence, including duplicates. -/
structure Bounds (occurrences depth alphabet : Nat) (classes : Constraints) : Prop where
  occurrences : classes.flatten.length ≤ occurrences
  depth : ∀ paths ∈ classes, ∀ path ∈ paths, path.length ≤ depth
  alphabet : ∀ paths ∈ classes, ∀ path ∈ paths, ∀ index ∈ path, index < alphabet

/-- Contradiction imposes no path or class obligation. -/
def OptionBounds (occurrences depth alphabet : Nat) (classes : Option Constraints) : Prop :=
  ∀ output, classes = some output → Bounds occurrences depth alphabet output

/-- Normalized class count, per-class size, and total occurrences remain distinct. -/
def Envelope (occurrences depth alphabet : Nat) (classes : Option Constraints) : Prop :=
  ∀ output, classes = some output →
    output.length ≤ occurrences ∧
    (∀ paths ∈ output, paths.length ≤ wordCount alphabet (normalizedDepth occurrences depth)) ∧
    Bounds (occurrences * wordCount alphabet (normalizedDepth occurrences depth))
      (normalizedDepth occurrences depth) alphabet output

/-- Every normalized envelope also supplies its total physical path bound. -/
theorem Envelope.bounds {occurrences depth alphabet : Nat} {classes : Option Constraints}
    (bound : Envelope occurrences depth alphabet classes) :
    OptionBounds (occurrences * wordCount alphabet (normalizedDepth occurrences depth))
      (normalizedDepth occurrences depth) alphabet classes := fun output done => (bound output done).2.2

private theorem words_length (alphabet : List Nat) (depth : Nat) :
    (words alphabet depth).length = wordCount alphabet.length depth := by
  induction depth with
  | zero => rfl
  | succ depth ih => simp [words, wordCount, List.length_flatMap, ih, List.map_const', List.sum_replicate_nat, Nat.add_comm]

private theorem prepared_member (classes : Constraints) (path : Path)
    (member : path ∈ members (complete (prepare classes))) : path ∈ classes.flatten := by
  obtain ⟨paths, present, member⟩ := (mem_members _ _).mp ((complete_members _ _).mp member)
  obtain ⟨original, originalMember, rfl⟩ := List.mem_map.mp (List.mem_filter.mp present).1
  exact List.mem_flatten.mpr ⟨original, originalMember, List.mem_eraseDups.mp member⟩

private theorem fix_bounds (fuel : Nat) (classes output : Constraints)
    (gap : Nat) (anchors : List Path) (alphabet : List Nat)
    (normal : NormalState classes) (segmented : SegmentedState gap classes)
    (anchored : Anchored anchors classes) (allowed : UsesAlphabet alphabet classes)
    (done : fixMaybe fuel classes = .normalized output) :
    SegmentedState gap output ∧ Anchored anchors output ∧ UsesAlphabet alphabet output := by
  induction fuel generalizing classes with
  | zero => simp [fixMaybe] at done
  | succ fuel ih =>
      cases stepped : congruenceStep classes with
      | none => simp [fixMaybe, stepped] at done
      | some next =>
          by_cases same : next = classes
          · subst next
            have equal : output = classes := by simpa [fixMaybe, stepped] using done.symm
            subst output
            exact ⟨segmented, anchored, allowed⟩
          · exact ih next (step_normal classes next normal.1 stepped)
              (step_segmented gap classes next segmented stepped)
              (step_anchored anchors classes next normal.1 anchored stepped)
              (step_alphabet alphabet classes next allowed stepped)
              (by simpa [fixMaybe, stepped, same] using done)

private theorem flatten_bound (classes : Constraints) (limit : Nat)
    (bound : ∀ paths ∈ classes, paths.length ≤ limit) : classes.flatten.length ≤ classes.length * limit := by
  induction classes with
  | nil => simp
  | cons paths rest ih =>
      have first := bound paths List.mem_cons_self
      have tail := ih (fun own member => bound own (List.mem_cons_of_mem paths member))
      simp only [List.flatten_cons, List.length_append, List.length_cons, Nat.add_mul, Nat.one_mul]
      omega

private theorem normalized_bounds (fuel : Nat) (classes output : Constraints)
    (occurrences depth alphabet : Nat) (input : Bounds occurrences depth alphabet classes)
    (done : mkEqConstraints fuel classes = .normalized output) :
    output.length ≤ occurrences ∧
    (∀ paths ∈ output, paths.length ≤ wordCount alphabet (normalizedDepth occurrences depth)) ∧
    Bounds (occurrences * wordCount alphabet (normalizedDepth occurrences depth))
      (normalizedDepth occurrences depth) alphabet output := by
  let initial := complete (prepare classes)
  have normal : NormalState initial := complete_normal _ (prepare_active _)
  have original : ∀ path ∈ members initial, path ∈ classes.flatten := prepared_member classes
  have anchorCount : (members initial).length ≤ occurrences := by
    have unique : (members initial).Nodup := paths_eraseDups_nodup _
    exact Nat.le_trans (unique.length_le_of_subset original) input.occurrences
  have segmented : SegmentedState (depth + 1) initial := by
    intro path member
    obtain ⟨paths, present, member⟩ := List.mem_flatten.mp (original path member)
    exact .short (by simp) (by have := input.depth paths present path member; simp only [List.length_nil]; omega)
  have allowed : UsesAlphabet (List.range alphabet) initial := by
    intro path member index inPath
    obtain ⟨paths, present, member⟩ := List.mem_flatten.mp (original path member)
    exact List.mem_range.mpr (input.alphabet paths present path member index inPath)
  obtain ⟨segmented, anchored, allowed⟩ := fix_bounds fuel initial output (depth + 1) (members initial)
    (List.range alphabet) normal segmented (initially_anchored initial normal.1) allowed done
  obtain ⟨active, consistent, apart, fixed⟩ := mkEqConstraints_invariants fuel classes output done
  have outputNormal := step_normal output output active fixed
  have classCount := Nat.le_trans (anchored_class_bound _ _ anchored apart) anchorCount
  have depths : ∀ paths ∈ output, ∀ path ∈ paths, path.length ≤ normalizedDepth occurrences depth := by
    intro paths present path member
    have bound := segmented_length_bound (depth + 1) output consistent segmented path ((mem_members _ _).mpr ⟨paths, present, member⟩)
    exact Nat.le_trans bound (Nat.mul_le_mul_left _ (by omega))
  have alphabets : ∀ paths ∈ output, ∀ path ∈ paths, ∀ index ∈ path, index < alphabet := by
    intro paths present path member index inPath
    exact List.mem_range.mp (allowed path ((mem_members _ _).mpr ⟨paths, present, member⟩) index inPath)
  have pathCounts : ∀ paths ∈ output, paths.length ≤ wordCount alphabet (normalizedDepth occurrences depth) := by
    intro paths present
    have unique : paths.Nodup := by
      rw [← outputNormal.2.2.2 paths present]
      exact canonicalClass_nodup _
    have subset : ∀ path ∈ paths, path ∈ words (List.range alphabet) (normalizedDepth occurrences depth) := by
      intro path member
      exact (words_correct _ _ _).mpr ⟨depths paths present path member,
        fun index inPath => List.mem_range.mpr (alphabets paths present path member index inPath)⟩
    have lengthBound := unique.length_le_of_subset subset
    simpa only [words_length, List.length_range] using lengthBound
  refine ⟨classCount, pathCounts, ?_, depths, alphabets⟩
  have total := flatten_bound output (wordCount alphabet (normalizedDepth occurrences depth)) pathCounts
  exact Nat.le_trans total (Nat.mul_le_mul_right _ classCount)

/-- The actual total source normalizer derives its envelope from the raw input bounds. -/
theorem normalize (classes : Constraints) (occurrences depth alphabet : Nat)
    (input : Bounds occurrences depth alphabet classes) :
    Envelope occurrences depth alphabet (SourceCompactGuards.normalize classes) := by
  intro output done
  unfold SourceCompactGuards.normalize at done
  rw [SourceCompactGuards.arrayNormalize_eq] at done
  cases actual : mkEqConstraints (normalizationBound classes) classes with
  | timeout | contradiction => simp [actual, SymbolicEqualityBridge.resultClasses] at done
  | normalized result =>
      have same : result = output := by simpa [actual, SymbolicEqualityBridge.resultClasses] using done
      subst output
      exact normalized_bounds _ classes result occurrences depth alphabet input actual

/-- Appending raw inputs adds occurrences and takes the maximum original depth. -/
theorem Bounds.append {firstCount secondCount firstDepth secondDepth alphabet : Nat} {first second : Constraints}
    (left : Bounds firstCount firstDepth alphabet first) (right : Bounds secondCount secondDepth alphabet second) :
    Bounds (firstCount + secondCount) (max firstDepth secondDepth) alphabet (first ++ second) := by
  refine ⟨by simpa only [List.flatten_append, List.length_append] using Nat.add_le_add left.occurrences right.occurrences, ?_, ?_⟩
  · intro paths member path inPath
    rcases List.mem_append.mp member with member | member
    · exact Nat.le_trans (left.depth paths member path inPath) (Nat.le_max_left _ _)
    · exact Nat.le_trans (right.depth paths member path inPath) (Nat.le_max_right _ _)
  · intro paths member path inPath index included
    rcases List.mem_append.mp member with member | member
    · exact left.alphabet paths member path inPath index included
    · exact right.alphabet paths member path inPath index included

private theorem empty_envelope (occurrences depth alphabet : Nat) : Envelope occurrences depth alphabet (some []) := by
  intro output done
  cases done
  exact ⟨Nat.zero_le _, by simp, by constructor <;> simp⟩

/-- Actual equality conjunction includes contradiction and the literal empty shortcut. -/
theorem combine {firstCount secondCount firstDepth secondDepth alphabet : Nat} (first second : Option Constraints)
    (left : OptionBounds firstCount firstDepth alphabet first) (right : OptionBounds secondCount secondDepth alphabet second) :
    Envelope (firstCount + secondCount) (max firstDepth secondDepth) alphabet (SourceCompactGuards.combineEqualities first second) := by
  cases first with
  | none => intro output done; simp [SourceCompactGuards.combineEqualities] at done
  | some first =>
      cases second with
      | none => intro output done; simp [SourceCompactGuards.combineEqualities] at done
      | some second =>
          have input := (left first rfl).append (right second rfl)
          cases first <;> cases second
          · exact empty_envelope _ _ _
          all_goals exact normalize _ _ _ _ input

end MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryConstraintEnvelope
