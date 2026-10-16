import MicroCFTA.SourceEqualityConjoinAllocation
import MicroCFTA.SourceEqualityPartialPrecheckAllocation

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
structure Bounds (occurrences depth : Nat) (classes : Constraints) : Prop where
  occurrences : classes.flatten.length ≤ occurrences
  depth : ∀ paths ∈ classes, ∀ path ∈ paths, path.length ≤ depth

/-- Contradiction imposes no path or class obligation. -/
def OptionBounds (occurrences depth : Nat) (classes : Option Constraints) : Prop :=
  ∀ output, classes = some output → Bounds occurrences depth output

/-- Class count, per-class size, and total occurrences remain distinct. -/
def Envelope (occurrences depth : Nat) (classes : Option Constraints) : Prop :=
  ∀ output, classes = some output →
    output.length ≤ occurrences ∧
    (∀ paths ∈ output, paths.length ≤ wordCount (occurrences * depth) (normalizedDepth occurrences depth)) ∧
    Bounds (occurrences * wordCount (occurrences * depth) (normalizedDepth occurrences depth))
      (normalizedDepth occurrences depth) output

/-- Every normalized envelope supplies its total physical path bound. -/
theorem Envelope.bounds {occurrences depth : Nat} {classes : Option Constraints}
    (bound : Envelope occurrences depth classes) :
    OptionBounds (occurrences * wordCount (occurrences * depth) (normalizedDepth occurrences depth))
      (normalizedDepth occurrences depth) classes := fun output done => (bound output done).2.2

/-- A larger alphabet cardinality gives a conservative finite word count. -/
theorem wordCount_mono {first second : Nat} (enough : first ≤ second) (depth : Nat) :
    wordCount first depth ≤ wordCount second depth := by
  induction depth with
  | zero => exact Nat.le_refl _
  | succ depth ih => exact Nat.add_le_add_left (Nat.mul_le_mul enough ih) _

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

private theorem flatten_bound {α : Type} (classes : List (List α)) (limit : Nat)
    (bound : ∀ paths ∈ classes, paths.length ≤ limit) : classes.flatten.length ≤ classes.length * limit := by
  induction classes with
  | nil => simp
  | cons paths rest ih =>
      have first := bound paths List.mem_cons_self
      have tail := ih (fun own member => bound own (List.mem_cons_of_mem paths member))
      simp only [List.flatten_cons, List.length_append, List.length_cons, Nat.add_mul, Nat.one_mul]
      omega

private theorem normalized_bounds (fuel : Nat) (classes output : Constraints)
    (occurrences depth : Nat) (input : Bounds occurrences depth classes)
    (done : mkEqConstraints fuel classes = .normalized output) :
    output.length ≤ occurrences ∧
    (∀ paths ∈ output, paths.length ≤ wordCount (occurrences * depth) (normalizedDepth occurrences depth)) ∧
    Bounds (occurrences * wordCount (occurrences * depth) (normalizedDepth occurrences depth))
      (normalizedDepth occurrences depth) output := by
  let initial := complete (prepare classes)
  let alphabet := initialAlphabet initial
  have normal : NormalState initial := complete_normal _ (prepare_active _)
  have original : ∀ path ∈ members initial, path ∈ classes.flatten := prepared_member classes
  have anchorCount : (members initial).length ≤ occurrences := by
    have unique : (members initial).Nodup := paths_eraseDups_nodup _
    exact Nat.le_trans (unique.length_le_of_subset original) input.occurrences
  have alphabetCount : alphabet.length ≤ occurrences * depth := by
    have unique : alphabet.Nodup := EqualityTrie.eraseDups_nodup _
    have subset : ∀ index ∈ alphabet, index ∈ classes.flatten.flatten := by
      intro index member
      obtain ⟨path, present, included⟩ := List.mem_flatten.mp (List.mem_eraseDups.mp member)
      exact List.mem_flatten.mpr ⟨path, original path present, included⟩
    have total := flatten_bound classes.flatten depth (by
      intro path member
      obtain ⟨paths, present, included⟩ := List.mem_flatten.mp member
      exact input.depth paths present path included)
    exact Nat.le_trans (unique.length_le_of_subset subset)
      (Nat.le_trans total (Nat.mul_le_mul_right depth input.occurrences))
  have segmented : SegmentedState (depth + 1) initial := by
    intro path member
    obtain ⟨paths, present, member⟩ := List.mem_flatten.mp (original path member)
    exact .short (by simp) (by have := input.depth paths present path member; simp only [List.length_nil]; omega)
  obtain ⟨segmented, anchored, allowed⟩ := fix_bounds fuel initial output (depth + 1) (members initial)
    alphabet normal segmented (initially_anchored initial normal.1) (initially_allowed initial) done
  obtain ⟨active, consistent, apart, fixed⟩ := mkEqConstraints_invariants fuel classes output done
  have outputNormal := step_normal output output active fixed
  have classCount := Nat.le_trans (anchored_class_bound _ _ anchored apart) anchorCount
  have depths : ∀ paths ∈ output, ∀ path ∈ paths, path.length ≤ normalizedDepth occurrences depth := by
    intro paths present path member
    have bound := segmented_length_bound (depth + 1) output consistent segmented path ((mem_members _ _).mpr ⟨paths, present, member⟩)
    exact Nat.le_trans bound (Nat.mul_le_mul_left _ (by omega))
  have pathCounts : ∀ paths ∈ output, paths.length ≤ wordCount (occurrences * depth) (normalizedDepth occurrences depth) := by
    intro paths present
    have unique : paths.Nodup := by
      rw [← outputNormal.2.2.2 paths present]
      exact canonicalClass_nodup _
    have subset : ∀ path ∈ paths, path ∈ words alphabet (normalizedDepth occurrences depth) := by
      intro path member
      exact (words_correct _ _ _).mpr ⟨depths paths present path member,
        allowed path ((mem_members _ _).mpr ⟨paths, present, member⟩)⟩
    have lengthBound := unique.length_le_of_subset subset
    rw [words_length] at lengthBound
    exact Nat.le_trans lengthBound (wordCount_mono alphabetCount _)
  refine ⟨classCount, pathCounts, ?_, depths⟩
  have total := flatten_bound output (wordCount (occurrences * depth) (normalizedDepth occurrences depth)) pathCounts
  exact Nat.le_trans total (Nat.mul_le_mul_right _ classCount)

/-- The actual source normalizer derives its envelope from raw count and depth alone. -/
theorem normalize (classes : Constraints) (occurrences depth : Nat)
    (input : Bounds occurrences depth classes) :
    Envelope occurrences depth (SourceCompactGuards.normalize classes) := by
  intro output done
  unfold SourceCompactGuards.normalize at done
  rw [SourceCompactGuards.arrayNormalize_eq] at done
  cases actual : mkEqConstraints (normalizationBound classes) classes with
  | timeout | contradiction => simp [actual, SymbolicEqualityBridge.resultClasses] at done
  | normalized result =>
      have same : result = output := by simpa [actual, SymbolicEqualityBridge.resultClasses] using done
      subst output
      exact normalized_bounds _ classes result occurrences depth input actual

/-- Appending raw inputs adds occurrences and takes the maximum original depth. -/
theorem Bounds.append {firstCount secondCount firstDepth secondDepth : Nat} {first second : Constraints}
    (left : Bounds firstCount firstDepth first) (right : Bounds secondCount secondDepth second) :
    Bounds (firstCount + secondCount) (max firstDepth secondDepth) (first ++ second) := by
  refine ⟨by simpa only [List.flatten_append, List.length_append] using Nat.add_le_add left.occurrences right.occurrences, ?_⟩
  intro paths member path inPath
  rcases List.mem_append.mp member with member | member
  · exact Nat.le_trans (left.depth paths member path inPath) (Nat.le_max_left _ _)
  · exact Nat.le_trans (right.depth paths member path inPath) (Nat.le_max_right _ _)

private theorem empty_envelope (occurrences depth : Nat) : Envelope occurrences depth (some []) := by
  intro output done
  cases done
  exact ⟨Nat.zero_le _, by simp, by constructor <;> simp⟩

/-- Actual equality conjunction includes contradiction and the literal empty shortcut. -/
theorem combine {firstCount secondCount firstDepth secondDepth : Nat} (first second : Option Constraints)
    (left : OptionBounds firstCount firstDepth first) (right : OptionBounds secondCount secondDepth second) :
    Envelope (firstCount + secondCount) (max firstDepth secondDepth) (SourceCompactGuards.combineEqualities first second) := by
  cases first with
  | none => intro output done; simp [SourceCompactGuards.combineEqualities] at done
  | some first =>
      cases second with
      | none => intro output done; simp [SourceCompactGuards.combineEqualities] at done
      | some second =>
          have input := (left first rfl).append (right second rfl)
          cases first <;> cases second
          · exact empty_envelope _ _
          all_goals exact normalize _ _ _ input

/-- Physical payload bounds refer to the actual original record path lists. -/
def PayloadBounds (occurrences depth : Nat) (payload : SourceEqualityPrecheck.Constraint) : Prop :=
  OptionBounds occurrences depth (SourceEqualityInheritedPayload.classes payload)

/-- Cached physical readback retains the input class envelope exactly. -/
theorem read_bounds (equalities : Option Constraints) (occurrences depth : Nat)
    (cached : SourceEqualityGuardReadback.Cached equalities) (input : OptionBounds occurrences depth equalities)
    (payload : SourceEqualityPrecheck.Constraint) (done : SourceEqualityPhysicalPayload.read equalities = .ok payload) :
    PayloadBounds occurrences depth payload := by
  unfold PayloadBounds
  rw [SourceEqualityConstraintAllocation.read_classes equalities cached payload done]
  exact input

/-- Actual inherited-first physical combination derives its output envelope. -/
theorem payload_combine {firstCount secondCount firstDepth secondDepth : Nat}
    (inherited own combined : SourceEqualityPrecheck.Constraint)
    (left : PayloadBounds firstCount firstDepth inherited) (right : PayloadBounds secondCount secondDepth own)
    (done : SourceEqualityInheritedPayload.combine inherited own = .ok combined) :
    Envelope (firstCount + secondCount) (max firstDepth secondDepth)
      (SourceEqualityInheritedPayload.classes combined) := by
  have same := SourceEqualityConstraintAllocation.read_classes
    (SourceCompactGuards.combineEqualities (SourceEqualityInheritedPayload.classes inherited) (SourceEqualityInheritedPayload.classes own))
    (SourceEqualityGuardReadback.combine_cached _ _) combined done
  rw [same]
  exact combine _ _ left right

private theorem record_length (index : Nat) (original output : Record)
    (coherent : Coherent original) (ascending : EqualityTrie.Ascending original.trie)
    (done : SourceEqualityDescend.record index original = some output) : output.paths.length ≤ original.paths.length := by
  have checked := SourceEqualityDescend.record_wellFormed index original coherent ascending output done
  have unique : output.paths.Nodup := by
    rw [← checked.1.2.1]
    exact canonicalClass_nodup _
  have mapped : (output.paths.map (index :: ·)).Nodup := by
    change (output.paths.map (index :: ·)).Pairwise (· ≠ ·)
    rw [List.pairwise_map]
    exact unique.imp (fun different same => different (List.cons.inj same).2)
  have subset : ∀ path ∈ output.paths.map (index :: ·), path ∈ original.paths := by
    intro path member
    obtain ⟨suffix, present, rfl⟩ := List.mem_map.mp member
    exact (SourceEqualityDescend.record_pairs index original coherent output done suffix).mp present
  simpa only [List.length_map] using mapped.length_le_of_subset subset

private theorem filtered_size (index : Nat) (originals : List Record)
    (valid : ∀ original ∈ originals, Coherent original ∧ EqualityTrie.Ascending original.trie) :
    (((originals.filterMap (SourceEqualityDescend.record index)).map Record.paths).flatten).length ≤
      ((originals.map Record.paths).flatten).length := by
  induction originals with
  | nil => simp
  | cons original rest ih =>
      have tail := ih (fun current member => valid current (List.mem_cons_of_mem original member))
      cases done : SourceEqualityDescend.record index original with
      | none =>
          simp only [List.filterMap_cons, done, List.map_cons, List.flatten_cons, List.length_append]
          omega
      | some output =>
          have first := record_length index original output (valid original List.mem_cons_self).1
            (valid original List.mem_cons_self).2 done
          simp only [List.filterMap_cons, done, List.map_cons, List.flatten_cons, List.length_append]
          omega

private theorem descended_bounds (index : Nat) (originals : List Record) (occurrences depth : Nat)
    (valid : ∀ original ∈ originals, Coherent original ∧ EqualityTrie.Ascending original.trie)
    (input : Bounds occurrences depth (originals.map Record.paths)) :
    Bounds occurrences (depth - 1) ((SourceEqualityDescend.records index originals).map Record.paths) := by
  refine ⟨?_, ?_⟩
  · have same := (((SourceEqualityDescend.records_perm index originals).map Record.paths).flatten).length_eq
    rw [same]
    exact Nat.le_trans (filtered_size index originals valid) input.occurrences
  · intro paths member path included
    obtain ⟨output, present, rfl⟩ := List.mem_map.mp member
    obtain ⟨original, originalMember, done⟩ := List.mem_filterMap.mp
      ((SourceEqualityDescend.records_perm index originals).mem_iff.mp present)
    have inherited := (SourceEqualityDescend.record_pairs index original (valid original originalMember).1 output done path).mp included
    have bound := input.depth original.paths (List.mem_map.mpr ⟨original, originalMember, rfl⟩) (index :: path) inherited
    simp only [List.length_cons] at bound
    omega

/-- Actual indexed trie descent does not increase occurrences and shortens retained paths. -/
theorem payload_descend (payload : SourceEqualityPrecheck.Constraint) (index occurrences depth : Nat)
    (valid : SourceEqualityDescend.WellFormed payload) (input : PayloadBounds occurrences depth payload) :
    PayloadBounds occurrences (depth - 1) (SourceEqualityDescend.descend payload index) := by
  cases payload with
  | none => intro output done; simp [SourceEqualityDescend.descend, SourceEqualityInheritedPayload.classes] at done
  | some originals =>
      intro output done
      have initial := input (originals.map Record.paths) rfl
      have checked := descended_bounds index originals occurrences depth
        (fun original member => ⟨(valid originals rfl original member).1, (valid originals rfl original member).2.1⟩) initial
      cases originals with
      | nil => simpa [SourceEqualityDescend.descend, SourceEqualityInheritedPayload.classes] using initial
      | cons original rest =>
          have same : (SourceEqualityDescend.records index (original :: rest)).map Record.paths = output :=
            Option.some.inj done
          rw [← same]
          exact checked

/-- Actual live precheck records are only the ordered original own records. -/
theorem precheck_bounds (own inherited : SourceEqualityPrecheck.Constraint) (occurrences depth : Nat)
    (input : PayloadBounds occurrences depth own) (records : List Record)
    (done : SourceEqualityPrecheck.precheck own inherited = .ok (.classes records)) :
    Bounds occurrences depth (records.map Record.paths) := by
  obtain ⟨originals, own, same, _⟩ := SourceEqualityPrecheck.live_payload own inherited records done
  subst records
  have bounded := input (originals.map Record.paths) (by rw [own]; rfl)
  have perm := (ordered_perm originals).map Record.paths
  refine ⟨?_, ?_⟩
  · rw [perm.flatten.length_eq]
    exact bounded.occurrences
  · intro paths member
    exact bounded.depth paths (perm.mem_iff.mp member)

/-- The parent path bound follows from the initial own payload, regardless of inherited size. -/
theorem precheck_paths (own inherited : SourceEqualityPrecheck.Constraint) (occurrences depth : Nat)
    (input : PayloadBounds occurrences depth own) :
    ∀ records, SourceEqualityPrecheck.precheck own inherited = .ok (.classes records) →
      ∀ record ∈ records, ∀ path ∈ record.paths, path.length ≤ depth := by
  intro records done record member path included
  exact (precheck_bounds own inherited occurrences depth input records done).depth record.paths
    (List.mem_map.mpr ⟨record, member, rfl⟩) path included

/-- Actual allocation and precheck derive the parent path obligation from the initial effective guard field. -/
theorem allocated_precheck_paths (stored : SourceEqualityConstraintAllocation.Value) (guard : SourceGuards.Guard Formula)
    (inherited : SourceEqualityConstraintAllocation.Value) (before : SourceEqualityConstraintMemoAllocation.State)
    (valid : SourceEqualityConstraintMemoAllocation.Valid before)
    (storedReady : SourceEqualityConstraintAllocation.Ready before.constraints stored)
    (inheritedReady : SourceEqualityConstraintAllocation.Ready before.constraints inherited)
    (original : Option Constraints) (cached : SourceEqualityGuardReadback.Cached original)
    (built : SourceEqualityPhysicalPayload.read original = .ok stored.payload) (occurrences depth : Nat)
    (input : OptionBounds occurrences depth
      (SourceCompactGuards.sourceEqualities (⟨original, guard⟩ : SourceSymbolicIndex.Constraint Formula))) :
    ∀ records, (SourceEqualityPartialPrecheckAllocation.run stored guard inherited before).1 = .ok (.classes records) →
      ∀ record ∈ records, ∀ path ∈ record.paths, path.length ≤ depth := by
  intro records done
  obtain ⟨own, branch, ownRead, actual, exact, _valid, _growth⟩ :=
    SourceEqualityPartialPrecheckAllocation.run_correct stored guard inherited before valid storedReady inheritedReady original cached built
  have same := Except.ok.inj (actual.symm.trans done)
  subst branch
  have bound := read_bounds _ occurrences depth (SourceEqualityGuardReadback.source_cached _ cached) input own.payload ownRead
  exact precheck_paths own.payload inherited.payload occurrences depth bound records exact

end MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryConstraintEnvelope
