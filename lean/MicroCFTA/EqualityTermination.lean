import MicroCFTA.EqualitySaturation

/-!
# Prefix rewriting and source saturation

Input equality classes generate a right congruence on paths. Saturation
simulates each finite derivation when one path is recorded. A derived strict
prefix equality then causes the source contradiction check to finish.
-/

namespace MicroCFTA.EqualityTermination
open MicroCFTA.Language MicroCFTA.EqualityNormalize MicroCFTA.EqualitySaturation

/-- Equality derivations permit input equations, transitivity, and a common suffix. -/
inductive Equivalent (original : Constraints) : List Nat → List Nat → Prop where
  | reflexive (path : List Nat) : Equivalent original path path
  | input (paths : Class) : paths ∈ original → left ∈ paths → right ∈ paths → Equivalent original left right
  | trans : Equivalent original left middle → Equivalent original middle right → Equivalent original left right
  | suffix : Equivalent original left right → Equivalent original (left ++ rest) (right ++ rest)

/-- Every generated path equality can be used in either direction. -/
theorem equivalent_symm (original : Constraints) (left right : List Nat) (equal : Equivalent original left right) :
    Equivalent original right left := by
  induction equal with
  | reflexive path => exact .reflexive path
  | input paths member first second => exact .input paths member second first
  | trans first second leftIH rightIH => exact .trans rightIH leftIH
  | suffix equal ih => exact .suffix ih

/-- A derivation preserves optional lookup equality in each satisfying complete term. -/
theorem equivalent_lookup (original : Constraints) (active : Active original) (term : Term Symbol)
    (satisfied : Satisfies term original) (left right : List Nat) (equal : Equivalent original left right) :
    term.atPath left = term.atPath right := by
  induction equal with
  | reflexive path => rfl
  | input paths member first second =>
      obtain ⟨value, atLeft, atRight⟩ := class_pair_equal term paths (active paths member) (satisfied paths member) _ _ first second
      exact atLeft.trans atRight.symm
  | trans first second leftIH rightIH => exact leftIH.trans rightIH
  | suffix equal ih => simp only [atPath_append, ih]

/-- Execute a fixed number of source steps without the early fixed-point return. -/
def evolve : Nat → Constraints → Option Constraints
  | 0, classes => some classes
  | fuel + 1, classes => (congruenceStep classes).bind (evolve fuel)

/-- Step-count addition composes executions in the expected order. -/
theorem evolve_add (first second : Nat) (classes : Constraints) :
    evolve (first + second) classes = (evolve first classes).bind (evolve second) := by
  induction first generalizing classes with
  | zero => simp [evolve]
  | succ first ih =>
      simp only [Nat.succ_add, evolve]
      cases stepped : congruenceStep classes with
      | none => rfl
      | some next => simpa using ih next

/-- Successful step sequences preserve every original class inside a current component. -/
theorem evolve_covers (fuel : Nat) (classes output : Constraints) (success : evolve fuel classes = some output) :
    Covers classes output := by
  induction fuel generalizing classes with
  | zero => simp [evolve] at success; subst output; exact fun paths member => ⟨paths, member, fun _ present => present⟩
  | succ fuel ih =>
      cases stepped : congruenceStep classes with
      | none => simp [evolve, stepped] at success
      | some next =>
          have recursive : evolve fuel next = some output := by simpa [evolve, stepped] using success
          exact covers_trans classes next output (step_covers classes next stepped) (ih next recursive)

/-- Successful source step sequences retain canonical component invariants. -/
theorem evolve_normal (fuel : Nat) (classes output : Constraints) (normal : NormalState classes)
    (success : evolve fuel classes = some output) : NormalState output := by
  induction fuel generalizing classes with
  | zero => simp [evolve] at success; subst output; exact normal
  | succ fuel ih =>
      cases stepped : congruenceStep classes with
      | none => simp [evolve, stepped] at success
      | some next =>
          have recursive : evolve fuel next = some output := by simpa [evolve, stepped] using success
          exact ih next (step_normal classes next normal.1 stepped) recursive

/-- Direct component equality is transitive in canonical states. -/
theorem inSame_trans (classes : Constraints) (normal : NormalState classes) (left middle right : List Nat)
    (first : inSame classes left middle = true) (second : inSame classes middle right = true) :
    inSame classes left right = true :=
  (normal_connected classes normal left right).mpr (.trans
    ((normal_connected classes normal left middle).mp first)
    ((normal_connected classes normal middle right).mp second))

/-- Every recorded path has a reflexive same-component membership. -/
theorem inSame_self (classes : Constraints) (path : List Nat) (member : path ∈ members classes) : inSame classes path path = true := by
  obtain ⟨paths, pathsMember, present⟩ := (mem_members _ _).mp member
  exact (inSame_correct _ _ _).mpr ⟨paths, pathsMember, present, present⟩

/-- One source step propagates every stored class equality to a recorded common suffix. -/
theorem step_suffix (classes output : Constraints) (left right rest : List Nat)
    (equal : inSame classes left right = true) (recorded : left ++ rest ∈ members classes)
    (success : congruenceStep classes = some output) : inSame output (left ++ rest) (right ++ rest) = true := by
  by_cases empty : rest = []
  · subst rest
    simpa using inSame_mono classes output (step_covers classes output success) left right equal
  · obtain ⟨paths, pathsMember, leftMember, rightMember⟩ := (inSame_correct _ _ _).mp equal
    have requested : rest ∈ suffixes paths classes := (mem_suffixes _ _ _).mpr
      ⟨left, leftMember, left ++ rest, recorded, empty, rfl⟩
    have generated : extendClass paths rest ∈ addCongruences classes := List.mem_append_right _
      (List.mem_flatMap.mpr ⟨paths, pathsMember, List.mem_map.mpr ⟨rest, requested, rfl⟩⟩)
    have outputEq : complete (addCongruences classes) = output := by
      dsimp only [congruenceStep] at success
      split at success
      next contradiction => simp at success
      next consistent => exact Option.some.inj success
    obtain ⟨component, componentMember, included⟩ := complete_covers (addCongruences classes) (extendClass paths rest) generated
    rw [outputEq] at componentMember
    exact (inSame_correct _ _ _).mpr ⟨component, componentMember,
      included (left ++ rest) ((mem_extendClass _ _ _).mpr ⟨left, leftMember, rfl⟩),
      included (right ++ rest) ((mem_extendClass _ _ _).mpr ⟨right, rightMember, rfl⟩)⟩

/-- Every input equality is retained by a class-containment invariant. -/
theorem input_inSame (original classes : Constraints) (covered : Covers original classes)
    (paths : Class) (member : paths ∈ original) (left right : List Nat) (first : left ∈ paths) (second : right ∈ paths) :
    inSame classes left right = true := by
  obtain ⟨component, componentMember, includes⟩ := covered paths member
  exact (inSame_correct _ _ _).mpr ⟨component, componentMember, includes left first, includes right second⟩

/-- Finite equality derivations are eventually recorded, or a contradiction ends execution. -/
theorem simulate_equivalent (original : Constraints) (left right : List Nat) (equal : Equivalent original left right)
    (classes : Constraints) (normal : NormalState classes) (covered : Covers original classes)
    (rest : List Nat) (recorded : left ++ rest ∈ members classes) :
    ∃ fuel, evolve fuel classes = none ∨ ∃ output, evolve fuel classes = some output ∧
      inSame output (left ++ rest) (right ++ rest) = true := by
  induction equal generalizing classes rest with
  | reflexive path => exact ⟨0, Or.inr ⟨classes, rfl, inSame_self classes (path ++ rest) recorded⟩⟩
  | input paths member first second =>
      cases stepped : congruenceStep classes with
      | none => exact ⟨1, Or.inl (by simp [evolve, stepped])⟩
      | some output => exact ⟨1, Or.inr ⟨output, by simp [evolve, stepped],
          step_suffix classes output _ _ rest (input_inSame original classes covered paths member _ _ first second) recorded stepped⟩⟩
  | @trans left middle right first second firstIH secondIH =>
      obtain ⟨firstFuel, failure | ⟨intermediate, firstRun, firstEqual⟩⟩ := firstIH classes normal covered rest recorded
      · exact ⟨firstFuel, Or.inl failure⟩
      · have middleRecorded : middle ++ rest ∈ members intermediate := by
          obtain ⟨paths, member, _, present⟩ := (inSame_correct _ _ _).mp firstEqual
          exact (mem_members _ _).mpr ⟨paths, member, present⟩
        have intermediateNormal := evolve_normal firstFuel classes intermediate normal firstRun
        have intermediateCover := covers_trans original classes intermediate covered (evolve_covers firstFuel classes intermediate firstRun)
        obtain ⟨secondFuel, failure | ⟨output, secondRun, secondEqual⟩⟩ :=
          secondIH intermediate intermediateNormal intermediateCover rest middleRecorded
        · exact ⟨firstFuel + secondFuel, Or.inl (by simp [evolve_add, firstRun, failure])⟩
        · refine ⟨firstFuel + secondFuel, Or.inr ⟨output, by simp [evolve_add, firstRun, secondRun], ?_⟩⟩
          exact inSame_trans output (evolve_normal secondFuel intermediate output intermediateNormal secondRun) _ _ _
            (inSame_mono intermediate output (evolve_covers secondFuel intermediate output secondRun) _ _ firstEqual) secondEqual
  | @suffix left right suffix equal ih =>
      have requested : left ++ (suffix ++ rest) ∈ members classes := by simpa [List.append_assoc] using recorded
      simpa [List.append_assoc] using ih classes normal covered (suffix ++ rest) requested

/-- A true source fixed point remains unchanged for every further step. -/
theorem evolve_fixed (fuel : Nat) (classes : Constraints) (fixed : congruenceStep classes = some classes) :
    evolve fuel classes = some classes := by
  induction fuel with
  | zero => rfl
  | succ fuel ih => simp [evolve, fixed, ih]

/-- If the step sequence reports a contradiction, the source early-stop loop also reports it. -/
theorem contradiction_reaches_fixMaybe (fuel : Nat) (classes : Constraints) (failure : evolve fuel classes = none) :
    ∃ bound, fixMaybe bound classes = .contradiction := by
  induction fuel generalizing classes with
  | zero => simp [evolve] at failure
  | succ fuel ih =>
      cases stepped : congruenceStep classes with
      | none => exact ⟨1, by simp [fixMaybe, stepped]⟩
      | some next =>
          have recursive : evolve fuel next = none := by simpa [evolve, stepped] using failure
          by_cases stable : next = classes
          · subst next
            rw [evolve_fixed fuel classes stepped] at recursive
            contradiction
          · obtain ⟨bound, result⟩ := ih next recursive
            exact ⟨bound + 1, by simp [fixMaybe, stepped, stable, result]⟩

/-- Strict-prefix same-component membership is detected at the next source step. -/
theorem next_detects_prefix (classes : Constraints) (left suffix : List Nat) (nonempty : suffix ≠ [])
    (equal : inSame classes left (left ++ suffix) = true) : congruenceStep classes = none := by
  have lifted := inSame_mono classes (complete (addCongruences classes))
    (fun paths member => complete_covers _ paths (List.mem_append_left _ member)) left (left ++ suffix) equal
  obtain ⟨paths, member, first, second⟩ := (inSame_correct _ _ _).mp lifted
  have different : left ≠ left ++ suffix := by
    intro same
    have lengths := congrArg List.length same
    simp only [List.length_append] at lengths
    exact nonempty (List.length_eq_zero_iff.mp (by omega))
  have contradiction := (isContradicting_correct _).mpr ⟨paths, member, left, first, left ++ suffix, second, ⟨suffix, rfl⟩, different⟩
  simp [congruenceStep, contradiction]

/-- A derived strict-prefix equality at a recorded path forces finite source rejection. -/
theorem derived_prefix_terminates (original classes : Constraints) (normal : NormalState classes)
    (covered : Covers original classes) (path suffix : List Nat) (nonempty : suffix ≠ [])
    (recorded : path ∈ members classes) (equal : Equivalent original path (path ++ suffix)) :
    ∃ bound, fixMaybe bound classes = .contradiction := by
  obtain ⟨fuel, failure | ⟨output, success, found⟩⟩ := simulate_equivalent original path (path ++ suffix) equal
    classes normal covered [] (by simpa using recorded)
  · exact contradiction_reaches_fixMaybe fuel classes failure
  · have next : congruenceStep output = none := next_detects_prefix output path suffix nonempty (by simpa using found)
    have failure : evolve (fuel + 1) classes = none := by
      rw [evolve_add, success]
      simp [evolve, next]
    exact contradiction_reaches_fixMaybe (fuel + 1) classes failure


/-- A path interval has bounded gaps between recorded class members. -/
inductive Segments (gap : Nat) (classes : Constraints) : List Nat → List Nat → Prop where
  | short : first.IsPrefix last → last.length ≤ first.length + gap → Segments gap classes first last
  | step : first.IsPrefix middle → first.length < middle.length → middle.IsPrefix last →
      middle.length ≤ first.length + gap → middle ∈ members classes →
      Segments gap classes middle last → Segments gap classes first last

/-- Every segmented interval follows the path-prefix order. -/
theorem segments_prefix (gap : Nat) (classes : Constraints) (first last : List Nat)
    (segments : Segments gap classes first last) : first.IsPrefix last := by
  cases segments with
  | short initial _ => exact initial
  | step initial _ remaining _ _ _ => exact initial.trans remaining

/-- Adding recorded paths preserves a segmentation certificate. -/
theorem segments_mono (gap : Nat) (before after : Constraints)
    (monotone : ∀ path ∈ members before, path ∈ members after) (first last : List Nat)
    (segments : Segments gap before first last) : Segments gap after first last := by
  induction segments with
  | short initial bound => exact .short initial bound
  | step initial proper remaining bound recorded nested ih => exact .step initial proper remaining bound (monotone _ recorded) ih

/-- An existing segmentation can be cut at any intermediate prefix. -/
theorem segments_cut (gap : Nat) (classes : Constraints) (first last cut : List Nat)
    (segments : Segments gap classes first last) (starts : first.IsPrefix cut) (ends : cut.IsPrefix last) :
    Segments gap classes cut last := by
  induction segments with
  | short initial bound => exact .short ends (by have := starts.length_le; omega)
  | @step middle last first initial proper remaining bound recorded nested ih =>
      rcases List.prefix_or_prefix_of_prefix ends remaining with before | after
      · by_cases same : cut = middle
        · subst cut; exact nested
        · have strict : cut.length < middle.length := by
            have le := before.length_le
            by_cases strict : cut.length < middle.length
            · exact strict
            · exact False.elim (same (before.eq_of_length (by omega)))
          exact .step before strict remaining (by have := starts.length_le; omega) recorded nested
      · exact ih after ends

/-- Segmented intervals join at a recorded boundary. -/
theorem segments_join (gap : Nat) (classes : Constraints) (first middle last : List Nat)
    (left : Segments gap classes first middle) (right : Segments gap classes middle last)
    (recorded : middle ∈ members classes) : Segments gap classes first last := by
  induction left with
  | @short first middle initial bound =>
      by_cases same : first = middle
      · subst first; exact right
      · have strict : first.length < middle.length := by
          have le := initial.length_le
          by_cases strict : first.length < middle.length
          · exact strict
          · exact False.elim (same (initial.eq_of_length (by omega)))
        exact .step initial strict (segments_prefix gap classes middle last right) bound recorded right
  | @step pivot middle first initial proper remaining bound present nested ih =>
      exact .step initial proper (remaining.trans (segments_prefix gap classes middle last right)) bound present (ih right recorded)

/-- Replace a known prefix by another path. -/
def replacePrefix (base replacement path : List Nat) : List Nat := replacement ++ path.drop base.length

/-- Prefix replacement preserves prefix order above the replacement point. -/
theorem replacePrefix_prefix (base replacement first last : List Nat) (starts : base.IsPrefix first)
    (ends : first.IsPrefix last) : (replacePrefix base replacement first).IsPrefix (replacePrefix base replacement last) := by
  obtain ⟨firstSuffix, rfl⟩ := starts
  obtain ⟨lastSuffix, rfl⟩ := ends
  exact ⟨lastSuffix, by simp [replacePrefix, List.append_assoc]⟩

/-- Prefix replacement changes all descendant lengths by the same amount. -/
theorem replacePrefix_length (base replacement path : List Nat) (initial : base.IsPrefix path) :
    (replacePrefix base replacement path).length + base.length = replacement.length + path.length := by
  obtain ⟨suffix, rfl⟩ := initial
  simp [replacePrefix, Nat.add_comm, Nat.add_left_comm]

/-- Segmentation follows prefix replacement when each translated boundary is recorded. -/
theorem segments_replace (gap : Nat) (before after : Constraints) (base replacement first last : List Nat)
    (segments : Segments gap before first last) (initial : base.IsPrefix first)
    (records : ∀ path ∈ members before, base.IsPrefix path → replacePrefix base replacement path ∈ members after) :
    Segments gap after (replacePrefix base replacement first) (replacePrefix base replacement last) := by
  induction segments with
  | short starts bound =>
      have firstLength := replacePrefix_length base replacement _ initial
      have lastLength := replacePrefix_length base replacement _ (initial.trans starts)
      exact .short (replacePrefix_prefix base replacement _ _ initial starts) (by omega)
  | @step middle last first starts proper ends bound recorded nested ih =>
      have atMiddle := initial.trans starts
      have firstLength := replacePrefix_length base replacement first initial
      have middleLength := replacePrefix_length base replacement middle atMiddle
      exact .step (replacePrefix_prefix base replacement first middle initial starts) (by omega)
        (replacePrefix_prefix base replacement middle last atMiddle ends) (by omega)
        (records middle recorded atMiddle) (ih atMiddle)

/-- Source suffix propagation records every translated boundary used by segmentation. -/
theorem step_replace_member (classes output : Constraints) (base replacement path : List Nat)
    (equal : inSame classes base replacement = true) (recorded : path ∈ members classes)
    (initial : base.IsPrefix path) (success : congruenceStep classes = some output) :
    replacePrefix base replacement path ∈ members output := by
  obtain ⟨suffix, rfl⟩ := initial
  have propagated := step_suffix classes output base replacement suffix equal recorded success
  obtain ⟨paths, member, _, present⟩ := (inSame_correct _ _ _).mp propagated
  simpa [replacePrefix] using (mem_members _ _).mpr ⟨paths, member, present⟩

/-- Every recorded path has a bounded-gap segmentation from the root. -/
def SegmentedState (gap : Nat) (classes : Constraints) : Prop :=
  ∀ path ∈ members classes, Segments gap classes [] path

/-- One source step preserves the original maximum gap between marked prefixes. -/
theorem step_segmented (gap : Nat) (classes output : Constraints) (segmented : SegmentedState gap classes)
    (success : congruenceStep classes = some output) : SegmentedState gap output := by
  have outputEq : complete (addCongruences classes) = output := by
    dsimp only [congruenceStep] at success
    split at success
    next contradiction => simp at success
    next consistent => exact Option.some.inj success
  have retained : ∀ path ∈ members classes, path ∈ members output := by
    intro path member
    obtain ⟨paths, pathsMember, present⟩ := (mem_members _ _).mp member
    obtain ⟨component, componentMember, included⟩ := step_covers classes output success paths pathsMember
    exact (mem_members _ _).mpr ⟨component, componentMember, included path present⟩
  intro path recorded
  have added : path ∈ members (addCongruences classes) := by
    rw [← outputEq] at recorded
    exact (complete_members _ _).mp recorded
  obtain ⟨paths, pathsMember, present⟩ := (mem_members _ _).mp added
  rcases List.mem_append.mp pathsMember with old | generated
  · exact segments_mono gap classes output retained [] path (segmented path ((mem_members _ _).mpr ⟨paths, old, present⟩))
  · obtain ⟨source, sourceMember, suffixMember⟩ := List.mem_flatMap.mp generated
    obtain ⟨suffix, requested, same⟩ := List.mem_map.mp suffixMember
    subst paths
    obtain ⟨replacement, replacementMember, rfl⟩ := (mem_extendClass _ _ _).mp present
    obtain ⟨base, baseMember, extension, extensionMember, _, extensionEq⟩ := (mem_suffixes _ _ _).mp requested
    have replacementRecorded : replacement ∈ members classes := (mem_members _ _).mpr ⟨source, sourceMember, replacementMember⟩
    have baseInitial : base.IsPrefix extension := ⟨suffix, extensionEq⟩
    have first := segments_mono gap classes output retained [] replacement (segmented replacement replacementRecorded)
    have tail := segments_cut gap classes [] extension base (segmented extension extensionMember) (by simp) baseInitial
    have equal : inSame classes base replacement = true := (inSame_correct _ _ _).mpr ⟨source, sourceMember, baseMember, replacementMember⟩
    have translated := segments_replace gap classes output base replacement base extension tail (List.prefix_refl base)
      (fun path member initial => step_replace_member classes output base replacement path equal member initial success)
    have translated' : Segments gap output replacement (replacement ++ suffix) := by
      rw [← extensionEq] at translated
      simpa [replacePrefix] using translated
    exact segments_join gap output [] replacement (replacement ++ suffix) first translated' (retained replacement replacementRecorded)

/-- A class is encountered by a path when one of its members is a prefix. -/
def encounters (paths : Class) (path : List Nat) : Bool := paths.any (fun member => decide (member.IsPrefix path))

/-- Count the classes encountered along one path. -/
def prefixRank (classes : Constraints) (path : List Nat) : Nat := classes.countP (fun paths => encounters paths path)

/-- Extending a path retains every encountered class. -/
theorem encounters_mono (paths : Class) (first last : List Nat) (initial : first.IsPrefix last)
    (seen : encounters paths first = true) : encounters paths last = true := by
  obtain ⟨member, present, starts⟩ := List.any_eq_true.mp seen
  apply List.any_eq_true.mpr
  exact ⟨member, present, by simp only [decide_eq_true_eq] at starts ⊢; exact starts.trans initial⟩

/-- Prefix ranks are monotone. -/
theorem prefixRank_mono (classes : Constraints) (first last : List Nat) (initial : first.IsPrefix last) :
    prefixRank classes first ≤ prefixRank classes last :=
  countP_mono _ _ _ (fun paths _ => encounters_mono paths first last initial)

/-- A new marked proper prefix encounters a new class when no prefix contradiction exists. -/
theorem prefixRank_strict (classes : Constraints) (consistent : isContradicting classes = false)
    (first last : List Nat) (initial : first.IsPrefix last) (proper : first.length < last.length)
    (recorded : last ∈ members classes) : prefixRank classes first < prefixRank classes last := by
  obtain ⟨paths, member, present⟩ := (mem_members _ _).mp recorded
  have seen : encounters paths last = true := List.any_eq_true.mpr ⟨last, present, by simp⟩
  have absent : encounters paths first = false := by
    cases found : encounters paths first with
    | false => rfl
    | true =>
        obtain ⟨earlier, earlierMember, starts⟩ := List.any_eq_true.mp found
        have starts' : earlier.IsPrefix first := by simpa using starts
        have different : earlier ≠ last := by intro same; subst earlier; have := starts'.length_le; omega
        have contradiction := (isContradicting_correct classes).mpr
          ⟨paths, member, earlier, earlierMember, last, present, starts'.trans initial, different⟩
        rw [consistent] at contradiction
        contradiction
  exact countP_strict _ _ _ (fun paths _ => encounters_mono paths first last initial) ⟨paths, member, absent, seen⟩

/-- Segmentation and consistency bound path length by the number of encountered classes. -/
theorem segments_weighted_bound (gap : Nat) (classes : Constraints) (consistent : isContradicting classes = false)
    (first last : List Nat) (segments : Segments gap classes first last) :
    last.length + gap * prefixRank classes first ≤ first.length + gap * (prefixRank classes last + 1) := by
  induction segments with
  | short initial bound =>
      have rankBound := Nat.mul_le_mul_left gap (prefixRank_mono classes _ _ initial)
      simp only [Nat.mul_add, Nat.mul_one]
      omega
  | @step middle last first initial proper remaining bound recorded nested ih =>
      have strict := prefixRank_strict classes consistent first middle initial proper recorded
      have rankBound := Nat.mul_le_mul_left gap (show prefixRank classes first + 1 ≤ prefixRank classes middle by omega)
      simp only [Nat.mul_add, Nat.mul_one] at rankBound ⊢
      simp only [Nat.mul_add, Nat.mul_one] at ih
      omega

/-- A consistent segmented state has a finite uniform bound on all path lengths. -/
theorem segmented_length_bound (gap : Nat) (classes : Constraints) (consistent : isContradicting classes = false)
    (segmented : SegmentedState gap classes) (path : List Nat) (member : path ∈ members classes) :
    path.length ≤ gap * (classes.length + 1) := by
  have weighted := segments_weighted_bound gap classes consistent [] path (segmented path member)
  have rankBound : prefixRank classes path ≤ classes.length := List.countP_le_length
  have productBound := Nat.mul_le_mul_left gap (show prefixRank classes path + 1 ≤ classes.length + 1 by omega)
  simp only [List.length_nil, Nat.zero_add] at weighted
  omega


/-- Every component contains one path from a fixed finite anchor set. -/
def Anchored (anchors : List (List Nat)) (classes : Constraints) : Prop :=
  ∀ paths ∈ classes, ∃ path, path ∈ paths ∧ path ∈ anchors

/-- Distinct components need distinct anchors, so their count is bounded. -/
theorem anchored_class_bound (anchors : List (List Nat)) (classes : Constraints)
    (anchored : Anchored anchors classes)
    (disjoint : classes.Pairwise (fun left right => overlap left right = false)) : classes.length ≤ anchors.length := by
  classical
  let pick : Class → List Nat := fun paths => if member : paths ∈ classes then Classical.choose (anchored paths member) else []
  have chosen : ∀ paths ∈ classes, pick paths ∈ paths ∧ pick paths ∈ anchors := by
    intro paths member
    simpa [pick, member] using Classical.choose_spec (anchored paths member)
  have unique : (classes.map pick).Nodup := by
    change (classes.map pick).Pairwise (· ≠ ·)
    rw [List.pairwise_map]
    apply disjoint.imp_of_mem
    intro left right leftMember rightMember apart same
    have shared := (overlap_correct left right).mpr
      ⟨pick left, (chosen left leftMember).1, same ▸ (chosen right rightMember).1⟩
    rw [apart] at shared
    contradiction
  have subset : ∀ path ∈ classes.map pick, path ∈ anchors := by
    intro path member
    obtain ⟨paths, pathsMember, rfl⟩ := List.mem_map.mp member
    exact (chosen paths pathsMember).2
  have bound := unique.length_le_of_subset subset
  simpa using bound

/-- Each source step preserves an original-path anchor in every component. -/
theorem step_anchored (anchors : List (List Nat)) (classes output : Constraints)
    (active : Active classes) (anchored : Anchored anchors classes)
    (success : congruenceStep classes = some output) : Anchored anchors output := by
  have normal := step_normal classes output active success
  have outputEq : complete (addCongruences classes) = output := by
    dsimp only [congruenceStep] at success
    split at success
    next contradiction => simp at success
    next consistent => exact Option.some.inj success
  intro component componentMember
  have inherits : ∀ source ∈ classes, ∀ shared, shared ∈ source → shared ∈ component →
      ∃ path, path ∈ component ∧ path ∈ anchors := by
    intro source sourceMember shared inSource inComponent
    obtain ⟨retained, retainedMember, included⟩ := step_covers classes output success source sourceMember
    have same := components_equal output normal.2.1 retained component retainedMember componentMember shared (included shared inSource) inComponent
    obtain ⟨anchor, anchorMember, original⟩ := anchored source sourceMember
    exact ⟨anchor, by simpa [same] using included anchor anchorMember, original⟩
  obtain ⟨path, present, _, _, _⟩ := normal.1 component componentMember
  have pathRecorded : path ∈ members output := (mem_members _ _).mpr ⟨component, componentMember, present⟩
  have added : path ∈ members (addCongruences classes) := by
    rw [← outputEq] at pathRecorded
    exact (complete_members _ _).mp pathRecorded
  obtain ⟨paths, pathsMember, atPath⟩ := (mem_members _ _).mp added
  rcases List.mem_append.mp pathsMember with old | generated
  · exact inherits paths old path atPath present
  · obtain ⟨source, sourceMember, mapped⟩ := List.mem_flatMap.mp generated
    obtain ⟨suffix, requested, same⟩ := List.mem_map.mp mapped
    subst paths
    obtain ⟨base, baseMember, originalPath, originalMember, _, equal⟩ := (mem_suffixes _ _ _).mp requested
    have generatedMember : extendClass source suffix ∈ addCongruences classes := List.mem_append_right _
      (List.mem_flatMap.mpr ⟨source, sourceMember, List.mem_map.mpr ⟨suffix, requested, rfl⟩⟩)
    obtain ⟨retained, retainedMember, included⟩ := complete_covers (addCongruences classes) (extendClass source suffix) generatedMember
    rw [outputEq] at retainedMember
    have same := components_equal output normal.2.1 retained component retainedMember componentMember path (included path atPath) present
    have originalInComponent : originalPath ∈ component := by
      have originalInGenerated := (mem_extendClass originalPath source suffix).mpr ⟨base, baseMember, equal⟩
      simpa [same] using included originalPath originalInGenerated
    obtain ⟨oldClass, oldClassMember, inOld⟩ := (mem_members _ _).mp originalMember
    exact inherits oldClass oldClassMember originalPath inOld originalInComponent

/-- Every active initial class has an anchor in its own finite recorded-path set. -/
theorem initially_anchored (classes : Constraints) (active : Active classes) : Anchored (members classes) classes := by
  intro paths member
  obtain ⟨path, present, _, _, _⟩ := active paths member
  exact ⟨path, present, (mem_members _ _).mpr ⟨paths, member, present⟩⟩

/-- Recorded paths use only indices from a fixed finite alphabet. -/
def UsesAlphabet (alphabet : List Nat) (classes : Constraints) : Prop :=
  ∀ path ∈ members classes, ∀ index ∈ path, index ∈ alphabet

/-- Source suffix generation introduces no new child indices. -/
theorem step_alphabet (alphabet : List Nat) (classes output : Constraints)
    (allowed : UsesAlphabet alphabet classes) (success : congruenceStep classes = some output) : UsesAlphabet alphabet output := by
  have outputEq : complete (addCongruences classes) = output := by
    dsimp only [congruenceStep] at success
    split at success
    next contradiction => simp at success
    next consistent => exact Option.some.inj success
  intro path member index inPath
  have added : path ∈ members (addCongruences classes) := by
    rw [← outputEq] at member
    exact (complete_members _ _).mp member
  obtain ⟨paths, pathsMember, present⟩ := (mem_members _ _).mp added
  rcases List.mem_append.mp pathsMember with old | generated
  · exact allowed path ((mem_members _ _).mpr ⟨paths, old, present⟩) index inPath
  · obtain ⟨source, sourceMember, mapped⟩ := List.mem_flatMap.mp generated
    obtain ⟨suffix, requested, same⟩ := List.mem_map.mp mapped
    subst paths
    obtain ⟨replacement, replacementMember, rfl⟩ := (mem_extendClass _ _ _).mp present
    rcases List.mem_append.mp inPath with inReplacement | inSuffix
    · exact allowed replacement ((mem_members _ _).mpr ⟨source, sourceMember, replacementMember⟩) index inReplacement
    · obtain ⟨base, _, original, originalMember, _, equal⟩ := (mem_suffixes _ _ _).mp requested
      apply allowed original originalMember index
      rw [← equal]
      exact List.mem_append_right _ inSuffix

/-- All finite paths over an alphabet up to a supplied length. -/
def words (alphabet : List Nat) : Nat → List (List Nat)
  | 0 => [[]]
  | bound + 1 => [] :: alphabet.flatMap (fun index => (words alphabet bound).map (index :: ·))

/-- The finite word domain is exact. -/
theorem words_correct (alphabet : List Nat) (bound : Nat) (path : List Nat) :
    path ∈ words alphabet bound ↔ path.length ≤ bound ∧ ∀ index ∈ path, index ∈ alphabet := by
  induction bound generalizing path with
  | zero => cases path <;> simp [words]
  | succ bound ih =>
      cases path with
      | nil => simp [words]
      | cons index rest =>
          simp [words, ih, and_assoc, and_left_comm, and_comm]


/-- Every successful state lies in a fixed finite path domain. -/
theorem bounded_state (gap : Nat) (anchors : List (List Nat)) (alphabet : List Nat) (classes : Constraints)
    (normal : NormalState classes) (consistent : isContradicting classes = false)
    (segmented : SegmentedState gap classes) (anchored : Anchored anchors classes) (allowed : UsesAlphabet alphabet classes) :
    Within (words alphabet (gap * (anchors.length + 1))) classes := by
  intro path member
  apply (words_correct alphabet _ path).mpr
  have classBound := anchored_class_bound anchors classes anchored normal.2.1
  have lengthBound := segmented_length_bound gap classes consistent segmented path member
  have productBound := Nat.mul_le_mul_left gap (show classes.length + 1 ≤ anchors.length + 1 by omega)
  exact ⟨Nat.le_trans lengthBound productBound, allowed path member⟩


/-- A bounded-gap, anchored state reaches a fixed point or contradiction in finitely many steps. -/
theorem fixMaybe_finishes_bounded (gap : Nat) (anchors : List (List Nat)) (alphabet : List Nat)
    (fuel : Nat) (classes : Constraints) (normal : NormalState classes)
    (segmented : SegmentedState gap classes) (anchored : Anchored anchors classes) (allowed : UsesAlphabet alphabet classes)
    (enough : (pathPairs (words alphabet (gap * (anchors.length + 1)))).length -
      relationCount (words alphabet (gap * (anchors.length + 1))) classes + 1 ≤ fuel) :
    fixMaybe fuel classes ≠ .timeout := by
  induction fuel generalizing classes with
  | zero => omega
  | succ fuel ih =>
      cases stepped : congruenceStep classes with
      | none => simp [fixMaybe, stepped]
      | some next =>
          by_cases stable : next = classes
          · simp [fixMaybe, stepped, stable]
          · have nextNormal := step_normal classes next normal.1 stepped
            have nextSegmented := step_segmented gap classes next segmented stepped
            have nextAnchored := step_anchored anchors classes next normal.1 anchored stepped
            have nextAllowed := step_alphabet alphabet classes next allowed stepped
            have consistent := (congruenceStep_invariants classes next normal.1 stepped).2
            have within := bounded_state gap anchors alphabet next nextNormal consistent nextSegmented nextAnchored nextAllowed
            have growth := relationCount_strict (words alphabet (gap * (anchors.length + 1))) classes next
              normal nextNormal (step_covers classes next stepped) within stable
            have currentBound := relationCount_bound (words alphabet (gap * (anchors.length + 1))) classes
            have nextBound := relationCount_bound (words alphabet (gap * (anchors.length + 1))) next
            have finished := ih next nextNormal nextSegmented nextAnchored nextAllowed (by omega)
            simpa [fixMaybe, stepped, stable] using finished

/-- The initial finite path set bounds the maximum unmarked path segment. -/
def initialGap (classes : Constraints) : Nat := MicroCFTA.EqualityTrie.pathBudget (members classes)

/-- Every original path fits within one bounded segment. -/
theorem initially_segmented (classes : Constraints) : SegmentedState (initialGap classes) classes := by
  intro path member
  have bound := MicroCFTA.EqualityTrie.pathBudget_sufficient (members classes) path member
  exact .short (by simp) (by simp only [List.length_nil, Nat.zero_add]; exact Nat.le_of_lt bound)

/-- Collect the child indices that occur in the initial paths. -/
def initialAlphabet (classes : Constraints) : List Nat := (members classes).flatten.eraseDups

/-- Initial child indices lie in their computed finite alphabet. -/
theorem initially_allowed (classes : Constraints) : UsesAlphabet (initialAlphabet classes) classes := by
  intro path member index present
  simp only [initialAlphabet, List.mem_eraseDups, List.mem_flatten]
  exact ⟨path, member, present⟩

/-- A finite path domain for every successful state descended from the initial one. -/
def saturationDomain (classes : Constraints) : List (List Nat) :=
  words (initialAlphabet classes) (initialGap classes * ((members classes).length + 1))

/-- A conservative proof bound on strict relation growth and the final stopping step. -/
def saturationBound (classes : Constraints) : Nat := (pathPairs (saturationDomain classes)).length + 1

/-- Every canonical active state terminates without a finite-model premise. -/
theorem fixMaybe_terminates (classes : Constraints) (normal : NormalState classes) :
    fixMaybe (saturationBound classes) classes ≠ .timeout := by
  apply fixMaybe_finishes_bounded (initialGap classes) (members classes) (initialAlphabet classes)
    (saturationBound classes) classes normal (initially_segmented classes) (initially_anchored classes normal.1)
    (initially_allowed classes)
  unfold saturationBound saturationDomain
  omega

/-- The concrete normalization bound uses the prepared canonical starting state. -/
def normalizationBound (classes : Constraints) : Nat := saturationBound (complete (prepare classes))

/-- Source normalization always stops, including unsatisfiable inputs. -/
theorem mkEqConstraints_terminates (classes : Constraints) :
    mkEqConstraints (normalizationBound classes) classes ≠ .timeout :=
  fixMaybe_terminates (complete (prepare classes)) (complete_normal (prepare classes) (prepare_active classes))

/-- Total finite normalization has exactly the original existing-path PCS meaning. -/
theorem mkEqConstraints_total_correct (term : Term Symbol) (classes : Constraints) :
    RunSat term (mkEqConstraints (normalizationBound classes) classes) ↔ Satisfies term classes :=
  mkEqConstraints_correct term (normalizationBound classes) classes (mkEqConstraints_terminates classes)

/-- The terminating normalizer can only reject or return a fixed-point class list. -/
theorem mkEqConstraints_total_cases (classes : Constraints) :
    mkEqConstraints (normalizationBound classes) classes = .contradiction ∨
      ∃ output, mkEqConstraints (normalizationBound classes) classes = .normalized output ∧
        NormalState output ∧ isContradicting output = false ∧ congruenceStep output = some output := by
  have finished := mkEqConstraints_terminates classes
  cases result : mkEqConstraints (normalizationBound classes) classes with
  | timeout => exact False.elim (finished result)
  | contradiction => exact Or.inl rfl
  | normalized output =>
      obtain ⟨active, consistent, disjoint, fixed⟩ := mkEqConstraints_invariants _ _ _ result
      have normal := step_normal output output active fixed
      exact Or.inr ⟨output, rfl, normal, consistent, fixed⟩

end MicroCFTA.EqualityTermination
