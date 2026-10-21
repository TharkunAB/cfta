import MicroCFTA.Language
import MicroCFTA.EqualityTrie

/-!
# Equality-class normalization

Classes denote equality of their distinct existing paths. Empty and singleton
classes impose no condition. A `Same p p` guard still requires path existence.

The executable completion below merges overlapping finite path sets. The
Haskell implementation uses union-find to compute these same components.
Completion has an exact connected-component characterization. Canonical
partitions with that characterization are equal. The source ST array loop
must still establish that characterization.

Congruence generation and bounded fixed-point iteration are explicit phases.
The sorted strict-extension range optimization has the same suffix set as the
full scan. Every completed bounded execution preserves the input denotation.
This module does not prove a bound that makes every saturation run finish.
-/

namespace MicroCFTA.EqualityNormalize
open MicroCFTA.Language

abbrev Path := List Nat
abbrev Class := List Path
abbrev Constraints := List Class

/-- A PCS class equates every pair of distinct paths. Trivial classes impose no condition. -/
def ClassSat (term : Term Symbol) (paths : Class) : Prop :=
  ∀ left ∈ paths, ∀ right ∈ paths, left ≠ right → PathsEqual term left right

/-- All equality classes constrain the same complete term. -/
def Satisfies (term : Term Symbol) (classes : Constraints) : Prop :=
  ∀ paths ∈ classes, ClassSat term paths

/-- A constraint-list head contributes one class condition. -/
theorem satisfies_cons (term : Term Symbol) (paths : Class) (classes : Constraints) :
    Satisfies term (paths :: classes) ↔ ClassSat term paths ∧ Satisfies term classes := by
  simp [Satisfies]

/-- A class has at least two distinct set members. -/
def Nontrivial (paths : Class) : Prop := ∃ left ∈ paths, ∃ right ∈ paths, left ≠ right

/-- Every class in the normalization state has at least two members. -/
def Active (classes : Constraints) : Prop := ∀ paths ∈ classes, Nontrivial paths

/-- Existing-path equality is symmetric. -/
theorem pathsEqual_symm {term : Term Symbol} {left right : Path} (equal : PathsEqual term left right) :
    PathsEqual term right left := by
  obtain ⟨value, first, second⟩ := equal
  exact ⟨value, second, first⟩

/-- Existing-path equality is transitive. -/
theorem pathsEqual_trans {term : Term Symbol} {left middle right : Path}
    (first : PathsEqual term left middle) (second : PathsEqual term middle right) :
    PathsEqual term left right := by
  obtain ⟨value, leftValue, middleValue⟩ := first
  obtain ⟨other, sameMiddle, rightValue⟩ := second
  have same : value = other := Option.some.inj (middleValue.symm.trans sameMiddle)
  subst other
  exact ⟨value, leftValue, rightValue⟩

/-- Class semantics depends only on its set of paths. -/
theorem classSat_congr (term : Term Symbol) (left right : Class)
    (same : ∀ path, path ∈ left ↔ path ∈ right) : ClassSat term left ↔ ClassSat term right := by
  constructor
  · intro satisfies first firstMember second secondMember different
    exact satisfies first ((same first).mpr firstMember) second ((same second).mpr secondMember) different
  · intro satisfies first firstMember second secondMember different
    exact satisfies first ((same first).mp firstMember) second ((same second).mp secondMember) different

/-- Set insertion removes duplicates without changing PCS semantics. -/
theorem classSat_eraseDups (term : Term Symbol) (paths : Class) :
    ClassSat term paths.eraseDups ↔ ClassSat term paths :=
  classSat_congr term _ _ (by intro path; simp)

/-- A set with fewer than two members imposes no equality. -/
theorem trivial_satisfies (term : Term Symbol) (paths : Class) (trivial : ¬Nontrivial paths) : ClassSat term paths := by
  intro left leftMember right rightMember different
  exact False.elim (trivial ⟨left, leftMember, right, rightMember, different⟩)

/-- Decide whether a class has two distinct paths. -/
def nontrivialB (paths : Class) : Bool := paths.any (fun left => paths.any (fun right => decide (left ≠ right)))

/-- The finite class test is exact. -/
theorem nontrivialB_correct (paths : Class) : nontrivialB paths = true ↔ Nontrivial paths := by
  simp [nontrivialB, Nontrivial, List.any_eq_true]

/-- Remove repeated paths and classes with fewer than two set members. -/
def prepare (classes : Constraints) : Constraints :=
  (classes.map List.eraseDups).filter nontrivialB

/-- Input preparation preserves every PCS equality condition. -/
theorem prepare_correct (term : Term Symbol) (classes : Constraints) :
    Satisfies term (prepare classes) ↔ Satisfies term classes := by
  constructor
  · intro output paths member
    by_cases active : Nontrivial paths.eraseDups
    · apply (classSat_eraseDups term paths).mp
      exact output paths.eraseDups (List.mem_filter.mpr
        ⟨List.mem_map.mpr ⟨paths, member, rfl⟩, (nontrivialB_correct _).mpr active⟩)
    · exact (classSat_eraseDups term paths).mp (trivial_satisfies term paths.eraseDups active)
  · intro original paths member
    obtain ⟨mapped, _⟩ := List.mem_filter.mp member
    obtain ⟨source, sourceMember, rfl⟩ := List.mem_map.mp mapped
    exact (classSat_eraseDups term source).mpr (original source sourceMember)

/-- Preparation establishes the required path-existence invariant. -/
theorem prepare_active (classes : Constraints) : Active (prepare classes) := by
  intro paths member
  exact (nontrivialB_correct paths).mp (List.mem_filter.mp member).2

/-- Each path in a nontrivial satisfied class denotes an existing subterm. -/
theorem class_member_exists (term : Term Symbol) (paths : Class) (active : Nontrivial paths)
    (satisfied : ClassSat term paths) (path : Path) (member : path ∈ paths) :
    ∃ value, term.atPath path = some value := by
  obtain ⟨left, leftMember, right, rightMember, different⟩ := active
  by_cases same : path = left
  · subst path
    obtain ⟨value, found, _⟩ := satisfied left leftMember right rightMember different
    exact ⟨value, found⟩
  · obtain ⟨value, found, _⟩ := satisfied path member left leftMember same
    exact ⟨value, found⟩

/-- In an active class, the equality relation includes reflexive existing-path cases. -/
theorem class_pair_equal (term : Term Symbol) (paths : Class) (active : Nontrivial paths)
    (satisfied : ClassSat term paths) (left right : Path) (leftMember : left ∈ paths) (rightMember : right ∈ paths) :
    PathsEqual term left right := by
  by_cases same : left = right
  · subst right
    obtain ⟨value, found⟩ := class_member_exists term paths active satisfied left leftMember
    exact ⟨value, found, found⟩
  · exact satisfied left leftMember right rightMember same

/-- Class intersection is a finite shared-member test. -/
def overlap (left right : Class) : Bool := left.any (fun path => decide (path ∈ right))

/-- The overlap test finds precisely a common path. -/
theorem overlap_correct (left right : Class) : overlap left right = true ↔ ∃ path, path ∈ left ∧ path ∈ right := by
  simp [overlap, List.any_eq_true]

/-- The union of overlapping classes has exactly the two original equality conditions. -/
theorem merge_correct (term : Term Symbol) (left right : Class) (shared : overlap left right = true) :
    ClassSat term (left ++ right).eraseDups ↔ ClassSat term left ∧ ClassSat term right := by
  rw [classSat_eraseDups]
  obtain ⟨pivot, pivotLeft, pivotRight⟩ := (overlap_correct _ _).mp shared
  constructor
  · intro merged
    exact ⟨fun p hp q hq different => merged p (List.mem_append_left _ hp) q (List.mem_append_left _ hq) different,
      fun p hp q hq different => merged p (List.mem_append_right _ hp) q (List.mem_append_right _ hq) different⟩
  · rintro ⟨leftSat, rightSat⟩
    have cross : ∀ p ∈ left, ∀ q ∈ right, p ≠ q → PathsEqual term p q := by
      intro p hp q hq different
      by_cases first : p = pivot
      · subst p
        exact rightSat pivot pivotRight q hq different
      by_cases second : q = pivot
      · subst q
        exact leftSat p hp pivot pivotLeft different
      exact pathsEqual_trans (leftSat p hp pivot pivotLeft first)
        (pathsEqual_symm (rightSat q hq pivot pivotRight second))
    intro p hp q hq different
    rcases List.mem_append.mp hp with hp | hp <;> rcases List.mem_append.mp hq with hq | hq
    · exact leftSat p hp q hq different
    · exact cross p hp q hq different
    · exact pathsEqual_symm (cross q hq p hp (Ne.symm different))
    · exact rightSat p hp q hq different

/-- Merge one selected class with its first overlapping later class. -/
def joinOne (paths : Class) : Constraints → Option Constraints
  | [] => none
  | next :: rest =>
      if overlap paths next then some ((paths ++ next).eraseDups :: rest)
      else (joinOne paths rest).map (next :: ·)

/-- Execute the first available class merge. -/
def mergeOne : Constraints → Option Constraints
  | [] => none
  | paths :: rest =>
      match joinOne paths rest with
      | some merged => some merged
      | none => (mergeOne rest).map (paths :: ·)

/-- Joining one class preserves all equality conditions. -/
theorem joinOne_correct (term : Term Symbol) (paths : Class) (rest output : Constraints)
    (success : joinOne paths rest = some output) :
    Satisfies term output ↔ ClassSat term paths ∧ Satisfies term rest := by
  induction rest generalizing output with
  | nil => simp [joinOne] at success
  | cons next rest ih =>
      by_cases shared : overlap paths next = true
      · simp [joinOne, shared] at success
        subst output
        simp only [Satisfies, List.mem_cons, forall_eq_or_imp]
        rw [merge_correct term paths next shared]
        exact and_assoc
      · cases recursive : joinOne paths rest with
        | none => simp [joinOne, shared, recursive] at success
        | some merged =>
            have same : output = next :: merged := by simpa [joinOne, shared, recursive] using success.symm
            subst output
            rw [satisfies_cons, satisfies_cons, ih merged recursive]
            exact and_left_comm

/-- One overlap merge preserves the complete constraint set. -/
theorem mergeOne_correct (term : Term Symbol) (classes output : Constraints)
    (success : mergeOne classes = some output) : Satisfies term output ↔ Satisfies term classes := by
  induction classes generalizing output with
  | nil => simp [mergeOne] at success
  | cons paths rest ih =>
      cases joined : joinOne paths rest with
      | some merged =>
          simp [mergeOne, joined] at success
          subst output
          simpa [Satisfies] using joinOne_correct term paths rest merged joined
      | none =>
          cases recursive : mergeOne rest with
          | none => simp [mergeOne, joined, recursive] at success
          | some merged =>
              have same : output = paths :: merged := by simpa [mergeOne, joined, recursive] using success.symm
              subst output
              rw [satisfies_cons, satisfies_cons, ih merged recursive]


/-- Inclusion in a larger class preserves nontriviality. -/
theorem nontrivial_mono (left right : Class) (subset : ∀ path ∈ left, path ∈ right)
    (active : Nontrivial left) : Nontrivial right := by
  obtain ⟨first, firstMember, second, secondMember, different⟩ := active
  exact ⟨first, subset first firstMember, second, subset second secondMember, different⟩

/-- Joining two classes does not create a trivial class. -/
theorem joinOne_active (paths : Class) (rest output : Constraints) (first : Nontrivial paths)
    (active : Active rest) (success : joinOne paths rest = some output) : Active output := by
  induction rest generalizing output with
  | nil => simp [joinOne] at success
  | cons next rest ih =>
      by_cases shared : overlap paths next = true
      · simp [joinOne, shared] at success
        subst output
        intro cls member
        rcases List.mem_cons.mp member with rfl | member
        · exact nontrivial_mono paths _ (by intro path member; simp [member]) first
        · exact active cls (by simp [member])
      · cases recursive : joinOne paths rest with
        | none => simp [joinOne, shared, recursive] at success
        | some merged =>
            have same : output = next :: merged := by simpa [joinOne, shared, recursive] using success.symm
            subst output
            intro cls member
            rcases List.mem_cons.mp member with rfl | member
            · exact active cls (by simp)
            · exact ih merged (fun cls present => active cls (by simp [present])) recursive cls member

/-- One completion merge preserves nontrivial classes. -/
theorem mergeOne_active (classes output : Constraints) (active : Active classes)
    (success : mergeOne classes = some output) : Active output := by
  induction classes generalizing output with
  | nil => simp [mergeOne] at success
  | cons paths rest ih =>
      cases joined : joinOne paths rest with
      | some merged =>
          simp [mergeOne, joined] at success
          subst output
          exact joinOne_active paths rest merged (active paths (by simp))
            (fun cls member => active cls (by simp [member])) joined
      | none =>
          cases recursive : mergeOne rest with
          | none => simp [mergeOne, joined, recursive] at success
          | some merged =>
              have same : output = paths :: merged := by simpa [mergeOne, joined, recursive] using success.symm
              subst output
              intro cls member
              rcases List.mem_cons.mp member with rfl | member
              · exact active cls (by simp)
              · exact ih merged (fun cls present => active cls (by simp [present])) recursive cls member

/-- A successful join removes one of the original classes. -/
theorem joinOne_length (paths : Class) (rest output : Constraints) (success : joinOne paths rest = some output) :
    output.length = rest.length := by
  induction rest generalizing output with
  | nil => simp [joinOne] at success
  | cons next rest ih =>
      by_cases shared : overlap paths next = true
      · simp [joinOne, shared] at success
        subst output
        rfl
      · cases recursive : joinOne paths rest with
        | none => simp [joinOne, shared, recursive] at success
        | some merged =>
            have same : output = next :: merged := by simpa [joinOne, shared, recursive] using success.symm
            subst output
            simp [ih merged recursive]

/-- Every completion merge strictly decreases the number of classes. -/
theorem mergeOne_length (classes output : Constraints) (success : mergeOne classes = some output) :
    output.length + 1 = classes.length := by
  induction classes generalizing output with
  | nil => simp [mergeOne] at success
  | cons paths rest ih =>
      cases joined : joinOne paths rest with
      | some merged =>
          simp [mergeOne, joined] at success
          subst output
          simp [joinOne_length paths rest merged joined]
      | none =>
          cases recursive : mergeOne rest with
          | none => simp [mergeOne, joined, recursive] at success
          | some merged =>
              have same : output = paths :: merged := by simpa [mergeOne, joined, recursive] using success.symm
              subst output
              simp [ih merged recursive]

/-- Failure to join means that the selected class has no later overlap. -/
theorem joinOne_none (paths : Class) (rest : Constraints) :
    joinOne paths rest = none ↔ ∀ next ∈ rest, overlap paths next = false := by
  induction rest with
  | nil => simp [joinOne]
  | cons next rest ih =>
      cases shared : overlap paths next <;> simp [joinOne, shared, ih]

/-- Completion stops precisely at disjoint classes. -/
theorem mergeOne_none (classes : Constraints) :
    mergeOne classes = none ↔ classes.Pairwise (fun left right => overlap left right = false) := by
  induction classes with
  | nil => simp [mergeOne]
  | cons paths rest ih =>
      cases joined : joinOne paths rest with
      | none =>
          simp [mergeOne, joined, List.pairwise_cons, ih]
          exact fun _ => (joinOne_none paths rest).mp joined
      | some merged =>
          have hasOverlap : ¬∀ next ∈ rest, overlap paths next = false := by
            intro none
            have impossible := (joinOne_none paths rest).mpr none
            rw [joined] at impossible
            contradiction
          simp [mergeOne, joined, List.pairwise_cons, hasOverlap]

/-- Repeated overlap merging with an explicit termination bound. -/
def completeFuel : Nat → Constraints → Constraints
  | 0, classes => classes
  | fuel + 1, classes =>
      match mergeOne classes with
      | none => classes
      | some merged => completeFuel fuel merged

/-- Overlap is symmetric even though the executable scan uses one list. -/
theorem overlap_symm (left right : Class) : overlap left right = overlap right left := by
  cases first : overlap left right <;> cases second : overlap right left <;> try rfl
  · obtain ⟨path, rightMember, leftMember⟩ := (overlap_correct right left).mp second
    have impossible := (overlap_correct left right).mpr ⟨path, leftMember, rightMember⟩
    simp [first] at impossible
  · obtain ⟨path, leftMember, rightMember⟩ := (overlap_correct left right).mp first
    have impossible := (overlap_correct right left).mpr ⟨path, rightMember, leftMember⟩
    simp [second] at impossible

/-- Canonical ascending enumeration of one finite path set. -/
def canonicalClass (paths : Class) : Class := paths.eraseDups.mergeSort (fun left right => left ≤ right)

/-- Canonicalize paths and then order the classes, as the source completion does. -/
def canonicalize (classes : Constraints) : Constraints :=
  (classes.map canonicalClass).mergeSort (fun left right => left ≤ right)

/-- Canonical ordering does not change class membership. -/
theorem mem_canonicalClass (path : Path) (paths : Class) : path ∈ canonicalClass paths ↔ path ∈ paths := by
  simp [canonicalClass]

/-- Canonical path-set conversion preserves class equality conditions. -/
theorem canonicalClass_correct (term : Term Symbol) (paths : Class) : ClassSat term (canonicalClass paths) ↔ ClassSat term paths :=
  classSat_congr term _ _ (fun path => mem_canonicalClass path paths)

/-- Canonical class ordering preserves the complete equality condition. -/
theorem canonicalize_correct (term : Term Symbol) (classes : Constraints) :
    Satisfies term (canonicalize classes) ↔ Satisfies term classes := by
  simp only [Satisfies, canonicalize, List.mem_mergeSort, List.forall_mem_map, canonicalClass_correct]

/-- Set enumeration retains nontrivial classes. -/
theorem canonicalize_active (classes : Constraints) (active : Active classes) : Active (canonicalize classes) := by
  intro paths member
  have mapped : paths ∈ classes.map canonicalClass := by simpa [canonicalize] using member
  obtain ⟨source, sourceMember, rfl⟩ := List.mem_map.mp mapped
  exact nontrivial_mono source _ (fun path present => (mem_canonicalClass path source).mpr present) (active source sourceMember)

/-- Overlap is independent of canonical set enumeration. -/
theorem overlap_canonicalClass (left right : Class) : overlap (canonicalClass left) (canonicalClass right) = overlap left right := by
  apply Bool.eq_iff_iff.mpr
  simp only [overlap_correct, mem_canonicalClass]

/-- Canonical sorting retains disjoint components. -/
theorem canonicalize_disjoint (classes : Constraints)
    (disjoint : classes.Pairwise (fun left right => overlap left right = false)) :
    (canonicalize classes).Pairwise (fun left right => overlap left right = false) := by
  have mapped : (classes.map canonicalClass).Pairwise (fun left right => overlap left right = false) := disjoint.map canonicalClass (fun left right absent => by simpa [overlap_canonicalClass] using absent)
  exact mapped.perm (List.mergeSort_perm _ _).symm (fun absent => by rw [overlap_symm]; exact absent)

/-- Completion can merge at most the original number of classes. -/
def complete (classes : Constraints) : Constraints := canonicalize (completeFuel classes.length classes)

/-- Every finite completion pass preserves exactly the original equality conditions. -/
theorem completeFuel_correct (term : Term Symbol) (fuel : Nat) (classes : Constraints) :
    Satisfies term (completeFuel fuel classes) ↔ Satisfies term classes := by
  induction fuel generalizing classes with
  | zero => rfl
  | succ fuel ih =>
      cases merged : mergeOne classes with
      | none => simp [completeFuel, merged]
      | some output =>
          simp only [completeFuel, merged]
          exact (ih output).trans (mergeOne_correct term classes output merged)

/-- Completion preserves the path-existence invariant. -/
theorem completeFuel_active (fuel : Nat) (classes : Constraints) (active : Active classes) :
    Active (completeFuel fuel classes) := by
  induction fuel generalizing classes with
  | zero => exact active
  | succ fuel ih =>
      cases merged : mergeOne classes with
      | none => simpa [completeFuel, merged] using active
      | some output => simpa [completeFuel, merged] using ih output (mergeOne_active classes output active merged)

/-- The computed completion bound is sufficient to reach disjoint classes. -/
theorem completeFuel_disjoint (fuel : Nat) (classes : Constraints) (enough : classes.length ≤ fuel) :
    (completeFuel fuel classes).Pairwise (fun left right => overlap left right = false) := by
  induction fuel generalizing classes with
  | zero => have empty : classes = [] := List.length_eq_zero_iff.mp (by omega); simp [completeFuel, empty]
  | succ fuel ih =>
      cases merged : mergeOne classes with
      | none => simpa [completeFuel, merged] using (mergeOne_none classes).mp merged
      | some output =>
          have shorter := mergeOne_length classes output merged
          simpa [completeFuel, merged] using ih output (by omega)

/-- Canonical component completion preserves the original equality conditions. -/
theorem complete_correct (term : Term Symbol) (classes : Constraints) : Satisfies term (complete classes) ↔ Satisfies term classes :=
  (canonicalize_correct term _).trans (completeFuel_correct term _ _)

/-- Canonical component completion retains nontrivial classes. -/
theorem complete_active (classes : Constraints) (active : Active classes) : Active (complete classes) :=
  canonicalize_active _ (completeFuel_active _ _ active)

/-- Canonical completion returns pairwise disjoint components. -/
theorem complete_disjoint (classes : Constraints) : (complete classes).Pairwise (fun left right => overlap left right = false) :=
  canonicalize_disjoint _ (completeFuel_disjoint _ _ (Nat.le_refl _))

/-- Executable completion returns semantically equivalent disjoint active classes. -/
theorem complete_spec (term : Term Symbol) (classes : Constraints) (active : Active classes) :
    (Satisfies term (complete classes) ↔ Satisfies term classes) ∧ Active (complete classes) ∧
      (complete classes).Pairwise (fun left right => overlap left right = false) :=
  ⟨complete_correct term _, complete_active _ active, complete_disjoint _⟩


/-- All recorded paths, interpreted as a finite set. -/
def members (classes : Constraints) : List Path := classes.flatten.eraseDups

/-- Recorded-path membership exposes its source class. -/
theorem mem_members (path : Path) (classes : Constraints) :
    path ∈ members classes ↔ ∃ paths ∈ classes, path ∈ paths := by
  simp [members]

/-- Return the nonempty suffix of a strict path extension. -/
def strictSuffix (base extension : Path) : Option Path :=
  if base.IsPrefix extension ∧ base ≠ extension then some (extension.drop base.length) else none

/-- Prefix-suffix extraction is exact, including its strictness condition. -/
theorem strictSuffix_correct (base extension suffix : Path) :
    strictSuffix base extension = some suffix ↔ suffix ≠ [] ∧ base ++ suffix = extension := by
  constructor
  · intro selected
    unfold strictSuffix at selected
    split at selected
    next condition =>
      obtain ⟨rest, same⟩ := condition.1
      subst extension
      have equal : rest = suffix := by simpa using selected
      subst rest
      refine ⟨?_, rfl⟩
      intro empty
      simp [empty] at condition
    next condition => simp at selected
  · rintro ⟨nonempty, rfl⟩
    have distinct : base ≠ base ++ suffix := by
      intro equal
      have lengths := congrArg List.length equal
      simp only [List.length_append] at lengths
      have empty : suffix = [] := List.length_eq_zero_iff.mp (by omega)
      contradiction
    simp [strictSuffix, distinct]

/-- Every suffix read from a class and any recorded strict extension. -/
def suffixes (paths : Class) (classes : Constraints) : List Path :=
  (paths.flatMap (fun base => (members classes).filterMap (strictSuffix base))).eraseDups

/-- The suffix table records precisely the class's recorded strict extensions. -/
theorem mem_suffixes (suffix : Path) (paths : Class) (classes : Constraints) :
    suffix ∈ suffixes paths classes ↔
      ∃ base ∈ paths, ∃ extension ∈ members classes, suffix ≠ [] ∧ base ++ suffix = extension := by
  simp [suffixes, List.mem_flatMap, strictSuffix_correct]

/-- Extend every class member by the same suffix and preserve set semantics. -/
def extendClass (paths : Class) (suffix : Path) : Class := (paths.map (· ++ suffix)).eraseDups

/-- Generated classes contain exactly the uniformly extended paths. -/
theorem mem_extendClass (path : Path) (paths : Class) (suffix : Path) :
    path ∈ extendClass paths suffix ↔ ∃ base ∈ paths, base ++ suffix = path := by
  simp [extendClass]

/-- A common path suffix preserves distinctness of class members. -/
theorem extendClass_active (paths : Class) (suffix : Path) (active : Nontrivial paths) :
    Nontrivial (extendClass paths suffix) := by
  obtain ⟨left, leftMember, right, rightMember, different⟩ := active
  refine ⟨left ++ suffix, (mem_extendClass _ _ _).mpr ⟨left, leftMember, rfl⟩,
    right ++ suffix, (mem_extendClass _ _ _).mpr ⟨right, rightMember, rfl⟩, ?_⟩
  intro same
  exact different (List.append_cancel_right same)

/-- Add exactly the prefix-induced equality classes used by normalization. -/
def addCongruences (classes : Constraints) : Constraints :=
  classes ++ classes.flatMap (fun paths => (suffixes paths classes).map (extendClass paths))

/-- Prefix-induced classes remain nontrivial. -/
theorem addCongruences_active (classes : Constraints) (active : Active classes) : Active (addCongruences classes) := by
  intro paths member
  rcases List.mem_append.mp member with original | generated
  · exact active paths original
  · obtain ⟨source, sourceMember, built⟩ := List.mem_flatMap.mp generated
    obtain ⟨suffix, _, rfl⟩ := List.mem_map.mp built
    exact extendClass_active source suffix (active source sourceMember)

/-- Every recorded path exists under a satisfying assignment to active classes. -/
theorem member_exists (term : Term Symbol) (classes : Constraints) (active : Active classes)
    (satisfied : Satisfies term classes) (path : Path) (member : path ∈ members classes) :
    ∃ value, term.atPath path = some value := by
  obtain ⟨paths, pathsMember, pathMember⟩ := (mem_members path classes).mp member
  exact class_member_exists term paths (active paths pathsMember) (satisfied paths pathsMember) path pathMember

/-- Equal existing subterms inherit every suffix that exists at one class member. -/
theorem extendClass_satisfied (term : Term Symbol) (paths : Class) (active : Nontrivial paths)
    (satisfied : ClassSat term paths) (base suffix : Path) (baseMember : base ∈ paths)
    (existing : ∃ value, term.atPath (base ++ suffix) = some value) : ClassSat term (extendClass paths suffix) := by
  obtain ⟨value, found⟩ := existing
  have shared : ∀ path ∈ paths, term.atPath (path ++ suffix) = some value := by
    intro path member
    obtain ⟨root, atBase, atOther⟩ := class_pair_equal term paths active satisfied base path baseMember member
    rw [atPath_append, atBase] at found
    simpa [atPath_append, atOther] using found
  intro left leftMember right rightMember _
  obtain ⟨first, firstMember, rfl⟩ := (mem_extendClass _ _ _).mp leftMember
  obtain ⟨second, secondMember, rfl⟩ := (mem_extendClass _ _ _).mp rightMember
  exact ⟨value, shared first firstMember, shared second secondMember⟩

/-- Congruence generation preserves exactly the required existing-path equalities. -/
theorem addCongruences_correct (term : Term Symbol) (classes : Constraints) (active : Active classes) :
    Satisfies term (addCongruences classes) ↔ Satisfies term classes := by
  constructor
  · intro result paths member
    exact result paths (List.mem_append_left _ member)
  · intro original paths member
    rcases List.mem_append.mp member with originalMember | generated
    · exact original paths originalMember
    · obtain ⟨source, sourceMember, built⟩ := List.mem_flatMap.mp generated
      obtain ⟨suffix, suffixMember, rfl⟩ := List.mem_map.mp built
      obtain ⟨base, baseMember, extension, extensionMember, _, equal⟩ :=
        (mem_suffixes suffix source classes).mp suffixMember
      apply extendClass_satisfied term source (active source sourceMember) (original source sourceMember) base suffix baseMember
      rw [equal]
      exact member_exists term classes active original extension extensionMember

/-- Check each class for an equality with a proper descendant path. -/
def isContradicting (classes : Constraints) : Bool :=
  classes.any (fun paths => paths.any (fun left => paths.any (fun right =>
    decide (left.IsPrefix right ∧ left ≠ right))))

/-- The contradiction scan reports exactly a strict-prefix pair in one class. -/
theorem isContradicting_correct (classes : Constraints) :
    isContradicting classes = true ↔ ∃ paths ∈ classes, ∃ left ∈ paths, ∃ right ∈ paths,
      left.IsPrefix right ∧ left ≠ right := by
  simp [isContradicting, List.any_eq_true]

/-- Every reported contradiction is impossible for a finite complete term. -/
theorem contradiction_sound (term : Term Symbol) (classes : Constraints)
    (contradiction : isContradicting classes = true) : ¬ Satisfies term classes := by
  intro satisfied
  obtain ⟨paths, pathsMember, left, leftMember, right, rightMember, initial, different⟩ :=
    (isContradicting_correct classes).mp contradiction
  obtain ⟨suffix, rfl⟩ := initial
  have nonempty : suffix ≠ [] := by intro empty; simp [empty] at different
  exact strict_prefix_paths_not_equal term left suffix nonempty
    (satisfied paths pathsMember left leftMember (left ++ suffix) rightMember different)

/-- One source normalization step: generate, complete, and check for contradictions. -/
def congruenceStep (classes : Constraints) : Option Constraints :=
  let closed := complete (addCongruences classes)
  if isContradicting closed then none else some closed

/-- A contradictory result denotes no complete terms. -/
def ResultSat (term : Term Symbol) : Option Constraints → Prop
  | none => False
  | some classes => Satisfies term classes

/-- One executable congruence step has exactly the original denotation. -/
theorem congruenceStep_correct (term : Term Symbol) (classes : Constraints) (active : Active classes) :
    ResultSat term (congruenceStep classes) ↔ Satisfies term classes := by
  have equivalent := (complete_correct term (addCongruences classes)).trans
    (addCongruences_correct term classes active)
  by_cases contradictory : isContradicting (complete (addCongruences classes)) = true
  · simp only [congruenceStep, contradictory, ↓reduceIte, ResultSat, false_iff]
    intro satisfied
    exact contradiction_sound term _ contradictory (equivalent.mpr satisfied)
  · change Satisfies term (complete (addCongruences classes)) ↔ Satisfies term classes at equivalent
    simpa [congruenceStep, contradictory, ResultSat] using equivalent

/-- A successful step preserves active classes and rules out every strict-prefix equality. -/
theorem congruenceStep_invariants (classes output : Constraints) (active : Active classes)
    (success : congruenceStep classes = some output) : Active output ∧ isContradicting output = false := by
  dsimp only [congruenceStep] at success
  split at success
  next contradictory => simp at success
  next consistent =>
    have same : output = complete (addCongruences classes) := Option.some.inj success.symm
    subst output
    exact ⟨complete_active _ (addCongruences_active classes active), Bool.eq_false_iff.mpr consistent⟩


/-- A bounded fixed-point execution distinguishes timeout from contradiction. -/
inductive RunResult where
  | timeout
  | contradiction
  | normalized (classes : Constraints)
  deriving DecidableEq

/-- Interpret a completed normalization result. -/
def RunSat (term : Term Symbol) : RunResult → Prop
  | .timeout => False
  | .contradiction => False
  | .normalized classes => Satisfies term classes

/-- Iterate the source partial step until it fails, stabilizes, or consumes its bound. -/
def fixMaybe : Nat → Constraints → RunResult
  | 0, _ => .timeout
  | fuel + 1, classes =>
      match congruenceStep classes with
      | none => .contradiction
      | some next => if next = classes then .normalized classes else fixMaybe fuel next

/-- Every completed fixed-point execution preserves exactly the input language. -/
theorem fixMaybe_correct (term : Term Symbol) (fuel : Nat) (classes : Constraints)
    (active : Active classes) (finished : fixMaybe fuel classes ≠ .timeout) :
    RunSat term (fixMaybe fuel classes) ↔ Satisfies term classes := by
  induction fuel generalizing classes with
  | zero => simp [fixMaybe] at finished
  | succ fuel ih =>
      cases stepped : congruenceStep classes with
      | none => simpa [fixMaybe, stepped, RunSat, ResultSat] using congruenceStep_correct term classes active
      | some next =>
          by_cases stable : next = classes
          · simp [fixMaybe, stepped, stable, RunSat]
          · have nextActive := (congruenceStep_invariants classes next active stepped).1
            have nextFinished : fixMaybe fuel next ≠ .timeout := by simpa [fixMaybe, stepped, stable] using finished
            have current := congruenceStep_correct term classes active
            rw [stepped] at current
            simpa [fixMaybe, stepped, stable] using (ih next nextActive nextFinished).trans current

/-- A successful step has disjoint output classes. -/
theorem congruenceStep_disjoint (classes output : Constraints) (success : congruenceStep classes = some output) :
    output.Pairwise (fun left right => overlap left right = false) := by
  dsimp only [congruenceStep] at success
  split at success
  next contradictory => simp at success
  next consistent =>
    have same : output = complete (addCongruences classes) := Option.some.inj success.symm
    subst output
    exact complete_disjoint _

/-- A normalized result is active, disjoint, contradiction-free, and a step fixed point. -/
theorem fixMaybe_invariants (fuel : Nat) (classes output : Constraints) (active : Active classes)
    (success : fixMaybe fuel classes = .normalized output) :
    Active output ∧ isContradicting output = false ∧
      output.Pairwise (fun left right => overlap left right = false) ∧ congruenceStep output = some output := by
  induction fuel generalizing classes with
  | zero => simp [fixMaybe] at success
  | succ fuel ih =>
      cases stepped : congruenceStep classes with
      | none => simp [fixMaybe, stepped] at success
      | some next =>
          by_cases stable : next = classes
          · subst next
            have same : output = classes := by simpa [fixMaybe, stepped] using success.symm
            subst output
            have invariant := congruenceStep_invariants classes classes active stepped
            exact ⟨invariant.1, invariant.2, congruenceStep_disjoint classes classes stepped, stepped⟩
          · have recursive : fixMaybe fuel next = .normalized output := by simpa [fixMaybe, stepped, stable] using success
            exact ih next (congruenceStep_invariants classes next active stepped).1 recursive

/-- Normalize input path lists after set insertion, trivial-class removal, and completion. -/
def mkEqConstraints (fuel : Nat) (classes : Constraints) : RunResult := fixMaybe fuel (complete (prepare classes))

/-- Completed bounded normalization is equivalent to the original PCS constraints. -/
theorem mkEqConstraints_correct (term : Term Symbol) (fuel : Nat) (classes : Constraints)
    (finished : mkEqConstraints fuel classes ≠ .timeout) :
    RunSat term (mkEqConstraints fuel classes) ↔ Satisfies term classes :=
  (fixMaybe_correct term fuel _ (complete_active _ (prepare_active classes)) finished).trans
    ((complete_correct term _).trans (prepare_correct term classes))

/-- Successful normalization establishes the invariants needed by trie construction. -/
theorem mkEqConstraints_invariants (fuel : Nat) (classes output : Constraints)
    (success : mkEqConstraints fuel classes = .normalized output) :
    Active output ∧ isContradicting output = false ∧
      output.Pairwise (fun left right => overlap left right = false) ∧ congruenceStep output = some output :=
  fixMaybe_invariants fuel _ output (complete_active _ (prepare_active classes)) success

/-- Combining completed constraint sets normalizes their conjunction. -/
def combineEqConstraints (fuel : Nat) : RunResult → RunResult → RunResult
  | .timeout, _ => .timeout
  | _, .timeout => .timeout
  | .contradiction, _ => .contradiction
  | _, .contradiction => .contradiction
  | .normalized left, .normalized right => mkEqConstraints fuel (left ++ right)

/-- Completed combination denotes exactly the conjunction of both inputs. -/
theorem combineEqConstraints_correct (term : Term Symbol) (fuel : Nat) (left right : RunResult)
    (finished : combineEqConstraints fuel left right ≠ .timeout) :
    RunSat term (combineEqConstraints fuel left right) ↔ RunSat term left ∧ RunSat term right := by
  cases left with
  | timeout => simp [combineEqConstraints] at finished
  | contradiction => cases right <;> simp_all [combineEqConstraints, RunSat]
  | normalized first =>
      cases right with
      | timeout => simp [combineEqConstraints] at finished
      | contradiction => simp [combineEqConstraints, RunSat]
      | normalized second =>
          have correct := mkEqConstraints_correct term fuel (first ++ second) finished
          simpa [combineEqConstraints, RunSat, Satisfies, or_imp, forall_and] using correct

/-- Duplicate elimination provides ordinary set distinctness for path classes. -/
theorem paths_eraseDups_nodup (paths : Class) : paths.eraseDups.Nodup := by
  cases paths with
  | nil => simp
  | cons path rest =>
      rw [List.eraseDups_cons]
      refine List.nodup_cons.mpr ⟨?_, paths_eraseDups_nodup (rest.filter (fun other => !other == path))⟩
      simp [List.mem_eraseDups]
termination_by paths.length
decreasing_by
  have shorter := List.length_filter_le (fun other => !other == path) rest
  simp only [List.length_cons]
  omega

/-- A consistent class set is a supported terminal-or-branch trie input. -/
theorem consistent_supported (classes : Constraints) (consistent : isContradicting classes = false)
    (paths : Class) (member : paths ∈ classes) : EqualityTrie.Supported paths.eraseDups := by
  apply (paths_eraseDups_nodup paths).imp_of_mem
  intro left right leftMember rightMember different
  have leftPresent : left ∈ paths := by simpa using leftMember
  have rightPresent : right ∈ paths := by simpa using rightMember
  refine ⟨?_, ?_⟩
  · intro initial
    have contradiction := (isContradicting_correct classes).mpr
      ⟨paths, member, left, leftPresent, right, rightPresent, initial, different⟩
    rw [consistent] at contradiction
    contradiction
  · intro initial
    have contradiction := (isContradicting_correct classes).mpr
      ⟨paths, member, right, rightPresent, left, leftPresent, initial, Ne.symm different⟩
    rw [consistent] at contradiction
    contradiction

/-- Every normalized class has an exact valid, sorted, distinct trie representation. -/
theorem normalized_class_trie (fuel : Nat) (classes output : Constraints)
    (success : mkEqConstraints fuel classes = .normalized output) (paths : Class) (member : paths ∈ output) :
    ∃ trie, EqualityTrie.toPathTrie paths.eraseDups = some trie ∧ EqualityTrie.Valid trie ∧
      (EqualityTrie.fromPathTrie trie).Nodup ∧
      (EqualityTrie.fromPathTrie trie).Pairwise (List.Lex (· < ·)) ∧
      ∀ path, path ∈ EqualityTrie.fromPathTrie trie ↔ path ∈ paths := by
  have supported := consistent_supported output (mkEqConstraints_invariants fuel classes output success).2.1 paths member
  obtain ⟨trie, built, valid, unique, ordered, perm⟩ := EqualityTrie.toPathTrie_sorted_distinct paths.eraseDups supported
  exact ⟨trie, built, valid, unique, ordered, fun path => perm.mem_iff.trans (by simp)⟩

/-- Descend one class through a child and preserve its set of suffix paths. -/
def descendClass (index : Nat) (paths : Class) : Class := (EqualityTrie.tailsAt index paths).eraseDups

/-- Descend every class and discard classes that no longer impose an equality. -/
def eqConstraintsDescend (index : Nat) (classes : Constraints) : Constraints :=
  prepare (classes.map (descendClass index))

/-- Class descent is exactly the restriction to paths starting at one child. -/
theorem mem_descendClass (index : Nat) (paths : Class) (suffix : Path) :
    suffix ∈ descendClass index paths ↔ index :: suffix ∈ paths := by
  simp [descendClass, EqualityTrie.mem_tailsAt]

/-- Descended constraints express precisely the surviving same-child equality pairs. -/
theorem eqConstraintsDescend_exact (term : Term Symbol) (index : Nat) (classes : Constraints) :
    Satisfies term (eqConstraintsDescend index classes) ↔
      ∀ paths ∈ classes, ∀ left, index :: left ∈ paths → ∀ right, index :: right ∈ paths →
        left ≠ right → PathsEqual term left right := by
  rw [eqConstraintsDescend, prepare_correct]
  simp only [Satisfies, List.forall_mem_map, ClassSat, mem_descendClass]

/-- Looking up one existing child commutes with both equality paths. -/
theorem pathsEqual_child (symbol : Symbol) (children : List (Term Symbol)) (index : Nat) (child : Term Symbol)
    (found : children[index]? = some child) (left right : Path) :
    PathsEqual (.node symbol children) (index :: left) (index :: right) ↔ PathsEqual child left right := by
  simp [PathsEqual, Term.atPath, found]

/-- Every satisfied parent constraint supplies every retained child constraint. -/
theorem eqConstraintsDescend_sound (symbol : Symbol) (children : List (Term Symbol))
    (index : Nat) (child : Term Symbol) (found : children[index]? = some child) (classes : Constraints)
    (satisfied : Satisfies (.node symbol children) classes) : Satisfies child (eqConstraintsDescend index classes) := by
  rw [eqConstraintsDescend_exact]
  intro paths pathsMember left leftMember right rightMember different
  exact (pathsEqual_child symbol children index child found left right).mp
    (satisfied paths pathsMember (index :: left) leftMember (index :: right) rightMember (by simp [different]))

/-- PCS singleton removal permits an absent path; a reflexive guard does not. -/
theorem singleton_is_not_reflexive_guard (symbol : Symbol) :
    ClassSat (.node symbol []) [[0]] ∧ ¬ PathsEqual (.node symbol []) [0] [0] := by
  constructor
  · intro left leftMember right rightMember different
    simp only [List.mem_singleton] at leftMember rightMember
    exact False.elim (different (leftMember.trans rightMember.symm))
  · simp [PathsEqual, Term.atPath]


/-- A proper prefix precedes its extension in the path ordering. -/
theorem strictPrefix_lex (base extension : Path) (initial : base.IsPrefix extension) (different : base ≠ extension) :
    List.Lex (· < ·) base extension := by
  obtain ⟨suffix, rfl⟩ := initial
  have nonempty : suffix ≠ [] := by intro empty; simp [empty] at different
  induction base with
  | nil => cases suffix with | nil => contradiction | cons index rest => exact .nil
  | cons index rest ih => exact .cons (ih (by intro same; apply different; simpa using congrArg (index :: ·) same))

/-- All paths between a prefix and one of its extensions share that prefix. -/
theorem prefix_interval (base middle extension : Path)
    (before : List.Lex (· < ·) base middle) (after : List.Lex (· < ·) middle extension)
    (initial : base.IsPrefix extension) : base.IsPrefix middle := by
  induction base generalizing middle extension with
  | nil => simp
  | cons index rest ih =>
      cases middle with
      | nil => cases before
      | cons key suffix =>
          cases extension with
          | nil => cases after
          | cons other tail =>
              obtain ⟨same, nested⟩ := List.cons_prefix_cons.mp initial
              subst other
              rcases List.cons_lex_cons_iff.mp before with less | ⟨same, nestedBefore⟩
              · rcases List.cons_lex_cons_iff.mp after with reverse | ⟨same, _⟩ <;> omega
              · subst key
                rcases List.cons_lex_cons_iff.mp after with reverse | ⟨_, nestedAfter⟩
                · omega
                · exact List.cons_prefix_cons.mpr ⟨rfl, ih suffix tail nestedBefore nestedAfter nested⟩

/-- The strict-extension predicate is a single interval after its base in a sorted path set. -/
theorem takeWhile_strict_extensions (base : Path) (rest : List Path)
    (sorted : (base :: rest).Pairwise (List.Lex (· < ·))) :
    rest.takeWhile (fun extension => decide (base.IsPrefix extension ∧ base ≠ extension)) =
      rest.filter (fun extension => decide (base.IsPrefix extension ∧ base ≠ extension)) := by
  induction rest with
  | nil => rfl
  | cons path rest ih =>
      obtain ⟨baseBefore, restSorted⟩ := List.pairwise_cons.mp sorted
      obtain ⟨pathBefore, tailSorted⟩ := List.pairwise_cons.mp restSorted
      have tailBaseSorted : (base :: rest).Pairwise (List.Lex (· < ·)) :=
        List.pairwise_cons.mpr ⟨fun later member => baseBefore later (by simp [member]), tailSorted⟩
      by_cases extension : base.IsPrefix path ∧ base ≠ path
      · have selected : decide (base.IsPrefix path ∧ base ≠ path) = true := by simp only [decide_eq_true_eq]; exact extension
        rw [List.takeWhile_cons_of_pos (p := fun extension : Path => decide (base.IsPrefix extension ∧ base ≠ extension)) selected, List.filter_cons_of_pos (p := fun extension : Path => decide (base.IsPrefix extension ∧ base ≠ extension)) selected, ih tailBaseSorted]
      · have noLater : ∀ later ∈ rest, ¬(base.IsPrefix later ∧ base ≠ later) := by
          intro later member extended
          have initial := prefix_interval base path later (baseBefore path (by simp)) (pathBefore later member) extended.1
          have different : base ≠ path := by
            intro same
            subst path
            exact List.lex_irrefl (fun n : Nat => Nat.lt_irrefl n) base (baseBefore base (by simp))
          exact extension ⟨initial, different⟩
        have empty : rest.filter (fun later => decide (base.IsPrefix later ∧ base ≠ later)) = [] := by
          apply List.filter_eq_nil_iff.mpr
          intro later member
          simp [noLater later member]
        have absent : ¬decide (base.IsPrefix path ∧ base ≠ path) := by simpa only [decide_eq_true_eq] using extension
        rw [List.takeWhile_cons_of_neg (p := fun extension : Path => decide (base.IsPrefix extension ∧ base ≠ extension)) absent, List.filter_cons_of_neg (p := fun extension : Path => decide (base.IsPrefix extension ∧ base ≠ extension)) absent, empty]

/-- Full-set strict suffix lookup equals the source sorted-tail range lookup. -/
theorem strict_suffix_range (before : List Path) (base : Path) (rest : List Path)
    (sorted : (before ++ base :: rest).Pairwise (List.Lex (· < ·))) (suffix : Path) :
    suffix ∈ (before ++ base :: rest).filterMap (strictSuffix base) ↔
      suffix ∈ (rest.takeWhile (fun extension => decide (base.IsPrefix extension ∧ base ≠ extension))).map
        (fun extension => extension.drop base.length) := by
  obtain ⟨_, tailSorted, crosses⟩ := List.pairwise_append.mp sorted
  rw [takeWhile_strict_extensions base rest tailSorted]
  simp only [List.mem_filterMap, List.mem_map, List.mem_filter, decide_eq_true_eq]
  constructor
  · rintro ⟨extension, member, selected⟩
    obtain ⟨nonempty, equal⟩ := (strictSuffix_correct base extension suffix).mp selected
    have initial : base.IsPrefix extension := ⟨suffix, equal⟩
    have different : base ≠ extension := by
      intro same
      have lengths := congrArg List.length (equal.trans same.symm)
      simp only [List.length_append] at lengths
      exact nonempty (List.length_eq_zero_iff.mp (by omega))
    have later : extension ∈ rest := by
      rcases List.mem_append.mp member with earlier | tailMember
      · have backwards := crosses extension earlier base (by simp)
        have forwards := strictPrefix_lex base extension initial different
        exact False.elim ((List.lex_asymm (by intro a b forward backward; omega) forwards) backwards)
      · rcases List.mem_cons.mp tailMember with same | present
        · exact False.elim (different same.symm)
        · exact present
    have extracted : extension.drop base.length = suffix := by
      unfold strictSuffix at selected
      simpa [initial, different] using selected
    exact ⟨extension, ⟨later, initial, different⟩, extracted⟩
  · rintro ⟨extension, ⟨member, initial, different⟩, same⟩
    exact ⟨extension, List.mem_append_right _ (List.mem_cons_of_mem _ member), by simp [strictSuffix, initial, different, same]⟩


/-- Every old class is contained in some new class. -/
def Covers (before after : Constraints) : Prop :=
  ∀ paths ∈ before, ∃ larger ∈ after, ∀ path ∈ paths, path ∈ larger

/-- Class containment composes across completion steps. -/
theorem covers_trans (first second third : Constraints) (left : Covers first second) (right : Covers second third) :
    Covers first third := by
  intro paths member
  obtain ⟨middle, middleMember, includes⟩ := left paths member
  obtain ⟨last, lastMember, preserves⟩ := right middle middleMember
  exact ⟨last, lastMember, fun path present => preserves path (includes path present)⟩

/-- One join retains every original class within a resulting class. -/
theorem joinOne_covers (paths : Class) (rest output : Constraints) (success : joinOne paths rest = some output) :
    Covers (paths :: rest) output := by
  induction rest generalizing output with
  | nil => simp [joinOne] at success
  | cons next rest ih =>
      by_cases shared : overlap paths next = true
      · simp [joinOne, shared] at success
        subst output
        intro original member
        rcases List.mem_cons.mp member with same | member
        · subst original
          exact ⟨(paths ++ next).eraseDups, by simp, by intro path present; simp [present]⟩
        · rcases List.mem_cons.mp member with same | member
          · subst original
            exact ⟨(paths ++ next).eraseDups, by simp, by intro path present; simp [present]⟩
          · exact ⟨original, by simp [member], fun _ present => present⟩
      · cases recursive : joinOne paths rest with
        | none => simp [joinOne, shared, recursive] at success
        | some merged =>
            have same : output = next :: merged := by simpa [joinOne, shared, recursive] using success.symm
            subst output
            intro original member
            by_cases equal : original = next
            · subst original
              exact ⟨next, by simp, fun _ present => present⟩
            · have previous : original ∈ paths :: rest := by simpa [equal] using member
              obtain ⟨larger, largerMember, included⟩ := ih merged recursive original previous
              exact ⟨larger, by simp [largerMember], included⟩

/-- Each completion step only combines classes; it does not split them. -/
theorem mergeOne_covers (classes output : Constraints) (success : mergeOne classes = some output) : Covers classes output := by
  induction classes generalizing output with
  | nil => simp [mergeOne] at success
  | cons paths rest ih =>
      cases joined : joinOne paths rest with
      | some merged =>
          simp [mergeOne, joined] at success
          subst output
          exact joinOne_covers paths rest merged joined
      | none =>
          cases recursive : mergeOne rest with
          | none => simp [mergeOne, joined, recursive] at success
          | some merged =>
              have same : output = paths :: merged := by simpa [mergeOne, joined, recursive] using success.symm
              subst output
              intro original member
              rcases List.mem_cons.mp member with same | member
              · subst original
                exact ⟨paths, by simp, fun _ present => present⟩
              · obtain ⟨larger, largerMember, included⟩ := ih merged recursive original member
                exact ⟨larger, by simp [largerMember], included⟩

/-- Finite completion retains each input class inside one completed component. -/
theorem completeFuel_covers (fuel : Nat) (classes : Constraints) : Covers classes (completeFuel fuel classes) := by
  induction fuel generalizing classes with
  | zero => exact fun paths member => ⟨paths, member, fun _ present => present⟩
  | succ fuel ih =>
      cases merged : mergeOne classes with
      | none => simpa [completeFuel, merged] using
          (show Covers classes classes from fun paths member => ⟨paths, member, fun _ present => present⟩)
      | some output => simpa [completeFuel, merged] using covers_trans classes output _ (mergeOne_covers classes output merged) (ih output)

/-- Canonical completion retains each input class within one component. -/
theorem complete_covers (classes : Constraints) : Covers classes (complete classes) := by
  intro paths member
  obtain ⟨component, componentMember, includes⟩ := completeFuel_covers classes.length classes paths member
  refine ⟨canonicalClass component, ?_, fun path present => (mem_canonicalClass path component).mpr (includes path present)⟩
  simpa [complete, canonicalize] using (List.mem_map.mpr ⟨component, componentMember, rfl⟩ :
    canonicalClass component ∈ (completeFuel classes.length classes).map canonicalClass)

/-- At a step fixed point, every generated suffix class occurs inside an output component. -/
theorem fixedPoint_congruence_closed (classes : Constraints) (fixed : congruenceStep classes = some classes)
    (paths : Class) (member : paths ∈ classes) (suffix : Path) (requested : suffix ∈ suffixes paths classes) :
    ∃ component ∈ classes, ∀ path ∈ paths, path ++ suffix ∈ component := by
  have closed : complete (addCongruences classes) = classes := by
    dsimp only [congruenceStep] at fixed
    split at fixed
    next contradiction => simp at fixed
    next consistent => exact Option.some.inj fixed
  have generated : extendClass paths suffix ∈ addCongruences classes :=
    List.mem_append_right _ (List.mem_flatMap.mpr ⟨paths, member, List.mem_map.mpr ⟨suffix, requested, rfl⟩⟩)
  obtain ⟨component, componentMember, included⟩ := complete_covers
    (addCongruences classes) (extendClass paths suffix) generated
  rw [closed] at componentMember
  exact ⟨component, componentMember, fun path present => included (path ++ suffix)
    ((mem_extendClass _ _ _).mpr ⟨path, present, rfl⟩)⟩


/-- Distinct completed components cannot share a path. -/
theorem disjoint_components (classes : Constraints)
    (disjoint : classes.Pairwise (fun left right => overlap left right = false))
    (left right : Class) (leftMember : left ∈ classes) (rightMember : right ∈ classes) (different : left ≠ right) :
    overlap left right = false := by
  induction classes with
  | nil => simp at leftMember
  | cons first rest ih =>
      obtain ⟨before, recursive⟩ := List.pairwise_cons.mp disjoint
      rcases List.mem_cons.mp leftMember with same | leftRest
      · subst first
        rcases List.mem_cons.mp rightMember with same | rightMember
        · exact False.elim (different same.symm)
        · exact before right rightMember
      · rcases List.mem_cons.mp rightMember with same | rightRest
        · subst first
          rw [overlap_symm]
          exact before left leftRest
        · exact ih recursive leftRest rightRest

/-- A shared path identifies a unique completed component. -/
theorem components_equal (classes : Constraints)
    (disjoint : classes.Pairwise (fun left right => overlap left right = false))
    (left right : Class) (leftMember : left ∈ classes) (rightMember : right ∈ classes)
    (path : Path) (inLeft : path ∈ left) (inRight : path ∈ right) : left = right := by
  by_cases same : left = right
  · exact same
  · have empty := disjoint_components classes disjoint left right leftMember rightMember same
    have shared := (overlap_correct left right).mpr ⟨path, inLeft, inRight⟩
    rw [empty] at shared
    contradiction

/-- One member of the first class is a proper prefix of a member of the second. -/
def Subsumes (first second : Class) : Prop :=
  ∃ left ∈ first, ∃ right ∈ second, left.IsPrefix right ∧ left ≠ right

/-- Prefix-induced saturation makes class subsumption transitive. -/
theorem fixedPoint_subsumption_transitive (classes : Constraints)
    (fixed : congruenceStep classes = some classes) (first middle last : Class)
    (middleMember : middle ∈ classes) (lastMember : last ∈ classes)
    (firstSubsumes : Subsumes first middle) (secondSubsumes : Subsumes middle last) : Subsumes first last := by
  obtain ⟨base, baseMember, extended, extendedMember, initial, different⟩ := firstSubsumes
  obtain ⟨middleBase, middleBaseMember, lastPath, lastPathMember, nextInitial, nextDifferent⟩ := secondSubsumes
  obtain ⟨firstSuffix, firstEqual⟩ := initial
  obtain ⟨nextSuffix, nextEqual⟩ := nextInitial
  have nextNonempty : nextSuffix ≠ [] := by intro empty; simp [empty] at nextEqual; exact nextDifferent nextEqual
  have suffixMember : nextSuffix ∈ suffixes middle classes :=
    (mem_suffixes _ _ _).mpr ⟨middleBase, middleBaseMember, lastPath,
      (mem_members _ _).mpr ⟨last, lastMember, lastPathMember⟩, nextNonempty, nextEqual⟩
  obtain ⟨component, componentMember, extendedInto⟩ := fixedPoint_congruence_closed classes fixed middle middleMember nextSuffix suffixMember
  have common : lastPath ∈ component := nextEqual ▸ extendedInto middleBase middleBaseMember
  have same := components_equal classes (congruenceStep_disjoint classes classes fixed)
    component last componentMember lastMember lastPath common lastPathMember
  subst component
  refine ⟨base, baseMember, extended ++ nextSuffix, extendedInto extended extendedMember, ?_, ?_⟩
  · exact ⟨firstSuffix ++ nextSuffix, by rw [← List.append_assoc, firstEqual]⟩
  · intro equal
    have strictLength : base.length < extended.length := by
      have lengthEq := congrArg List.length firstEqual
      have suffixNonempty : firstSuffix ≠ [] := by intro empty; simp [empty] at firstEqual; exact different firstEqual
      have positive := List.length_pos_iff.mpr suffixNonempty
      simp only [List.length_append] at lengthEq
      omega
    have lengthEq := congrArg List.length equal
    simp only [List.length_append] at lengthEq
    omega

/-- The finite-tree contradiction check makes subsumption irreflexive on normalized classes. -/
theorem consistent_subsumption_irreflexive (classes : Constraints) (consistent : isContradicting classes = false)
    (paths : Class) (member : paths ∈ classes) : ¬Subsumes paths paths := by
  rintro ⟨left, leftMember, right, rightMember, initial, different⟩
  have contradiction := (isContradicting_correct classes).mpr
    ⟨paths, member, left, leftMember, right, rightMember, initial, different⟩
  rw [consistent] at contradiction
  contradiction


/-- Connectivity generated by the input equality classes on their recorded paths. -/
inductive Connected (classes : Constraints) : Path → Path → Prop where
  | edge (paths : Class) : paths ∈ classes → left ∈ paths → right ∈ paths → Connected classes left right
  | trans : Connected classes left middle → Connected classes middle right → Connected classes left right

/-- Class connectivity is symmetric. -/
theorem connected_symm (classes : Constraints) (left right : Path) (connected : Connected classes left right) :
    Connected classes right left := by
  induction connected with
  | edge paths member first second => exact .edge paths member second first
  | trans first second leftIH rightIH => exact .trans rightIH leftIH

/-- Every generated component contains only input-connected path pairs. -/
def ComponentsConnected (original output : Constraints) : Prop :=
  ∀ paths ∈ output, ∀ left ∈ paths, ∀ right ∈ paths, Connected original left right

/-- Every input class is connected by its own generating edges. -/
theorem input_connected (classes : Constraints) : ComponentsConnected classes classes :=
  fun paths member _ leftMember _ rightMember => .edge paths member leftMember rightMember

/-- A union along one common path adds no new connectivity beyond transitivity. -/
theorem merged_connected (classes : Constraints) (left right : Class)
    (first : ∀ p ∈ left, ∀ q ∈ left, Connected classes p q)
    (second : ∀ p ∈ right, ∀ q ∈ right, Connected classes p q)
    (shared : overlap left right = true) :
    ∀ p ∈ (left ++ right).eraseDups, ∀ q ∈ (left ++ right).eraseDups, Connected classes p q := by
  obtain ⟨pivot, pivotLeft, pivotRight⟩ := (overlap_correct _ _).mp shared
  intro p pMember q qMember
  have hp : p ∈ left ∨ p ∈ right := by simpa using pMember
  have hq : q ∈ left ∨ q ∈ right := by simpa using qMember
  rcases hp with hp | hp <;> rcases hq with hq | hq
  · exact first p hp q hq
  · exact .trans (first p hp pivot pivotLeft) (second pivot pivotRight q hq)
  · exact .trans (second p hp pivot pivotRight) (first pivot pivotLeft q hq)
  · exact second p hp q hq

/-- One join preserves the input-connectivity invariant. -/
theorem joinOne_connected (original : Constraints) (paths : Class) (rest output : Constraints)
    (known : ComponentsConnected original (paths :: rest)) (success : joinOne paths rest = some output) :
    ComponentsConnected original output := by
  induction rest generalizing output with
  | nil => simp [joinOne] at success
  | cons next rest ih =>
      by_cases shared : overlap paths next = true
      · simp [joinOne, shared] at success
        subst output
        intro cls member
        rcases List.mem_cons.mp member with same | member
        · subst cls
          exact merged_connected original paths next (known paths (by simp)) (known next (by simp)) shared
        · exact known cls (by simp [member])
      · cases recursive : joinOne paths rest with
        | none => simp [joinOne, shared, recursive] at success
        | some merged =>
            have same : output = next :: merged := by simpa [joinOne, shared, recursive] using success.symm
            subst output
            intro cls member
            rcases List.mem_cons.mp member with same | member
            · subst cls
              exact known next (by simp)
            · exact ih merged (fun cls present => known cls (by simp only [List.mem_cons] at present ⊢; rcases present with same | member; exact Or.inl same; exact Or.inr (Or.inr member))) recursive cls member

/-- A completion merge creates only input-connected components. -/
theorem mergeOne_connected (original classes output : Constraints) (known : ComponentsConnected original classes)
    (success : mergeOne classes = some output) : ComponentsConnected original output := by
  induction classes generalizing output with
  | nil => simp [mergeOne] at success
  | cons paths rest ih =>
      cases joined : joinOne paths rest with
      | some merged =>
          simp [mergeOne, joined] at success
          subst output
          exact joinOne_connected original paths rest merged known joined
      | none =>
          cases recursive : mergeOne rest with
          | none => simp [mergeOne, joined, recursive] at success
          | some merged =>
              have same : output = paths :: merged := by simpa [mergeOne, joined, recursive] using success.symm
              subst output
              intro cls member
              rcases List.mem_cons.mp member with same | member
              · subst cls
                exact known paths (by simp)
              · exact ih merged (fun cls present => known cls (by simp [present])) recursive cls member

/-- A bounded merge sequence creates only original connected components. -/
theorem completeFuel_connected (original : Constraints) (fuel : Nat) (classes : Constraints)
    (known : ComponentsConnected original classes) : ComponentsConnected original (completeFuel fuel classes) := by
  induction fuel generalizing classes with
  | zero => exact known
  | succ fuel ih =>
      cases merged : mergeOne classes with
      | none => simpa [completeFuel, merged] using known
      | some output => simpa [completeFuel, merged] using ih output (mergeOne_connected original classes output known merged)

/-- Canonical completion introduces no equality beyond input connectivity. -/
theorem complete_connected (classes : Constraints) : ComponentsConnected classes (complete classes) := by
  intro paths member left leftMember right rightMember
  have mapped : paths ∈ (completeFuel classes.length classes).map canonicalClass := by simpa [complete, canonicalize] using member
  obtain ⟨source, sourceMember, rfl⟩ := List.mem_map.mp mapped
  exact completeFuel_connected classes classes.length classes (input_connected classes) source sourceMember
    left ((mem_canonicalClass _ _).mp leftMember) right ((mem_canonicalClass _ _).mp rightMember)

/-- Completion computes exactly the connected components of the input class relation. -/
theorem complete_components (classes : Constraints) (left right : Path) :
    (∃ paths ∈ complete classes, left ∈ paths ∧ right ∈ paths) ↔ Connected classes left right := by
  constructor
  · rintro ⟨paths, member, first, second⟩
    exact complete_connected classes paths member left first right second
  · intro connected
    induction connected with
    | edge paths member first second =>
        obtain ⟨component, componentMember, included⟩ := complete_covers classes paths member
        exact ⟨component, componentMember, included _ first, included _ second⟩
    | @trans left middle right first second leftIH rightIH =>
        obtain ⟨firstComponent, firstMember, atLeft, sharedLeft⟩ := leftIH
        obtain ⟨secondComponent, secondMember, sharedRight, atRight⟩ := rightIH
        have same := components_equal (complete classes) (complete_disjoint classes) firstComponent secondComponent
          firstMember secondMember middle sharedLeft sharedRight
        subst secondComponent
        exact ⟨firstComponent, firstMember, atLeft, atRight⟩

/-- The source finite path table contains exactly the vertices of class connectivity. -/
theorem connected_member (classes : Constraints) (left right : Path) (connected : Connected classes left right) :
    left ∈ members classes ∧ right ∈ members classes := by
  induction connected with
  | edge paths member first second =>
      exact ⟨(mem_members _ _).mpr ⟨paths, member, first⟩, (mem_members _ _).mpr ⟨paths, member, second⟩⟩
  | trans first second leftIH rightIH => exact ⟨leftIH.1, rightIH.2⟩

/-- Completion neither creates nor removes recorded paths. -/
theorem complete_members (classes : Constraints) (path : Path) :
    path ∈ members (complete classes) ↔ path ∈ members classes := by
  constructor
  · intro member
    obtain ⟨paths, pathsMember, present⟩ := (mem_members _ _).mp member
    exact (connected_member classes path path ((complete_components classes path path).mp
      ⟨paths, pathsMember, present, present⟩)).1
  · intro member
    obtain ⟨paths, pathsMember, present⟩ := (mem_members _ _).mp member
    obtain ⟨component, componentMember, included⟩ := complete_covers classes paths pathsMember
    exact (mem_members _ _).mpr ⟨component, componentMember, included path present⟩


/-- Canonical classes have no repeated paths. -/
theorem canonicalClass_nodup (paths : Class) : (canonicalClass paths).Nodup :=
  (List.mergeSort_perm _ _).symm.nodup (paths_eraseDups_nodup paths)

/-- Canonical classes use ascending path order. -/
theorem canonicalClass_ordered (paths : Class) : (canonicalClass paths).Pairwise (· ≤ ·) := by
  have sorted := List.pairwise_mergeSort (le := fun left right : Path => decide (left ≤ right))
    (by intro left middle right first second; simp only [decide_eq_true_eq] at *; exact List.le_trans first second)
    (by intro left right; simp only [Bool.or_eq_true, decide_eq_true_eq]; exact List.le_total left right)
    paths.eraseDups
  simpa [canonicalClass] using sorted

/-- The canonical class representation is uniquely determined by path membership. -/
theorem canonicalClass_ext (left right : Class) (same : ∀ path, path ∈ left ↔ path ∈ right) :
    canonicalClass left = canonicalClass right := by
  have perm := (List.perm_ext_iff_of_nodup (canonicalClass_nodup left) (canonicalClass_nodup right)).mpr
    (fun path => (mem_canonicalClass path left).trans ((same path).trans (mem_canonicalClass path right).symm))
  exact perm.eq_of_pairwise (fun _ _ _ _ first second => List.le_antisymm first second)
    (canonicalClass_ordered left) (canonicalClass_ordered right)

/-- Repeated canonical set enumeration does not change its result. -/
theorem canonicalClass_idempotent (paths : Class) : canonicalClass (canonicalClass paths) = canonicalClass paths :=
  canonicalClass_ext _ _ (fun path => mem_canonicalClass path paths)

/-- The canonical component list uses ascending class order. -/
theorem canonicalize_ordered (classes : Constraints) : (canonicalize classes).Pairwise (· ≤ ·) := by
  have sorted := List.pairwise_mergeSort (le := fun left right : Class => decide (left ≤ right))
    (by intro left middle right first second; simp only [decide_eq_true_eq] at *; exact List.le_trans first second)
    (by intro left right; simp only [Bool.or_eq_true, decide_eq_true_eq]; exact List.le_total left right)
    (classes.map canonicalClass)
  simpa [canonicalize] using sorted

/-- Every stored component uses the canonical path-set representation. -/
theorem canonicalize_members (classes : Constraints) (paths : Class) (member : paths ∈ canonicalize classes) :
    canonicalClass paths = paths := by
  have mapped : paths ∈ classes.map canonicalClass := by simpa [canonicalize] using member
  obtain ⟨source, _, rfl⟩ := List.mem_map.mp mapped
  exact canonicalClass_idempotent source

/-- Nonempty disjoint components cannot repeat in the output list. -/
theorem disjoint_components_nodup (classes : Constraints) (active : Active classes)
    (disjoint : classes.Pairwise (fun left right => overlap left right = false)) : classes.Nodup := by
  apply disjoint.imp_of_mem
  intro left right leftMember _ absent same
  subst right
  obtain ⟨path, member, _, _, _⟩ := active left leftMember
  have shared := (overlap_correct left left).mpr ⟨path, member, member⟩
  rw [absent] at shared
  contradiction

/-- A connected-component result is unique once both set and component orders are canonical. -/
theorem canonical_partition_unique (original first second : Constraints)
    (firstActive : Active first) (secondActive : Active second)
    (firstDisjoint : first.Pairwise (fun left right => overlap left right = false))
    (secondDisjoint : second.Pairwise (fun left right => overlap left right = false))
    (firstOrdered : first.Pairwise (· ≤ ·)) (secondOrdered : second.Pairwise (· ≤ ·))
    (firstCanonical : ∀ paths ∈ first, canonicalClass paths = paths)
    (secondCanonical : ∀ paths ∈ second, canonicalClass paths = paths)
    (firstExact : ∀ left right, (∃ paths ∈ first, left ∈ paths ∧ right ∈ paths) ↔ Connected original left right)
    (secondExact : ∀ left right, (∃ paths ∈ second, left ∈ paths ∧ right ∈ paths) ↔ Connected original left right) :
    first = second := by
  have componentMatch : ∀ left ∈ first, ∃ right ∈ second, left = right := by
    intro left leftMember
    obtain ⟨pivot, pivotMember, _, _, _⟩ := firstActive left leftMember
    obtain ⟨right, rightMember, pivotRight, _⟩ := (secondExact pivot pivot).mpr
      ((firstExact pivot pivot).mp ⟨left, leftMember, pivotMember, pivotMember⟩)
    have equalMembers : ∀ path, path ∈ left ↔ path ∈ right := by
      intro path
      constructor
      · intro member
        obtain ⟨other, otherMember, pivotOther, pathOther⟩ := (secondExact pivot path).mpr
          ((firstExact pivot path).mp ⟨left, leftMember, pivotMember, member⟩)
        have same := components_equal second secondDisjoint other right otherMember rightMember pivot pivotOther pivotRight
        simpa [same] using pathOther
      · intro member
        obtain ⟨other, otherMember, pivotOther, pathOther⟩ := (firstExact pivot path).mpr
          ((secondExact pivot path).mp ⟨right, rightMember, pivotRight, member⟩)
        have same := components_equal first firstDisjoint other left otherMember leftMember pivot pivotOther pivotMember
        simpa [same] using pathOther
    have equal := canonicalClass_ext left right equalMembers
    rw [firstCanonical left leftMember, secondCanonical right rightMember] at equal
    exact ⟨right, rightMember, equal⟩
  have sameMembers : ∀ paths, paths ∈ first ↔ paths ∈ second := by
    intro paths
    constructor
    · intro member
      obtain ⟨other, otherMember, rfl⟩ := componentMatch paths member
      exact otherMember
    · intro member
      obtain ⟨pivot, pivotMember, _, _, _⟩ := secondActive paths member
      obtain ⟨other, otherMember, pivotOther, _⟩ := (firstExact pivot pivot).mpr
        ((secondExact pivot pivot).mp ⟨paths, member, pivotMember, pivotMember⟩)
      obtain ⟨matched, matchedMember, equal⟩ := componentMatch other otherMember
      have pivotMatched : pivot ∈ matched := equal ▸ pivotOther
      have same := components_equal second secondDisjoint paths matched member matchedMember pivot pivotMember pivotMatched
      rw [same, ← equal]
      exact otherMember
  have perm := (List.perm_ext_iff_of_nodup (disjoint_components_nodup first firstActive firstDisjoint)
    (disjoint_components_nodup second secondActive secondDisjoint)).mpr sameMembers
  exact perm.eq_of_pairwise (fun _ _ _ _ left right => List.le_antisymm left right) firstOrdered secondOrdered

/-- Any canonical union-find partition of the input relation equals this concrete completion. -/
theorem complete_matches_partition (original output : Constraints) (active : Active original)
    (outputActive : Active output) (outputDisjoint : output.Pairwise (fun left right => overlap left right = false))
    (outputOrdered : output.Pairwise (· ≤ ·)) (outputCanonical : ∀ paths ∈ output, canonicalClass paths = paths)
    (outputExact : ∀ left right, (∃ paths ∈ output, left ∈ paths ∧ right ∈ paths) ↔ Connected original left right) :
    complete original = output :=
  canonical_partition_unique original (complete original) output (complete_active original active) outputActive
    (complete_disjoint original) outputDisjoint (canonicalize_ordered _) outputOrdered
    (canonicalize_members _) outputCanonical (complete_components original) outputExact

end MicroCFTA.EqualityNormalize
