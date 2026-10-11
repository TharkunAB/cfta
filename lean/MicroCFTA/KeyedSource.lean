import MicroCFTA.GroupedRecord
import MicroCFTA.GroupedMinimum

/-!
# Typed grouped recursive class construction

Each keyed occurrence reads that key's count, mass, decoder, and sampler.
The source builds the four fields together through map, pay, same-key choice,
and zero-inclusive product splits. Closed finite sources supply the leaves.
-/

namespace MicroCFTA.KeyedSource
open Probability SamplerReplay GroupedRecord

/-- Typed source operations used inside a mutually recursive key family. -/
inductive Recipe (Key Root : Type) : Type → Type 1 where
  | finite (source : FiniteSource.Source α) : Recipe Key Root α
  | retained (mass : Nat → Rat) (positive : ∀ size, 0 < mass size) (source : FiniteSource.Source α) : Recipe Key Root α
  | occurrence (key : Key) : Recipe Key Root Root
  | map (transform : α → β) (inner : Recipe Key Root α) : Recipe Key Root β
  | pay (inner : Recipe Key Root α) : Recipe Key Root α
  | choice (left right : Recipe Key Root α) : Recipe Key Root α
  | ap (functions : Recipe Key Root (α → β)) (arguments : Recipe Key Root α) : Recipe Key Root β

/-- Finite derivations specify the mutual key language without consulting any compiled class. -/
inductive Derives (program : Key → Recipe Key Root Root) : {α : Type} → Recipe Key Root α → α → Nat → Prop where
  | finite (source : FiniteSource.Source α) (value : α) (size : Nat)
      (member : value ∈ FiniteSource.classMembers source size) : Derives program (.finite source) value size
  | retained (mass : Nat → Rat) (positive : ∀ size, 0 < mass size) (source : FiniteSource.Source α)
      (value : α) (size : Nat) (member : value ∈ FiniteSource.classMembers source size) :
      Derives program (.retained mass positive source) value size
  | occurrence (key : Key) (value : Root) (size : Nat) (inner : Derives program (program key) value size) :
      Derives program (.occurrence key) value size
  | map (transform : α → β) (inner : Recipe Key Root α) (value : α) (size : Nat)
      (child : Derives program inner value size) : Derives program (.map transform inner) (transform value) size
  | pay (inner : Recipe Key Root α) (value : α) (size : Nat) (child : Derives program inner value size) :
      Derives program (.pay inner) value (size + 1)
  | left (left right : Recipe Key Root α) (value : α) (size : Nat) (child : Derives program left value size) :
      Derives program (.choice left right) value size
  | right (left right : Recipe Key Root α) (value : α) (size : Nat) (child : Derives program right value size) :
      Derives program (.choice left right) value size
  | ap (functions : Recipe Key Root (α → β)) (arguments : Recipe Key Root α) (function : α → β) (argument : α)
      (leftSize rightSize : Nat) (left : Derives program functions function leftSize)
      (right : Derives program arguments argument rightSize) :
      Derives program (.ap functions arguments) (function argument) (leftSize + rightSize)

/-- Source minimum expressions retain key presence, pay, choice, and product operations. -/
def minimumExpr : Recipe Key Root α → GroupedMinimum.Expression Key
  | .finite source | .retained _ _ source => .source (SourceMinimum.minimum source).toList
  | .occurrence key => .occurrence key
  | .map _ inner => minimumExpr inner
  | .pay inner => .pay (minimumExpr inner)
  | .choice left right => .choice (minimumExpr left) (minimumExpr right)
  | .ap functions arguments => .product (minimumExpr functions) (minimumExpr arguments)

/-- Erase the family to exactly the expression input of grouped minimum discovery. -/
def minimumProgram (program : Key → Recipe Key Root Root) : Key → GroupedMinimum.Expression Key :=
  fun key => minimumExpr (program key)

/-- Every actual member yields a witnessed minimum-expression derivation no larger than its own size. -/
theorem derivation_lower (program : Key → Recipe Key Root Root) (recipe : Recipe Key Root α)
    (value : α) (size : Nat) (derived : Derives program recipe value size) :
    ∃ lower, GroupedMinimum.Derives (minimumProgram program) (minimumExpr recipe) lower ∧ lower ≤ size := by
  induction derived with
  | finite source value size member | retained mass positive source value size member =>
      obtain ⟨lower, found, bound⟩ := SourceMinimum.member_bound source size value member
      exact ⟨lower, .source _ lower (by simp [found]), bound⟩
  | occurrence key value size inner ih =>
      obtain ⟨lower, derived, bound⟩ := ih
      exact ⟨lower, .occurrence key lower derived, bound⟩
  | map transform inner value size child ih => exact ih
  | pay inner value size child ih =>
      obtain ⟨lower, derived, bound⟩ := ih
      exact ⟨lower + 1, .pay _ lower derived, by omega⟩
  | left left right value size child ih =>
      obtain ⟨lower, derived, bound⟩ := ih
      exact ⟨lower, .left _ _ lower derived, bound⟩
  | right left right value size child ih =>
      obtain ⟨lower, derived, bound⟩ := ih
      exact ⟨lower, .right _ _ lower derived, bound⟩
  | ap functions arguments function argument leftSize rightSize left right ihl ihr =>
      obtain ⟨leftMinimum, leftDerived, leftBound⟩ := ihl
      obtain ⟨rightMinimum, rightDerived, rightBound⟩ := ihr
      exact ⟨leftMinimum + rightMinimum, .product _ _ _ _ leftDerived rightDerived, by omega⟩

/-- Run the actual grouped key/minimum probe over the typed recursive program. -/
def minima (keys : List Key) (complete : ∀ key, key ∈ keys) (program : Key → Recipe Key Root Root) : GroupedProbe.Table Key :=
  GroupedMinimum.discover keys complete (minimumProgram program)

/-- Every body subexpression's computed minimum is a lower bound for each actual finite member. -/
theorem derivation_minimum (keys : List Key) (complete : ∀ key, key ∈ keys) (program : Key → Recipe Key Root Root)
    (recipe : Recipe Key Root α) (value : α) (size : Nat) (derived : Derives program recipe value size) :
    ∃ lower, GroupedMinimum.evaluate (minimumExpr recipe) (minima keys complete program) = some (some lower) ∧ lower ≤ size := by
  obtain ⟨lower, erased, bound⟩ := derivation_lower program recipe value size derived
  have fixed := GroupedProbe.converge_fixed keys complete (GroupedMinimum.build (minimumProgram program)) (fun _ => none)
  obtain ⟨smaller, found, smallerBound⟩ := GroupedMinimum.evaluate_complete (minimumProgram program)
    (minima keys complete program) fixed (minimumExpr recipe) lower erased
  exact ⟨smaller, found, by omega⟩

/-- The source size guard excludes a same-size occurrence unless its product sibling costs positive size. -/
def guarded : Recipe Key Root α → GroupedProbe.Table Key → Bool
  | .finite _, _ | .retained _ _ _, _ => true
  | .occurrence _, _ => false
  | .map _ inner, known => guarded inner known
  | .pay _, _ => true
  | .choice left right, known => guarded left known && guarded right known
  | .ap functions arguments, known =>
      (guarded functions known || decide ((GroupedMinimum.evaluate (minimumExpr arguments) known).join ≠ some 0)) &&
      (guarded arguments known || decide ((GroupedMinimum.evaluate (minimumExpr functions) known).join ≠ some 0))

/-- Independent ordered class members retain all keyed occurrence members and every product split. -/
def values : Recipe Key Root α → (Key → Nat → List Root) → Nat → List α
  | .finite source, _, size | .retained _ _ source, _, size => FiniteSource.classMembers source size
  | .occurrence key, environment, size => environment key size
  | .map transform inner, environment, size => (values inner environment size).map transform
  | .pay inner, environment, size => match size with | 0 => [] | next + 1 => values inner environment next
  | .choice left right, environment, size => values left environment size ++ values right environment size
  | .ap functions arguments, environment, size => (List.range (size + 1)).flatMap fun split =>
      Decoder.applyValues (values functions environment split) (values arguments environment (size - split))

/-- An environment of genuine key members can produce only genuine body derivations. -/
theorem values_sound (program : Key → Recipe Key Root Root) (recipe : Recipe Key Root α)
    (environment : Key → Nat → List Root)
    (sound : ∀ key size value, value ∈ environment key size → Derives program (program key) value size)
    (size : Nat) (value : α) (member : value ∈ values recipe environment size) : Derives program recipe value size := by
  induction recipe generalizing size with
  | finite source => exact .finite source value size member
  | retained mass positive source => exact .retained mass positive source value size member
  | occurrence key => exact .occurrence key value size (sound key size value member)
  | map transform inner ih =>
      obtain ⟨input, present, rfl⟩ := List.mem_map.mp member
      exact .map transform inner input size (ih size input present)
  | pay inner ih =>
      cases size with
      | zero => simp [values] at member
      | succ size => exact .pay inner value size (ih size value member)
  | choice left right ihl ihr =>
      rcases List.mem_append.mp member with present | present
      · exact .left left right value size (ihl size value present)
      · exact .right left right value size (ihr size value present)
  | ap functions arguments ihf iha =>
      obtain ⟨split, within, function, functionMember, argument, argumentMember, rfl⟩ :=
        (by simpa only [values, Decoder.applyValues, List.mem_flatMap, List.mem_map] using member)
      have bound : split ≤ size := by have := List.mem_range.mp within; omega
      have derived := Derives.ap functions arguments function argument split (size - split)
        (ihf split function functionMember) (iha (size - split) argument argumentMember)
      simpa [Nat.add_sub_of_le bound] using derived

/-- Product enumeration includes the exact split of every pair of source members. -/
theorem values_product_member (functions : Recipe Key Root (α → β)) (arguments : Recipe Key Root α)
    (environment : Key → Nat → List Root) (function : α → β) (argument : α) (leftSize rightSize : Nat)
    (leftMember : function ∈ values functions environment leftSize)
    (rightMember : argument ∈ values arguments environment rightSize) :
    function argument ∈ values (.ap functions arguments) environment (leftSize + rightSize) := by
  simp only [values, Decoder.applyValues, List.mem_flatMap, List.mem_map]
  exact ⟨leftSize, List.mem_range.mpr (by omega), function, leftMember, argument, by simpa using rightMember, rfl⟩

/-- The actual grouped minimum table justifies every size cutoff, including cross-key product guards. -/
theorem values_complete (keys : List Key) (complete : ∀ key, key ∈ keys) (program : Key → Recipe Key Root Root)
    (budget : Nat) (environment : Key → Nat → List Root)
    (available : ∀ key size, size < budget → ∀ value, Derives program (program key) value size → value ∈ environment key size)
    (recipe : Recipe Key Root α) (value : α) (size : Nat) (derivation : Derives program recipe value size) :
    (size < budget → value ∈ values recipe environment size) ∧
      (size ≤ budget → guarded recipe (minima keys complete program) = true → value ∈ values recipe environment size) := by
  induction derivation with
  | finite source value size member | retained mass positive source value size member => exact ⟨fun _ => member, fun _ _ => member⟩
  | occurrence key value size inner ih =>
      exact ⟨fun within => available key size within value inner, by simp [guarded]⟩
  | map transform inner value size child ih =>
      exact ⟨fun within => List.mem_map.mpr ⟨value, ih.1 within, rfl⟩,
        fun within guard => List.mem_map.mpr ⟨value, ih.2 within guard, rfl⟩⟩
  | pay inner value size child ih =>
      exact ⟨fun within => ih.1 (by omega), fun within _ => ih.1 (by omega)⟩
  | left left right value size child ih =>
      refine ⟨fun within => List.mem_append_left _ (ih.1 within), ?_⟩
      intro within guard
      exact List.mem_append_left _ (ih.2 within (Bool.and_eq_true_iff.mp guard).1)
  | right left right value size child ih =>
      refine ⟨fun within => List.mem_append_right _ (ih.1 within), ?_⟩
      intro within guard
      exact List.mem_append_right _ (ih.2 within (Bool.and_eq_true_iff.mp guard).2)
  | ap functions arguments function argument leftSize rightSize left right ihl ihr =>
      refine ⟨fun within => values_product_member functions arguments environment function argument _ _
        (ihl.1 (by omega)) (ihr.1 (by omega)), ?_⟩
      intro within guard
      have parts := Bool.and_eq_true_iff.mp guard
      have leftMember : function ∈ values functions environment leftSize := by
        rcases Bool.or_eq_true_iff.mp parts.1 with leftGuard | sibling
        · exact ihl.2 (by omega) leftGuard
        · have nonzero := of_decide_eq_true sibling
          obtain ⟨lower, found, bound⟩ := derivation_minimum keys complete program arguments argument rightSize right
          have positive : lower ≠ 0 := by intro zero; apply nonzero; simp [found, zero]
          exact ihl.1 (by omega)
      have rightMember : argument ∈ values arguments environment rightSize := by
        rcases Bool.or_eq_true_iff.mp parts.2 with rightGuard | sibling
        · exact ihr.2 (by omega) rightGuard
        · have nonzero := of_decide_eq_true sibling
          obtain ⟨lower, found, bound⟩ := derivation_minimum keys complete program functions function leftSize left
          have positive : lower ≠ 0 := by intro zero; apply nonzero; simp [found, zero]
          exact ihr.1 (by omega)
      exact values_product_member functions arguments environment function argument _ _ leftMember rightMember

/-- Construct all class record fields with the grouped source operations. -/
def record : Recipe Key Root α → (Key → Classes Root) → Nat → Group α
  | .finite source, _, size => finiteClass source size
  | .retained mass _ source, _, size => GroupedRecord.retained (mass size) (FiniteSource.atSize source size)
  | .occurrence key, environment, size => environment key size
  | .map transform inner, environment, size => GroupedRecord.map transform (record inner environment size)
  | .pay inner, environment, size => GroupedRecord.pay (record inner environment) size
  | .choice left right, environment, size => merge [record left environment size, record right environment size]
  | .ap functions arguments, environment, size => productClasses (record functions environment) (record arguments environment) size

/-- The decoder's member order is exactly the independent keyed source stream. -/
theorem record_values (recipe : Recipe Key Root α) (environment : Key → Classes Root) (size : Nat) :
    Decoder.values (record recipe environment size).members.plan =
      values recipe (fun key size => Decoder.values (environment key size).members.plan) size := by
  induction recipe generalizing size with
  | finite source => exact FiniteSource.class_members source size
  | retained mass positive source => exact FiniteSource.class_members source size
  | occurrence key => rfl
  | map transform inner ih => simp [record, values, GroupedRecord.map, mapRecord, Decoder.values, ih]
  | pay inner ih =>
      cases size <;> simp [record, values, GroupedRecord.pay, GroupedRecord.empty, FiniteSource.empty, SamplerReplay.source, Decoder.values, ih]
  | choice left right ihl ihr => simp [record, values, merge_values, ihl, ihr]
  | ap functions arguments ihf iha => simp [record, values, productClasses_values, ihf, iha]

/-- Every body operation preserves coherent masses, ranks, and positive conditional sampling. -/
theorem record_valid (recipe : Recipe Key Root α) (environment : Key → Classes Root)
    (valid : ∀ key size, GroupedRecord.Valid (environment key size)) (size : Nat) :
    GroupedRecord.Valid (record recipe environment size) := by
  induction recipe generalizing size with
  | finite source => exact finiteClass_valid source size
  | retained mass positive source => exact retained_valid (mass size) (positive size) _ (FiniteSource.class_live source size)
  | occurrence key => exact valid key size
  | map transform inner ih => exact map_valid _ _ (ih size)
  | pay inner ih => exact pay_valid _ ih size
  | choice left right ihl ihr =>
      apply merge_valid
      intro group present
      rcases List.mem_cons.mp present with rfl | later
      · exact ihl size
      · have same := List.mem_singleton.mp later
        subst group
        exact ihr size
  | ap functions arguments ihf iha => exact productClasses_valid _ _ ihf iha size

/-- The simultaneous class knot accesses every key only at strictly smaller sizes. -/
def family (program : Key → Recipe Key Root Root) (size : Nat) (key : Key) : Group Root :=
  record (program key) (fun childKey childSize =>
    if _smaller : childSize < size then family program childSize childKey else GroupedRecord.empty) size
termination_by size

/-- All keys' parallel class records satisfy the invariant at every size. -/
theorem family_valid (program : Key → Recipe Key Root Root) (size : Nat) (key : Key) :
    GroupedRecord.Valid (family program size key) := by
  induction size using Nat.strongRecOn generalizing key with
  | ind size ih =>
      rw [family]
      apply record_valid
      intro childKey childSize
      split
      next smaller => exact ih childSize smaller childKey
      next => exact empty_valid

/-- Independent recursive class order uses the same size-recursive member equation. -/
def languageClass (program : Key → Recipe Key Root Root) (size : Nat) (key : Key) : List Root :=
  values (program key) (fun childKey childSize => if _smaller : childSize < size then languageClass program childSize childKey else []) size
termination_by size

/-- The actual compiled key record retains every member of its independent finite class equation. -/
theorem family_values (program : Key → Recipe Key Root Root) (size : Nat) (key : Key) :
    Decoder.values (family program size key).members.plan = languageClass program size key := by
  induction size using Nat.strongRecOn generalizing key with
  | ind size ih =>
      rw [family, record_values, languageClass]
      congr 1
      funext childKey childSize
      by_cases smaller : childSize < size
      · simp only [dite_eq_left smaller, ih childSize smaller]
      · simp [smaller, GroupedRecord.empty, FiniteSource.empty, SamplerReplay.source, Decoder.values]

/-- Key class counts are exactly the lengths of their complete ordered member streams. -/
theorem family_count (program : Key → Recipe Key Root Root) (size : Nat) (key : Key) :
    Decoder.count (family program size key).members.plan = (languageClass program size key).length := by
  rw [Decoder.count_correct, family_values]

/-- The mutually recursive compiled family contains every finite derivation and no other value. -/
theorem family_exact (keys : List Key) (complete : ∀ key, key ∈ keys) (program : Key → Recipe Key Root Root)
    (accepted : ∀ key, guarded (program key) (minima keys complete program) = true)
    (size : Nat) (key : Key) (value : Root) :
    value ∈ Decoder.values (family program size key).members.plan ↔ Derives program (program key) value size := by
  induction size using Nat.strongRecOn generalizing key value with
  | ind size ih =>
      rw [family, record_values]
      constructor
      · intro member
        apply values_sound program (program key) _ _ size value member
        intro childKey childSize child present
        split at present
        next smaller => exact (ih childSize smaller childKey child).mp present
        next => simp [GroupedRecord.empty, FiniteSource.empty, SamplerReplay.source, Decoder.values] at present
      · intro derived
        apply (values_complete keys complete program size _ _ (program key) value size derived).2
          (Nat.le_refl size) (accepted key)
        intro childKey childSize smaller child derivation
        simpa only [dite_eq_left smaller] using (ih childSize smaller childKey child).mpr derivation

end MicroCFTA.KeyedSource
