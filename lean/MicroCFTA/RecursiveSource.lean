import MicroCFTA.SourceMinimum

/-!
# Guarded recursive source records

The accepted recursive source algebra contains closed finite sources, maps,
pays, equal-weight recursive choices, and products. Atomic and weighted finite
choices occur inside closed finite sources. Exact-size records recurse only
at smaller sizes. The minimum and guard metadata justify every cutoff.
-/

namespace MicroCFTA.RecursiveSource
open Probability SamplerReplay FiniteSource

/-- A typed recursive body with one distinguished root occurrence. -/
inductive Recipe (Root : Type) : Type → Type 1 where
  | finite (source : Source α) : Recipe Root α
  | occurrence : Recipe Root Root
  | map (transform : α → β) (inner : Recipe Root α) : Recipe Root β
  | pay (inner : Recipe Root α) : Recipe Root α
  | choice (left right : Recipe Root α) : Recipe Root α
  | ap (functions : Recipe Root (α → β)) (arguments : Recipe Root α) : Recipe Root β

/-- The source metadata expression is computed from the actual recursive body. -/
def minimumExpr : Recipe Root α → RecursionProbe.MinimumExpr
  | .finite source => .source (SourceMinimum.minimum source)
  | .occurrence => .occurrence
  | .map _ inner => minimumExpr inner
  | .pay inner => .pay (minimumExpr inner)
  | .choice left right => .choice (minimumExpr left) (minimumExpr right)
  | .ap functions arguments => .product (minimumExpr functions) (minimumExpr arguments)

/-- The assumed recursive minimum flows through standard source metadata operations. -/
def minimum (recipe : Recipe Root α) (assumed : Option Nat) : Option Nat :=
  RecursionProbe.evaluate (minimumExpr recipe) assumed

/-- The size-guard test is exactly pay guarding or a sibling without a size-zero member. -/
def guarded : Recipe Root α → Option Nat → Bool
  | .finite _, _ => true
  | .occurrence, _ => false
  | .map _ inner, assumed => guarded inner assumed
  | .pay _, _ => true
  | .choice left right, assumed => guarded left assumed && guarded right assumed
  | .ap functions arguments, assumed =>
      (guarded functions assumed || decide (minimum arguments assumed ≠ some 0)) &&
      (guarded arguments assumed || decide (minimum functions assumed ≠ some 0))

/-- Finite derivations describe the recursive language independently of the counted compiler. -/
inductive Derives (body : Recipe Root Root) : {α : Type} → Recipe Root α → α → Nat → Prop where
  | finite (source : Source α) (value : α) (size : Nat) (member : value ∈ classMembers source size) :
      Derives body (.finite source) value size
  | occurrence (value : Root) (size : Nat) (inner : Derives body body value size) :
      Derives body .occurrence value size
  | map (transform : α → β) (inner : Recipe Root α) (value : α) (size : Nat)
      (child : Derives body inner value size) : Derives body (.map transform inner) (transform value) size
  | pay (inner : Recipe Root α) (value : α) (size : Nat) (child : Derives body inner value size) :
      Derives body (.pay inner) value (size + 1)
  | left (left right : Recipe Root α) (value : α) (size : Nat) (child : Derives body left value size) :
      Derives body (.choice left right) value size
  | right (left right : Recipe Root α) (value : α) (size : Nat) (child : Derives body right value size) :
      Derives body (.choice left right) value size
  | ap (functions : Recipe Root (α → β)) (arguments : Recipe Root α) (function : α → β) (value : α)
      (functionSize argumentSize : Nat) (left : Derives body functions function functionSize)
      (right : Derives body arguments value argumentSize) :
      Derives body (.ap functions arguments) (function value) (functionSize + argumentSize)

/-- Fixed minimum metadata is a proved lower bound for every finite recursive derivation. -/
theorem derives_minimum (body : Recipe Root Root) (assumed : Option Nat)
    (fixed : minimum body assumed = assumed) (recipe : Recipe Root α) (value : α) (size : Nat)
    (derivation : Derives body recipe value size) :
    ∃ lower, minimum recipe assumed = some lower ∧ lower ≤ size := by
  induction derivation with
  | finite source value size member => exact SourceMinimum.member_bound source size value member
  | occurrence value size inner ih =>
      obtain ⟨lower, found, bound⟩ := ih
      exact ⟨lower, fixed ▸ found, bound⟩
  | map transform inner value size child ih => exact ih
  | pay inner value size child ih =>
      obtain ⟨lower, found, bound⟩ := ih
      refine ⟨lower + 1, ?_, by omega⟩
      change (minimum inner assumed).map (· + 1) = some (lower + 1)
      rw [found]
      rfl
  | left left right value size child ih =>
      obtain ⟨lower, found, bound⟩ := ih
      obtain ⟨smallest, kept, smaller⟩ := MinimumSize.best_improves_left (minimum left assumed) (minimum right assumed) lower found
      exact ⟨smallest, kept, by omega⟩
  | right left right value size child ih =>
      obtain ⟨lower, found, bound⟩ := ih
      obtain ⟨smallest, kept, smaller⟩ := MinimumSize.best_improves_right (minimum left assumed) (minimum right assumed) lower found
      exact ⟨smallest, kept, by omega⟩
  | ap functions arguments function value functionSize argumentSize left right ihl ihr =>
      obtain ⟨leftMinimum, leftFound, leftBound⟩ := ihl
      obtain ⟨rightMinimum, rightFound, rightBound⟩ := ihr
      refine ⟨leftMinimum + rightMinimum, ?_, by omega⟩
      change RecursionProbe.productMinimum (minimum functions assumed) (minimum arguments assumed) = _
      simp [RecursionProbe.productMinimum, leftFound, rightFound]

/-- Evaluate a recursive recipe's member language against an independently supplied class environment. -/
def values : Recipe Root α → (Nat → List Root) → Nat → List α
  | .finite source, _, size => classMembers source size
  | .occurrence, environment, size => environment size
  | .map transform inner, environment, size => (values inner environment size).map transform
  | .pay inner, environment, size => match size with | 0 => [] | next + 1 => values inner environment next
  | .choice left right, environment, size => values left environment size ++ values right environment size
  | .ap functions arguments, environment, size => (List.range (size + 1)).flatMap fun split =>
      Decoder.applyValues (values functions environment split) (values arguments environment (size - split))

/-- Every evaluated member has a finite derivation when each supplied occurrence does. -/
theorem values_sound (body : Recipe Root Root) (recipe : Recipe Root α) (environment : Nat → List Root)
    (sound : ∀ size value, value ∈ environment size → Derives body body value size)
    (size : Nat) (value : α) (member : value ∈ values recipe environment size) :
    Derives body recipe value size := by
  induction recipe generalizing size with
  | finite source => exact .finite source value size member
  | occurrence => exact .occurrence value size (sound size value member)
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

/-- Product members use the source's exact split position and function-major order. -/
theorem values_product_member (functions : Recipe Root (α → β)) (arguments : Recipe Root α)
    (environment : Nat → List Root) (function : α → β) (argument : α) (leftSize rightSize : Nat)
    (leftMember : function ∈ values functions environment leftSize)
    (rightMember : argument ∈ values arguments environment rightSize) :
    function argument ∈ values (.ap functions arguments) environment (leftSize + rightSize) := by
  simp only [values, Decoder.applyValues, List.mem_flatMap, List.mem_map]
  exact ⟨leftSize, List.mem_range.mpr (by omega), function, leftMember, argument, by simpa using rightMember, rfl⟩

/-- Guard metadata makes an equal-size occurrence unnecessary; positive siblings also provide a guard. -/
theorem values_complete (body : Recipe Root Root) (assumed : Option Nat)
    (fixed : minimum body assumed = assumed) (budget : Nat) (environment : Nat → List Root)
    (complete : ∀ size, size < budget → ∀ value, Derives body body value size → value ∈ environment size)
    (recipe : Recipe Root α) (value : α) (size : Nat) (derivation : Derives body recipe value size) :
    (size < budget → value ∈ values recipe environment size) ∧
      (size ≤ budget → guarded recipe assumed = true → value ∈ values recipe environment size) := by
  induction derivation with
  | finite source value size member => exact ⟨fun _ => member, fun _ _ => member⟩
  | occurrence value size inner ih =>
      exact ⟨fun within => complete size within value inner, by simp [guarded]⟩
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
  | ap functions arguments function value functionSize argumentSize left right ihl ihr =>
      refine ⟨fun within => values_product_member functions arguments environment function value _ _
        (ihl.1 (by omega)) (ihr.1 (by omega)), ?_⟩
      intro within guard
      have parts := Bool.and_eq_true_iff.mp guard
      have leftMember : function ∈ values functions environment functionSize := by
        rcases Bool.or_eq_true_iff.mp parts.1 with leftGuard | sibling
        · exact ihl.2 (by omega) leftGuard
        · have nonzero : minimum arguments assumed ≠ some 0 := of_decide_eq_true sibling
          obtain ⟨lower, found, bound⟩ := derives_minimum body assumed fixed arguments value argumentSize right
          have positive : lower ≠ 0 := by intro zero; exact nonzero (zero ▸ found)
          exact ihl.1 (by omega)
      have rightMember : value ∈ values arguments environment argumentSize := by
        rcases Bool.or_eq_true_iff.mp parts.2 with rightGuard | sibling
        · exact ihr.2 (by omega) rightGuard
        · have nonzero : minimum functions assumed ≠ some 0 := of_decide_eq_true sibling
          obtain ⟨lower, found, bound⟩ := derives_minimum body assumed fixed functions function functionSize left
          have positive : lower ≠ 0 := by intro zero; exact nonzero (zero ▸ found)
          exact ihr.1 (by omega)
      exact values_product_member functions arguments environment function value _ _ leftMember rightMember

/-- Construct count/decoder/sampler fields with the same source operations at one exact size. -/
def record : Recipe Root α → (Nat → Record Root) → Nat → Record α
  | .finite source, _, size => atSize source size
  | .occurrence, environment, size => environment size
  | .map transform inner, environment, size => mapRecord transform (record inner environment size)
  | .pay inner, environment, size => match size with | 0 => empty | next + 1 => record inner environment next
  | .choice left right, environment, size => countChoice [record left environment size, record right environment size]
  | .ap functions arguments, environment, size => countChoice ((List.range (size + 1)).map fun split =>
      applyRecord (record functions environment split) (record arguments environment (size - split)))

/-- Counted records have exactly the independent recursive-body member semantics. -/
theorem record_values (recipe : Recipe Root α) (environment : Nat → Record Root) (size : Nat) :
    Decoder.values (record recipe environment size).plan =
      values recipe (fun size => Decoder.values (environment size).plan) size := by
  induction recipe generalizing size with
  | finite source => exact class_members source size
  | occurrence => rfl
  | map transform inner ih => simp [record, values, mapRecord, Decoder.values, ih]
  | pay inner ih => cases size <;> simp [record, values, empty, SamplerReplay.source, Decoder.values, ih]
  | choice left right ihl ihr => simp [record, values, countChoice_members, ihl, ihr]
  | ap functions arguments ihf iha =>
      simp [record, values, countChoice_members, List.flatMap_map, applyRecord, Decoder.values, ihf, iha]

/-- Probability semantics uses member counts at size choices and preserves each closed atomic distribution. -/
def probabilities : Recipe Root α → (Nat → List Root) → (Nat → Distribution Root) → Nat → Distribution α
  | .finite source, _, _, size => classDistribution source size
  | .occurrence, _, environment, size => environment size
  | .map transform inner, members, environment, size => Probability.map transform (probabilities inner members environment size)
  | .pay inner, members, environment, size => match size with | 0 => [] | next + 1 => probabilities inner members environment next
  | .choice left right, members, environment, size => weightedChoice
      [((values left members size).length, ((values left members size).length : Rat), probabilities left members environment size),
       ((values right members size).length, ((values right members size).length : Rat), probabilities right members environment size)]
  | .ap functions arguments, members, environment, size => weightedChoice ((List.range (size + 1)).map fun split =>
      let count := (values functions members split).length * (values arguments members (size - split)).length
      (count, (count : Rat), Probability.map (fun pair => pair.1 pair.2)
        (product (probabilities functions members environment split) (probabilities arguments members environment (size - split)))))

/-- Constructed body samplers equal the independent probability recurrence. -/
theorem record_probabilities (recipe : Recipe Root α) (environment : Nat → Record Root) (size : Nat) :
    (record recipe environment size).sampling.values = probabilities recipe
      (fun size => Decoder.values (environment size).plan) (fun size => (environment size).sampling.values) size := by
  induction recipe generalizing size with
  | finite source => exact class_distribution source size
  | occurrence => rfl
  | map transform inner ih => simp [record, probabilities, mapRecord, Sampler.mapSampler, ih]
  | pay inner ih => cases size <;> simp [record, probabilities, empty, SamplerReplay.source, normalize, scale, ih]
  | choice left right ihl ihr =>
      simp [record, probabilities, countChoice, many_values, Decoder.count_correct, record_values, ihl, ihr]
  | ap functions arguments ihf iha =>
      simp [record, probabilities, countChoice, many_values, List.map_map, Function.comp_def,
        applyRecord, Sampler.productSampler, Decoder.count_correct, Decoder.values,
        Decoder.length_applyValues, record_values, ihf, iha]

/-- Each body construction preserves normalized live mass, positive rank coverage, and decoder replay. -/
theorem record_live (recipe : Recipe Root α) (environment : Nat → Record Root) (size : Nat)
    (valid : ∀ size, LiveValid (environment size)) : LiveValid (record recipe environment size) := by
  induction recipe generalizing size with
  | finite source => exact class_live source size
  | occurrence => exact valid size
  | map transform inner ih => exact map_live _ _ (ih size)
  | pay inner ih => cases size with | zero => exact empty_live | succ size => exact ih size
  | choice left right ihl ihr =>
      apply countChoice_live
      intro chosen present
      rcases List.mem_cons.mp present with rfl | remaining
      · exact ihl size
      · have same := List.mem_singleton.mp remaining
        subst chosen
        exact ihr size
  | ap functions arguments ihf iha =>
      apply countChoice_live
      intro chosen present
      obtain ⟨split, _, rfl⟩ := List.mem_map.mp present
      exact apply_live _ _ (ihf split) (iha (size - split))

/-- The finite class compiler reads recursive classes only at strictly smaller sizes. -/
def family (body : Recipe Root Root) (size : Nat) : Record Root :=
  record body (fun childSize => if _smaller : childSize < size then family body childSize else empty) size
termination_by size

/-- The recursive count/decoder/sampler knot has a valid finite record at every size. -/
theorem family_live (body : Recipe Root Root) (size : Nat) : LiveValid (family body size) := by
  induction size using Nat.strongRecOn with
  | ind size ih =>
      rw [family]
      apply record_live
      intro childSize
      split
      next smaller => exact ih childSize smaller
      next => exact empty_live

/-- Independent finite class semantics expands recursive references only below the current size. -/
def languageClass (body : Recipe Root Root) (size : Nat) : List Root :=
  values body (fun childSize => if _smaller : childSize < size then languageClass body childSize else []) size
termination_by size

/-- The recursive probability recurrence uses the same public count and atomic weighting policy. -/
def classProbability (body : Recipe Root Root) (size : Nat) : Distribution Root :=
  probabilities body
    (fun childSize => if childSize < size then languageClass body childSize else [])
    (fun childSize => if _smaller : childSize < size then classProbability body childSize else []) size
termination_by size

/-- Compiled member order equals the independently defined class stream, including repeated values. -/
theorem family_values (body : Recipe Root Root) (size : Nat) :
    Decoder.values (family body size).plan = languageClass body size := by
  induction size using Nat.strongRecOn with
  | ind size ih =>
      rw [family, record_values, languageClass]
      congr 1
      funext childSize
      by_cases smaller : childSize < size
      · simp only [dite_eq_left smaller, ih childSize smaller]
      · simp [smaller, empty, SamplerReplay.source, Decoder.values]

/-- The stored recursive count is the exact number of ordered class members. -/
theorem family_count (body : Recipe Root Root) (size : Nat) :
    Decoder.count (family body size).plan = (languageClass body size).length := by
  rw [Decoder.count_correct, family_values]

/-- Every recursive class preserves its declared source distribution, including atomic weights. -/
theorem family_probability (body : Recipe Root Root) (size : Nat) :
    (family body size).sampling.values = classProbability body size := by
  induction size using Nat.strongRecOn with
  | ind size ih =>
      rw [family, record_probabilities, classProbability]
      congr 1
      · funext childSize
        by_cases smaller : childSize < size
        · simp only [dite_eq_left smaller, ite_eq_left smaller, family_values]
        · simp [smaller, empty, SamplerReplay.source, Decoder.values]
      · funext childSize
        by_cases smaller : childSize < size
        · simp only [dite_eq_left smaller, ih childSize smaller]
        · simp [smaller, empty, SamplerReplay.source, normalize, scale]

/-- The source's minimum probe computes the assumption used to check the body. -/
def assumption (body : Recipe Root Root) : Option Nat :=
  (RecursionProbe.converge (RecursionProbe.expressionBody (minimumExpr body) true false false)).assumption

/-- Standard recursive source constructors establish their minimum fixed point without a caller premise. -/
theorem assumption_fixed (body : Recipe Root Root) : minimum body (assumption body) = assumption body := by
  have fixed := RecursionProbe.expression_minimum_fixed (minimumExpr body) true false false
  have actual := (RecursionProbe.converge_correct
    (RecursionProbe.expressionBody (minimumExpr body) true false false)).1
  rw [actual] at fixed
  exact fixed

/-- Every accepted recursive body has exactly its finite derivations at each compiled size. -/
theorem family_exact (body : Recipe Root Root) (accepted : guarded body (assumption body) = true)
    (size : Nat) (value : Root) :
    value ∈ Decoder.values (family body size).plan ↔ Derives body body value size := by
  induction size using Nat.strongRecOn generalizing value with
  | ind size ih =>
      rw [family, record_values]
      constructor
      · intro member
        apply values_sound body body _ _ size value member
        intro childSize child present
        split at present
        next smaller => exact (ih childSize smaller child).mp present
        next => simp [empty, SamplerReplay.source, Decoder.values] at present
      · intro derived
        apply (values_complete body (assumption body) (assumption_fixed body) size _ _ body value size derived).2
          (Nat.le_refl size) accepted
        intro childSize smaller child derivation
        simpa only [dite_eq_left smaller] using (ih childSize smaller child).mpr derivation

/-- Exact-size recursive decoding succeeds precisely for the finite derivation language. -/
theorem family_rank_exact (body : Recipe Root Root) (accepted : guarded body (assumption body) = true)
    (size : Nat) (value : Root) :
    (∃ rank, rank < Decoder.count (family body size).plan ∧
      Decoder.decode (family body size).plan rank = some value) ↔ Derives body body value size := by
  rw [← Decoder.mem_values_iff, family_exact body accepted]

/-- Bounded recursive compilation composes the exact class records and their count-weighted sampler. -/
def bounded (body : Recipe Root Root) (bound : Nat) : Record Root := boundedRecord (family body) bound

/-- The bounded recursive record has normalized live mass, total valid ranks, and decoder replay. -/
theorem bounded_live (body : Recipe Root Root) (bound : Nat) : LiveValid (bounded body bound) :=
  SamplerReplay.bounded_live _ _ (family_live body)

/-- Bounded recursive probabilities choose classes by their exact counts and preserve within-class weights. -/
theorem bounded_probability (body : Recipe Root Root) (bound : Nat) :
    (bounded body bound).sampling.values =
      weightedChoice ((List.range (bound + 1)).map fun size =>
        ((languageClass body size).length, ((languageClass body size).length : Rat), classProbability body size)) := by
  simp [bounded, boundedRecord, many_values, List.map_map, Function.comp_def, family_count, family_probability]

/-- No finite derivation below the bound is dropped, and no other value is admitted. -/
theorem bounded_exact (body : Recipe Root Root) (accepted : guarded body (assumption body) = true)
    (bound : Nat) (value : Root) :
    value ∈ Decoder.values (bounded body bound).plan ↔ ∃ size, size ≤ bound ∧ Derives body body value size := by
  simp only [bounded, boundedRecord, manyRecord, manyPlan_values, List.flatMap_map, List.mem_flatMap]
  constructor
  · rintro ⟨size, within, present⟩
    exact ⟨size, by have := List.mem_range.mp within; omega, (family_exact body accepted size value).mp present⟩
  · rintro ⟨size, within, derived⟩
    exact ⟨size, List.mem_range.mpr (by omega), (family_exact body accepted size value).mpr derived⟩

/-- Positive sampled outcomes are exactly the bounded recursive derivation language. -/
theorem bounded_sample_exact (body : Recipe Root Root) (accepted : guarded body (assumption body) = true)
    (bound : Nat) (value : Root) :
    (∃ rank mass, 0 < mass ∧ (mass, (rank, value)) ∈ (bounded body bound).sampling.ranked) ↔
      ∃ size, size ≤ bound ∧ Derives body body value size := by
  rw [← bounded_exact body accepted]
  have valid := bounded_live body bound
  constructor
  · rintro ⟨rank, mass, _, present⟩
    have decoded := valid.1.2 _ present
    exact (Decoder.mem_values_iff _ _).mpr ⟨rank, decoded_bound _ _ _ decoded, decoded⟩
  · intro present
    obtain ⟨rank, within, decoded⟩ := (Decoder.mem_values_iff _ _).mp present
    obtain ⟨mass, found, positive, sampled, same⟩ := valid.2.1 rank within
    have equal : found = value := Option.some.inj (same.symm.trans decoded)
    exact ⟨rank, mass, positive, equal ▸ sampled⟩

end MicroCFTA.RecursiveSource
