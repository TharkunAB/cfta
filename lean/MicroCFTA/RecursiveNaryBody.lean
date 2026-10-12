import MicroCFTA.RecursiveTermAlignment
import MicroCFTA.RecursiveTermMass

/-!
# Typed recursive bodies with ordered n-ary choices

Each choice keeps one flat source branch number. The binary source algebra
is a lowering target. It does not add private binary choice wrappers.
-/
namespace MicroCFTA.RecursiveNaryBody
open Language GeneratorCombinators

abbrev EngineTerm (Symbol : Type) := Term (Label Symbol)

/-- A typed recursive body with one root and arbitrary ordered choices. -/
inductive Recipe (Root Symbol : Type) : Type → Type 1 where
  | finite (source : FiniteSource.Source (α × EngineTerm Symbol)) : Recipe Root Symbol α
  | occurrence : Recipe Root Symbol Root
  | map (transform : α → β) (inner : Recipe Root Symbol α) : Recipe Root Symbol β
  | pay (inner : Recipe Root Symbol α) : Recipe Root Symbol α
  | choice (count : Nat) (branches : Fin count → Recipe Root Symbol α) : Recipe Root Symbol α
  | ap (functions : Recipe Root Symbol (α → β)) (arguments : Recipe Root Symbol α) : Recipe Root Symbol β
  | label (symbol : Symbol) (inner : Recipe Root Symbol α) : Recipe Root Symbol α

/-- The empty alternative has no class members and no positive mass. -/
def empty : RecursiveSource.Recipe Root α := .finite (.source [] (by simp))

/-- Lower alternatives in source order without adding any term constructor. -/
def alternatives : List (RecursiveSource.Recipe Root α) → RecursiveSource.Recipe Root α
  | [] => empty
  | [first] => first
  | first :: second :: rest => .choice first (alternatives (second :: rest))

/-- A private branch label uses its position in the complete source list. -/
def wrap (branch : Nat) (term : EngineTerm Symbol) : EngineTerm Symbol :=
  .node (.choice branch) [term]

/-- Value choices retain every source branch, including empty branches. -/
def valueRecipe : Recipe Root Symbol α → RecursiveSource.Recipe Root α
  | .finite source => .finite (.map Prod.fst source)
  | .occurrence => .occurrence
  | .map transform inner => .map transform (valueRecipe inner)
  | .pay inner => .pay (valueRecipe inner)
  | .choice _ branches => alternatives (List.ofFn fun index => valueRecipe (branches index))
  | .ap functions arguments => .ap (valueRecipe functions) (valueRecipe arguments)
  | .label _ inner => .pay (valueRecipe inner)

/-- Term choices insert the flat branch label before the source lowering. -/
def termRecipe : Recipe Root Symbol α → RecursiveSource.Recipe (EngineTerm Symbol) (EngineTerm Symbol)
  | .finite source => .finite (.map Prod.snd source)
  | .occurrence => .occurrence
  | .map _ inner => termRecipe inner
  | .pay inner => .pay (termRecipe inner)
  | .choice _ branches => alternatives (List.ofFn fun index =>
      .map (wrap index.val) (termRecipe (branches index)))
  | .ap functions arguments => .ap
      (.map (fun function argument => .node .apply [function, argument]) (termRecipe functions))
      (termRecipe arguments)
  | .label symbol inner => .pay (.map (SupportTerms.labelTerm symbol) (termRecipe inner))

/-- The paired interpretation retains each value and its complete source term. -/
def pairedRecipe : Recipe Root Symbol α →
    RecursiveSource.Recipe (Root × EngineTerm Symbol) (α × EngineTerm Symbol)
  | .finite source => .finite source
  | .occurrence => .occurrence
  | .map transform inner => .map (fun entry => (transform entry.1, entry.2)) (pairedRecipe inner)
  | .pay inner => .pay (pairedRecipe inner)
  | .choice _ branches => alternatives (List.ofFn fun index =>
      .map (fun entry => (entry.1, wrap index.val entry.2)) (pairedRecipe (branches index)))
  | .ap functions arguments => .ap
      (.map (fun function argument =>
        (function.1 argument.1, .node .apply [function.2, argument.2])) (pairedRecipe functions))
      (pairedRecipe arguments)
  | .label symbol inner => .pay
      (.map (fun entry => (entry.1, SupportTerms.labelTerm symbol entry.2)) (pairedRecipe inner))

/-- Choice lowering preserves the complete ordered member list. -/
theorem alternatives_values (branches : List (RecursiveSource.Recipe Root α))
    (environment : Nat → List Root) (size : Nat) :
    RecursiveSource.values (alternatives branches) environment size =
      branches.flatMap (fun branch => RecursiveSource.values branch environment size) := by
  induction branches with
  | nil => simp [alternatives, empty, RecursiveSource.values, FiniteSource.classMembers]
  | cons first rest ih =>
      cases rest with
      | nil => simp [alternatives]
      | cons next later => simpa [alternatives, RecursiveSource.values] using congrArg (List.append (RecursiveSource.values first environment size)) ih

/-- Choice metadata uses the same ordered binary lowering as its records. -/
def minimumAlternatives : List RecursionProbe.MinimumExpr → RecursionProbe.MinimumExpr
  | [] => .source none
  | [first] => first
  | first :: second :: rest => .choice first (minimumAlternatives (second :: rest))

/-- Minimum metadata depends only on the ordered child metadata. -/
theorem alternatives_minimum (branches : List (RecursiveSource.Recipe Root α)) :
    RecursiveSource.minimumExpr (alternatives branches) =
      minimumAlternatives (branches.map RecursiveSource.minimumExpr) := by
  induction branches with
  | nil => simp [alternatives, empty, RecursiveSource.minimumExpr, SourceMinimum.minimum, minimumAlternatives]
  | cons first rest ih =>
      cases rest with
      | nil => rfl
      | cons next later => simp only [alternatives, RecursiveSource.minimumExpr, List.map_cons, minimumAlternatives] at *; rw [ih]

/-- Every choice branch must pass the recursive guard. -/
theorem alternatives_guarded (branches : List (RecursiveSource.Recipe Root α)) (assumed : Option Nat) :
    RecursiveSource.guarded (alternatives branches) assumed =
      branches.all (fun branch => RecursiveSource.guarded branch assumed) := by
  induction branches with
  | nil => rfl
  | cons first rest ih =>
      cases rest with
      | nil => simp [alternatives]
      | cons next later => simpa only [alternatives, RecursiveSource.guarded, List.all_cons] using congrArg (Bool.and (RecursiveSource.guarded first assumed)) ih

/-- Each lowered class retains the independent value-index order. -/
theorem body_values (recipe : Recipe Root Symbol α)
    (environment : Nat → List (Root × EngineTerm Symbol)) (size : Nat) :
    (RecursiveSource.values (pairedRecipe recipe) environment size).map Prod.fst =
      RecursiveSource.values (valueRecipe recipe) (fun size => (environment size).map Prod.fst) size := by
  induction recipe generalizing size with
  | finite source => rfl
  | occurrence => rfl
  | map transform inner ih => simpa [pairedRecipe, valueRecipe, RecursiveSource.values, List.map_map, Function.comp_def] using congrArg (List.map transform) (ih size)
  | pay inner ih => cases size <;> simp [pairedRecipe, valueRecipe, RecursiveSource.values, ih]
  | choice count branches ih =>
      simp only [pairedRecipe, valueRecipe, alternatives_values, List.map_flatMap]
      simp only [List.flatMap, List.map_ofFn, RecursiveSource.values, List.map_map, Function.comp_def]
      congr 2
      funext index
      exact ih index size
  | label symbol inner ih => cases size <;> simp [pairedRecipe, valueRecipe, RecursiveSource.values, List.map_map, Function.comp_def, ih]
  | ap functions arguments ihf iha =>
      simp only [pairedRecipe, valueRecipe, RecursiveSource.values, Decoder.applyValues,
        List.map_flatMap, List.flatMap_map, List.map_map, Function.comp_def]
      congr 1
      funext split
      rw [← ihf split, ← iha (size - split)]
      simp [List.flatMap_map, List.map_map, Function.comp_def]

/-- Each lowered class retains the independent flat-labelled term order. -/
theorem body_terms (recipe : Recipe Root Symbol α)
    (environment : Nat → List (Root × EngineTerm Symbol)) (size : Nat) :
    (RecursiveSource.values (pairedRecipe recipe) environment size).map Prod.snd =
      RecursiveSource.values (termRecipe recipe) (fun size => (environment size).map Prod.snd) size := by
  induction recipe generalizing size with
  | finite source => rfl
  | occurrence => rfl
  | map transform inner ih => simpa [pairedRecipe, termRecipe, RecursiveSource.values, List.map_map, Function.comp_def] using ih size
  | pay inner ih => cases size <;> simp [pairedRecipe, termRecipe, RecursiveSource.values, ih]
  | choice count branches ih =>
      simp only [pairedRecipe, termRecipe, alternatives_values, List.map_flatMap]
      simp only [List.flatMap, List.map_ofFn, RecursiveSource.values, List.map_map, Function.comp_def]
      congr 2
      funext index
      simpa [List.map_map, Function.comp_def] using congrArg (List.map (wrap index.val)) (ih index size)
  | label symbol inner ih =>
      cases size with
      | zero => rfl
      | succ size =>
          simpa [pairedRecipe, termRecipe, RecursiveSource.values, List.map_map, Function.comp_def] using
            congrArg (List.map (SupportTerms.labelTerm symbol)) (ih size)
  | ap functions arguments ihf iha =>
      simp only [pairedRecipe, termRecipe, RecursiveSource.values, Decoder.applyValues,
        List.map_flatMap, List.flatMap_map, List.map_map, Function.comp_def]
      congr 1
      funext split
      rw [← ihf split, ← iha (size - split)]
      simp [List.flatMap_map, List.map_map, Function.comp_def]

/-- The recursive term knot inserts the private boundary at every occurrence. -/
def termBody (body : Recipe Root Symbol Root) : RecursiveSource.Recipe (EngineTerm Symbol) (EngineTerm Symbol) :=
  .map (fun term => .node .recursion [term]) (termRecipe body)

/-- The paired knot inserts the same boundary without changing the value. -/
def pairedBody (body : Recipe Root Symbol Root) :
    RecursiveSource.Recipe (Root × EngineTerm Symbol) (Root × EngineTerm Symbol) :=
  .map (fun entry => (entry.1, .node .recursion [entry.2])) (pairedRecipe body)

/-- Every recursive class has the source value-index order, including duplicates. -/
theorem family_values (body : Recipe Root Symbol Root) (size : Nat) :
    (RecursiveSource.languageClass (pairedBody body) size).map Prod.fst =
      RecursiveSource.languageClass (valueRecipe body) size := by
  induction size using Nat.strongRecOn with
  | ind size ih =>
      rw [RecursiveSource.languageClass, RecursiveSource.languageClass]
      simp only [pairedBody, RecursiveSource.values, List.map_map, Function.comp_def]
      rw [body_values]
      congr 1
      funext childSize
      by_cases smaller : childSize < size
      · simpa only [dite_eq_left smaller, ite_eq_left smaller, pairedBody] using ih childSize smaller
      · simp [smaller]

/-- Every recursive class has the source term-index order and private boundaries. -/
theorem family_terms (body : Recipe Root Symbol Root) (size : Nat) :
    (RecursiveSource.languageClass (pairedBody body) size).map Prod.snd =
      RecursiveSource.languageClass (termBody body) size := by
  induction size using Nat.strongRecOn with
  | ind size ih =>
      rw [RecursiveSource.languageClass, RecursiveSource.languageClass]
      simp only [pairedBody, termBody, RecursiveSource.values, List.map_map, Function.comp_def]
      have step := congrArg (List.map (fun term : EngineTerm Symbol => Term.node Label.recursion [term]))
        (body_terms body (fun childSize =>
          if childSize < size then RecursiveSource.languageClass (pairedBody body) childSize else []) size)
      simp only [List.map_map, Function.comp_def, pairedBody] at step
      simp only [dite_eq_ite]
      rw [step]
      congr 2
      funext childSize
      by_cases smaller : childSize < size
      · simpa only [dite_eq_left smaller, ite_eq_left smaller, termBody, pairedBody] using ih childSize smaller
      · simp [smaller]

/-- The independently built value and term indexes have the same class cardinality. -/
theorem class_counts (body : Recipe Root Symbol Root) (size : Nat) :
    Decoder.count (RecursiveSource.family (valueRecipe body) size).plan =
      Decoder.count (RecursiveSource.family (termBody body) size).plan := by
  rw [RecursiveSource.family_count, RecursiveSource.family_count,
    ← family_values body size, ← family_terms body size]
  simp

/-- Selecting the value field from the correlated index gives the actual value index. -/
theorem decode_value (body : Recipe Root Symbol Root) (size rank : Nat) :
    (Decoder.decode (RecursiveSource.family (pairedBody body) size).plan rank).map Prod.fst =
      Decoder.decode (RecursiveSource.family (valueRecipe body) size).plan rank := by
  simp only [Decoder.decode_correct, RecursiveSource.family_values]
  rw [← family_values body size, List.getElem?_map]

/-- Selecting the term field from the correlated index gives the actual term index. -/
theorem decode_term (body : Recipe Root Symbol Root) (size rank : Nat) :
    (Decoder.decode (RecursiveSource.family (pairedBody body) size).plan rank).map Prod.snd =
      Decoder.decode (RecursiveSource.family (termBody body) size).plan rank := by
  simp only [Decoder.decode_correct, RecursiveSource.family_values]
  rw [← family_terms body size, List.getElem?_map]

/-- All three interpretations derive the same minimum-size expression. -/
theorem minimum_expressions (recipe : Recipe Root Symbol α) :
    RecursiveSource.minimumExpr (pairedRecipe recipe) = RecursiveSource.minimumExpr (valueRecipe recipe) ∧
    RecursiveSource.minimumExpr (termRecipe recipe) = RecursiveSource.minimumExpr (valueRecipe recipe) := by
  induction recipe with
  | finite source => simp [pairedRecipe, valueRecipe, termRecipe, RecursiveSource.minimumExpr, SourceMinimum.minimum]
  | occurrence => exact ⟨rfl, rfl⟩
  | map transform inner ih => exact ih
  | pay inner ih | label symbol inner ih =>
      simp [pairedRecipe, valueRecipe, termRecipe, RecursiveSource.minimumExpr, ih]
  | choice count branches ih =>
      simp only [pairedRecipe, valueRecipe, termRecipe, alternatives_minimum, List.map_ofFn]
      constructor <;> congr 2 <;> funext index
      · exact (ih index).1
      · exact (ih index).2
  | ap left right ihl ihr =>
      simp [pairedRecipe, valueRecipe, termRecipe, RecursiveSource.minimumExpr, ihl, ihr]

/-- Positive sibling sizes justify the same recursive guard in every interpretation. -/
theorem body_guards (recipe : Recipe Root Symbol α) (assumed : Option Nat) :
    RecursiveSource.guarded (pairedRecipe recipe) assumed = RecursiveSource.guarded (valueRecipe recipe) assumed ∧
    RecursiveSource.guarded (termRecipe recipe) assumed = RecursiveSource.guarded (valueRecipe recipe) assumed := by
  induction recipe with
  | finite source | occurrence => exact ⟨rfl, rfl⟩
  | map transform inner ih => exact ih
  | pay inner ih | label symbol inner ih => exact ⟨rfl, rfl⟩
  | choice count branches ih =>
      simp only [pairedRecipe, valueRecipe, termRecipe, alternatives_guarded]
      have congrAll {A B : Type 1} (first : Fin count → A) (second : Fin count → B)
          (p : A → Bool) (q : B → Bool) (same : ∀ index, p (first index) = q (second index)) :
          (List.ofFn first).all p = (List.ofFn second).all q := by
        apply Bool.eq_iff_iff.mpr
        simp only [List.all_eq_true, List.mem_ofFn]
        constructor
        · intro all x ⟨index, found⟩
          rw [← found, ← same index]
          exact all _ ⟨index, rfl⟩
        · intro all x ⟨index, found⟩
          rw [← found, same index]
          exact all _ ⟨index, rfl⟩
      constructor
      · apply congrAll; intro index; exact (ih index).1
      · apply congrAll; intro index; exact (ih index).2
  | ap left right ihl ihr =>
      simp only [pairedRecipe, valueRecipe, termRecipe, RecursiveSource.guarded,
        RecursiveSource.minimum, RecursiveSource.minimumExpr, (minimum_expressions left).1, (minimum_expressions left).2,
        (minimum_expressions right).1, (minimum_expressions right).2, ihl.1, ihl.2, ihr.1, ihr.2]
      exact ⟨rfl, rfl⟩

/-- The actual value guard also accepts the correlated recursive body. -/
theorem paired_guard (body : Recipe Root Symbol Root)
    (accepted : RecursiveSource.guarded (valueRecipe body) (RecursiveSource.assumption (valueRecipe body)) = true) :
    RecursiveSource.guarded (pairedBody body) (RecursiveSource.assumption (pairedBody body)) = true := by
  have minimum : RecursiveSource.minimumExpr (pairedBody body) = RecursiveSource.minimumExpr (valueRecipe body) :=
    (minimum_expressions body).1
  have sameAssumption : RecursiveSource.assumption (pairedBody body) = RecursiveSource.assumption (valueRecipe body) := by
    simp only [RecursiveSource.assumption, minimum]
  change RecursiveSource.guarded (pairedRecipe body) (RecursiveSource.assumption (pairedBody body)) = true
  rw [sameAssumption, (body_guards body _).1]
  exact accepted

/-- The independent term body passes the same source guard. -/
theorem term_guard (body : Recipe Root Symbol Root)
    (accepted : RecursiveSource.guarded (valueRecipe body) (RecursiveSource.assumption (valueRecipe body)) = true) :
    RecursiveSource.guarded (termBody body) (RecursiveSource.assumption (termBody body)) = true := by
  have minimum : RecursiveSource.minimumExpr (termBody body) = RecursiveSource.minimumExpr (valueRecipe body) :=
    (minimum_expressions body).2
  have sameAssumption : RecursiveSource.assumption (termBody body) = RecursiveSource.assumption (valueRecipe body) := by
    simp only [RecursiveSource.assumption, minimum]
  change RecursiveSource.guarded (termRecipe body) (RecursiveSource.assumption (termBody body)) = true
  rw [sameAssumption, (body_guards body _).2]
  exact accepted

/-- Each valid value rank selects exactly the term at that same class position. -/
theorem rank_alignment (body : Recipe Root Symbol Root) (size rank : Nat)
    (within : rank < Decoder.count (RecursiveSource.family (valueRecipe body) size).plan) :
    ∃ value term,
      Decoder.decode (RecursiveSource.family (pairedBody body) size).plan rank = some (value, term) ∧
      Decoder.decode (RecursiveSource.family (valueRecipe body) size).plan rank = some value ∧
      Decoder.decode (RecursiveSource.family (termBody body) size).plan rank = some term := by
  have count : Decoder.count (RecursiveSource.family (pairedBody body) size).plan =
      Decoder.count (RecursiveSource.family (valueRecipe body) size).plan := by
    rw [RecursiveSource.family_count, RecursiveSource.family_count, ← family_values body size]
    simp
  obtain ⟨⟨value, term⟩, selected⟩ := Decoder.decode_exists _ rank (count ▸ within)
  exact ⟨value, term, selected,
    by simpa [selected] using (decode_value body size rank).symm,
    by simpa [selected] using (decode_term body size rank).symm⟩

/-- The correlated record keeps all finite typed derivations and only those derivations. -/
theorem paired_exact (body : Recipe Root Symbol Root)
    (accepted : RecursiveSource.guarded (valueRecipe body) (RecursiveSource.assumption (valueRecipe body)) = true)
    (size : Nat) (value : Root) (term : EngineTerm Symbol) :
    (∃ rank, rank < Decoder.count (RecursiveSource.family (valueRecipe body) size).plan ∧
      Decoder.decode (RecursiveSource.family (valueRecipe body) size).plan rank = some value ∧
      Decoder.decode (RecursiveSource.family (termBody body) size).plan rank = some term) ↔
      RecursiveSource.Derives (pairedBody body) (pairedBody body) (value, term) size := by
  rw [← RecursiveSource.family_rank_exact (pairedBody body) (paired_guard body accepted)]
  have count : Decoder.count (RecursiveSource.family (pairedBody body) size).plan =
      Decoder.count (RecursiveSource.family (valueRecipe body) size).plan := by
    rw [RecursiveSource.family_count, RecursiveSource.family_count, ← family_values body size]
    simp
  constructor
  · rintro ⟨rank, within, selectedValue, selectedTerm⟩
    obtain ⟨foundValue, foundTerm, paired, actualValue, actualTerm⟩ := rank_alignment body size rank within
    have sameValue := Option.some.inj (actualValue.symm.trans selectedValue)
    have sameTerm := Option.some.inj (actualTerm.symm.trans selectedTerm)
    exact ⟨rank, count ▸ within, by simpa [sameValue, sameTerm] using paired⟩
  · rintro ⟨rank, within, paired⟩
    exact ⟨rank, count ▸ within,
      by simpa [paired] using (decode_value body size rank).symm,
      by simpa [paired] using (decode_term body size rank).symm⟩

/-- Bounding retains the same value order across the complete size prefix. -/
theorem bounded_values (body : Recipe Root Symbol Root) (bound : Nat) :
    (Decoder.values (RecursiveSource.bounded (pairedBody body) bound).plan).map Prod.fst =
      Decoder.values (RecursiveSource.bounded (valueRecipe body) bound).plan := by
  simp [RecursiveSource.bounded, SamplerReplay.boundedRecord, SamplerReplay.manyRecord,
    SamplerReplay.manyPlan_values, List.flatMap_map, List.map_flatMap,
    RecursiveSource.family_values, family_values]

/-- Bounding retains the same term order across the complete size prefix. -/
theorem bounded_terms (body : Recipe Root Symbol Root) (bound : Nat) :
    (Decoder.values (RecursiveSource.bounded (pairedBody body) bound).plan).map Prod.snd =
      Decoder.values (RecursiveSource.bounded (termBody body) bound).plan := by
  simp [RecursiveSource.bounded, SamplerReplay.boundedRecord, SamplerReplay.manyRecord,
    SamplerReplay.manyPlan_values, List.flatMap_map, List.map_flatMap,
    RecursiveSource.family_values, family_terms]

/-- Every bounded value rank has a corresponding term, so bounded inspection is total. -/
theorem bounded_rank_alignment (body : Recipe Root Symbol Root) (bound rank : Nat)
    (within : rank < Decoder.count (RecursiveSource.bounded (valueRecipe body) bound).plan) :
    ∃ value term,
      Decoder.decode (RecursiveSource.bounded (pairedBody body) bound).plan rank = some (value, term) ∧
      Decoder.decode (RecursiveSource.bounded (valueRecipe body) bound).plan rank = some value ∧
      Decoder.decode (RecursiveSource.bounded (termBody body) bound).plan rank = some term := by
  have count : Decoder.count (RecursiveSource.bounded (pairedBody body) bound).plan =
      Decoder.count (RecursiveSource.bounded (valueRecipe body) bound).plan := by
    rw [Decoder.count_correct, Decoder.count_correct, ← bounded_values body bound]
    simp
  obtain ⟨⟨value, term⟩, selected⟩ := Decoder.decode_exists _ rank (count ▸ within)
  refine ⟨value, term, selected, ?_, ?_⟩
  · rw [Decoder.decode_correct, ← bounded_values body bound, List.getElem?_map, ← Decoder.decode_correct, selected]
    rfl
  · rw [Decoder.decode_correct, ← bounded_terms body bound, List.getElem?_map, ← Decoder.decode_correct, selected]
    rfl


/-- The choice minimum is the source fold over all child minima. -/
theorem alternatives_evaluate (branches : List (RecursiveSource.Recipe Root α)) (assumed : Option Nat) :
    RecursiveSource.minimum (alternatives branches) assumed =
      (branches.map fun branch => RecursiveSource.minimum branch assumed).foldr MinimumSize.best none := by
  induction branches with
  | nil => rfl
  | cons first rest ih =>
      cases rest with
      | nil =>
          change RecursiveSource.minimum first assumed = MinimumSize.best (RecursiveSource.minimum first assumed) none
          cases RecursiveSource.minimum first assumed <;> rfl
      | cons next later =>
          change MinimumSize.best (RecursiveSource.minimum first assumed)
            (RecursiveSource.minimum (alternatives (next :: later)) assumed) = _
          rw [ih]
          rfl

/-- A lowered choice has exactly the finite derivations of its ordered children. -/
theorem alternatives_derives (body : RecursiveSource.Recipe Root Root)
    (branches : List (RecursiveSource.Recipe Root α)) (value : α) (size : Nat) :
    RecursiveSource.Derives body (alternatives branches) value size ↔
      ∃ branch ∈ branches, RecursiveSource.Derives body branch value size := by
  induction branches with
  | nil =>
      constructor
      · intro derivation
        cases derivation with
        | finite _ _ _ member =>
            simp [FiniteSource.classMembers] at member
      · simp
  | cons first rest ih =>
      cases rest with
      | nil => simp [alternatives]
      | cons next later =>
          constructor
          · intro derivation
            cases derivation with
            | left _ _ _ _ child => exact ⟨first, by simp, child⟩
            | right _ _ _ _ child =>
                obtain ⟨branch, present, derived⟩ := ih.mp child
                exact ⟨branch, by simp [present], derived⟩
          · rintro ⟨branch, present, derived⟩
            rcases List.mem_cons.mp present with same | laterMember
            · subst branch; exact .left _ _ _ _ derived
            · exact .right _ _ _ _ (ih.mpr ⟨branch, laterMember, derived⟩)

/-- Value choices traverse every child in the original source order. -/
theorem choice_values (count : Nat) (branches : Fin count → Recipe Root Symbol α)
    (environment : Nat → List Root) (size : Nat) :
    RecursiveSource.values (valueRecipe (.choice count branches)) environment size =
      (List.ofFn fun index => RecursiveSource.values (valueRecipe (branches index)) environment size).flatten := by
  simp only [valueRecipe, alternatives_values, List.flatMap, List.map_ofFn, Function.comp_def]

/-- Every term keeps the branch number from the complete source list. -/
theorem choice_terms (count : Nat) (branches : Fin count → Recipe Root Symbol α)
    (environment : Nat → List (EngineTerm Symbol)) (size : Nat) :
    RecursiveSource.values (termRecipe (.choice count branches)) environment size =
      (List.ofFn fun index => (RecursiveSource.values (termRecipe (branches index)) environment size).map
        (wrap index.val)).flatten := by
  simp only [termRecipe, alternatives_values, List.flatMap, List.map_ofFn, Function.comp_def,
    RecursiveSource.values]

/-- A branch can be empty at small sizes and have members at a later size. -/
def sparseBranches : Fin 3 → Recipe Nat String Nat
  | ⟨0, _⟩ => .label "L" (.finite (.pure (1, .node .pure [])))
  | ⟨1, _⟩ => .pay (.pay (.pay (.label "M" (.finite (.pure (7, .node .pure []))))))
  | ⟨2, _⟩ => .label "U" (.map Nat.succ .occurrence)

/-- This knot retains branch two after a branch with an empty current class. -/
def sparseBody : Recipe Nat String Nat := .choice 3 sparseBranches

theorem sparse_guarded :
    RecursiveSource.guarded (valueRecipe sparseBody) (RecursiveSource.assumption (valueRecipe sparseBody)) = true := by
  cbv

theorem sparse_class_values :
    RecursiveSource.languageClass (valueRecipe sparseBody) 3 = [3] := by
  cbv

/-- The middle branch is empty at size two but is a nonempty source alternative. -/
theorem sparse_middle_later :
    (RecursiveSource.values (valueRecipe (sparseBranches ⟨1, by decide⟩)) (fun _ => []) 2).length = 0 ∧
    (RecursiveSource.values (valueRecipe (sparseBranches ⟨1, by decide⟩)) (fun _ => []) 4).length = 1 := by
  cbv

/-- The first recursive constructor retains label two, not a binary nesting label. -/
theorem sparse_branch_two :
    Decoder.decode (RecursiveSource.family (termBody sparseBody) 2).plan 0 =
      some (.node .recursion [.node (.choice 2) [.node (.user "U")
        [.node .recursion [.node (.choice 0) [.node (.user "L") []]]]]]) := by
  cbv

/-- The raw singleton choice keeps its source wrapper. -/
theorem singleton_wrapper :
    RecursiveSource.values
      (termRecipe (.choice 1 (fun _ => .finite (.pure (7, .node .pure []))) : Recipe Nat String Nat))
      (fun _ => []) 0 = [.node (.choice 0) [.node .pure []]] := by
  cbv

/-- The raw empty choice has no member at any size. -/
theorem empty_choice (size : Nat) :
    RecursiveSource.values
      (termRecipe (.choice 0 Fin.elim0 : Recipe Nat String Nat)) (fun _ => []) size = [] := by
  simp [termRecipe, alternatives, empty, RecursiveSource.values, FiniteSource.classMembers]

end MicroCFTA.RecursiveNaryBody
