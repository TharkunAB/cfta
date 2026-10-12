import MicroCFTA.RecursiveSource
import MicroCFTA.SupportTerms

/-!
# Value and term indexes of heterogeneous recursive bodies

The two source indexes traverse the same finite recipe. Function values can
have different types at each application. Term construction retains the
private application, choice, and recursion nodes. A third interpretation
retains each value together with its term. Projection proves that both
independent indexes have the same class positions and counts.
-/
namespace MicroCFTA.RecursiveTermAlignment
open Language GeneratorCombinators

abbrev EngineTerm (Symbol : Type) := Term (Label Symbol)

/-- A recursive body with finite correlated inputs and the source operations. -/
inductive Recipe (Root Symbol : Type) : Type → Type 1 where
  | finite (source : FiniteSource.Source (α × EngineTerm Symbol)) : Recipe Root Symbol α
  | occurrence : Recipe Root Symbol Root
  | map (transform : α → β) (inner : Recipe Root Symbol α) : Recipe Root Symbol β
  | pay (inner : Recipe Root Symbol α) : Recipe Root Symbol α
  | choice (left right : Recipe Root Symbol α) : Recipe Root Symbol α
  | ap (functions : Recipe Root Symbol (α → β)) (arguments : Recipe Root Symbol α) : Recipe Root Symbol β
  | label (symbol : Symbol) (inner : Recipe Root Symbol α) : Recipe Root Symbol α

/-- The value index uses the source map, pay, choice, and product schedule. -/
def valueRecipe : Recipe Root Symbol α → RecursiveSource.Recipe Root α
  | .finite source => .finite (.map Prod.fst source)
  | .occurrence => .occurrence
  | .map transform inner => .map transform (valueRecipe inner)
  | .pay inner => .pay (valueRecipe inner)
  | .choice left right => .choice (valueRecipe left) (valueRecipe right)
  | .ap functions arguments => .ap (valueRecipe functions) (valueRecipe arguments)
  | .label _ inner => .pay (valueRecipe inner)

/-- The term index follows the source's independent term-building operations. -/
def termRecipe : Recipe Root Symbol α → RecursiveSource.Recipe (EngineTerm Symbol) (EngineTerm Symbol)
  | .finite source => .finite (.map Prod.snd source)
  | .occurrence => .occurrence
  | .map _ inner => termRecipe inner
  | .pay inner => .pay (termRecipe inner)
  | .choice left right => .choice
      (.map (fun term => .node (.choice 0) [term]) (termRecipe left))
      (.map (fun term => .node (.choice 1) [term]) (termRecipe right))
  | .ap functions arguments => .ap
      (.map (fun function argument => .node .apply [function, argument]) (termRecipe functions))
      (termRecipe arguments)
  | .label symbol inner => .pay (.map (SupportTerms.labelTerm symbol) (termRecipe inner))

/-- A correlated interpretation records both fields in their common rank order. -/
def pairedRecipe : Recipe Root Symbol α →
    RecursiveSource.Recipe (Root × EngineTerm Symbol) (α × EngineTerm Symbol)
  | .finite source => .finite source
  | .occurrence => .occurrence
  | .map transform inner => .map (fun entry => (transform entry.1, entry.2)) (pairedRecipe inner)
  | .pay inner => .pay (pairedRecipe inner)
  | .choice left right => .choice
      (.map (fun entry => (entry.1, .node (.choice 0) [entry.2])) (pairedRecipe left))
      (.map (fun entry => (entry.1, .node (.choice 1) [entry.2])) (pairedRecipe right))
  | .ap functions arguments => .ap
      (.map (fun function argument =>
        (function.1 argument.1, .node .apply [function.2, argument.2])) (pairedRecipe functions))
      (pairedRecipe arguments)
  | .label symbol inner => .pay
      (.map (fun entry => (entry.1, SupportTerms.labelTerm symbol entry.2)) (pairedRecipe inner))

/-- Each body class keeps exactly the independently constructed value order. -/
theorem body_values (recipe : Recipe Root Symbol α)
    (environment : Nat → List (Root × EngineTerm Symbol)) (size : Nat) :
    (RecursiveSource.values (pairedRecipe recipe) environment size).map Prod.fst =
      RecursiveSource.values (valueRecipe recipe) (fun size => (environment size).map Prod.fst) size := by
  induction recipe generalizing size with
  | finite source => rfl
  | occurrence => rfl
  | map transform inner ih => simpa [pairedRecipe, valueRecipe, RecursiveSource.values, List.map_map, Function.comp_def] using congrArg (List.map transform) (ih size)
  | pay inner ih => cases size <;> simp [pairedRecipe, valueRecipe, RecursiveSource.values, ih]
  | choice left right ihl ihr => simp [pairedRecipe, valueRecipe, RecursiveSource.values, List.map_map, Function.comp_def, ihl, ihr]
  | label symbol inner ih => cases size <;> simp [pairedRecipe, valueRecipe, RecursiveSource.values, List.map_map, Function.comp_def, ih]
  | ap functions arguments ihf iha =>
      simp only [pairedRecipe, valueRecipe, RecursiveSource.values, Decoder.applyValues,
        List.map_flatMap, List.flatMap_map, List.map_map, Function.comp_def]
      congr 1
      funext split
      rw [← ihf split, ← iha (size - split)]
      simp [List.flatMap_map, List.map_map, Function.comp_def]

/-- Each body class keeps exactly the independently constructed term order. -/
theorem body_terms (recipe : Recipe Root Symbol α)
    (environment : Nat → List (Root × EngineTerm Symbol)) (size : Nat) :
    (RecursiveSource.values (pairedRecipe recipe) environment size).map Prod.snd =
      RecursiveSource.values (termRecipe recipe) (fun size => (environment size).map Prod.snd) size := by
  induction recipe generalizing size with
  | finite source => rfl
  | occurrence => rfl
  | map transform inner ih => simpa [pairedRecipe, termRecipe, RecursiveSource.values, List.map_map, Function.comp_def] using ih size
  | pay inner ih => cases size <;> simp [pairedRecipe, termRecipe, RecursiveSource.values, ih]
  | choice left right ihl ihr =>
      simp only [pairedRecipe, termRecipe, RecursiveSource.values, List.map_append, List.map_map, Function.comp_def]
      rw [← ihl size, ← ihr size]
      simp [List.map_map, Function.comp_def]
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
  | choice left right ihl ihr | ap left right ihl ihr =>
      simp [pairedRecipe, valueRecipe, termRecipe, RecursiveSource.minimumExpr, ihl, ihr]

/-- Positive sibling sizes justify the same recursive guard in every interpretation. -/
theorem body_guards (recipe : Recipe Root Symbol α) (assumed : Option Nat) :
    RecursiveSource.guarded (pairedRecipe recipe) assumed = RecursiveSource.guarded (valueRecipe recipe) assumed ∧
    RecursiveSource.guarded (termRecipe recipe) assumed = RecursiveSource.guarded (valueRecipe recipe) assumed := by
  induction recipe with
  | finite source | occurrence => exact ⟨rfl, rfl⟩
  | map transform inner ih => exact ih
  | pay inner ih | label symbol inner ih => exact ⟨rfl, rfl⟩
  | choice left right ihl ihr =>
      simp [pairedRecipe, valueRecipe, termRecipe, RecursiveSource.guarded, ihl, ihr]
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

/-- This body has two recursive arguments of different intermediate function types. -/
def binaryBody : Recipe Nat String Nat :=
  .choice (.label "L" (.finite (.pure (1, .node .pure []))))
    (.label "B" (.ap (.ap (.finite (.pure (Nat.add, .node .pure []))) .occurrence) .occurrence))

theorem binary_guarded :
    RecursiveSource.guarded (valueRecipe binaryBody) (RecursiveSource.assumption (valueRecipe binaryBody)) = true := by
  cbv

theorem binary_count :
    Decoder.count (RecursiveSource.family (valueRecipe binaryBody) 5).plan = 2 ∧
    Decoder.count (RecursiveSource.family (termBody binaryBody) 5).plan = 2 := by
  cbv

/-- Equal user values keep two ranks and two different constructor terms. -/
theorem binary_duplicate_values :
    Decoder.decode (RecursiveSource.family (valueRecipe binaryBody) 5).plan 0 = some 3 ∧
    Decoder.decode (RecursiveSource.family (valueRecipe binaryBody) 5).plan 1 = some 3 ∧
    Decoder.decode (RecursiveSource.family (termBody binaryBody) 5).plan 0 ≠
      Decoder.decode (RecursiveSource.family (termBody binaryBody) 5).plan 1 := by
  cbv
  intro same
  simp at same

end MicroCFTA.RecursiveTermAlignment
