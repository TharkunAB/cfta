import MicroCFTA.KeyedSource
import MicroCFTA.KeyedMinimumWitness
import MicroCFTA.SupportTerms
import MicroCFTA.KeyedTermBoundary

/-!
# Correlated value and term indexes of mutually recursive key families

Each key has its own body and size classes. The value and term compilers use
the same typed operations. A paired compiler retains their common rank order.
The family boundary is a key-specific term constructor supplied by the source
adapter. It does not use the single-root Recursion constructor.
-/
namespace MicroCFTA.KeyedTermAlignment
open Language GeneratorCombinators

abbrev EngineTerm (Symbol : Type) := Term (Label Symbol)

/-- Typed keyed bodies retain each finite value together with its actual private term. -/
inductive Recipe (Key Root Symbol : Type) : Type → Type 1 where
  | finite (source : FiniteSource.Source (α × EngineTerm Symbol)) : Recipe Key Root Symbol α
  | retained (mass : Nat → Rat) (positive : ∀ size, 0 < mass size)
      (source : FiniteSource.Source (α × EngineTerm Symbol)) : Recipe Key Root Symbol α
  | occurrence (key : Key) : Recipe Key Root Symbol Root
  | map (transform : α → β) (inner : Recipe Key Root Symbol α) : Recipe Key Root Symbol β
  | pay (inner : Recipe Key Root Symbol α) : Recipe Key Root Symbol α
  | choice (left right : Recipe Key Root Symbol α) : Recipe Key Root Symbol α
  | ap (functions : Recipe Key Root Symbol (α → β)) (arguments : Recipe Key Root Symbol α) : Recipe Key Root Symbol β
  | label (symbol : Symbol) (inner : Recipe Key Root Symbol α) : Recipe Key Root Symbol α

/-- Sparse retained masses need positivity only at sizes with a source member.
The unused mass at an empty class is replaced by one before entering the core algebra. -/
def retainedLive (mass : Nat → Rat) (source : FiniteSource.Source (α × EngineTerm Symbol))
    (positive : ∀ size, 0 < Decoder.count (FiniteSource.atSize source size).plan → 0 < mass size) :
    Recipe Key Root Symbol α :=
  .retained (fun size => if 0 < Decoder.count (FiniteSource.atSize source size).plan then mass size else 1)
    (by
      intro size
      split
      next live => exact positive size live
      next => decide) source

/-- The independently compiled value fields. -/
def valueRecipe : Recipe Key Root Symbol α → KeyedSource.Recipe Key Root α
  | .finite source => .finite (.map Prod.fst source)
  | .retained mass positive source => .retained mass positive (.map Prod.fst source)
  | .occurrence key => .occurrence key
  | .map transform inner => .map transform (valueRecipe inner)
  | .pay inner => .pay (valueRecipe inner)
  | .choice left right => .choice (valueRecipe left) (valueRecipe right)
  | .ap functions arguments => .ap (valueRecipe functions) (valueRecipe arguments)
  | .label _ inner => .pay (valueRecipe inner)

/-- The independently compiled term fields retain the source operation wrappers. -/
def termRecipe : Recipe Key Root Symbol α → KeyedSource.Recipe Key (EngineTerm Symbol) (EngineTerm Symbol)
  | .finite source => .finite (.map Prod.snd source)
  | .retained mass positive source => .retained mass positive (.map Prod.snd source)
  | .occurrence key => .occurrence key
  | .map _ inner => termRecipe inner
  | .pay inner => .pay (termRecipe inner)
  | .choice left right => .choice
      (.map (fun term => .node (.choice 0) [term]) (termRecipe left))
      (.map (fun term => .node (.choice 1) [term]) (termRecipe right))
  | .ap functions arguments => .ap
      (.map (fun function argument => .node .apply [function, argument]) (termRecipe functions))
      (termRecipe arguments)
  | .label symbol inner => .pay (.map (SupportTerms.labelTerm symbol) (termRecipe inner))

/-- The paired compiler fixes which term belongs to each value occurrence. -/
def pairedRecipe : Recipe Key Root Symbol α →
    KeyedSource.Recipe Key (Root × EngineTerm Symbol) (α × EngineTerm Symbol)
  | .finite source => .finite source
  | .retained mass positive source => .retained mass positive source
  | .occurrence key => .occurrence key
  | .map transform inner => .map (fun entry => (transform entry.1, entry.2)) (pairedRecipe inner)
  | .pay inner => .pay (pairedRecipe inner)
  | .choice left right => .choice
      (.map (fun entry => (entry.1, .node (.choice 0) [entry.2])) (pairedRecipe left))
      (.map (fun entry => (entry.1, .node (.choice 1) [entry.2])) (pairedRecipe right))
  | .ap functions arguments => .ap
      (.map (fun function argument => (function.1 argument.1, .node .apply [function.2, argument.2]))
        (pairedRecipe functions)) (pairedRecipe arguments)
  | .label symbol inner => .pay
      (.map (fun entry => (entry.1, SupportTerms.labelTerm symbol entry.2)) (pairedRecipe inner))

/-- Filling an unused sparse mass cannot change the actual retained class mass. -/
theorem retainedLive_mass (mass : Nat → Rat) (source : FiniteSource.Source (α × EngineTerm Symbol))
    (positive : ∀ size, 0 < Decoder.count (FiniteSource.atSize source size).plan → 0 < mass size)
    (environment : Key → GroupedRecord.Classes (Root × EngineTerm Symbol)) (size : Nat) :
    (KeyedSource.record (pairedRecipe (retainedLive mass source positive)) environment size).mass =
      if 0 < Decoder.count (FiniteSource.atSize source size).plan then mass size else 0 := by
  simp only [retainedLive, pairedRecipe, KeyedSource.record, GroupedRecord.retained]
  split <;> simp_all

/-- Every body preserves the exact value order under arbitrary per-key environments. -/
theorem body_values (recipe : Recipe Key Root Symbol α)
    (environment : Key → Nat → List (Root × EngineTerm Symbol)) (size : Nat) :
    (KeyedSource.values (pairedRecipe recipe) environment size).map Prod.fst =
      KeyedSource.values (valueRecipe recipe) (fun key size => (environment key size).map Prod.fst) size := by
  induction recipe generalizing size with
  | finite source | retained mass positive source => rfl
  | occurrence key => rfl
  | map transform inner ih =>
      simpa [pairedRecipe, valueRecipe, KeyedSource.values, List.map_map, Function.comp_def] using congrArg (List.map transform) (ih size)
  | pay inner ih => cases size <;> simp [pairedRecipe, valueRecipe, KeyedSource.values, ih]
  | choice left right ihl ihr => simp [pairedRecipe, valueRecipe, KeyedSource.values, List.map_map, Function.comp_def, ihl, ihr]
  | label symbol inner ih => cases size <;> simp [pairedRecipe, valueRecipe, KeyedSource.values, List.map_map, Function.comp_def, ih]
  | ap functions arguments ihf iha =>
      simp only [pairedRecipe, valueRecipe, KeyedSource.values, Decoder.applyValues,
        List.map_flatMap, List.flatMap_map, List.map_map, Function.comp_def]
      congr 1
      funext split
      rw [← ihf split, ← iha (size - split)]
      simp [List.flatMap_map, List.map_map, Function.comp_def]

/-- Every body preserves the complete private term at the same class position. -/
theorem body_terms (recipe : Recipe Key Root Symbol α)
    (environment : Key → Nat → List (Root × EngineTerm Symbol)) (size : Nat) :
    (KeyedSource.values (pairedRecipe recipe) environment size).map Prod.snd =
      KeyedSource.values (termRecipe recipe) (fun key size => (environment key size).map Prod.snd) size := by
  induction recipe generalizing size with
  | finite source | retained mass positive source => rfl
  | occurrence key => rfl
  | map transform inner ih => simpa [pairedRecipe, termRecipe, KeyedSource.values, List.map_map, Function.comp_def] using ih size
  | pay inner ih => cases size <;> simp [pairedRecipe, termRecipe, KeyedSource.values, ih]
  | choice left right ihl ihr =>
      simp only [pairedRecipe, termRecipe, KeyedSource.values, List.map_append, List.map_map, Function.comp_def]
      rw [← ihl size, ← ihr size]
      simp [List.map_map, Function.comp_def]
  | label symbol inner ih =>
      cases size with
      | zero => rfl
      | succ size =>
          simpa [pairedRecipe, termRecipe, KeyedSource.values, List.map_map, Function.comp_def] using
            congrArg (List.map (SupportTerms.labelTerm symbol)) (ih size)
  | ap functions arguments ihf iha =>
      simp only [pairedRecipe, termRecipe, KeyedSource.values, Decoder.applyValues,
        List.map_flatMap, List.flatMap_map, List.map_map, Function.comp_def]
      congr 1
      funext split
      rw [← ihf split, ← iha (size - split)]
      simp [List.flatMap_map, List.map_map, Function.comp_def]

/-- Value recursion uses the original body at every key. -/
def valueProgram (program : Key → Recipe Key Root Symbol Root) : Key → KeyedSource.Recipe Key Root Root :=
  fun key => valueRecipe (program key)

/-- Member terms apply the source family boundary for the selected key. -/
def termProgram (wrap : Key → EngineTerm Symbol → EngineTerm Symbol)
    (program : Key → Recipe Key Root Symbol Root) : Key → KeyedSource.Recipe Key (EngineTerm Symbol) (EngineTerm Symbol) :=
  fun key => .map (wrap key) (termRecipe (program key))

/-- Correlated member terms apply exactly the same key boundary. -/
def pairedProgram (wrap : Key → EngineTerm Symbol → EngineTerm Symbol)
    (program : Key → Recipe Key Root Symbol Root) :
    Key → KeyedSource.Recipe Key (Root × EngineTerm Symbol) (Root × EngineTerm Symbol) :=
  fun key => .map (fun entry => (entry.1, wrap key entry.2)) (pairedRecipe (program key))

/-- The simultaneous knot preserves ordered value projections for every key and size. -/
theorem family_values (wrap : Key → EngineTerm Symbol → EngineTerm Symbol)
    (program : Key → Recipe Key Root Symbol Root) (size : Nat) (key : Key) :
    (KeyedSource.languageClass (pairedProgram wrap program) size key).map Prod.fst =
      KeyedSource.languageClass (valueProgram program) size key := by
  induction size using Nat.strongRecOn generalizing key with
  | ind size ih =>
      rw [KeyedSource.languageClass, KeyedSource.languageClass]
      simp only [pairedProgram, valueProgram, KeyedSource.values, List.map_map, Function.comp_def]
      rw [body_values]
      congr 1
      funext childKey childSize
      by_cases smaller : childSize < size
      · simpa only [dite_eq_left smaller, ite_eq_left smaller, pairedProgram, valueProgram] using ih childSize smaller childKey
      · simp [smaller]

/-- The simultaneous term knot has exactly the paired term projection, including every key boundary. -/
theorem family_terms (wrap : Key → EngineTerm Symbol → EngineTerm Symbol)
    (program : Key → Recipe Key Root Symbol Root) (size : Nat) (key : Key) :
    (KeyedSource.languageClass (pairedProgram wrap program) size key).map Prod.snd =
      KeyedSource.languageClass (termProgram wrap program) size key := by
  induction size using Nat.strongRecOn generalizing key with
  | ind size ih =>
      rw [KeyedSource.languageClass, KeyedSource.languageClass]
      simp only [pairedProgram, termProgram, KeyedSource.values, List.map_map, Function.comp_def]
      have step := congrArg (List.map (wrap key))
        (body_terms (program key) (fun childKey childSize =>
          if childSize < size then KeyedSource.languageClass (pairedProgram wrap program) childSize childKey else []) size)
      simp only [List.map_map, Function.comp_def] at step
      simp only [dite_eq_ite]
      rw [step]
      congr 2
      funext childKey childSize
      by_cases smaller : childSize < size
      · simpa only [dite_eq_left smaller, ite_eq_left smaller, termProgram, pairedProgram] using ih childSize smaller childKey
      · simp [smaller]

/-- All independent class indexes have the same counted rank interval. -/
theorem class_counts (wrap : Key → EngineTerm Symbol → EngineTerm Symbol)
    (program : Key → Recipe Key Root Symbol Root) (size : Nat) (key : Key) :
    Decoder.count (KeyedSource.family (pairedProgram wrap program) size key).members.plan =
      Decoder.count (KeyedSource.family (valueProgram program) size key).members.plan ∧
    Decoder.count (KeyedSource.family (termProgram wrap program) size key).members.plan =
      Decoder.count (KeyedSource.family (valueProgram program) size key).members.plan := by
  simp only [KeyedSource.family_count]
  have values := congrArg List.length (family_values wrap program size key)
  have terms := congrArg List.length (family_terms wrap program size key)
  simp only [List.length_map] at values terms
  exact ⟨values, terms.symm.trans values⟩

/-- The paired decoder projects to the independent value decoder at every rank. -/
theorem decode_value (wrap : Key → EngineTerm Symbol → EngineTerm Symbol)
    (program : Key → Recipe Key Root Symbol Root) (size rank : Nat) (key : Key) :
    (Decoder.decode (KeyedSource.family (pairedProgram wrap program) size key).members.plan rank).map Prod.fst =
      Decoder.decode (KeyedSource.family (valueProgram program) size key).members.plan rank := by
  simp only [Decoder.decode_correct, KeyedSource.family_values]
  rw [← family_values wrap program size key, List.getElem?_map]

/-- The paired decoder projects to the independent term decoder at every rank. -/
theorem decode_term (wrap : Key → EngineTerm Symbol → EngineTerm Symbol)
    (program : Key → Recipe Key Root Symbol Root) (size rank : Nat) (key : Key) :
    (Decoder.decode (KeyedSource.family (pairedProgram wrap program) size key).members.plan rank).map Prod.snd =
      Decoder.decode (KeyedSource.family (termProgram wrap program) size key).members.plan rank := by
  simp only [Decoder.decode_correct, KeyedSource.family_values]
  rw [← family_terms wrap program size key, List.getElem?_map]

/-- Every valid value rank has a correlated private term at that same key, size, and class rank. -/
theorem rank_alignment (wrap : Key → EngineTerm Symbol → EngineTerm Symbol)
    (program : Key → Recipe Key Root Symbol Root) (size rank : Nat) (key : Key)
    (within : rank < Decoder.count (KeyedSource.family (valueProgram program) size key).members.plan) :
    ∃ value term,
      Decoder.decode (KeyedSource.family (pairedProgram wrap program) size key).members.plan rank = some (value, term) ∧
      Decoder.decode (KeyedSource.family (valueProgram program) size key).members.plan rank = some value ∧
      Decoder.decode (KeyedSource.family (termProgram wrap program) size key).members.plan rank = some term := by
  obtain ⟨⟨value, term⟩, selected⟩ := Decoder.decode_exists _ rank ((class_counts wrap program size key).1 ▸ within)
  exact ⟨value, term, selected,
    by simpa [selected] using (decode_value wrap program size rank key).symm,
    by simpa [selected] using (decode_term wrap program size rank key).symm⟩

/-- Retained mass and term wrappers do not change key presence or minimum-size expressions. -/
theorem minimum_expressions (recipe : Recipe Key Root Symbol α) :
    KeyedSource.minimumExpr (pairedRecipe recipe) = KeyedSource.minimumExpr (valueRecipe recipe) ∧
    KeyedSource.minimumExpr (termRecipe recipe) = KeyedSource.minimumExpr (valueRecipe recipe) := by
  induction recipe with
  | finite source | retained mass positive source =>
      simp [pairedRecipe, valueRecipe, termRecipe, KeyedSource.minimumExpr, SourceMinimum.minimum]
  | occurrence key => exact ⟨rfl, rfl⟩
  | map transform inner ih => exact ih
  | pay inner ih | label symbol inner ih => simp [pairedRecipe, valueRecipe, termRecipe, KeyedSource.minimumExpr, ih]
  | choice left right ihl ihr | ap left right ihl ihr =>
      simp [pairedRecipe, valueRecipe, termRecipe, KeyedSource.minimumExpr, ihl, ihr]

/-- All three compilers use the same per-key guard, including cross-key positive product siblings. -/
theorem body_guards (recipe : Recipe Key Root Symbol α) (known : GroupedProbe.Table Key) :
    KeyedSource.guarded (pairedRecipe recipe) known = KeyedSource.guarded (valueRecipe recipe) known ∧
    KeyedSource.guarded (termRecipe recipe) known = KeyedSource.guarded (valueRecipe recipe) known := by
  induction recipe with
  | finite source | retained mass positive source | occurrence key => exact ⟨rfl, rfl⟩
  | map transform inner ih => exact ih
  | pay inner ih | label symbol inner ih => exact ⟨rfl, rfl⟩
  | choice left right ihl ihr => simp [pairedRecipe, valueRecipe, termRecipe, KeyedSource.guarded, ihl, ihr]
  | ap left right ihl ihr =>
      simp only [pairedRecipe, valueRecipe, termRecipe, KeyedSource.guarded, KeyedSource.minimumExpr,
        (minimum_expressions left).1, (minimum_expressions left).2,
        (minimum_expressions right).1, (minimum_expressions right).2, ihl.1, ihl.2, ihr.1, ihr.2]
      exact ⟨by trivial, by trivial⟩

/-- Minimum discovery receives identical programs in all interpretations. -/
theorem minimum_programs (wrap : Key → EngineTerm Symbol → EngineTerm Symbol)
    (program : Key → Recipe Key Root Symbol Root) :
    KeyedSource.minimumProgram (pairedProgram wrap program) = KeyedSource.minimumProgram (valueProgram program) ∧
    KeyedSource.minimumProgram (termProgram wrap program) = KeyedSource.minimumProgram (valueProgram program) := by
  constructor <;> funext key
  · exact (minimum_expressions (program key)).1
  · exact (minimum_expressions (program key)).2

/-- The actual finite-key minimum discovery gives the same metadata to every index. -/
theorem minima_equal (keys : List Key) (complete : ∀ key, key ∈ keys)
    (wrap : Key → EngineTerm Symbol → EngineTerm Symbol) (program : Key → Recipe Key Root Symbol Root) :
    KeyedSource.minima keys complete (pairedProgram wrap program) = KeyedSource.minima keys complete (valueProgram program) ∧
    KeyedSource.minima keys complete (termProgram wrap program) = KeyedSource.minima keys complete (valueProgram program) := by
  simp [KeyedSource.minima, (minimum_programs wrap program).1, (minimum_programs wrap program).2]

/-- Accepted source body guards also justify both independently tied term interpretations. -/
theorem family_guards (keys : List Key) (complete : ∀ key, key ∈ keys)
    (wrap : Key → EngineTerm Symbol → EngineTerm Symbol) (program : Key → Recipe Key Root Symbol Root)
    (accepted : ∀ key, KeyedSource.guarded (valueProgram program key)
      (KeyedSource.minima keys complete (valueProgram program)) = true) :
    (∀ key, KeyedSource.guarded (pairedProgram wrap program key)
      (KeyedSource.minima keys complete (pairedProgram wrap program)) = true) ∧
    (∀ key, KeyedSource.guarded (termProgram wrap program key)
      (KeyedSource.minima keys complete (termProgram wrap program)) = true) := by
  constructor <;> intro key
  · change KeyedSource.guarded (pairedRecipe (program key)) _ = true
    rw [(minima_equal keys complete wrap program).1, (body_guards (program key) _).1]
    exact accepted key
  · change KeyedSource.guarded (termRecipe (program key)) _ = true
    rw [(minima_equal keys complete wrap program).2, (body_guards (program key) _).2]
    exact accepted key

/-- The correlated family recognizes exactly its independent finite typed derivations. -/
theorem paired_exact (keys : List Key) (complete : ∀ key, key ∈ keys)
    (wrap : Key → EngineTerm Symbol → EngineTerm Symbol) (program : Key → Recipe Key Root Symbol Root)
    (accepted : ∀ key, KeyedSource.guarded (valueProgram program key)
      (KeyedSource.minima keys complete (valueProgram program)) = true)
    (size : Nat) (key : Key) (value : Root) (term : EngineTerm Symbol) :
    (value, term) ∈ Decoder.values (KeyedSource.family (pairedProgram wrap program) size key).members.plan ↔
      KeyedSource.Derives (pairedProgram wrap program) (pairedProgram wrap program key) (value, term) size :=
  KeyedSource.family_exact keys complete _ (family_guards keys complete wrap program accepted).1 size key _

/-- The source productive-key filter retains exactly the keys with an actual term class. -/
theorem live_keys_exact (keys : List Key) (complete : ∀ key, key ∈ keys)
    (wrap : Key → EngineTerm Symbol → EngineTerm Symbol) (program : Key → Recipe Key Root Symbol Root)
    (accepted : ∀ key, KeyedSource.guarded (valueProgram program key)
      (KeyedSource.minima keys complete (valueProgram program)) = true) (key : Key) :
    key ∈ GroupedMinimum.liveKeys keys (KeyedSource.minima keys complete (valueProgram program)) ↔
      ∃ size, 0 < Decoder.count (KeyedSource.family (termProgram wrap program) size key).members.plan := by
  rw [← (minima_equal keys complete wrap program).2,
    KeyedMinimumWitness.liveKeys_exact keys complete (termProgram wrap program) key]
  constructor
  · rintro ⟨term, size, derived⟩
    have member := (KeyedSource.family_exact keys complete (termProgram wrap program)
      (family_guards keys complete wrap program accepted).2 size key term).mpr derived
    refine ⟨size, ?_⟩
    rw [Decoder.count_correct]
    exact List.length_pos_iff.mpr (List.ne_nil_of_mem member)
  · rintro ⟨size, positive⟩
    rw [Decoder.count_correct] at positive
    obtain ⟨term, member⟩ := List.exists_mem_of_ne_nil _ (List.length_pos_iff.mp positive)
    exact ⟨term, size, (KeyedSource.family_exact keys complete (termProgram wrap program)
      (family_guards keys complete wrap program accepted).2 size key term).mp member⟩

/-- Bounding one member key preserves the entire ordered prefix of value classes. -/
theorem bounded_values (wrap : Key → EngineTerm Symbol → EngineTerm Symbol)
    (program : Key → Recipe Key Root Symbol Root) (key : Key) (bound : Nat) :
    (Decoder.values (GroupedRecord.bounded (fun size => KeyedSource.family (pairedProgram wrap program) size key) bound).plan).map Prod.fst =
      Decoder.values (GroupedRecord.bounded (fun size => KeyedSource.family (valueProgram program) size key) bound).plan := by
  simp [GroupedRecord.bounded, SamplerReplay.boundedRecord, SamplerReplay.manyRecord,
    SamplerReplay.manyPlan_values, List.flatMap_map, List.map_flatMap, KeyedSource.family_values, family_values]

/-- The bounded term index retains the same class offsets and member order. -/
theorem bounded_terms (wrap : Key → EngineTerm Symbol → EngineTerm Symbol)
    (program : Key → Recipe Key Root Symbol Root) (key : Key) (bound : Nat) :
    (Decoder.values (GroupedRecord.bounded (fun size => KeyedSource.family (pairedProgram wrap program) size key) bound).plan).map Prod.snd =
      Decoder.values (GroupedRecord.bounded (fun size => KeyedSource.family (termProgram wrap program) size key) bound).plan := by
  simp [GroupedRecord.bounded, SamplerReplay.boundedRecord, SamplerReplay.manyRecord,
    SamplerReplay.manyPlan_values, List.flatMap_map, List.map_flatMap, KeyedSource.family_values, family_terms]

/-- The exact source member wrapper uses the key's finite map position twice. -/
def sourceWrap (position : Key → Nat) : Key → EngineTerm Symbol → EngineTerm Symbol :=
  fun key => KeyedTermBoundary.atKeyTerm (position key)

/-- Actual source term family with AtKey [Key position [], Family [Key position [], body]]. -/
def sourceTermProgram (position : Key → Nat) (program : Key → Recipe Key Root Symbol Root) :=
  termProgram (sourceWrap position) program

/-- Actual source paired family for the same finite key-position table. -/
def sourcePairedProgram (position : Key → Nat) (program : Key → Recipe Key Root Symbol Root) :=
  pairedProgram (sourceWrap position) program

/-- The source private family wrappers do not change any key's value count or class rank. -/
theorem source_rank_alignment (position : Key → Nat) (program : Key → Recipe Key Root Symbol Root)
    (size rank : Nat) (key : Key)
    (within : rank < Decoder.count (KeyedSource.family (valueProgram program) size key).members.plan) :
    ∃ value term,
      Decoder.decode (KeyedSource.family (sourcePairedProgram position program) size key).members.plan rank = some (value, term) ∧
      Decoder.decode (KeyedSource.family (valueProgram program) size key).members.plan rank = some value ∧
      Decoder.decode (KeyedSource.family (sourceTermProgram position program) size key).members.plan rank = some term :=
  rank_alignment (sourceWrap position) program size rank key within

/-- Two keys mutually recurse. The two retained branches have equal values and distinct choice terms. -/
def twoKeyExample : Bool → Recipe Bool Nat Nat Nat
  | false => .choice
      (.choice
        (.retained (fun _ => 9) (by intro; decide) (.pure (0, .node .pure [])))
        (.retained (fun _ => 1) (by intro; decide) (.pure (0, .node .pure []))))
      (.label 10 (.map Nat.succ (.occurrence true)))
  | true => .label 11 (.map Nat.succ (.occurrence false))

/-- The example's finite key order is false, then true. -/
def twoKeyPosition (key : Bool) : Nat := if key then 1 else 0

/-- The first mutual occurrence has the exact AtKey and Family wrappers from the source. -/
example : Decoder.decode (KeyedSource.family (sourceTermProgram twoKeyPosition twoKeyExample) 1 true).members.plan 0 =
    some (KeyedTermBoundary.atKeyTerm 1
      (.node (.user 11) [KeyedTermBoundary.atKeyTerm 0
        (.node (.choice 0) [.node (.choice 0) [.node .pure []]])])) := by cbv

/-- A second mutual step retains both finite derivations, despite their equal user values. -/
example : Decoder.values (KeyedSource.family (valueProgram twoKeyExample) 2 false).members.plan = [2, 2] := by cbv

end MicroCFTA.KeyedTermAlignment
