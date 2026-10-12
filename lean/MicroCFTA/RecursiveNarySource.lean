import MicroCFTA.RecursiveNaryRankMass
import MicroCFTA.RecursiveChoiceAssociativity
import MicroCFTA.RecursiveSamplerUnfolding

/-!
# Flat source records and typed n-ary lowering

The source records use one flat count-weighted choice. Their complete plan
member lists and sampler fields equal the lowered records. The plan trees
can differ. The member order and every replay rank are equal.
-/
namespace MicroCFTA.RecursiveNarySource
open Language GeneratorCombinators RecursiveNaryBody Probability SamplerReplay
open RecursiveChoiceAssociativity

/-- Record equality at the observable member and sampler fields. -/
def Fields (left right : Record α) : Prop :=
  Decoder.values left.plan = Decoder.values right.plan ∧
  left.sampling.values = right.sampling.values ∧ left.sampling.ranked = right.sampling.ranked

theorem fields_count (left right : Record α) (same : Fields left right) :
    Decoder.count left.plan = Decoder.count right.plan := by
  rw [Decoder.count_correct, Decoder.count_correct, same.1]

/-- Choice lowering preserves all ordered decoder members. -/
theorem alternatives_plan (branches : List (RecursiveSource.Recipe Root α))
    (environment : Nat → Record Root) (size : Nat) :
    Decoder.values (RecursiveSource.record (RecursiveNaryBody.alternatives branches) environment size).plan =
      Decoder.values (FiniteSource.countChoice
        (branches.map fun branch => RecursiveSource.record branch environment size)).plan := by
  simp only [RecursiveSource.record_values, alternatives_values, FiniteSource.countChoice_members,
    List.flatMap_map]

/-- Flat and lowered alternatives have identical counts, values, masses, and rank order. -/
theorem alternatives_fields (branches : List (RecursiveSource.Recipe Root α))
    (environment : Nat → Record Root) (size : Nat)
    (coherent : ∀ branch ∈ branches, Coherent (RecursiveSource.record branch environment size)) :
    Fields (RecursiveSource.record (RecursiveNaryBody.alternatives branches) environment size)
      (FiniteSource.countChoice (branches.map fun branch => RecursiveSource.record branch environment size)) := by
  refine ⟨alternatives_plan branches environment size, ?_⟩
  induction branches with
  | nil =>
      simp only [List.map_nil, RecursiveNaryBody.alternatives, RecursiveNaryBody.empty,
        RecursiveSource.record, FiniteSource.atSize]
      split <;> exact ⟨rfl, rfl⟩
  | cons first rest ih =>
      cases rest with
      | nil =>
          have single := countChoice_single (RecursiveSource.record first environment size) (coherent first (by simp))
          exact ⟨single.1.symm, single.2.symm⟩
      | cons next later =>
          have tail := ih (fun branch present => coherent branch (by simp [present]))
          have tailCount := congrArg List.length (alternatives_plan (next :: later) environment size)
          rw [← Decoder.count_correct, ← Decoder.count_correct] at tailCount
          have replace := countChoice_fields_congr
            [RecursiveSource.record first environment size,
              RecursiveSource.record (RecursiveNaryBody.alternatives (next :: later)) environment size]
            [RecursiveSource.record first environment size,
              FiniteSource.countChoice ((next :: later).map fun branch => RecursiveSource.record branch environment size)]
            (.cons ⟨rfl, rfl, rfl⟩ (.cons ⟨tailCount, tail⟩ .nil))
          exact ⟨replace.1.trans (countChoice_cons_values _ _), replace.2.trans (countChoice_cons_ranked _ _)⟩

/-- Value maps preserve all observable record fields. -/
theorem map_fields (transform : α → β) (left right : Record α) (same : Fields left right) :
    Fields (mapRecord transform left) (mapRecord transform right) := by
  rcases same with ⟨members, values, ranked⟩
  simp only [Fields, mapRecord, Decoder.values, Sampler.mapSampler]
  rw [members, values, ranked]
  exact ⟨rfl, rfl, rfl⟩

/-- Products retain function-major ranks and all input run masses. -/
theorem apply_fields (leftFunctions rightFunctions : Record (α → β))
    (leftArguments rightArguments : Record α)
    (functions : Fields leftFunctions rightFunctions) (arguments : Fields leftArguments rightArguments) :
    Fields (applyRecord leftFunctions leftArguments) (applyRecord rightFunctions rightArguments) := by
  have count := fields_count _ _ arguments
  rcases functions with ⟨fm, fv, fr⟩
  rcases arguments with ⟨am, av, ar⟩
  simp only [Fields, applyRecord, Decoder.values, Sampler.productSampler]
  rw [fm, fv, fr, am, av, ar, count]
  exact ⟨rfl, rfl, rfl⟩

/-- Flat choices preserve pairwise equal child fields. -/
theorem choice_fields (left right : List (Record α)) (same : RecursiveRankMass.Related Fields left right) :
    Fields (FiniteSource.countChoice left) (FiniteSource.countChoice right) := by
  constructor
  · simp only [FiniteSource.countChoice_members]
    induction same with
    | nil => rfl
    | cons fields remaining ih => simp only [List.flatMap_cons]; rw [fields.1, ih]
  · apply countChoice_fields_congr
    induction same with
    | nil => exact .nil
    | cons fields remaining ih => exact .cons ⟨fields_count _ _ fields, fields.2⟩ ih

/-- Indexed branch lists retain all pairwise field equalities. -/
theorem indexed_fields (count : Nat) (left right : Fin count → Record α)
    (same : ∀ index, Fields (left index) (right index)) :
    Fields (FiniteSource.countChoice (List.ofFn left)) (FiniteSource.countChoice (List.ofFn right)) := by
  apply choice_fields
  have related : ∀ keys : List (Fin count), RecursiveRankMass.Related Fields (keys.map left) (keys.map right) := by
    intro keys
    induction keys with
    | nil => exact .nil
    | cons key rest ih => exact .cons (same key) ih
  simpa only [List.map_ofFn, Function.comp_def, id_eq] using related (List.ofFn id)

/-- Observable field equality is symmetric. -/
theorem fields_symm {left right : Record α} (same : Fields left right) : Fields right left :=
  ⟨same.1.symm, same.2.1.symm, same.2.2.symm⟩

/-- Observable field equality composes. -/
theorem fields_trans {first second third : Record α} (left : Fields first second) (right : Fields second third) :
    Fields first third := ⟨left.1.trans right.1, left.2.1.trans right.2.1, left.2.2.trans right.2.2⟩

/-- Every flat branch can use an independently compiled but field-equal child. -/
theorem alternatives_records (count : Nat) (flat : Fin count → Record α)
    (lowered : Fin count → RecursiveSource.Recipe Root α) (environment : Nat → Record Root)
    (valid : ∀ size, LiveValid (environment size)) (size : Nat)
    (same : ∀ index, Fields (flat index) (RecursiveSource.record (lowered index) environment size)) :
    Fields (FiniteSource.countChoice (List.ofFn flat))
      (RecursiveSource.record (RecursiveNaryBody.alternatives (List.ofFn lowered)) environment size) := by
  apply fields_trans (indexed_fields count flat _ same)
  apply fields_symm
  have proof := alternatives_fields (List.ofFn lowered) environment size
    (fun branch _ => (RecursiveSource.record_live branch environment size valid).1)
  simpa only [List.map_ofFn, Function.comp_def] using proof

/-- The value compiler uses one flat source choice at every n-ary node. -/
def valueRecord : Recipe Root Symbol α → (Nat → Record Root) → Nat → Record α
  | .finite source, _, size => FiniteSource.atSize (.map Prod.fst source) size
  | .occurrence, environment, size => environment size
  | .map transform inner, environment, size => mapRecord transform (valueRecord inner environment size)
  | .pay inner, environment, size => match size with
      | 0 => FiniteSource.empty
      | size + 1 => valueRecord inner environment size
  | .choice count branches, environment, size => FiniteSource.countChoice
      (List.ofFn fun index : Fin count => valueRecord (branches index) environment size)
  | .ap functions arguments, environment, size => FiniteSource.countChoice
      ((List.range (size + 1)).map fun split => applyRecord
        (valueRecord functions environment split) (valueRecord arguments environment (size - split)))
  | .label _ inner, environment, size => match size with
      | 0 => FiniteSource.empty
      | size + 1 => valueRecord inner environment size

/-- The term compiler inserts each source branch wrapper before its flat choice. -/
def termRecord : Recipe Root Symbol α → (Nat → Record (EngineTerm Symbol)) → Nat → Record (EngineTerm Symbol)
  | .finite source, _, size => FiniteSource.atSize (.map Prod.snd source) size
  | .occurrence, environment, size => environment size
  | .map _ inner, environment, size => termRecord inner environment size
  | .pay inner, environment, size => match size with
      | 0 => FiniteSource.empty
      | size + 1 => termRecord inner environment size
  | .choice count branches, environment, size => FiniteSource.countChoice
      (List.ofFn fun index : Fin count => mapRecord (wrap index.val) (termRecord (branches index) environment size))
  | .ap functions arguments, environment, size => FiniteSource.countChoice
      ((List.range (size + 1)).map fun split => applyRecord
        (mapRecord (fun function argument => .node .apply [function, argument]) (termRecord functions environment split))
        (termRecord arguments environment (size - split)))
  | .label symbol inner, environment, size => match size with
      | 0 => FiniteSource.empty
      | size + 1 => mapRecord (SupportTerms.labelTerm symbol) (termRecord inner environment size)

/-- The paired compiler uses the same flat source choices and application ranks. -/
def pairedRecord : Recipe Root Symbol α → (Nat → Record (Root × EngineTerm Symbol)) → Nat → Record (α × EngineTerm Symbol)
  | .finite source, _, size => FiniteSource.atSize source size
  | .occurrence, environment, size => environment size
  | .map transform inner, environment, size => mapRecord (fun entry => (transform entry.1, entry.2)) (pairedRecord inner environment size)
  | .pay inner, environment, size => match size with
      | 0 => FiniteSource.empty
      | size + 1 => pairedRecord inner environment size
  | .choice count branches, environment, size => FiniteSource.countChoice
      (List.ofFn fun index : Fin count => mapRecord (fun entry => (entry.1, wrap index.val entry.2))
        (pairedRecord (branches index) environment size))
  | .ap functions arguments, environment, size => FiniteSource.countChoice
      ((List.range (size + 1)).map fun split => applyRecord
        (mapRecord (fun function argument => (function.1 argument.1, .node .apply [function.2, argument.2]))
          (pairedRecord functions environment split))
        (pairedRecord arguments environment (size - split)))
  | .label symbol inner, environment, size => match size with
      | 0 => FiniteSource.empty
      | size + 1 => mapRecord (fun entry => (entry.1, SupportTerms.labelTerm symbol entry.2)) (pairedRecord inner environment size)

/-- Lists preserve all child field equalities before flat source choice. -/
theorem list_fields (keys : List Key) (left right : Key → Record α)
    (same : ∀ key ∈ keys, Fields (left key) (right key)) :
    Fields (FiniteSource.countChoice (keys.map left)) (FiniteSource.countChoice (keys.map right)) := by
  apply choice_fields
  induction keys with
  | nil => exact .nil
  | cons key rest ih => exact .cons (same key (by simp)) (ih (fun k present => same k (by simp [present])))

/-- The full value compiler agrees with every lowered decoder and sampler field. -/
theorem value_record_fields (recipe : Recipe Root Symbol α) (environment : Nat → Record Root)
    (valid : ∀ size, LiveValid (environment size)) (size : Nat) :
    Fields (valueRecord recipe environment size) (RecursiveSource.record (valueRecipe recipe) environment size) := by
  induction recipe generalizing size with
  | finite source | occurrence => exact ⟨rfl, rfl, rfl⟩
  | map transform inner ih => exact map_fields _ _ _ (ih size)
  | pay inner ih | label symbol inner ih =>
      cases size with
      | zero => exact ⟨rfl, rfl, rfl⟩
      | succ size => exact ih size
  | choice count branches ih => exact alternatives_records count _ _ environment valid size (fun index => ih index size)
  | ap functions arguments ihf iha =>
      apply list_fields
      intro split _
      exact apply_fields _ _ _ _ (ihf split) (iha (size - split))

/-- The full term compiler retains flat labels, member order, and every rank mass. -/
theorem term_record_fields (recipe : Recipe Root Symbol α) (environment : Nat → Record (EngineTerm Symbol))
    (valid : ∀ size, LiveValid (environment size)) (size : Nat) :
    Fields (termRecord recipe environment size) (RecursiveSource.record (termRecipe recipe) environment size) := by
  induction recipe generalizing size with
  | finite source | occurrence => exact ⟨rfl, rfl, rfl⟩
  | map transform inner ih => exact ih size
  | pay inner ih =>
      cases size with
      | zero => exact ⟨rfl, rfl, rfl⟩
      | succ size => exact ih size
  | label symbol inner ih =>
      cases size with
      | zero => exact ⟨rfl, rfl, rfl⟩
      | succ size => exact map_fields _ _ _ (ih size)
  | choice count branches ih =>
      apply alternatives_records count _ _ environment valid size
      intro index
      exact map_fields _ _ _ (ih index size)
  | ap functions arguments ihf iha =>
      apply list_fields
      intro split _
      exact apply_fields _ _ _ _ (map_fields _ _ _ (ihf split)) (iha (size - split))

/-- The correlated compiler retains the same flat source record fields. -/
theorem paired_record_fields (recipe : Recipe Root Symbol α) (environment : Nat → Record (Root × EngineTerm Symbol))
    (valid : ∀ size, LiveValid (environment size)) (size : Nat) :
    Fields (pairedRecord recipe environment size) (RecursiveSource.record (pairedRecipe recipe) environment size) := by
  induction recipe generalizing size with
  | finite source | occurrence => exact ⟨rfl, rfl, rfl⟩
  | map transform inner ih => exact map_fields _ _ _ (ih size)
  | pay inner ih =>
      cases size with
      | zero => exact ⟨rfl, rfl, rfl⟩
      | succ size => exact ih size
  | label symbol inner ih =>
      cases size with
      | zero => exact ⟨rfl, rfl, rfl⟩
      | succ size => exact map_fields _ _ _ (ih size)
  | choice count branches ih =>
      apply alternatives_records count _ _ environment valid size
      intro index
      exact map_fields _ _ _ (ih index size)
  | ap functions arguments ihf iha =>
      apply list_fields
      intro split _
      exact apply_fields _ _ _ _ (map_fields _ _ _ (ihf split)) (iha (size - split))

/-- Equal ordered member lists give equal decoders at every valid or invalid rank. -/
theorem fields_decode (left right : Record α) (same : Fields left right) (rank : Nat) :
    Decoder.decode left.plan rank = Decoder.decode right.plan rank := by
  rw [Decoder.decode_correct, Decoder.decode_correct, same.1]

/-- Every guarded source family satisfies the complete record field equation. -/
theorem family_fields (body : RecursiveSource.Recipe Root Root)
    (accepted : RecursiveSource.guarded body (RecursiveSource.assumption body) = true) (size : Nat) :
    Fields (RecursiveSource.family body size) (RecursiveSource.record body (RecursiveSource.family body) size) := by
  refine ⟨?_, RecursiveSamplerUnfolding.sampler_unfold body accepted size,
    RecursiveSamplerUnfolding.ranked_unfold body accepted size⟩
  rw [RecursiveSource.record_values]
  exact RecursiveSourceUnfolding.family_unfold_values body accepted size

/-- The actual value family satisfies its flat n-ary source record equation. -/
theorem value_knot (body : Recipe Root Symbol Root)
    (accepted : RecursiveSource.guarded (valueRecipe body) (RecursiveSource.assumption (valueRecipe body)) = true)
    (size : Nat) :
    Fields (RecursiveSource.family (valueRecipe body) size)
      (valueRecord body (RecursiveSource.family (valueRecipe body)) size) :=
  fields_trans (family_fields (valueRecipe body) accepted size)
    (fields_symm (value_record_fields body _ (RecursiveSource.family_live _) size))

/-- The actual term family satisfies its flat source equation with the private root. -/
theorem term_knot (body : Recipe Root Symbol Root)
    (accepted : RecursiveSource.guarded (valueRecipe body) (RecursiveSource.assumption (valueRecipe body)) = true)
    (size : Nat) :
    Fields (RecursiveSource.family (termBody body) size)
      (mapRecord (fun term => .node .recursion [term])
        (termRecord body (RecursiveSource.family (termBody body)) size)) :=
  fields_trans (family_fields (termBody body) (term_guard body accepted) size)
    (fields_symm (map_fields _ _ _ (term_record_fields body _ (RecursiveSource.family_live _) size)))

/-- The paired family satisfies the same flat source equation at every size. -/
theorem paired_knot (body : Recipe Root Symbol Root)
    (accepted : RecursiveSource.guarded (valueRecipe body) (RecursiveSource.assumption (valueRecipe body)) = true)
    (size : Nat) :
    Fields (RecursiveSource.family (pairedBody body) size)
      (mapRecord (fun entry => (entry.1, .node .recursion [entry.2]))
        (pairedRecord body (RecursiveSource.family (pairedBody body)) size)) :=
  fields_trans (family_fields (pairedBody body) (paired_guard body accepted) size)
    (fields_symm (map_fields _ _ _ (paired_record_fields body _ (RecursiveSource.family_live _) size)))

end MicroCFTA.RecursiveNarySource
