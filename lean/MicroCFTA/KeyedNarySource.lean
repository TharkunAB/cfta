import MicroCFTA.KeyedNaryMass
import MicroCFTA.GroupedMergeAssociativity
import MicroCFTA.KeyedSamplerUnfolding

/-!
# Exact flat grouped source records for n-ary recursive families

Flat choices use retained key masses. The binary lowering preserves mass,
ordered decoder members, value probabilities, and complete ranked runs.
-/
namespace MicroCFTA.KeyedNarySource
open Language GeneratorCombinators Probability SamplerReplay KeyedNaryAlignment
open GroupedMergeAssociativity (Fields fields_count merge_cons merge_single merge_fields_congr)

/-- Observable group equality is symmetric. -/
theorem fields_symm {left right : GroupedRecord.Group α} (same : Fields left right) : Fields right left :=
  ⟨same.1.symm, same.2.1.symm, same.2.2.1.symm, same.2.2.2.symm⟩

/-- Observable group equality composes without requiring identical plan trees. -/
theorem fields_trans {first second third : GroupedRecord.Group α} (left : Fields first second) (right : Fields second third) :
    Fields first third :=
  ⟨left.1.trans right.1, left.2.1.trans right.2.1, left.2.2.1.trans right.2.2.1, left.2.2.2.trans right.2.2.2⟩

/-- Lowered alternatives retain every field of the actual flat same-key merge. -/
theorem alternatives_fields (branches : List (KeyedSource.Recipe Key Root α))
    (environment : Key → GroupedRecord.Classes Root)
    (valid : ∀ key size, GroupedRecord.Valid (environment key size)) (size : Nat) :
    Fields (KeyedSource.record (KeyedNaryAlignment.alternatives branches) environment size)
      (GroupedRecord.merge (branches.map fun branch => KeyedSource.record branch environment size)) := by
  induction branches with
  | nil =>
      simp only [List.map_nil, KeyedNaryAlignment.alternatives, KeyedNaryAlignment.empty, KeyedSource.record,
        GroupedRecord.finiteClass, FiniteSource.atSize]
      split <;> exact ⟨rfl, rfl, rfl, rfl⟩
  | cons first rest ih =>
      cases rest with
      | nil => exact fields_symm (merge_single _ (KeyedSource.record_valid first environment valid size))
      | cons next later =>
          apply fields_trans
            (merge_fields_congr
              [KeyedSource.record first environment size,
                KeyedSource.record (KeyedNaryAlignment.alternatives (next :: later)) environment size]
              [KeyedSource.record first environment size,
                GroupedRecord.merge ((next :: later).map fun branch => KeyedSource.record branch environment size)]
              (.cons ⟨rfl, rfl, rfl, rfl⟩ (.cons ih .nil)))
          apply merge_cons
          · exact KeyedSource.record_valid first environment valid size
          · intro group present
            obtain ⟨branch, _, rfl⟩ := List.mem_map.mp present
            exact KeyedSource.record_valid branch environment valid size

/-- Value mapping preserves group mass and every replay field. -/
theorem map_fields (transform : α → β) (left right : GroupedRecord.Group α) (same : Fields left right) :
    Fields (GroupedRecord.map transform left) (GroupedRecord.map transform right) := by
  rcases same with ⟨mass, members, values, ranked⟩
  simp only [Fields, GroupedRecord.map, mapRecord, Decoder.values, Sampler.mapSampler]
  rw [mass, members, values, ranked]
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- Grouped application preserves product mass and function-major rank fields. -/
theorem apply_fields (leftFunctions rightFunctions : GroupedRecord.Group (α → β))
    (leftArguments rightArguments : GroupedRecord.Group α)
    (functions : Fields leftFunctions rightFunctions) (arguments : Fields leftArguments rightArguments) :
    Fields (GroupedRecord.apply leftFunctions leftArguments) (GroupedRecord.apply rightFunctions rightArguments) := by
  have count := fields_count _ _ arguments
  rcases functions with ⟨fmass, fm, fv, fr⟩
  rcases arguments with ⟨amass, am, av, ar⟩
  simp only [Fields, GroupedRecord.apply, applyRecord, Decoder.values, Sampler.productSampler]
  rw [fmass, amass, fm, fv, fr, am, av, ar, count]
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- Ordered group lists preserve pairwise field equality before a flat merge. -/
theorem list_fields (keys : List Name) (left right : Name → GroupedRecord.Group α)
    (same : ∀ key ∈ keys, Fields (left key) (right key)) :
    Fields (GroupedRecord.merge (keys.map left)) (GroupedRecord.merge (keys.map right)) := by
  apply merge_fields_congr
  induction keys with
  | nil => exact .nil
  | cons key rest ih => exact .cons (same key (by simp)) (ih (fun k present => same k (by simp [present])))

/-- Every indexed branch retains its original position and its own key mass. -/
theorem indexed_fields (count : Nat) (left right : Fin count → GroupedRecord.Group α)
    (same : ∀ index, Fields (left index) (right index)) :
    Fields (GroupedRecord.merge (List.ofFn left)) (GroupedRecord.merge (List.ofFn right)) := by
  simpa only [List.map_ofFn, Function.comp_def, id_eq] using
    list_fields (List.ofFn id) left right (fun index _ => same index)

/-- Every flat child can use an independently compiled but field-equal grouped record. -/
theorem alternatives_records (count : Nat) (flat : Fin count → GroupedRecord.Group α)
    (lowered : Fin count → KeyedSource.Recipe Key Root α) (environment : Key → GroupedRecord.Classes Root)
    (valid : ∀ key size, GroupedRecord.Valid (environment key size)) (size : Nat)
    (same : ∀ index, Fields (flat index) (KeyedSource.record (lowered index) environment size)) :
    Fields (GroupedRecord.merge (List.ofFn flat))
      (KeyedSource.record (KeyedNaryAlignment.alternatives (List.ofFn lowered)) environment size) := by
  apply fields_trans (indexed_fields count flat _ same)
  apply fields_symm
  simpa only [List.map_ofFn, Function.comp_def] using alternatives_fields (List.ofFn lowered) environment valid size

/-- The source value compiler merges every flat same-key alternative by its retained mass. -/
def valueRecord : Recipe Key Root Symbol α → (Key → GroupedRecord.Classes Root) → Nat → GroupedRecord.Group α
  | .finite source, _, size => GroupedRecord.finiteClass (.map Prod.fst source) size
  | .retained mass _ source, _, size => GroupedRecord.retained (mass size) (FiniteSource.atSize (.map Prod.fst source) size)
  | .occurrence key, environment, size => environment key size
  | .map transform inner, environment, size => GroupedRecord.map transform (valueRecord inner environment size)
  | .pay inner, environment, size => GroupedRecord.pay (valueRecord inner environment) size
  | .choice _ branches, environment, size => GroupedRecord.merge (List.ofFn fun index => valueRecord (branches index) environment size)
  | .ap functions arguments, environment, size => GroupedRecord.productClasses (valueRecord functions environment) (valueRecord arguments environment) size
  | .label _ inner, environment, size => GroupedRecord.pay (valueRecord inner environment) size

/-- The independent source term compiler adds each flat branch wrapper before merging. -/
def termRecord : Recipe Key Root Symbol α → (Key → GroupedRecord.Classes (EngineTerm Symbol)) → Nat → GroupedRecord.Group (EngineTerm Symbol)
  | .finite source, _, size => GroupedRecord.finiteClass (.map Prod.snd source) size
  | .retained mass _ source, _, size => GroupedRecord.retained (mass size) (FiniteSource.atSize (.map Prod.snd source) size)
  | .occurrence key, environment, size => environment key size
  | .map _ inner, environment, size => termRecord inner environment size
  | .pay inner, environment, size => GroupedRecord.pay (termRecord inner environment) size
  | .choice _ branches, environment, size => GroupedRecord.merge (List.ofFn fun index =>
      GroupedRecord.map (branchTerm index.val) (termRecord (branches index) environment size))
  | .ap functions arguments, environment, size => GroupedRecord.productClasses
      (fun split => GroupedRecord.map (fun function argument => .node .apply [function, argument]) (termRecord functions environment split))
      (termRecord arguments environment) size
  | .label symbol inner, environment, size => GroupedRecord.pay
      (fun childSize => GroupedRecord.map (SupportTerms.labelTerm symbol) (termRecord inner environment childSize)) size

/-- The paired compiler retains the same branch masses and correlated member positions. -/
def pairedRecord : Recipe Key Root Symbol α → (Key → GroupedRecord.Classes (Root × EngineTerm Symbol)) → Nat → GroupedRecord.Group (α × EngineTerm Symbol)
  | .finite source, _, size => GroupedRecord.finiteClass source size
  | .retained mass _ source, _, size => GroupedRecord.retained (mass size) (FiniteSource.atSize source size)
  | .occurrence key, environment, size => environment key size
  | .map transform inner, environment, size => GroupedRecord.map (fun entry => (transform entry.1, entry.2)) (pairedRecord inner environment size)
  | .pay inner, environment, size => GroupedRecord.pay (pairedRecord inner environment) size
  | .choice _ branches, environment, size => GroupedRecord.merge (List.ofFn fun index =>
      GroupedRecord.map (fun entry => (entry.1, branchTerm index.val entry.2)) (pairedRecord (branches index) environment size))
  | .ap functions arguments, environment, size => GroupedRecord.productClasses
      (fun split => GroupedRecord.map (fun function argument => (function.1 argument.1, .node .apply [function.2, argument.2]))
        (pairedRecord functions environment split)) (pairedRecord arguments environment) size
  | .label symbol inner, environment, size => GroupedRecord.pay
      (fun childSize => GroupedRecord.map (fun entry => (entry.1, SupportTerms.labelTerm symbol entry.2))
        (pairedRecord inner environment childSize)) size

/-- Every flat value record has the complete observable fields of its lowering. -/
theorem value_record_fields (recipe : Recipe Key Root Symbol α) (environment : Key → GroupedRecord.Classes Root)
    (valid : ∀ key size, GroupedRecord.Valid (environment key size)) (size : Nat) :
    Fields (valueRecord recipe environment size) (KeyedSource.record (valueRecipe recipe) environment size) := by
  induction recipe generalizing size with
  | finite source | retained mass positive source | occurrence key => exact ⟨rfl, rfl, rfl, rfl⟩
  | map transform inner ih => exact map_fields _ _ _ (ih size)
  | pay inner ih | label symbol inner ih =>
      cases size with
      | zero => exact ⟨rfl, rfl, rfl, rfl⟩
      | succ size => exact ih size
  | choice count branches ih => exact alternatives_records count _ _ environment valid size (fun index => ih index size)
  | ap functions arguments ihf iha =>
      apply list_fields
      intro split _
      exact apply_fields _ _ _ _ (ihf split) (iha (size - split))

/-- Every flat term record keeps its source branch labels and full ranked mass. -/
theorem term_record_fields (recipe : Recipe Key Root Symbol α) (environment : Key → GroupedRecord.Classes (EngineTerm Symbol))
    (valid : ∀ key size, GroupedRecord.Valid (environment key size)) (size : Nat) :
    Fields (termRecord recipe environment size) (KeyedSource.record (termRecipe recipe) environment size) := by
  induction recipe generalizing size with
  | finite source | retained mass positive source | occurrence key => exact ⟨rfl, rfl, rfl, rfl⟩
  | map transform inner ih => exact ih size
  | pay inner ih =>
      cases size with
      | zero => exact ⟨rfl, rfl, rfl, rfl⟩
      | succ size => exact ih size
  | label symbol inner ih =>
      cases size with
      | zero => exact ⟨rfl, rfl, rfl, rfl⟩
      | succ size => exact map_fields _ _ _ (ih size)
  | choice count branches ih =>
      apply alternatives_records count _ _ environment valid size
      intro index
      exact map_fields _ _ _ (ih index size)
  | ap functions arguments ihf iha =>
      apply list_fields
      intro split _
      exact apply_fields _ _ _ _ (map_fields _ _ _ (ihf split)) (iha (size - split))

/-- The correlated compiler retains all flat key masses, ordered terms, and sampler runs. -/
theorem paired_record_fields (recipe : Recipe Key Root Symbol α) (environment : Key → GroupedRecord.Classes (Root × EngineTerm Symbol))
    (valid : ∀ key size, GroupedRecord.Valid (environment key size)) (size : Nat) :
    Fields (pairedRecord recipe environment size) (KeyedSource.record (pairedRecipe recipe) environment size) := by
  induction recipe generalizing size with
  | finite source | retained mass positive source | occurrence key => exact ⟨rfl, rfl, rfl, rfl⟩
  | map transform inner ih => exact map_fields _ _ _ (ih size)
  | pay inner ih =>
      cases size with
      | zero => exact ⟨rfl, rfl, rfl, rfl⟩
      | succ size => exact ih size
  | label symbol inner ih =>
      cases size with
      | zero => exact ⟨rfl, rfl, rfl, rfl⟩
      | succ size => exact map_fields _ _ _ (ih size)
  | choice count branches ih =>
      apply alternatives_records count _ _ environment valid size
      intro index
      exact map_fields _ _ _ (ih index size)
  | ap functions arguments ihf iha =>
      apply list_fields
      intro split _
      exact apply_fields _ _ _ _ (map_fields _ _ _ (ihf split)) (iha (size - split))

/-- Equal ordered members give decoder equality at every valid or invalid rank. -/
theorem fields_decode (left right : GroupedRecord.Group α) (same : Fields left right) (rank : Nat) :
    Decoder.decode left.members.plan rank = Decoder.decode right.members.plan rank := by
  rw [Decoder.decode_correct, Decoder.decode_correct, same.2.1]

/-- Every guarded simultaneous family satisfies its complete grouped record equations. -/
theorem family_fields (keys : List Key) (complete : ∀ key, key ∈ keys)
    (program : Key → KeyedSource.Recipe Key Root Root)
    (accepted : ∀ key, KeyedSource.guarded (program key) (KeyedSource.minima keys complete program) = true)
    (size : Nat) (key : Key) :
    Fields (KeyedSource.family program size key)
      (KeyedSource.record (program key) (fun childKey childSize => KeyedSource.family program childSize childKey) size) := by
  have fields := KeyedSamplerUnfolding.fields_unfold keys complete program accepted size key
  refine ⟨fields.1, ?_, fields.2, KeyedSamplerUnfolding.ranked_unfold keys complete program accepted size key⟩
  rw [KeyedSource.record_values]
  exact KeyedSourceUnfolding.family_unfold_values keys complete program accepted size key

/-- The actual value family satisfies each flat mass-weighted source knot equation. -/
theorem value_knot (keys : List Key) (complete : ∀ key, key ∈ keys)
    (program : Key → Recipe Key Root Symbol Root)
    (accepted : ∀ key, KeyedSource.guarded (valueProgram program key)
      (KeyedSource.minima keys complete (valueProgram program)) = true) (size : Nat) (key : Key) :
    Fields (KeyedSource.family (valueProgram program) size key)
      (valueRecord (program key) (fun childKey childSize => KeyedSource.family (valueProgram program) childSize childKey) size) :=
  fields_trans (family_fields keys complete (valueProgram program) accepted size key)
    (fields_symm (value_record_fields (program key) _ (fun childKey childSize => KeyedSource.family_valid _ childSize childKey) size))

/-- The term family satisfies each flat source knot with its exact AtKey and Family wrapper. -/
theorem term_knot (keys : List Key) (complete : ∀ key, key ∈ keys) (code : Key → Nat)
    (program : Key → Recipe Key Root Symbol Root)
    (accepted : ∀ key, KeyedSource.guarded (valueProgram program key)
      (KeyedSource.minima keys complete (valueProgram program)) = true) (size : Nat) (key : Key) :
    Fields (KeyedSource.family (sourceTermProgram code program) size key)
      (GroupedRecord.map (KeyedTermBoundary.atKeyTerm (code key))
        (termRecord (program key) (fun childKey childSize => KeyedSource.family (sourceTermProgram code program) childSize childKey) size)) :=
  fields_trans (family_fields keys complete (sourceTermProgram code program)
    (family_guards keys complete (sourceWrap code) program accepted).2 size key)
    (fields_symm (map_fields _ _ _ (term_record_fields (program key) _
      (fun childKey childSize => KeyedSource.family_valid _ childSize childKey) size)))

/-- The paired family retains the same flat source mass and correlated replay fields. -/
theorem paired_knot (keys : List Key) (complete : ∀ key, key ∈ keys) (code : Key → Nat)
    (program : Key → Recipe Key Root Symbol Root)
    (accepted : ∀ key, KeyedSource.guarded (valueProgram program key)
      (KeyedSource.minima keys complete (valueProgram program)) = true) (size : Nat) (key : Key) :
    Fields (KeyedSource.family (sourcePairedProgram code program) size key)
      (GroupedRecord.map (fun entry => (entry.1, KeyedTermBoundary.atKeyTerm (code key) entry.2))
        (pairedRecord (program key) (fun childKey childSize => KeyedSource.family (sourcePairedProgram code program) childSize childKey) size)) :=
  fields_trans (family_fields keys complete (sourcePairedProgram code program)
    (family_guards keys complete (sourceWrap code) program accepted).1 size key)
    (fields_symm (map_fields _ _ _ (paired_record_fields (program key) _
      (fun childKey childSize => KeyedSource.family_valid _ childSize childKey) size)))

end MicroCFTA.KeyedNarySource
