import MicroCFTA.IntegerLabelCodec
import MicroCFTA.SymbolicBijections
import Std.Data.String.ToNat

/-!
# Open integer key offsets and formula composition

The source joins coordinate blocks in child order. Each formula receives a
simultaneous name substitution before the joined formula is constructed.
-/
namespace MicroCFTA.OpenIntegerKeys
open FullSyntax

abbrev integerName := IntegerLabelCodec.integerName

/-- The source reserved coordinate names are distinct for distinct indexes. -/
theorem integerName_injective : Function.Injective integerName := by
  intro left right same
  apply Nat.repr_injective
  have suffix := String.append_right_inj "__cfta_integer_" |>.mp same
  exact suffix

/-- The actual `renameFrom` replacement table. -/
def renamePairs (offset width : Nat) : List (Name × Name) :=
  (List.range width).map (fun index => (integerName index, integerName (offset + index)))

/-- Source name-only substitution cannot fail, including under quantifiers. -/
def renameFrom (offset width : Nat) (formula : Formula) : Formula :=
  SourceFormula.substitute (renamePairs offset width) formula

/-- Lookup follows the first matching source coordinate, with no shifted-name reapplication. -/
theorem lookup_coordinates (offset : Nat) (indexes : List Nat) (index : Nat) :
    lookup (integerName index)
      (indexes.map (fun item => (integerName item, Term.var (integerName (offset + item))))) =
      if index ∈ indexes then some (.var (integerName (offset + index))) else none := by
  induction indexes with
  | nil => simp [lookup]
  | cons first rest ih =>
      have inject : integerName index = integerName first ↔ index = first :=
        ⟨fun same => integerName_injective same, fun same => same ▸ rfl⟩
      by_cases same : index = first <;> simp [lookup, inject, same, ih]

/-- A positive offset contains no identity replacement. -/
theorem positive_replacements (offset width : Nat) (positive : 0 < offset) :
    ((SourceFormula.replacements (renamePairs offset width)).filter fun entry => !identityReplacement entry) =
      SourceFormula.replacements (renamePairs offset width) := by
  apply List.filter_eq_self.mpr
  intro entry member
  obtain ⟨pair, present, rfl⟩ := List.mem_map.mp member
  obtain ⟨index, bound, rfl⟩ := List.mem_map.mp present
  have different : integerName index ≠ integerName (offset + index) := by
    intro equal
    have := integerName_injective equal
    omega
  simp [identityReplacement, different]

/-- A zero offset consists only of identity replacements and is removed by the source. -/
theorem zero_replacements (width : Nat) :
    ((SourceFormula.replacements (renamePairs 0 width)).filter fun entry => !identityReplacement entry) = [] := by
  apply List.filter_eq_nil_iff.mpr
  intro entry member
  obtain ⟨pair, present, rfl⟩ := List.mem_map.mp member
  obtain ⟨index, bound, rfl⟩ := List.mem_map.mp present
  simp [identityReplacement]

/-- Each original coordinate reads the corresponding coordinate in its shifted block. -/
theorem renamed_coordinate (model : Interpretation Value) (env : Name → Value)
    (offset width index : Nat) (bound : index < width) :
    SourceFormula.renamedEnvironment model env (renamePairs offset width) (integerName index) =
      env (integerName (offset + index)) := by
  by_cases zero : offset = 0
  · subst offset
    simp [SourceFormula.renamedEnvironment, zero_replacements, FormulaSubstitution.assignment, lookup]
  · have positive : 0 < offset := by omega
    unfold SourceFormula.renamedEnvironment
    rw [positive_replacements offset width positive]
    simp only [SourceFormula.replacements, renamePairs, List.map_map,
      Function.comp_def, FormulaSubstitution.assignment]
    rw [lookup_coordinates]
    simp [bound, evaluateTerm]

/-- A key formula refers only to its declared local coordinate block. -/
def Scoped (width : Nat) (formula : Formula) : Prop :=
  ∀ name ∈ formulaNames formula, ∃ index < width, name = integerName index

/-- Actual capture-avoiding substitution transports a scoped formula to its assigned block. -/
theorem rename_exact (model : Interpretation Value)
    (nullary : ∀ value, model.apply value [] = value)
    (global localEnv : Name → Value) (offset width : Nat) (formula : Formula)
    (within : Scoped width formula)
    (coordinates : ∀ index < width, localEnv (integerName index) = global (integerName (offset + index))) :
    Holds model global (renameFrom offset width formula) ↔ Holds model localEnv formula := by
  rw [renameFrom, SourceFormula.substitute_semantics model nullary]
  apply FormulaSemantics.formula_ext
  intro name member
  obtain ⟨index, bound, rfl⟩ := within name member
  exact (renamed_coordinate model global offset width index bound).trans (coordinates index bound).symm

/-- The source OpenKey fields that affect integer closure. Observations do not affect these operations. -/
structure Key where
  width : Nat
  formula : Formula
  points : Option Nat

/-- The source starts each block at the sum of all preceding widths. -/
def offsets (keys : List Key) : List Nat := (keys.map Key.width).scanl (· + ·) 0

/-- The zip used by `renamedFormulas`; the final scan entry is intentionally unused. -/
def placed (keys : List Key) : List (Nat × Key) := (offsets keys).zip keys

/-- The same zipped offsets with an explicit starting coordinate. -/
def placedFrom (start : Nat) : List Key → List (Nat × Key)
  | [] => []
  | key :: rest => (start, key) :: placedFrom (start + key.width) rest

/-- The source scan and zip execute the sequential block allocation. -/
theorem placedFrom_scan (start : Nat) (keys : List Key) :
    placedFrom start keys = ((keys.map Key.width).scanl (· + ·) start).zip keys := by
  induction keys generalizing start with
  | nil => simp [placedFrom]
  | cons first rest ih => simp [placedFrom, List.scanl_cons, ih]

theorem placed_exact (keys : List Key) : placed keys = placedFrom 0 keys := by
  simp [placed, offsets, placedFrom_scan]

/-- Each block lies entirely inside the allocated interval. -/
theorem placed_bounds (start : Nat) (keys : List Key) (entry : Nat × Key)
    (member : entry ∈ placedFrom start keys) :
    start ≤ entry.1 ∧ entry.1 + entry.2.width ≤ start + (keys.map Key.width).sum := by
  induction keys generalizing start with
  | nil => simp [placedFrom] at member
  | cons first rest ih =>
      simp only [placedFrom, List.mem_cons] at member
      rcases member with rfl | member
      · simp
      · have bound := ih (start + first.width) member
        simp only [List.map_cons, List.sum_cons]
        omega

/-- Source block allocation orders even zero-width keys without overlap. -/
theorem placed_ordered (start : Nat) (keys : List Key) :
    (placedFrom start keys).Pairwise (fun left right => left.1 + left.2.width ≤ right.1) := by
  induction keys generalizing start with
  | nil => simp [placedFrom]
  | cons first rest ih =>
      simp only [placedFrom, List.pairwise_cons]
      exact ⟨fun entry member => (placed_bounds _ rest entry member).1, ih _⟩

/-- Distinct coordinate blocks have distinct source names. -/
theorem block_names_disjoint (left right : Nat × Key) (before : left.1 + left.2.width ≤ right.1)
    (i j : Nat) (leftBound : i < left.2.width) (_rightBound : j < right.2.width) :
    integerName (left.1 + i) ≠ integerName (right.1 + j) := by
  intro same
  have := integerName_injective same
  omega

/-- Source renamed child formulas in the exact child order. -/
def renamedFormulas (keys : List Key) : List Formula :=
  (placed keys).map (fun entry => renameFrom entry.1 entry.2.width entry.2.formula)

/-- The source formula conjunction simplifies each binary fold step. -/
def conjoin (left right : Formula) : Formula := FormulaExecutable.simplify (.and [left, right])

def foldFormulas (formulas : List Formula) : Formula := formulas.foldr conjoin .top

/-- Conjunction simplification retains exactly both operands' meanings. -/
theorem conjoin_exact (model : Interpretation Value) (laws : FormulaSimplify.RelationLaws model)
    (env : Name → Value) (left right : Formula) :
    Holds model env (conjoin left right) ↔ Holds model env left ∧ Holds model env right := by
  rw [conjoin, FormulaExecutable.simplify_semantics model laws]
  simp [Holds, holdsAll]

theorem foldFormulas_exact (model : Interpretation Value) (laws : FormulaSimplify.RelationLaws model)
    (env : Name → Value) (formulas : List Formula) :
    Holds model env (foldFormulas formulas) ↔ ∀ formula ∈ formulas, Holds model env formula := by
  induction formulas with
  | nil => simp [foldFormulas, Holds]
  | cons first rest ih =>
      change Holds model env (conjoin first (foldFormulas rest)) ↔ _
      rw [conjoin_exact model laws, ih]
      simp

/-- The source optional product keeps an unknown count if any child count is unavailable. -/
def productPoints : List Key → Option Nat
  | [] => some 1
  | first :: rest => do
      let count ← first.points
      let remaining ← productPoints rest
      pure (count * remaining)

/-- Source `joinOpenKeys`; group observations are independently cleared by its caller. -/
def join (keys : List Key) : Key :=
  ⟨(keys.map Key.width).sum, foldFormulas (renamedFormulas keys), productPoints keys⟩

/-- Joining keys preserves every renamed child condition, including unbounded ones. -/
theorem join_exact (model : Interpretation Value) (laws : FormulaSimplify.RelationLaws model)
    (nullary : ∀ value, model.apply value [] = value) (env : Name → Value) (keys : List Key) :
    Holds model env (join keys).formula ↔ ∀ entry ∈ placed keys,
      Holds model (SourceFormula.renamedEnvironment model env (renamePairs entry.1 entry.2.width)) entry.2.formula := by
  rw [join, foldFormulas_exact model laws]
  simp only [renamedFormulas, List.forall_mem_map, renameFrom,
    SourceFormula.substitute_semantics model nullary]
  rfl

/-- Scoped keys describe the conjunction of independent coordinate blocks. -/
theorem join_blocks (model : Interpretation Value) (laws : FormulaSimplify.RelationLaws model)
    (nullary : ∀ value, model.apply value [] = value) (global : Name → Value)
    (locals : (Nat × Key) → Name → Value) (keys : List Key)
    (within : ∀ key ∈ keys, Scoped key.width key.formula)
    (coordinates : ∀ entry ∈ placed keys, ∀ index < entry.2.width,
      locals entry (integerName index) = global (integerName (entry.1 + index))) :
    Holds model global (join keys).formula ↔
      ∀ entry ∈ placed keys, Holds model (locals entry) entry.2.formula := by
  rw [join, foldFormulas_exact model laws]
  simp only [renamedFormulas, List.forall_mem_map]
  apply forall_congr'
  intro entry
  apply forall_congr'
  intro member
  have present : entry.2 ∈ keys := by
    exact List.of_mem_zip member |>.2
  exact rename_exact model nullary global (locals entry) entry.1 entry.2.width entry.2.formula
    (within entry.2 present) (coordinates entry member)

/-- Concatenation is injective when every component has its fixed declared width. -/
theorem flatten_injective (left right : List (List Value))
    (widths : left.map List.length = right.map List.length)
    (same : left.flatten = right.flatten) : left = right := by
  induction left generalizing right with
  | nil =>
      cases right with
      | nil => rfl
      | cons first rest => simp at widths
  | cons first rest ih =>
      cases right with
      | nil => simp at widths
      | cons other tail =>
          simp only [List.map_cons, List.cons.injEq] at widths
          have head := congrArg (List.take first.length) same
          have equal : first = other := by simpa [← widths.1] using head
          subst other
          simp only [List.flatten_cons, List.append_cancel_left_eq] at same
          exact congrArg (first :: ·) (ih tail widths.2 same)

/-- Every child tuple has the source width recorded by its corresponding key. -/
theorem product_widths (domains : Key → List (List Value)) (keys : List Key)
    (valid : ∀ key ∈ keys, ∀ tuple ∈ domains key, tuple.length = key.width)
    (blocks : List (List Value)) (member : blocks ∈ Language.products domains keys) :
    blocks.map List.length = keys.map Key.width := by
  induction keys generalizing blocks with
  | nil => simpa [Language.products] using member
  | cons first rest ih =>
      obtain ⟨front, frontMember, tail, tailMember, rfl⟩ :=
        (by simpa [Language.products, List.mem_flatMap, List.mem_map] using member :
          ∃ front ∈ domains first, ∃ tail ∈ Language.products domains rest, front :: tail = blocks)
      simp [valid first (by simp) front frontMember,
        ih (fun key member => valid key (by simp [member])) tail tailMember]

/-- Enumerate each Cartesian tuple by concatenating its consecutive child blocks. -/
def joinedTuples (domains : Key → List (List Value)) (keys : List Key) : List (List Value) :=
  (Language.products domains keys).map List.flatten

/-- The reference concatenation contains every and only the ordered child-domain tuples. -/
theorem joinedTuples_member (domains : Key → List (List Value)) (keys : List Key) (tuple : List Value) :
    tuple ∈ joinedTuples domains keys ↔
      ∃ blocks, Language.All₂ (fun key block => block ∈ domains key) keys blocks ∧ blocks.flatten = tuple := by
  simp [joinedTuples, List.mem_map, Language.mem_products]

/-- Flattening fixed-width blocks cannot create duplicate combined tuples. -/
theorem joinedTuples_nodup (domains : Key → List (List Value)) (keys : List Key)
    (valid : ∀ key ∈ keys, ∀ tuple ∈ domains key, tuple.length = key.width)
    (distinct : ∀ key ∈ keys, (domains key).Nodup) : (joinedTuples domains keys).Nodup := by
  apply List.pairwise_map.mpr
  apply (SymbolicDriver.products_nodup domains keys distinct).imp_of_mem
  intro left right leftMember rightMember different same
  apply different
  exact flatten_injective left right
    ((product_widths domains keys valid left leftMember).trans
      (product_widths domains keys valid right rightMember).symm) same

/-- The combined tuple count is the product of the child domain counts. -/
theorem joinedTuples_count (domains : Key → List (List Value)) (keys : List Key) :
    (joinedTuples domains keys).length = (keys.map (fun key => (domains key).length)).prod := by
  simp only [joinedTuples, List.length_map, SymbolicDriver.products_length]

/-- Exact child counts derive the source optional product metadata. -/
theorem productPoints_exact (domains : Key → List (List Value)) (keys : List Key)
    (counts : ∀ key ∈ keys, key.points = some (domains key).length) :
    productPoints keys = some (joinedTuples domains keys).length := by
  rw [joinedTuples_count]
  induction keys with
  | nil => rfl
  | cons first rest ih =>
      simp only [productPoints, counts first (by simp),
        ih (fun key member => counts key (by simp [member])), List.map_cons, List.prod_cons]
      rfl

/-- An unavailable child count remains unavailable; it is not replaced by zero. -/
theorem productPoints_unknown (keys : List Key) (key : Key) (member : key ∈ keys) (unknown : key.points = none) :
    productPoints keys = none := by
  induction keys with
  | nil => simp at member
  | cons first rest ih =>
      rcases List.mem_cons.mp member with rfl | member
      · simp [productPoints, unknown]
      · simp [productPoints, ih member]

/-- A distinct declaration table maps its actual name at each position back to that position. -/
theorem variableOf_at (names : List Name) (distinct : names.Nodup) (index : Nat) (bound : index < names.length) :
    LatticeInput.variableOf names names[index] = some index := by
  induction names generalizing index with
  | nil => simp at bound
  | cons first rest ih =>
      have unique := List.nodup_cons.mp distinct
      cases index with
      | zero => simp [LatticeInput.variableOf]
      | succ index =>
          have tailBound : index < rest.length := by simpa using bound
          have different : rest[index] ≠ first := by
            intro same
            exact unique.1 (same ▸ List.getElem_mem tailBound)
          simp [LatticeInput.variableOf, different, ih unique.2 index tailBound]

/-- The exact public lattice declaration order for one open coordinate block. -/
def names (width : Nat) : List Name := (List.range width).map integerName

theorem names_distinct (width : Nat) : (names width).Nodup := by
  apply List.pairwise_map.mpr
  exact (List.nodup_range : (List.range width).Nodup).imp (fun different same => different (integerName_injective same))

/-- The actual declaration parser finds every generated coordinate in source order. -/
theorem variableOf_integer (width index : Nat) (bound : index < width) :
    LatticeInput.variableOf (names width) (integerName index) = some index := by
  have found := variableOf_at (names width) (names_distinct width) index (by simpa [names] using bound)
  simpa [names] using found

/-- Use the actual lattice name table to interpret a concrete coordinate tuple. -/
def tupleEnv (tuple : List Int) : Name → Int :=
  LatticeInput.nameValues (names tuple.length) (fun index => tuple[index]?.getD 0)

/-- The tuple environment reads the declared coordinate itself. -/
theorem tupleEnv_at (tuple : List Int) (index : Nat) (bound : index < tuple.length) :
    tupleEnv tuple (integerName index) = tuple[index]?.getD 0 := by
  exact LatticeInput.nameValues_correct _ _ _ _ (variableOf_integer tuple.length index bound)

/-- The coordinate slice assigned to one child by source offset and width. -/
def slice (tuple : List Int) (offset width : Nat) : List Int := (tuple.drop offset).take width

theorem slice_length (tuple : List Int) (offset width : Nat) (bound : offset + width ≤ tuple.length) :
    (slice tuple offset width).length = width := by simp [slice]; omega

/-- Reading a local slice and reading the corresponding global coordinate give the same value. -/
theorem slice_coordinate (tuple : List Int) (offset width index : Nat)
    (allocated : offset + width ≤ tuple.length) (bound : index < width) :
    tupleEnv (slice tuple offset width) (integerName index) = tupleEnv tuple (integerName (offset + index)) := by
  rw [tupleEnv_at _ index (by rw [slice_length tuple offset width allocated]; exact bound),
    tupleEnv_at tuple (offset + index) (by omega)]
  simp [slice, bound, List.getElem?_drop]

/-- The joined source formula is exactly the conjunction of child formulas over their actual tuple slices. -/
theorem join_tuple_exact (model : Interpretation Int) (laws : FormulaSimplify.RelationLaws model)
    (nullary : ∀ value, model.apply value [] = value) (keys : List Key) (tuple : List Int)
    (within : ∀ key ∈ keys, Scoped key.width key.formula)
    (dimension : tuple.length = (join keys).width) :
    Holds model (tupleEnv tuple) (join keys).formula ↔ ∀ entry ∈ placed keys,
      Holds model (tupleEnv (slice tuple entry.1 entry.2.width)) entry.2.formula := by
  apply join_blocks model laws nullary (tupleEnv tuple)
    (fun entry => tupleEnv (slice tuple entry.1 entry.2.width)) keys within
  intro entry member index bound
  have allocated := (placed_bounds 0 keys entry (by simpa [placed_exact] using member)).2
  have fits : entry.1 + entry.2.width ≤ tuple.length := by
    simpa [dimension, join] using allocated
  exact slice_coordinate tuple entry.1 entry.2.width index fits bound

/-- Split a global tuple into the consecutive widths used by the source readers. -/
def cut : List Key → List Int → List (List Int)
  | [], _ => []
  | key :: rest, tuple => tuple.take key.width :: cut rest (tuple.drop key.width)

/-- Splitting a correctly sized tuple loses no coordinate. -/
theorem flatten_cut (keys : List Key) (tuple : List Int)
    (dimension : tuple.length = (keys.map Key.width).sum) : (cut keys tuple).flatten = tuple := by
  induction keys generalizing tuple with
  | nil => simp at dimension; subst tuple; rfl
  | cons first rest ih =>
      simp only [List.map_cons, List.sum_cons] at dimension
      simp only [cut, List.flatten_cons]
      rw [ih (tuple.drop first.width) (by simp; omega)]
      exact List.take_append_drop first.width tuple

/-- Declared widths recover every original block after concatenation. -/
theorem cut_flatten (keys : List Key) (blocks : List (List Int))
    (widths : blocks.map List.length = keys.map Key.width) : cut keys blocks.flatten = blocks := by
  induction keys generalizing blocks with
  | nil => cases blocks <;> simp_all [cut]
  | cons key rest ih =>
      cases blocks with
      | nil => simp at widths
      | cons block tail =>
          simp only [List.map_cons, List.cons.injEq] at widths
          simp [cut, ← widths.1, ih tail widths.2]

/-- The sequential reader split tests precisely the source offset slices. -/
theorem cut_domain_iff (domains : Key → List (List Int)) (keys : List Key) (tuple : List Int) (start : Nat) :
    Language.All₂ (fun key block => block ∈ domains key) keys (cut keys (tuple.drop start)) ↔
      ∀ entry ∈ placedFrom start keys, slice tuple entry.1 entry.2.width ∈ domains entry.2 := by
  induction keys generalizing start with
  | nil => simp [cut, placedFrom]; exact Language.All₂.nil
  | cons first rest ih =>
      constructor
      · intro matching entry member
        cases matching with
        | cons front tail =>
            simp only [placedFrom, List.mem_cons] at member
            rcases member with rfl | member
            · exact front
            · apply (ih (start + first.width)).mp _ entry member
              simpa [List.drop_drop, Nat.add_comm] using tail
      · intro all
        apply Language.All₂.cons (R := fun key block => block ∈ domains key)
          (all (start, first) (by simp [placedFrom]))
        have tail := (ih (start + first.width)).mpr
          (fun entry member => all entry (by simp [placedFrom, member]))
        simpa [List.drop_drop, Nat.add_comm] using tail

/-- Fixed-width Cartesian concatenation recognizes exactly the child-domain slices. -/
theorem joinedTuples_exact (domains : Key → List (List Int)) (keys : List Key)
    (valid : ∀ key ∈ keys, ∀ tuple ∈ domains key, tuple.length = key.width) (tuple : List Int) :
    tuple ∈ joinedTuples domains keys ↔ tuple.length = (keys.map Key.width).sum ∧
      ∀ entry ∈ placed keys, slice tuple entry.1 entry.2.width ∈ domains entry.2 := by
  constructor
  · intro member
    obtain ⟨blocks, matching, rfl⟩ := (joinedTuples_member domains keys tuple).mp member
    have widths := product_widths domains keys valid blocks ((Language.mem_products _ _ _).mpr matching)
    constructor
    · simp [List.length_flatten, widths]
    · rw [placed_exact]
      apply (cut_domain_iff domains keys blocks.flatten 0).mp
      simpa [cut_flatten keys blocks widths] using matching
  · rintro ⟨dimension, all⟩
    apply (joinedTuples_member domains keys tuple).mpr
    refine ⟨cut keys tuple, ?_, flatten_cut keys tuple dimension⟩
    have matching := (cut_domain_iff domains keys tuple 0).mpr (by simpa [placed_exact] using all)
    simpa using matching

/-- Exact finite child domains derive the complete joined formula language. -/
theorem joined_formula_exact (model : Interpretation Int) (laws : FormulaSimplify.RelationLaws model)
    (nullary : ∀ value, model.apply value [] = value) (keys : List Key)
    (within : ∀ key ∈ keys, Scoped key.width key.formula)
    (domains : Key → List (List Int))
    (exactDomains : ∀ key ∈ keys, ∀ tuple, tuple ∈ domains key ↔
      tuple.length = key.width ∧ Holds model (tupleEnv tuple) key.formula) (tuple : List Int) :
    tuple ∈ joinedTuples domains keys ↔
      tuple.length = (join keys).width ∧ Holds model (tupleEnv tuple) (join keys).formula := by
  have valid : ∀ key ∈ keys, ∀ point ∈ domains key, point.length = key.width :=
    fun key member point found => ((exactDomains key member point).mp found).1
  rw [joinedTuples_exact domains keys valid tuple]
  constructor
  · rintro ⟨dimension, all⟩
    refine ⟨dimension, (join_tuple_exact model laws nullary keys tuple within dimension).mpr ?_⟩
    intro entry member
    exact ((exactDomains entry.2 (List.of_mem_zip member).2 _).mp (all entry member)).2
  · rintro ⟨dimension, admitted⟩
    refine ⟨dimension, ?_⟩
    have all := (join_tuple_exact model laws nullary keys tuple within dimension).mp admitted
    intro entry member
    apply (exactDomains entry.2 (List.of_mem_zip member).2 _).mpr
    have allocated := (placed_bounds 0 keys entry (by simpa [placed_exact] using member)).2
    exact ⟨slice_length tuple entry.1 entry.2.width (by simpa [dimension, join] using allocated), all entry member⟩

/-- Correct child records yield distinct joined tuples, the exact formula language, and the source product count. -/
theorem join_finite_exact (model : Interpretation Int) (laws : FormulaSimplify.RelationLaws model)
    (nullary : ∀ value, model.apply value [] = value) (keys : List Key)
    (within : ∀ key ∈ keys, Scoped key.width key.formula)
    (domains : Key → List (List Int))
    (exactDomains : ∀ key ∈ keys, ∀ tuple, tuple ∈ domains key ↔
      tuple.length = key.width ∧ Holds model (tupleEnv tuple) key.formula)
    (distinct : ∀ key ∈ keys, (domains key).Nodup)
    (counts : ∀ key ∈ keys, key.points = some (domains key).length) :
    (joinedTuples domains keys).Nodup ∧
      (join keys).points = some (joinedTuples domains keys).length ∧
      ∀ tuple, tuple ∈ joinedTuples domains keys ↔
        tuple.length = (join keys).width ∧ Holds model (tupleEnv tuple) (join keys).formula := by
  exact ⟨joinedTuples_nodup domains keys
      (fun key member tuple found => ((exactDomains key member tuple).mp found).1) distinct,
    productPoints_exact domains keys counts,
    joined_formula_exact model laws nullary keys within domains exactDomains⟩

end MicroCFTA.OpenIntegerKeys
