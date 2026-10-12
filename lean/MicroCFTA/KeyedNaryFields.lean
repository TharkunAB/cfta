import MicroCFTA.KeyedNaryAlignment
import MicroCFTA.RecursiveNaryCausality

/-!
# Source callback fields of typed mutually recursive key bodies

Each occurrence reads the requested key's own count, selector, and callback.
Retained finite masses do not change term positions or leaf callbacks.
-/
namespace MicroCFTA.KeyedNaryFields
open Language GeneratorCombinators IntegerTermViews SizedRank
open RecursiveCallbackTermination RecursiveCallbackTables RecursiveCallbackDistinct
open RecursiveFieldBounds
abbrev Body := KeyedNaryAlignment.Recipe
abbrev LeafCallbacks := RecursiveCallbackAlignment.LeafCallbacks

/-- The callback compiler preserves each keyed source operation and finite leaf. -/
def compile [DecidableEq Symbol] (callbacks : LeafCallbacks Symbol) (roots : Key → Finite Symbol) :
    Body Key Root Symbol Value → Finite Symbol
  | .finite source | .retained _ _ source => RecursiveCallbackAlignment.finite callbacks source
  | .occurrence key => roots key
  | .map _ inner => compile callbacks roots inner
  | .pay inner => RecursiveFieldCombinators.pay (compile callbacks roots inner)
  | .choice _ branches => RecursiveNaryChoice.field (List.ofFn fun index => compile callbacks roots (branches index))
  | .ap functions arguments => RecursiveFieldCombinators.ap (compile callbacks roots functions) (compile callbacks roots arguments)
  | .label symbol inner => RecursiveFieldCombinators.label symbol (compile callbacks roots inner)

/-- Every assembled per-key field has its complete declared class interval. -/
theorem compiled_indexed [DecidableEq Symbol] (callbacks : LeafCallbacks Symbol)
    (roots : Key → Finite Symbol) (indexedRoots : ∀ key, FiniteIndex (roots key))
    (recipe : Body Key Root Symbol Value) : FiniteIndex (compile callbacks roots recipe) := by
  induction recipe with
  | finite source | retained mass positive source => exact RecursiveCallbackAlignment.finite_indexed callbacks source
  | occurrence key => exact indexedRoots key
  | map transform inner ih => exact ih
  | pay inner ih | label symbol inner ih | ap functions arguments ihf iha =>
      exact RecursiveFieldCombinators.field_indexed _
  | choice count branches ih =>
      apply RecursiveNaryChoice.field_indexed
      intro child present
      obtain ⟨index, rfl⟩ := List.mem_ofFn.mp present
      exact ih index

/-- Every per-key callback table has the independent term compiler's complete order. -/
theorem compiled_classes [DecidableEq Symbol] (callbacks : LeafCallbacks Symbol)
    (roots : Key → Finite Symbol) (indexedRoots : ∀ key, FiniteIndex (roots key))
    (recipe : Body Key Root Symbol Value) (size : Nat) :
    finiteClass (compile callbacks roots recipe) size =
      KeyedSource.values (KeyedNaryAlignment.termRecipe recipe) (fun key => finiteClass (roots key)) size := by
  induction recipe generalizing size with
  | finite source | retained mass positive source => exact RecursiveCallbackAlignment.finite_class callbacks source size
  | occurrence key => rfl
  | map transform inner ih => exact ih size
  | pay inner ih =>
      simp only [compile, RecursiveFieldCombinators.pay, RecursiveNaryFields.local_class]
      cases size <;> simp [classTerms, KeyedNaryAlignment.termRecipe, KeyedSource.values, ih]
  | label symbol inner ih =>
      simp only [compile, RecursiveFieldCombinators.label, RecursiveNaryFields.local_class]
      cases size <;> simp [classTerms, KeyedNaryAlignment.termRecipe, KeyedSource.values, ih]
  | ap functions arguments ihf iha =>
      simp only [compile, RecursiveFieldCombinators.ap, RecursiveNaryFields.local_class, classTerms,
        KeyedNaryAlignment.termRecipe, KeyedSource.values, ihf, iha]
  | choice count branches ih =>
      rw [compile, RecursiveNaryFields.choice_class _ (by
        intro child present
        obtain ⟨index, rfl⟩ := List.mem_ofFn.mp present
        exact compiled_indexed callbacks roots indexedRoots (branches index))]
      rw [RecursiveNaryChoice.classTerms, RecursiveNaryChoice.groups, KeyedNaryAlignment.choice_terms]
      congr 1
      apply List.ext_getElem?
      intro rank
      by_cases within : rank < count
      · simp [within, ih, RecursiveNaryChoice.wrap, KeyedNaryAlignment.branchTerm]
      · simp [within]

/-- Each finite or retained source supplies only its own leaf inverse law. -/
def LeavesExact (callbacks : LeafCallbacks Symbol) : Body Key Root Symbol Value → Prop
  | .finite source | .retained _ _ source => FiniteExact (RecursiveCallbackAlignment.finite callbacks source)
  | .occurrence _ => True
  | .map _ inner | .pay inner | .label _ inner => LeavesExact callbacks inner
  | .choice _ branches => ∀ index, LeavesExact callbacks (branches index)
  | .ap left right => LeavesExact callbacks left ∧ LeavesExact callbacks right

/-- All finite candidate flags remain inside their local class interval. -/
def LeavesBounded (callbacks : LeafCallbacks Symbol) : Body Key Root Symbol Value → Prop
  | .finite source | .retained _ _ source => RecursiveNaryChoice.Bounded (RecursiveCallbackAlignment.finite callbacks source)
  | .occurrence _ => True
  | .map _ inner | .pay inner | .label _ inner => LeavesBounded callbacks inner
  | .choice _ branches => ∀ index, LeavesBounded callbacks (branches index)
  | .ap left right => LeavesBounded callbacks left ∧ LeavesBounded callbacks right

/-- Every finite callback preserves checked-row order. -/
def LeavesOrdered (callbacks : LeafCallbacks Symbol) : Body Key Root Symbol Value → Prop
  | .finite source | .retained _ _ source => ∀ view wanted,
      ((RecursiveCallbackAlignment.finite callbacks source).positions view wanted).Pairwise (fun a b => before a b)
  | .occurrence _ => True
  | .map _ inner | .pay inner | .label _ inner => LeavesOrdered callbacks inner
  | .choice _ branches => ∀ index, LeavesOrdered callbacks (branches index)
  | .ap left right => LeavesOrdered callbacks left ∧ LeavesOrdered callbacks right

/-- Every finite callback preserves distinct positions before replay filtering. -/
def LeavesDistinct (callbacks : LeafCallbacks Symbol) : Body Key Root Symbol Value → Prop
  | .finite source | .retained _ _ source => RecursiveNaryChoice.Unique (RecursiveCallbackAlignment.finite callbacks source)
  | .occurrence _ => True
  | .map _ inner | .pay inner | .label _ inner => LeavesDistinct callbacks inner
  | .choice _ branches => ∀ index, LeavesDistinct callbacks (branches index)
  | .ap left right => LeavesDistinct callbacks left ∧ LeavesDistinct callbacks right

/-- Each keyed body needs root inverse laws only below the requested forest height. -/
theorem compiled_exact_below [DecidableEq Symbol] (callbacks : LeafCallbacks Symbol)
    (roots : Key → Finite Symbol) (indexedRoots : ∀ key, FiniteIndex (roots key))
    (limit : Nat) (exactRoots : ∀ key, ExactBelow limit (roots key))
    (recipe : Body Key Root Symbol Value) (leaves : LeavesExact callbacks recipe) :
    ExactBelow limit (compile callbacks roots recipe) := by
  induction recipe with
  | finite source | retained mass positive source => intro view wanted _; exact leaves view wanted
  | occurrence key => exact exactRoots key
  | map transform inner ih => exact ih leaves
  | pay inner ih | label symbol inner ih =>
      apply RecursiveFieldBounds.field_exact_below
      · exact ih leaves
      · exact compiled_indexed callbacks roots indexedRoots inner
  | ap functions arguments ihf iha =>
      apply RecursiveFieldBounds.field_exact_below
      · exact ⟨ihf leaves.1, iha leaves.2⟩
      · exact ⟨compiled_indexed callbacks roots indexedRoots functions, compiled_indexed callbacks roots indexedRoots arguments⟩
  | choice count branches ih =>
      apply RecursiveNaryFieldBounds.field_exact_below
      · intro child present
        obtain ⟨index, rfl⟩ := List.mem_ofFn.mp present
        exact compiled_indexed callbacks roots indexedRoots (branches index)
      · intro child present
        obtain ⟨index, rfl⟩ := List.mem_ofFn.mp present
        exact ih index (leaves index)

/-- Every keyed operation retains all candidate bounds. -/
theorem compiled_bounded [DecidableEq Symbol] (callbacks : LeafCallbacks Symbol) (roots : Key → Finite Symbol)
    (rootBounded : ∀ key, RecursiveNaryChoice.Bounded (roots key)) (recipe : Body Key Root Symbol Value)
    (leaves : LeavesBounded callbacks recipe) : RecursiveNaryChoice.Bounded (compile callbacks roots recipe) := by
  induction recipe with
  | finite source | retained mass positive source => exact leaves
  | occurrence key => exact rootBounded key
  | map transform inner ih => exact ih leaves
  | pay inner ih | label symbol inner ih => exact RecursiveFieldCombinators.field_bounded _ (ih leaves)
  | ap functions arguments ihf iha => exact RecursiveFieldCombinators.field_bounded _ ⟨ihf leaves.1, iha leaves.2⟩
  | choice count branches ih =>
      apply RecursiveNaryChoice.field_bounded
      intro child present
      obtain ⟨index, rfl⟩ := List.mem_ofFn.mp present
      exact ih index (leaves index)

/-- Every keyed operation retains source candidate order. -/
theorem compiled_ordered [DecidableEq Symbol] (callbacks : LeafCallbacks Symbol) (roots : Key → Finite Symbol)
    (rootOrdered : ∀ key view wanted, ((roots key).positions view wanted).Pairwise (fun a b => before a b))
    (recipe : Body Key Root Symbol Value) (leaves : LeavesOrdered callbacks recipe) :
    ∀ view wanted, ((compile callbacks roots recipe).positions view wanted).Pairwise (fun a b => before a b) := by
  induction recipe with
  | finite source | retained mass positive source => exact leaves
  | occurrence key => exact rootOrdered key
  | map transform inner ih => exact ih leaves
  | pay inner ih | label symbol inner ih => exact RecursiveFieldCombinators.field_ordered _ (ih leaves)
  | ap functions arguments ihf iha => exact RecursiveFieldCombinators.field_ordered _ ⟨ihf leaves.1, iha leaves.2⟩
  | choice count branches ih => exact RecursiveNaryChoice.positions_ordered _

/-- Every keyed operation retains distinct valid candidate positions. -/
theorem compiled_distinct [DecidableEq Symbol] (callbacks : LeafCallbacks Symbol) (roots : Key → Finite Symbol)
    (rootBounded : ∀ key, RecursiveNaryChoice.Bounded (roots key)) (rootDistinct : ∀ key, RecursiveNaryChoice.Unique (roots key))
    (recipe : Body Key Root Symbol Value) (bounded : LeavesBounded callbacks recipe)
    (distinct : LeavesDistinct callbacks recipe) : RecursiveNaryChoice.Unique (compile callbacks roots recipe) := by
  induction recipe with
  | finite source | retained mass positive source => exact distinct
  | occurrence key => exact rootDistinct key
  | map transform inner ih => exact ih bounded distinct
  | pay inner ih | label symbol inner ih =>
      exact RecursiveFieldCombinators.field_distinct _ (compiled_bounded callbacks roots rootBounded inner bounded) (ih bounded distinct)
  | ap functions arguments ihf iha =>
      exact RecursiveFieldCombinators.field_distinct _
        ⟨compiled_bounded callbacks roots rootBounded functions bounded.1,
          compiled_bounded callbacks roots rootBounded arguments bounded.2⟩
        ⟨ihf bounded.1 distinct.1, iha bounded.2 distinct.2⟩
  | choice count branches ih =>
      apply RecursiveNaryChoice.field_unique
      · intro child present
        obtain ⟨index, rfl⟩ := List.mem_ofFn.mp present
        exact compiled_bounded callbacks roots rootBounded (branches index) (bounded index)
      · intro child present
        obtain ⟨index, rfl⟩ := List.mem_ofFn.mp present
        exact ih index (bounded index) (distinct index)

/-- A body never requests a recursive forest taller than its input forest. -/
theorem compiled_agree [DecidableEq Symbol] (callbacks : LeafCallbacks Symbol) (left right : Key → Finite Symbol)
    (same : ∀ key, RecursiveNaryCausality.Agree limit (left key) (right key))
    (recipe : Body Key Root Symbol Value) :
    RecursiveNaryCausality.Agree limit (compile callbacks left recipe) (compile callbacks right recipe) := by
  induction recipe with
  | finite source | retained mass positive source => exact ⟨rfl, fun _ _ _ => rfl⟩
  | occurrence key => exact same key
  | map transform inner ih => exact ih
  | pay inner ih => exact RecursiveNaryCausality.local_fields (.pay (.finite _ _ ih))
  | label symbol inner ih => exact RecursiveNaryCausality.local_fields (.label symbol (.finite _ _ ih))
  | ap functions arguments ihf iha => exact RecursiveNaryCausality.local_fields (.ap (.finite _ _ ihf) (.finite _ _ iha))
  | choice count branches ih =>
      apply RecursiveNaryCausality.choice_fields
      have related : ∀ indexes : List (Fin count), RecursiveRankMass.Related (RecursiveNaryCausality.Agree limit)
          (indexes.map fun index => compile callbacks left (branches index))
          (indexes.map fun index => compile callbacks right (branches index)) := by
        intro indexes
        induction indexes with
        | nil => exact .nil
        | cons index rest tail => exact .cons (ih index) tail
      simpa only [List.map_ofFn, Function.comp_def, id_eq] using related (List.ofFn id)

end MicroCFTA.KeyedNaryFields
