import MicroCFTA.RecursiveNaryFieldBounds
import MicroCFTA.RecursiveNarySource

/-!
# Typed n-ary bodies as local source callback fields

The compiler inserts arbitrary recursive fields at occurrences. Its counts
and selectors agree with the independent ordered term classes. Its inverse
contract can be restricted to the height of the current request.
-/
namespace MicroCFTA.RecursiveNaryFields
open Language GeneratorCombinators IntegerTermViews SizedRank
open RecursiveCallbackTermination RecursiveCallbackTables
open RecursiveFieldBounds
abbrev Body := RecursiveNaryBody.Recipe
abbrev LeafCallbacks := RecursiveCallbackAlignment.LeafCallbacks

/-- Each source operation combines actual child callback fields. -/
def compile [DecidableEq Symbol] (callbacks : LeafCallbacks Symbol) (root : Finite Symbol) :
    Body Root Symbol Value → Finite Symbol
  | .finite source => RecursiveCallbackAlignment.finite callbacks source
  | .occurrence => root
  | .map _ inner => compile callbacks root inner
  | .pay inner => RecursiveFieldCombinators.pay (compile callbacks root inner)
  | .choice _ branches => RecursiveNaryChoice.field (List.ofFn fun index => compile callbacks root (branches index))
  | .ap functions arguments => RecursiveFieldCombinators.ap (compile callbacks root functions) (compile callbacks root arguments)
  | .label symbol inner => RecursiveFieldCombinators.label symbol (compile callbacks root inner)

/-- All assembled fields retain their complete source class interval. -/
theorem compiled_indexed [DecidableEq Symbol] (callbacks : LeafCallbacks Symbol)
    (root : Finite Symbol) (indexedRoot : FiniteIndex root) (recipe : Body Root Symbol Value) :
    FiniteIndex (compile callbacks root recipe) := by
  induction recipe with
  | finite source => exact RecursiveCallbackAlignment.finite_indexed callbacks source
  | occurrence => exact indexedRoot
  | map transform inner ih => exact ih
  | pay inner ih | label symbol inner ih | ap functions arguments ihf iha =>
      exact RecursiveFieldCombinators.field_indexed _
  | choice count branches ih =>
      apply RecursiveNaryChoice.field_indexed
      intro child present
      obtain ⟨index, rfl⟩ := List.mem_ofFn.mp present
      exact ih index

/-- The generic local selector returns exactly its tabulated source class. -/
theorem local_class [DecidableEq Symbol] (recipe : Recipe Symbol) (size : Nat) :
    finiteClass (RecursiveFieldCombinators.field recipe) size = classTerms (fun _ => []) recipe size := by
  apply List.ext_getElem?
  intro rank
  apply Option.ext
  intro term
  exact finite_lookup _ (RecursiveFieldCombinators.field_indexed recipe) ⟨size, rank⟩ term

/-- The local arbitrary-choice selector returns its flat source term class. -/
theorem choice_class (children : List (Finite Symbol))
    (indexed : ∀ child ∈ children, FiniteIndex child) (size : Nat) :
    finiteClass (RecursiveNaryChoice.field children) size = RecursiveNaryChoice.classTerms children size := by
  apply List.ext_getElem?
  intro rank
  apply Option.ext
  intro term
  rw [finite_lookup _ (RecursiveNaryChoice.field_indexed children indexed) ⟨size, rank⟩ term]
  change RecursiveNaryChoice.select children ⟨size, rank⟩ = some term ↔ _
  rw [RecursiveNaryChoice.select_table children indexed]

/-- Callback field classes retain the typed term compiler's complete order. -/
theorem compiled_classes [DecidableEq Symbol] (callbacks : LeafCallbacks Symbol)
    (root : Finite Symbol) (indexedRoot : FiniteIndex root)
    (recipe : Body Root Symbol Value) (size : Nat) :
    finiteClass (compile callbacks root recipe) size =
      RecursiveSource.values (RecursiveNaryBody.termRecipe recipe) (finiteClass root) size := by
  induction recipe generalizing size with
  | finite source => exact RecursiveCallbackAlignment.finite_class callbacks source size
  | occurrence => rfl
  | map transform inner ih => exact ih size
  | pay inner ih =>
      simp only [compile, RecursiveFieldCombinators.pay, local_class]
      cases size <;> simp [classTerms, RecursiveNaryBody.termRecipe, RecursiveSource.values, ih]
  | label symbol inner ih =>
      simp only [compile, RecursiveFieldCombinators.label, local_class]
      cases size <;> simp [classTerms, RecursiveNaryBody.termRecipe, RecursiveSource.values, ih]
  | ap functions arguments ihf iha =>
      simp only [compile, RecursiveFieldCombinators.ap, local_class, classTerms,
        RecursiveNaryBody.termRecipe, RecursiveSource.values, ihf, iha]
  | choice count branches ih =>
      rw [compile, choice_class _ (by
        intro child present
        obtain ⟨index, rfl⟩ := List.mem_ofFn.mp present
        exact compiled_indexed callbacks root indexedRoot (branches index))]
      rw [RecursiveNaryChoice.classTerms, RecursiveNaryChoice.groups, RecursiveNaryBody.choice_terms]
      congr 1
      apply List.ext_getElem?
      intro rank
      by_cases within : rank < count
      · simp [within, ih, RecursiveNaryChoice.wrap, RecursiveNaryBody.wrap]
      · simp [within]

/-- Finite leaves expose only their own local callback contracts. -/
def LeavesExact [DecidableEq Symbol] (callbacks : LeafCallbacks Symbol) : Body Root Symbol Value → Prop
  | .finite source => FiniteExact (RecursiveCallbackAlignment.finite callbacks source)
  | .occurrence => True
  | .map _ inner | .pay inner | .label _ inner => LeavesExact callbacks inner
  | .choice _ branches => ∀ index, LeavesExact callbacks (branches index)
  | .ap functions arguments => LeavesExact callbacks functions ∧ LeavesExact callbacks arguments

/-- Height-limited root correctness is sufficient for every n-ary body operation. -/
theorem compiled_exact_below [DecidableEq Symbol] (callbacks : LeafCallbacks Symbol)
    (root : Finite Symbol) (indexedRoot : FiniteIndex root) (limit : Nat) (exactRoot : ExactBelow limit root)
    (recipe : Body Root Symbol Value) (leaves : LeavesExact callbacks recipe) :
    ExactBelow limit (compile callbacks root recipe) := by
  induction recipe with
  | finite source => intro view wanted _; exact leaves view wanted
  | occurrence => exact exactRoot
  | map transform inner ih => exact ih leaves
  | pay inner ih | label symbol inner ih =>
      apply RecursiveFieldBounds.field_exact_below
      · exact ih leaves
      · exact compiled_indexed callbacks root indexedRoot inner
  | ap functions arguments ihf iha =>
      apply RecursiveFieldBounds.field_exact_below
      · exact ⟨ihf leaves.1, iha leaves.2⟩
      · exact ⟨compiled_indexed callbacks root indexedRoot functions, compiled_indexed callbacks root indexedRoot arguments⟩
  | choice count branches ih =>
      apply RecursiveNaryFieldBounds.field_exact_below
      · intro child present
        obtain ⟨index, rfl⟩ := List.mem_ofFn.mp present
        exact compiled_indexed callbacks root indexedRoot (branches index)
      · intro child present
        obtain ⟨index, rfl⟩ := List.mem_ofFn.mp present
        exact ih index (leaves index)

end MicroCFTA.RecursiveNaryFields
