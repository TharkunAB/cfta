import MicroCFTA.RecursiveCallbackTables
import MicroCFTA.RecursiveTermAlignment
import MicroCFTA.RecursiveSourceUnfolding

/-!
# Recursive callbacks and the independently compiled term index

The callback's count and leaf selector fields are built from finite source
classes. The whole recursive term table comes from the typed forward
compiler. Its source unfolding equation supplies the recursive boundary.
-/
namespace MicroCFTA.RecursiveCallbackAlignment
open Language GeneratorCombinators IntegerTermViews SizedRank
open RecursiveCallbackTermination RecursiveCallbackTables

/-- Finite forward derivations replay through the complete source class table. -/
theorem selects_lookup (environment : Nat → List (EngineTerm Symbol)) (self : Nat → Nat)
    (rootCounts : ∀ size, (environment size).length = self size) (body : Recipe Symbol)
    (rootEquation : ∀ size, environment size =
      (classTerms environment body size).map (fun term => Term.node Label.recursion [term]))
    (bodyIndexed : LeavesIndexed body) (recipe : Recipe Symbol) (position : Position) (term : EngineTerm Symbol)
    (selected : Selects self body recipe position term) (indexed : LeavesIndexed recipe) :
    (classTerms environment recipe position.size)[position.rank]? = some term := by
  induction selected with
  | finite source position term found => exact (finite_lookup source indexed position term).mpr found
  | occurrence position term child ih =>
      simp only [classTerms, rootEquation, List.getElem?_map, ih bodyIndexed, Option.map_some]
  | map inner position term child ih => exact ih indexed
  | pay inner position term child ih => exact ih indexed
  | left left right position term child ih =>
      have found := ih indexed.1
      have within := (List.getElem?_eq_some_iff.mp found).1
      simp only [classTerms]
      rw [List.getElem?_append_left (by simpa using within)]
      simp [List.getElem?_map, found]
  | right left right position term child ih =>
      have found := ih indexed.2
      simp only [RecursiveCheckedRanks.choiceRow, choicePosition]
      simp only [classTerms]
      rw [List.getElem?_append_right (by
        simp [class_length environment self rootCounts])]
      simp [List.getElem?_map, class_length environment self rootCounts, found]
  | ap functions arguments first second function argument left right ihf iha =>
      exact product_replay environment self rootCounts functions arguments first second function argument
        (ihf indexed.1) (iha indexed.2)
  | label symbol inner position term child ih =>
      simp only [classTerms, List.getElem?_map, ih indexed, Option.map_some]

/-- The source supplies each finite leaf's existing callback separately from its forward fields. -/
abbrev LeafCallbacks (Symbol : Type) :=
  {Value : Type} → FiniteSource.Source (Value × EngineTerm Symbol) → Callback Symbol

/-- Build the exact finite count and selector fields read by staticTerms. -/
def finite (callbacks : LeafCallbacks Symbol) (source : FiniteSource.Source (Value × EngineTerm Symbol)) : Finite Symbol :=
  ⟨fun size => (FiniteSource.classMembers source size).length,
    fun position => ((FiniteSource.classMembers source position.size).map Prod.snd)[position.rank]?,
    callbacks source⟩

theorem finite_indexed (callbacks : LeafCallbacks Symbol)
    (source : FiniteSource.Source (Value × EngineTerm Symbol)) : FiniteIndex (finite callbacks source) := by
  intro position
  constructor
  · rintro ⟨term, found⟩
    exact by simpa [finite] using (List.getElem?_eq_some_iff.mp found).1
  · intro within
    have bounded : position.rank < ((FiniteSource.classMembers source position.size).map Prod.snd).length := by
      simpa [finite] using within
    exact ⟨_, List.getElem?_eq_getElem bounded⟩

/-- Finite leaf tabulation recovers the original ordered terms without changing ranks. -/
theorem finite_class (callbacks : LeafCallbacks Symbol)
    (source : FiniteSource.Source (Value × EngineTerm Symbol)) (size : Nat) :
    finiteClass (finite callbacks source) size = (FiniteSource.classMembers source size).map Prod.snd := by
  apply List.ext_getElem?
  intro rank
  cases found : ((FiniteSource.classMembers source size).map Prod.snd)[rank]? with
  | some term => exact (finite_lookup _ (finite_indexed callbacks source) ⟨size, rank⟩ term).mpr found
  | none =>
      cases read : (finiteClass (finite callbacks source) size)[rank]? with
      | none => rfl
      | some term =>
          have impossible := (finite_lookup _ (finite_indexed callbacks source) ⟨size, rank⟩ term).mp read
          change ((FiniteSource.classMembers source size).map Prod.snd)[rank]? = some term at impossible
          rw [found] at impossible
          cases impossible

/-- Erase value computations while keeping every actual term callback constructor. -/
def compile (callbacks : LeafCallbacks Symbol) : RecursiveTermAlignment.Recipe Root Symbol Value → Recipe Symbol
  | .finite source => .finite (finite callbacks source)
  | .occurrence => .occurrence
  | .map _ inner => .map (compile callbacks inner)
  | .pay inner => .pay (compile callbacks inner)
  | .choice left right => .choice (compile callbacks left) (compile callbacks right)
  | .ap functions arguments => .ap (compile callbacks functions) (compile callbacks arguments)
  | .label symbol inner => .label symbol (compile callbacks inner)

/-- All count/selector obligations follow from the finite leaf constructors. -/
theorem compiled_indexed (callbacks : LeafCallbacks Symbol) (recipe : RecursiveTermAlignment.Recipe Root Symbol Value) :
    LeavesIndexed (compile callbacks recipe) := by
  induction recipe with
  | finite source => exact finite_indexed callbacks source
  | occurrence => trivial
  | map transform inner ih | pay inner ih | label symbol inner ih => exact ih
  | choice left right ihl ihr | ap left right ihl ihr => exact ⟨ihl, ihr⟩

/-- Callback tables are the typed term compiler's ordered body classes. -/
theorem compiled_classes (callbacks : LeafCallbacks Symbol) (recipe : RecursiveTermAlignment.Recipe Root Symbol Value)
    (environment : Nat → List (EngineTerm Symbol)) (size : Nat) :
    classTerms environment (compile callbacks recipe) size =
      RecursiveSource.values (RecursiveTermAlignment.termRecipe recipe) environment size := by
  induction recipe generalizing size with
  | finite source => exact finite_class callbacks source size
  | occurrence => rfl
  | map transform inner ih => exact ih size
  | pay inner ih | label symbol inner ih =>
      cases size <;> simp [compile, classTerms, RecursiveTermAlignment.termRecipe, RecursiveSource.values, ih]
  | choice left right ihl ihr =>
      simp [compile, classTerms, RecursiveTermAlignment.termRecipe, RecursiveSource.values, ihl, ihr]
  | ap functions arguments ihf iha =>
      simp [compile, classTerms, RecursiveTermAlignment.termRecipe, RecursiveSource.values, ihf, iha]

/-- The independently constructed recursive term classes used by public inspection. -/
def environment (body : RecursiveTermAlignment.Recipe Root Symbol Root) : Nat → List (EngineTerm Symbol) :=
  RecursiveSource.languageClass (RecursiveTermAlignment.termBody body)

/-- The actual value guard also accepts the independently compiled term knot. -/
theorem term_guard (body : RecursiveTermAlignment.Recipe Root Symbol Root)
    (accepted : RecursiveSource.guarded (RecursiveTermAlignment.valueRecipe body)
      (RecursiveSource.assumption (RecursiveTermAlignment.valueRecipe body)) = true) :
    RecursiveSource.guarded (RecursiveTermAlignment.termBody body)
      (RecursiveSource.assumption (RecursiveTermAlignment.termBody body)) = true := by
  have minimum : RecursiveSource.minimumExpr (RecursiveTermAlignment.termBody body) =
      RecursiveSource.minimumExpr (RecursiveTermAlignment.valueRecipe body) := (RecursiveTermAlignment.minimum_expressions body).2
  have assumption : RecursiveSource.assumption (RecursiveTermAlignment.termBody body) =
      RecursiveSource.assumption (RecursiveTermAlignment.valueRecipe body) := by
    simp only [RecursiveSource.assumption, minimum]
  change RecursiveSource.guarded (RecursiveTermAlignment.termRecipe body)
    (RecursiveSource.assumption (RecursiveTermAlignment.termBody body)) = true
  rw [assumption, (RecursiveTermAlignment.body_guards body _).2]
  exact accepted

/-- The callback knot equation is derived from the source guard and ordered unfolding. -/
theorem root_equation (callbacks : LeafCallbacks Symbol) (body : RecursiveTermAlignment.Recipe Root Symbol Root)
    (accepted : RecursiveSource.guarded (RecursiveTermAlignment.valueRecipe body)
      (RecursiveSource.assumption (RecursiveTermAlignment.valueRecipe body)) = true) (size : Nat) :
    environment body size = (classTerms (environment body) (compile callbacks body) size).map
      (fun term => Term.node Label.recursion [term]) := by
  rw [compiled_classes]
  exact RecursiveSourceUnfolding.languageClass_unfold _ (term_guard body accepted) size

end MicroCFTA.RecursiveCallbackAlignment
