import MicroCFTA.RecursiveNaryFields

/-!
# Complete bounded-request inverse for n-ary recursive bodies

Each recursive request consumes one private root. A forest-height bound
therefore suffices for all inverse calls. Source counts and selectors are
constructed independently from the typed value and term indexes.
-/
namespace MicroCFTA.RecursiveNaryInverse
open Language GeneratorCombinators IntegerTermViews SizedRank
open RecursiveCallbackTermination RecursiveCallbackTables RecursiveNaryFields
open RecursiveFieldBounds
open RecursiveNaryBody (valueRecipe termBody term_guard)

/-- The source uses value-index counts at each recursive size. -/
def rootCounts (body : Body Root Symbol Root) (size : Nat) : Nat :=
  Decoder.count (RecursiveSource.family (valueRecipe body) size).plan

/-- The source selects constructor terms through its independent term index. -/
def rootSelect (body : Body Root Symbol Root) (position : Position) : Option (EngineTerm Symbol) :=
  Decoder.decode (RecursiveSource.family (termBody body) position.size).plan position.rank

/-- Counts and selectors are fixed before a recursive callback is attached. -/
def rootField (body : Body Root Symbol Root) (callback : Callback Symbol) : Finite Symbol :=
  ⟨rootCounts body, rootSelect body, callback⟩

/-- Every recursive field has exactly the interval of its independent value count. -/
theorem root_indexed (body : Body Root Symbol Root) (callback : Callback Symbol) :
    FiniteIndex (rootField body callback) := by
  intro position
  change (∃ term, rootSelect body position = some term) ↔ position.rank < rootCounts body position.size
  rw [rootCounts, RecursiveNaryBody.class_counts]
  constructor
  · rintro ⟨term, selected⟩
    exact SamplerReplay.decoded_bound _ _ _ selected
  · intro within
    exact Decoder.decode_exists _ _ within

/-- The recursive field table is the actual independently built term class. -/
theorem root_class (body : Body Root Symbol Root) (callback : Callback Symbol) (size : Nat) :
    finiteClass (rootField body callback) size = RecursiveSource.languageClass (termBody body) size := by
  apply List.ext_getElem?
  intro rank
  apply Option.ext
  intro term
  rw [finite_lookup _ (root_indexed body callback) ⟨size, rank⟩ term]
  simp only [rootField, rootSelect, Decoder.decode_correct, RecursiveSource.family_values]

/-- A field selector is the complete class lookup when its index is total. -/
theorem select_class (source : Finite Symbol) (indexed : FiniteIndex source) (position : Position) :
    source.select position = (finiteClass source position.size)[position.rank]? := by
  apply Option.ext
  intro term
  exact (finite_lookup source indexed position term).symm

/-- The n-ary body selector satisfies the root equation with its own source counts. -/
theorem selector_knot [DecidableEq Symbol] (callbacks : LeafCallbacks Symbol)
    (body : Body Root Symbol Root)
    (accepted : RecursiveSource.guarded (valueRecipe body) (RecursiveSource.assumption (valueRecipe body)) = true)
    (callback : Callback Symbol) (position : Position) :
    rootSelect body position = ((compile callbacks (rootField body callback) body).select position).map
      (fun term => .node .recursion [term]) := by
  rw [select_class _ (compiled_indexed callbacks _ (root_indexed body callback) body),
    compiled_classes callbacks _ (root_indexed body callback) body position.size]
  rw [show finiteClass (rootField body callback) = RecursiveSource.languageClass (termBody body) from
    funext (root_class body callback)]
  rw [rootSelect, Decoder.decode_correct, RecursiveSource.family_values,
    RecursiveSourceUnfolding.languageClass_unfold (termBody body) (term_guard body accepted)]
  simp only [termBody, RecursiveSource.values, List.getElem?_map]

/-- Every view of a private recursive root retains that complete root. -/
theorem project_root (view : View) (term : EngineTerm Symbol) :
    project view (.node .recursion [term]) = [.node .recursion [term]] := by
  cases view <;> simp [project, labelled, spine, SupportTerms.applicationLeftChildren, SupportTerms.applicationTermChildren]

/-- Requests enter the body only through one complete private recursive root. -/
def unwrap : List (EngineTerm Symbol) → Option (EngineTerm Symbol)
  | [.node .recursion [term]] => some term
  | _ => none

theorem unwrap_some (wanted : List (EngineTerm Symbol)) (term : EngineTerm Symbol) :
    unwrap wanted = some term ↔ wanted = [.node .recursion [term]] := by
  unfold unwrap
  split
  · simp_all
  · rename_i absent
    constructor
    · simp
    · intro same
      subst wanted
      exact False.elim (absent term rfl)

/-- Fuel decreases once for each private recursive root in the request. -/
def fuelPositions [DecidableEq Symbol] (callbacks : LeafCallbacks Symbol) (body : Body Root Symbol Root) :
    Nat → Callback Symbol
  | 0 => fun _ _ => []
  | fuel + 1 => fun _ wanted => match unwrap wanted with
      | none => []
      | some child => (compile callbacks (rootField body (fuelPositions callbacks body fuel)) body).positions .whole [child]

/-- The requested forest height supplies enough fuel for every complete inverse match. -/
theorem fuel_exact [DecidableEq Symbol] (callbacks : LeafCallbacks Symbol) (body : Body Root Symbol Root)
    (accepted : RecursiveSource.guarded (valueRecipe body) (RecursiveSource.assumption (valueRecipe body)) = true)
    (leaves : RecursiveNaryFields.LeavesExact callbacks body) (fuel : Nat) :
    ExactBelow fuel (rootField body (fuelPositions callbacks body fuel)) := by
  induction fuel with
  | zero =>
      intro view wanted bound position
      constructor
      · simp [rootField, fuelPositions]
      · rintro ⟨term, selected, projected⟩
        rw [show (rootField body (fuelPositions callbacks body 0)).select position = rootSelect body position from rfl,
          selector_knot callbacks body accepted (fuelPositions callbacks body 0) position] at selected
        obtain ⟨child, _, rfl⟩ := Option.map_eq_some_iff.mp selected
        rw [← projected, project_root] at bound
        simp [forestHeight, Term.height] at bound
  | succ fuel ih =>
      intro view wanted bound position
      have exactBody := compiled_exact_below callbacks _ (root_indexed body _) fuel ih body leaves
      have equation := selector_knot callbacks body accepted (fuelPositions callbacks body fuel) position
      cases found : unwrap wanted with
      | none =>
          constructor
          · simp [rootField, fuelPositions, found]
          · rintro ⟨term, selected, projected⟩
            change rootSelect body position = some term at selected
            rw [equation] at selected
            obtain ⟨child, _, rfl⟩ := Option.map_eq_some_iff.mp selected
            have same : wanted = [.node .recursion [child]] := projected.symm.trans (project_root view child)
            have present := (unwrap_some wanted child).mpr same
            rw [found] at present
            contradiction
      | some child =>
          have same := (unwrap_some wanted child).mp found
          subst wanted
          have small : forestHeight ([child] : List (EngineTerm Symbol)) ≤ fuel := by
            simp_all [forestHeight, Term.height]
          change (position, true) ∈ fuelPositions callbacks body (fuel + 1) view [.node .recursion [child]] ↔ _
          change (position, true) ∈ (compile callbacks (rootField body (fuelPositions callbacks body fuel)) body).positions .whole [child] ↔ _
          rw [exactBody .whole [child] small position]
          change (∃ term, _ ∧ project .whole term = [child]) ↔
            ∃ term, rootSelect body position = some term ∧ project view term = [.node .recursion [child]]
          rw [equation]
          constructor
          · rintro ⟨term, selected, same⟩
            have childEq := StaticCheckedRanks.whole_eq term child same
            subst term
            exact ⟨.node .recursion [child], by simp [selected], project_root view child⟩
          · rintro ⟨term, selected, same⟩
            obtain ⟨inner, childSelected, termEq⟩ := Option.map_eq_some_iff.mp selected
            rw [← termEq] at same
            have childEq : inner = child := by
              simpa only [project_root, List.cons.injEq, Term.node.injEq, and_true, true_and] using same
            exact ⟨inner, childSelected, by simp only [project, childEq]⟩

/-- The inverse uses only the finite requested forest to select its recursion bound. -/
def positions [DecidableEq Symbol] (callbacks : LeafCallbacks Symbol) (body : Body Root Symbol Root) : Callback Symbol :=
  fun view wanted => fuelPositions callbacks body (forestHeight wanted) view wanted

/-- Every complete source term position is returned, and every true certificate replays. -/
theorem positions_exact [DecidableEq Symbol] (callbacks : LeafCallbacks Symbol) (body : Body Root Symbol Root)
    (accepted : RecursiveSource.guarded (valueRecipe body) (RecursiveSource.assumption (valueRecipe body)) = true)
    (leaves : RecursiveNaryFields.LeavesExact callbacks body) (view : View) (wanted : List (EngineTerm Symbol))
    (position : Position) :
    (position, true) ∈ positions callbacks body view wanted ↔
      ∃ term, rootSelect body position = some term ∧ project view term = wanted :=
  fuel_exact callbacks body accepted leaves (forestHeight wanted) view wanted (Nat.le_refl _) position

end MicroCFTA.RecursiveNaryInverse
