import MicroCFTA.FiniteLeafForestProgress

/-!
# Leaf-forest progress with multiple constructor symbols

The source self-intersection shortcut compares whole nodes. Equal rows at
one symbol do not trigger the shortcut when another symbol differs. All
other cases use Cartesian row products independently at each symbol.
-/
namespace MicroCFTA.FiniteLeafSymbolsProgress
open FiniteRowIntersection
open FiniteLeafForestProgress (Improves improves_refl improves_trans)

/-- Cartesian products improve even when one symbol column equals its other operand. -/
theorem product_improves (algebra : Conjunction Row) (inventory : List Row) (complete : ∀ row, row ∈ inventory)
    (left right : Rows Row) : Improves algebra inventory (product algebra left right) left := by
  classical
  by_cases same : product algebra left right = left
  · exact Or.inl same
  · apply Or.inr
    have progress := product_progress algebra inventory complete left right same
    have bounded : (measure algebra inventory (product algebra left right)).2 ≤ inventory.length := Nat.sub_le _ _
    rcases Prod.lex_def.mp progress with smaller | ⟨equal, smaller⟩
    · have multiplied := Nat.mul_le_mul_right (inventory.length + 1) (Nat.succ_le_of_lt smaller)
      rw [Nat.succ_mul] at multiplied
      simp only [FiniteLeafForestProgress.potential]
      omega
    · simp only [FiniteLeafForestProgress.potential]
      rw [equal]
      omega

/-- One leaf node keeps its distinct alternatives separately at each constructor symbol. -/
abbrev Node (Row : Type) (symbols : Nat) := Fin symbols → Rows Row

/-- EmptyNode has no alternative at any symbol. -/
def empty : Node Row symbols := fun _ _ => False

/-- Source intersection uses one whole-node identity shortcut. -/
noncomputable def intersect (algebra : Conjunction Row) (left right : Node Row symbols) : Node Row symbols := by
  classical
  exact if left = right then left else fun symbol => product algebra (left symbol) (right symbol)

/-- Each symbol column improves under the exact whole-node shortcut. -/
theorem intersect_improves (algebra : Conjunction Row) (inventory : List Row) (complete : ∀ row, row ∈ inventory)
    (left right : Node Row symbols) (symbol : Fin symbols) :
    Improves algebra inventory (intersect algebra left right symbol) (left symbol) := by
  unfold intersect
  split
  · exact improves_refl algebra inventory _
  · exact product_improves algebra inventory complete _ _

/-- Source operand order does not affect node intersection. -/
theorem intersect_comm (algebra : Conjunction Row) (left right : Node Row symbols) :
    intersect algebra left right = intersect algebra right left := by
  classical
  by_cases same : left = right
  · subst right; rfl
  · simp only [intersect, same, Ne.symm same, ↓reduceIte]
    funext symbol row
    apply propext
    constructor <;> rintro ⟨a, b, presentA, presentB, result⟩
    · exact ⟨b, a, presentB, presentA, (algebra.comm b a).trans result⟩
    · exact ⟨b, a, presentB, presentA, (algebra.comm b a).trans result⟩

/-- The source projection fold keeps its first operand as the seed. -/
noncomputable def intersectList (algebra : Conjunction Row) : List (Node Row symbols) → Node Row symbols
  | [] => empty
  | first :: rest => rest.foldr (intersect algebra) first

/-- Child positions and constructor symbols are separate finite coordinates. -/
abbrev Forest (Row : Type) (arity symbols : Nat) := Fin arity → Node Row symbols

/-- Every selected child reads all other projections from the same old forest. -/
noncomputable def reduceClass (algebra : Conjunction Row) (paths : List (Fin arity))
    (before : Forest Row arity symbols) : Forest Row arity symbols := by
  classical
  exact fun index => if index ∈ paths then
    intersect algebra (intersectList algebra ((paths.filter (· != index)).map before)) (before index)
    else before index

/-- Simultaneous edits improve each child and symbol coordinate. -/
theorem class_improves (algebra : Conjunction Row) (inventory : List Row) (complete : ∀ row, row ∈ inventory)
    (paths : List (Fin arity)) (before : Forest Row arity symbols) (index : Fin arity) (symbol : Fin symbols) :
    Improves algebra inventory (reduceClass algebra paths before index symbol) (before index symbol) := by
  unfold reduceClass
  split
  · rw [intersect_comm]
    exact intersect_improves algebra inventory complete _ _ _
  · exact improves_refl algebra inventory _

/-- The complete equality class schedule retains the source right-fold order. -/
noncomputable def schedule (algebra : Conjunction Row) (classes : List (List (Fin arity)))
    (before : Forest Row arity symbols) : Forest Row arity symbols := classes.foldr (reduceClass algebra) before

/-- Class composition cannot reverse any coordinate's progress. -/
theorem schedule_improves (algebra : Conjunction Row) (inventory : List Row) (complete : ∀ row, row ∈ inventory)
    (classes : List (List (Fin arity))) (before : Forest Row arity symbols) (index : Fin arity) (symbol : Fin symbols) :
    Improves algebra inventory (schedule algebra classes before index symbol) (before index symbol) := by
  induction classes with
  | nil => exact improves_refl algebra inventory _
  | cons paths rest ih =>
      exact improves_trans algebra inventory _ _ _ ih (class_improves algebra inventory complete paths _ index symbol)

/-- A source node is empty only when all its constructor columns are empty. -/
noncomputable def propagate (before : Forest Row arity symbols) : Forest Row arity symbols := by
  classical
  exact if ∃ index, before index = empty then fun _ => empty else before

/-- Whole-node empty propagation preserves every coordinate's progress. -/
theorem propagate_improves (algebra : Conjunction Row) (inventory : List Row) (complete : ∀ row, row ∈ inventory)
    (before : Forest Row arity symbols) (index : Fin arity) (symbol : Fin symbols) :
    Improves algebra inventory (propagate before index symbol) (before index symbol) := by
  unfold propagate
  split
  · exact FiniteLeafForestProgress.empty_improves algebra inventory complete _
  · exact improves_refl algebra inventory _

/-- A complete direct-child leaf pass preserves the source branch order. -/
noncomputable def pass (algebra : Conjunction Row) (skip contradiction : Bool)
    (classes : List (List (Fin arity))) (before : Forest Row arity symbols) : Forest Row arity symbols :=
  if skip then before else if contradiction then fun _ => empty else propagate (schedule algebra classes before)

/-- Every source pass improves each child-symbol coordinate independently. -/
theorem pass_improves (algebra : Conjunction Row) (inventory : List Row) (complete : ∀ row, row ∈ inventory)
    (skip contradiction : Bool) (classes : List (List (Fin arity))) (before : Forest Row arity symbols)
    (index : Fin arity) (symbol : Fin symbols) :
    Improves algebra inventory (pass algebra skip contradiction classes before index symbol) (before index symbol) := by
  cases skip <;> cases contradiction
  · exact improves_trans algebra inventory _ _ _ (schedule_improves algebra inventory complete classes before index symbol)
      (propagate_improves algebra inventory complete _ index symbol)
  · exact FiniteLeafForestProgress.empty_improves algebra inventory complete _
  · exact improves_refl algebra inventory _
  · exact improves_refl algebra inventory _

/-- Enumerate the whole finite child-symbol coordinate set. -/
def positions (arity symbols : Nat) : List (Fin arity × Fin symbols) :=
  (List.ofFn id).flatMap fun index => (List.ofFn id).map fun symbol => (index, symbol)

/-- Every coordinate occurs in the generated inventory. -/
theorem positions_complete (index : Fin arity) (symbol : Fin symbols) : (index, symbol) ∈ positions arity symbols := by
  simp [positions]

/-- Sum the already proved leaf potential over all child-symbol coordinates. -/
noncomputable def potential (algebra : Conjunction Row) (inventory : List Row) (forest : Forest Row arity symbols) : Nat :=
  ((positions arity symbols).map (fun position => FiniteLeafForestProgress.potential algebra inventory (forest position.1 position.2))).sum

/-- Every changing complete pass strictly decreases this finite sum. -/
theorem pass_strict (algebra : Conjunction Row) (inventory : List Row) (complete : ∀ row, row ∈ inventory)
    (skip contradiction : Bool) (classes : List (List (Fin arity))) (before : Forest Row arity symbols)
    (changed : pass algebra skip contradiction classes before ≠ before) :
    potential algebra inventory (pass algebra skip contradiction classes before) < potential algebra inventory before := by
  have summed := FiniteLeafForestProgress.sum_progress algebra inventory (positions arity symbols)
    (fun position => before position.1 position.2) (fun position => pass algebra skip contradiction classes before position.1 position.2)
    (fun position _ => pass_improves algebra inventory complete skip contradiction classes before position.1 position.2)
  apply Nat.lt_of_le_of_ne summed.1
  intro equal
  apply changed
  funext index symbol
  exact summed.2 equal (index, symbol) (positions_complete index symbol)

/-- Bounded execution follows the source structural fixed-point test. -/
noncomputable def run (algebra : Conjunction Row) (skip contradiction : Bool)
    (classes : List (List (Fin arity))) : Nat → Forest Row arity symbols → Option (Forest Row arity symbols)
  | 0, _ => none
  | fuel + 1, before => by
      classical
      exact let after := pass algebra skip contradiction classes before
        if after = before then some before else run algebra skip contradiction classes fuel after

/-- Every multi-symbol leaf schedule terminates within its derived potential bound. -/
theorem run_terminates (algebra : Conjunction Row) (inventory : List Row) (complete : ∀ row, row ∈ inventory)
    (skip contradiction : Bool) (classes : List (List (Fin arity))) (before : Forest Row arity symbols) :
    ∃ fuel after, run algebra skip contradiction classes fuel before = some after ∧
      pass algebra skip contradiction classes after = after ∧ fuel ≤ potential algebra inventory before + 1 := by
  classical
  let after := pass algebra skip contradiction classes before
  by_cases same : after = before
  · exact ⟨1, before, by simp [run, after] at same ⊢; exact same, same, by omega⟩
  · obtain ⟨fuel, final, finished, fixed, bounded⟩ := run_terminates algebra inventory complete skip contradiction classes after
    have smaller := pass_strict algebra inventory complete skip contradiction classes before same
    exact ⟨fuel + 1, final, by simpa only [run, show pass algebra skip contradiction classes before = after from rfl,
      same, ↓reduceIte] using finished, fixed, by change potential algebra inventory after < _ at smaller; omega⟩
termination_by potential algebra inventory before
decreasing_by exact pass_strict algebra inventory complete skip contradiction classes before same

/-- The actual canonical guard inventory removes any supplied finiteness or row-law premise. -/
theorem source_terminates (initial : List (SourceGuards.Guard FullSyntax.Formula))
    (skip contradiction : Bool) (classes : List (List (Fin arity)))
    (before : Forest (SourceLeafRowProgress.Row initial) arity symbols) :
    ∃ fuel after, run (SourceLeafRowProgress.algebra initial) skip contradiction classes fuel before = some after ∧
      pass (SourceLeafRowProgress.algebra initial) skip contradiction classes after = after ∧
      fuel ≤ potential (SourceLeafRowProgress.algebra initial) (SourceLeafRowProgress.inventory initial) before + 1 :=
  run_terminates (SourceLeafRowProgress.algebra initial) (SourceLeafRowProgress.inventory initial)
    (SourceLeafRowProgress.inventory_complete initial) skip contradiction classes before

end MicroCFTA.FiniteLeafSymbolsProgress
