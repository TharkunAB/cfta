import MicroCFTA.EqualityLeafProjectionPathWorker

/-!
# Exact empty and nullary projection cases

The empty finite predicate constructs literal EmptyNode without requests.
Every proper projection through a physical nullary leaf also returns that
literal value without allocation. These are source path-worker base cases.
-/
namespace MicroCFTA.EqualityRawLeafEmpty
open InternedConstructorTemplates InternedRecordCoherence InternedEdgeResidency
open EqualityLeafProjectionCompileAvailability EqualityLeafProjectionRepresentation
open EqualityRawLeafInventory (Leaf)
open EqualityRawLeafConstruction (ConstraintKey)
open EqualityLeafProjectionPathWorker

noncomputable local instance : DecidableEq ConstraintKey := by classical exact inferInstance

/-- The empty finite raw predicate contains no constructor alternative. -/
def zero : Leaf initial symbols := fun _ _ => False

/-- The generated finite inventory contributes no selected row to the empty predicate. -/
theorem choices_zero : EqualityRawLeafInventory.choices (zero (initial := initial) (symbols := symbols)) = [] := by
  classical
  simp only [EqualityRawLeafInventory.choices, List.flatMap_eq_nil_iff, List.map_eq_nil_iff, List.filter_eq_nil_iff]
  intro symbol _ row _ positive
  exact @of_decide_eq_true (zero symbol row) (Classical.propDecidable _) positive

/-- The empty finite predicate issues no physical source constructor request. -/
theorem build_zero : EqualityRawLeafCompiler.build (zero (initial := initial) (symbols := symbols)) = .pure .empty := by
  simp [EqualityRawLeafCompiler.build, EqualityRawLeafInventory.rawChoices, choices_zero,
    EqualityRawLeafConstruction.declarations, EqualityRawLeafConstruction.build, EqualityRawLeafConstruction.requests,
    EqualityLeafProjectionWorkers.sequence, Work.bind, makeNode, surviving, canonicalEdges, EnumerationBuilderCaches.canonicalIds]

/-- The finite zero represents EmptyNode in every current cache. -/
theorem zero_represents (state : State (Fin symbols) ConstraintKey) :
    Represents EqualityRawLeafCompiler.build (.leaf (zero (initial := initial))) state .empty := by
  simp only [Represents, EqualityLeafProjectionCompile.compile, build_zero, run]

/-- Projection through the literal empty node has no source effects. -/
theorem read_empty (path : EqualityLeafProjectionSyntax.Path) :
    read path (Value.empty : Value Symbol Guard) = .pure (some .empty) := by
  cases path <;> rfl

/-- Every nullary source row lacks the selected child and issues no recursive projection. -/
theorem rows_nullary (project : Value Symbol Guard → Work Symbol Guard (Option (Value Symbol Guard)))
    (index : Nat) (edges : List (EdgeValue Symbol Guard))
    (nullary : ∀ edge ∈ edges, edge.children = []) : rows project index edges = .pure (some []) := by
  induction edges with
  | nil => rfl
  | cons edge rest ih =>
      simp only [rows, nullary edge (by simp), List.getElem?_nil]
      exact ih (fun value member => nullary value (by simp [member]))

/-- Actual proper projection from any ordinary nullary value is allocation-free EmptyNode. -/
theorem read_nullary (index : Nat) (path : EqualityLeafProjectionSyntax.Path) (value : Value Symbol Guard)
    (ordinary : EqualityLeafProjectionUnion.OrdinaryRoot value)
    (nullary : ∀ edge ∈ nodeEdges value, edge.children = []) : read (index :: path) value = .pure (some .empty) := by
  cases value with
  | empty => rfl
  | node entry edges depth free =>
      simp only [EqualityLeafProjectionPathWorker.read, rows_nullary (read path) index edges nullary]
      simp [EqualityLeafProjectionWorkers.bindOptional, Work.bind, EqualityOrdinaryUnionSource.sourceUnion,
        makeNode, canonicalEdges, surviving, EnumerationBuilderCaches.canonicalIds]
  | reference | union | mu => cases ordinary

/-- The actual raw leaf builder derives both shape premises of proper path projection. -/
theorem read_built (leaf : Leaf initial symbols) (state : State (Fin symbols) ConstraintKey) (facts : Facts state)
    (index : Nat) (path : EqualityLeafProjectionSyntax.Path) :
    read (index :: path) (run (EqualityRawLeafCompiler.build leaf) state).1 = .pure (some .empty) :=
  read_nullary index path _
    (EqualityRawLeafAvailability.built_root _ state facts)
    (EqualityRawLeafAvailability.built_nullary (EqualityRawLeafInventory.rawChoices leaf) state facts)

/-- Every represented finite raw leaf satisfies the exact source projection base case. -/
theorem read_represented (leaf : Leaf initial symbols) (state : State (Fin symbols) ConstraintKey) (facts : Facts state)
    (value : Value (Fin symbols) ConstraintKey) (represented : Represents EqualityRawLeafCompiler.build (.leaf leaf) state value)
    (index : Nat) (path : EqualityLeafProjectionSyntax.Path) : read (index :: path) value = .pure (some .empty) := by
  have checked := read_built leaf state facts index path
  have exactInput : run (EqualityRawLeafCompiler.build leaf) state = (value, state) := represented
  simpa only [exactInput] using checked

end MicroCFTA.EqualityRawLeafEmpty
