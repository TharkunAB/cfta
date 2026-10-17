import MicroCFTA.SourceCurrentConjunctionTupleBounds
import MicroCFTA.SourceCurrentConjunctionRequirementNumeric

/-!
# Initial numeric allocation of one conjunction tuple

The original tuple and finite guard alphabet bound its equality classes.
Contradiction retains the original heap and the actual returned operation
cache. Live tuples enter requirements with that same operation cache.
-/
namespace MicroCFTA.SourceCurrentConjunctionTupleNumeric
open InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Edges)
open MergedColdReaderClosedInputs (ClosedEdges)
open SourceCurrentMemoMergeResourceControl (Fits)
open SourceCurrentConjunctionTupleBounds (shapeThrough)
namespace Alloc
export SourceCurrentConjunctionRowsAllocation (State Ready Effects OptionalReady Tuple)
end Alloc
variable {Symbol Formula : Type}
local notation "Guard" => SourceSymbolicIndex.Constraint Formula

/-- The initial tuple shape bounds the returned heap and every literal worklist width. -/
noncomputable def forecast (alphabet : List Guard) (count width resource : Nat) : Nat :=
  let shape := shapeThrough alphabet count
  max (SourceCurrentConjunctionRequirementResources.forecast shape width count shape resource)
    (max (width + shape) (count + count * shape))

/-- The tuple forecast retains the initial heap scalar. -/
theorem forecast_ge (alphabet : List Guard) (count width resource : Nat) :
    resource ≤ forecast alphabet count width resource :=
  Nat.le_trans (SourceCurrentConjunctionRequirementResources.forecast_ge _ _ _ _ _) (Nat.le_max_left _ _)

/-- Increasing the initial heap scalar retains the same original tuple forecast. -/
theorem forecast_mono (alphabet : List Guard) (count width : Nat) {first last : Nat} (increase : first ≤ last) :
    forecast alphabet count width first ≤ forecast alphabet count width last :=
  Nat.max_le_max (SourceCurrentConjunctionRequirementResources.forecast_mono _ _ _ _ increase) (Nat.le_refl _)

/-- Contradiction has no row; a live row retains its complete original shape bounds. -/
def OptionalBounds (shape width count : Nat) : Option (List (List (Value Symbol Guard))) → Prop
  | none => True
  | some rows => rows.length ≤ width + shape ∧ ∀ row ∈ rows, row.length ≤ count + count * shape

private theorem guard_bounds (alphabet : List Guard) (count : Nat) (tuple : List (EdgeValue Symbol Guard))
    (tupleCount : tuple.length ≤ count) (carrier : ∀ edge ∈ tuple, edge.entry.key.constraint ∈ alphabet)
    (classes : EqualityNormalize.Constraints)
    (live : SourceCurrentConjunctionEmptinessRows.combined (tuple.map SourceCurrentConjunctionEquality.edgeView) = some classes) :
    classes.length ≤ shapeThrough alphabet count ∧
      (∀ paths ∈ classes, paths.length ≤ shapeThrough alphabet count) ∧
      ∀ paths ∈ classes, ∀ path ∈ paths, path.length ≤ shapeThrough alphabet count := by
  have own := SourceCurrentConjunctionTupleBounds.combined_bounds alphabet tuple.length
    (tuple.map (fun edge => edge.entry.key.constraint)) (by simp only [List.length_map])
    (by
      intro guard member
      obtain ⟨edge, included, rfl⟩ := List.mem_map.mp member
      exact carrier edge included) classes ((SourceCurrentConjunctionTupleBounds.combined_edgeView tuple).trans live)
  have enough := SourceCurrentConjunctionTupleBounds.classShapeBound_le_shapeThrough alphabet tuple.length count tupleCount
  exact ⟨Nat.le_trans own.1 enough, fun paths member => Nat.le_trans (own.2.1 paths member) enough,
    fun paths member path present => Nat.le_trans (own.2.2 paths member path present) enough⟩

private theorem arity_le (tuple : List (EdgeValue Symbol Guard)) (width : Nat)
    (widths : ∀ edge ∈ tuple, edge.children.length ≤ width) :
    SourceCurrentConjunctionRequirements.arity tuple ≤ width := by
  cases tuple with
  | nil => simp [SourceCurrentConjunctionRequirements.arity]
  | cons first rest => exact widths first List.mem_cons_self

variable [DecidableEq (EdgeKey Symbol (SourceSymbolicIndex.Constraint Formula))]

/-- Initial tuple fields bound the actual allocated branch and replay its exact full state. -/
theorem bound {tuple : List (EdgeValue Symbol Guard)} {before after : Alloc.State Symbol Formula}
    {output : Option (List (List (Value Symbol Guard)))} (actual : Alloc.Tuple tuple before output after)
    (alphabet : List Guard) (count width resource : Nat) (ready : Alloc.Ready before)
    (resident : Edges before.heap tuple) (closed : ClosedEdges tuple) (fits : Fits resource before.heap)
    (tupleCount : tuple.length ≤ count) (widths : ∀ edge ∈ tuple, edge.children.length ≤ width)
    (carrier : ∀ edge ∈ tuple, edge.entry.key.constraint ∈ alphabet) :
    Alloc.Effects before after ∧ Alloc.OptionalReady after output ∧
      Fits (forecast alphabet count width resource) after.heap ∧
      OptionalBounds (shapeThrough alphabet count) width count output ∧
      ∀ work reader, SourceCurrentConjunctionProjectionResources.workerFuel (shapeThrough alphabet count) ≤ work →
        SourceCurrentProjectionUnionResources.readFuel (forecast alphabet count width resource) ≤ reader →
        SourceCurrentConjunctionRowsWorker.tuple work reader tuple before = .done output after := by
  have physical := actual.verified ready resident closed
  obtain ⟨observed, observedFold, _valid, _ready, observedClasses, _built, _growth, _fields⟩ :=
    SourceCurrentConjunctionEquality.fold_heap_correct tuple before.heap before.equality ready.valid ready.fields resident
  cases actual with
  | contradiction folded empty =>
      refine ⟨physical.1, physical.2, fits.mono (forecast_ge alphabet count width resource), trivial, ?_⟩
      intro work reader _ _
      simp only [SourceCurrentConjunctionRowsWorker.tuple, folded, empty]
  | live folded classes requirements =>
      have same := Option.some.inj (Except.ok.inj (observedFold.symm.trans folded))
      cases same
      have combined := observedClasses.symm.trans classes
      have shape := guard_bounds alphabet count tuple tupleCount carrier _ combined
      have numeric := SourceCurrentConjunctionRequirementNumeric.bound requirements (shapeThrough alphabet count) width count resource
        ready.semantic ready.costs resident closed fits tupleCount widths (arity_le tuple width widths)
        shape.1 shape.2.1 shape.2.2
      refine ⟨physical.1, physical.2, numeric.1.mono (Nat.le_max_left _ _), numeric.2.1, numeric.2.2.1, ?_⟩
      intro work reader enoughWork enoughRead
      have done := numeric.2.2.2 (SourceCurrentConjunctionEquality.fold tuple before.equality).2 work reader enoughWork
        (Nat.le_trans (SourceCurrentProjectionUnionResources.readFuel_mono (Nat.le_max_left _ _)) enoughRead)
      simp only [SourceCurrentConjunctionRowsWorker.tuple, folded, classes, done,
        SourceCurrentConjunctionRowsWorker.Outcome.bind]

/-- Initial resident closed tuple data constructs its own numeric allocation and worker return. -/
theorem complete (tuple : List (EdgeValue Symbol Guard)) (before : Alloc.State Symbol Formula)
    (alphabet : List Guard) (count width resource : Nat) (ready : Alloc.Ready before)
    (resident : Edges before.heap tuple) (closed : ClosedEdges tuple)
    (sameArity : SourceCurrentConjunctionRequirements.SameArity tuple) (fits : Fits resource before.heap)
    (tupleCount : tuple.length ≤ count) (widths : ∀ edge ∈ tuple, edge.children.length ≤ width)
    (carrier : ∀ edge ∈ tuple, edge.entry.key.constraint ∈ alphabet) :
    ∃ output after, ∃ actual : Alloc.Tuple tuple before output after,
      Alloc.Effects before after ∧ Alloc.OptionalReady after output ∧
      Fits (forecast alphabet count width resource) after.heap ∧
      OptionalBounds (shapeThrough alphabet count) width count output ∧
      ∀ work reader, SourceCurrentConjunctionProjectionResources.workerFuel (shapeThrough alphabet count) ≤ work →
        SourceCurrentProjectionUnionResources.readFuel (forecast alphabet count width resource) ≤ reader →
        SourceCurrentConjunctionRowsWorker.tuple work reader tuple before = .done output after := by
  obtain ⟨output, after, actual, _effects, _ready⟩ :=
    SourceCurrentConjunctionRowsAllocation.tuple_complete tuple before ready resident closed sameArity
  exact ⟨output, after, actual, bound actual alphabet count width resource ready resident closed fits tupleCount widths carrier⟩

end MicroCFTA.SourceCurrentConjunctionTupleNumeric
