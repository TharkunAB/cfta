import MicroCFTA.MergedProjectionTermination
import MicroCFTA.EqualityLeafProjectionProperPaths

/-!
# Runtime bounds for normalized merged projected-leaf constraints

Completed source equality normalization supplies proper paths. Actual
finite occurrence compilation supplies the initial complete runtime cache.
The original occurrence potential plus one bounds the repeated passes.
-/
namespace MicroCFTA.MergedProjectionBound
open InternedConstructorTemplates InternedRecordCoherence
open EqualityLeafProjectionCompileAvailability EqualityLeafProjectionRepresentation
open EqualityLeafProjectionSyntax (Tree Endpoints forestWeight)
open EqualityLeafProjectionCompile (Tag)
open EqualityRawLeafInventory (Leaf rank)
open EqualityRawLeafConstruction (ConstraintKey)
open EqualityRawLeafCompiler (build)
open MergedProjectionPass (sourcePass)
open MergedProjectionTermination (iterate)

noncomputable local instance : DecidableEq ConstraintKey := by classical exact inferInstance

/-- Normalized source classes derive every nonempty path needed by physical projection. -/
theorem proper_flatten (fuel : Nat) (input output selected : EqualityNormalize.Constraints)
    (normalized : EqualityNormalize.mkEqConstraints fuel input = .normalized output)
    (members : ∀ paths ∈ selected, paths ∈ output) : ∀ path ∈ selected.flatten, path ≠ [] := by
  intro path member
  obtain ⟨paths, selectedMember, pathMember⟩ := List.mem_flatten.mp member
  exact EqualityLeafProjectionProperPaths.selected_proper fuel input output selected normalized members paths selectedMember path pathMember

/-- A normalized fixed schedule reaches an actual physical fixed point within the original potential plus one. -/
theorem represented_bound (order : Value (Fin symbols) ConstraintKey → List (Fin symbols))
    (complete : MergedProjectionTargets.CompleteOrder order) (fuel : Nat) (input output selected : EqualityNormalize.Constraints)
    (normalized : EqualityNormalize.mkEqConstraints fuel input = .normalized output)
    (members : ∀ paths ∈ selected, paths ∈ output) (skip contradiction : Bool)
    (forest : List (Tree (Tag (Fin symbols) ConstraintKey) (Leaf initial symbols)))
    (endpoints : Endpoints selected.flatten forest)
    (state : State (Fin symbols) ConstraintKey) (facts : Facts state)
    (values : List (Value (Fin symbols) ConstraintKey)) (represented : RepresentsForest build forest state values) :
    let actual := run (iterate order skip contradiction selected (forestWeight rank forest + 1) values) state
    Facts actual.2 ∧ ∃ results trimmed, actual.1 = some results ∧ RepresentsForest build trimmed actual.2 results ∧
      Endpoints selected.flatten trimmed ∧ EqualityLeafProjectionSyntax.Progress (forestWeight rank) trimmed forest ∧
      run (sourcePass order skip contradiction selected results) actual.2 = (some results, actual.2) :=
  MergedProjectionTermination.iterate_completes order complete skip contradiction selected (forestWeight rank forest + 1)
    forest (proper_flatten fuel input output selected normalized members) endpoints state facts values represented (by omega)

/-- Actual finite occurrence construction derives the complete initial representation for the runtime bound. -/
theorem compiled_bound (order : Value (Fin symbols) ConstraintKey → List (Fin symbols))
    (complete : MergedProjectionTargets.CompleteOrder order) (fuel : Nat) (input output selected : EqualityNormalize.Constraints)
    (normalized : EqualityNormalize.mkEqConstraints fuel input = .normalized output)
    (members : ∀ paths ∈ selected, paths ∈ output) (skip contradiction : Bool)
    (forest : List (Tree (Tag (Fin symbols) ConstraintKey) (Leaf initial symbols)))
    (endpoints : Endpoints selected.flatten forest)
    (state : State (Fin symbols) ConstraintKey) (facts : Facts state) :
    let compiled := run (EqualityLeafProjectionCompile.compileForest build forest) state
    let actual := run (iterate order skip contradiction selected (forestWeight rank forest + 1) compiled.1) compiled.2
    Facts actual.2 ∧ ∃ results trimmed, actual.1 = some results ∧ RepresentsForest build trimmed actual.2 results ∧
      Endpoints selected.flatten trimmed ∧ EqualityLeafProjectionSyntax.Progress (forestWeight rank) trimmed forest ∧
      run (sourcePass order skip contradiction selected results) actual.2 = (some results, actual.2) := by
  let compiled := run (EqualityLeafProjectionCompile.compileForest build forest) state
  have compiledFacts := compileForest_available build EqualityRawLeafCompiler.leaves_available forest state facts
  have represented : RepresentsForest build forest compiled.2 compiled.1 :=
    replay (EqualityLeafProjectionCompile.compileForest build forest) state compiled.2 facts.coherent.valid (grows_refl compiled.2)
  exact represented_bound order complete fuel input output selected normalized members skip contradiction forest endpoints
    compiled.2 compiledFacts.1 compiled.1 represented

end MicroCFTA.MergedProjectionBound
