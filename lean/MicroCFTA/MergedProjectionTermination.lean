import MicroCFTA.MergedProjectionPass
import MicroCFTA.InternedNormalizationFree

/-!
# A bound for repeated merged projected-leaf equality passes

Iteration tests ordered physical node identities after each complete pass.
Every changing pass strictly decreases the finite occurrence potential.
The final unchanged pass returns a complete allocation-free fixed point
in the actual runtime cache. No proof-only cache is used by iteration.
-/
namespace MicroCFTA.MergedProjectionTermination
open InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open EqualityLeafProjectionCompileAvailability EqualityLeafProjectionRepresentation
open EqualityLeafProjectionWorkers (bindOptional)
open EqualityLeafProjectionSyntax (Path Tree Endpoints Progress forestWeight)
open EqualityLeafProjectionCompile (Tag)
open EqualityRawLeafInventory (Leaf rank)
open EqualityRawLeafConstruction (ConstraintKey)
open EqualityRawLeafCompiler (build)
open MergedProjectionPass (sourcePass)

noncomputable local instance : DecidableEq ConstraintKey := by classical exact inferInstance

/-- Repeat actual source passes until physical identities agree or the explicit bound expires. -/
noncomputable def iterate (order : Value (Fin symbols) ConstraintKey → List (Fin symbols))
    (skip contradiction : Bool) (classes : List (List Path)) (fuel : Nat)
    (values : List (Value (Fin symbols) ConstraintKey)) :
    Work (Fin symbols) ConstraintKey (Option (List (Value (Fin symbols) ConstraintKey))) :=
  match fuel with
  | 0 => .pure none
  | fuel + 1 => bindOptional (sourcePass order skip contradiction classes values) fun results =>
      if results.map Value.referenceOf = values.map Value.referenceOf then .pure (some results)
      else iterate order skip contradiction classes fuel results

/-- An unchanged identity list gives a complete allocation-free physical fixed point. -/
theorem unchanged_fixed (order : Value (Fin symbols) ConstraintKey → List (Fin symbols))
    (skip contradiction : Bool) (classes : List (List Path))
    (forest trimmed : List (Tree (Tag (Fin symbols) ConstraintKey) (Leaf initial symbols)))
    (state : State (Fin symbols) ConstraintKey) (facts : Facts state)
    (values results : List (Value (Fin symbols) ConstraintKey))
    (represented : RepresentsForest build forest state values)
    (afterFacts : Facts (run (sourcePass order skip contradiction classes values) state).2)
    (returned : (run (sourcePass order skip contradiction classes values) state).1 = some results)
    (output : RepresentsForest build trimmed (run (sourcePass order skip contradiction classes values) state).2 results)
    (same : results.map Value.referenceOf = values.map Value.referenceOf) :
    let after := (run (sourcePass order skip contradiction classes values) state).2
    run (sourcePass order skip contradiction classes results) after = (some results, after) := by
  let after := (run (sourcePass order skip contradiction classes values) state).2
  have later := forest_grows build forest state after facts.coherent.valid
    (InternedConstructorTemplates.run_correct _ state facts.coherent.valid).2 values represented
  have originals := forest_available build EqualityRawLeafCompiler.leaves_available forest after afterFacts values later
  have outputs := forest_available build EqualityRawLeafCompiler.leaves_available trimmed after afterFacts results output
  have sameValues := InternedNormalizationFree.value_lists_equal after afterFacts.coherent results values
    (fun value member => (outputs value member).resident) (fun value member => (originals value member).resident) same
  have replayed := replay (sourcePass order skip contradiction classes values) state after facts.coherent.valid (grows_refl after)
  rw [returned] at replayed
  rw [sameValues] at replayed ⊢
  exact replayed

/-- More fuel than the initial occurrence potential always reaches a physical fixed point. -/
theorem iterate_completes (order : Value (Fin symbols) ConstraintKey → List (Fin symbols))
    (complete : MergedProjectionTargets.CompleteOrder order) (skip contradiction : Bool) (classes : List (List Path)) (fuel : Nat)
    (forest : List (Tree (Tag (Fin symbols) ConstraintKey) (Leaf initial symbols)))
    (proper : ∀ path ∈ classes.flatten, path ≠ []) (endpoints : Endpoints classes.flatten forest)
    (state : State (Fin symbols) ConstraintKey) (facts : Facts state)
    (values : List (Value (Fin symbols) ConstraintKey)) (represented : RepresentsForest build forest state values)
    (enough : forestWeight rank forest < fuel) :
    let actual := run (iterate order skip contradiction classes fuel values) state
    Facts actual.2 ∧ ∃ results trimmed, actual.1 = some results ∧ RepresentsForest build trimmed actual.2 results ∧
      Endpoints classes.flatten trimmed ∧ Progress (forestWeight rank) trimmed forest ∧
      run (sourcePass order skip contradiction classes results) actual.2 = (some results, actual.2) := by
  induction fuel generalizing forest state values with
  | zero => omega
  | succ fuel ih =>
      let passed := run (sourcePass order skip contradiction classes values) state
      obtain ⟨passFacts, results, trimmed, passReturned, passRepresented, passProgress, passEndpoints, strict⟩ :=
        MergedProjectionPass.pass_progress order complete skip contradiction classes forest proper endpoints state facts values represented
      have nextEndpoints : Endpoints classes.flatten trimmed := by
        intro path member
        cases path with
        | nil => trivial
        | cons index path => exact passEndpoints index path (endpoints (index :: path) member)
      by_cases same : results.map Value.referenceOf = values.map Value.referenceOf
      · have executed : run (iterate order skip contradiction classes (fuel + 1) values) state = (some results, passed.2) := by
          simp only [iterate, bindOptional, run_bind, passReturned, ite_eq_left same, run]
          rfl
        have fixed := unchanged_fixed order skip contradiction classes forest trimmed state facts values results represented
          passFacts passReturned passRepresented same
        rw [executed]
        exact ⟨passFacts, results, trimmed, rfl, passRepresented, nextEndpoints, passProgress, fixed⟩
      · have decreased := strict same
        have remaining : forestWeight rank trimmed < fuel := by omega
        obtain ⟨finalFacts, finalValues, finalForest, finalReturned, finalRepresented, finalEndpoints, finalProgress, fixed⟩ :=
          ih trimmed nextEndpoints passed.2 passFacts results passRepresented remaining
        have executed : run (iterate order skip contradiction classes (fuel + 1) values) state =
            run (iterate order skip contradiction classes fuel results) passed.2 := by
          simp only [iterate, bindOptional, run_bind, passReturned, ite_eq_right same]
          rfl
        rw [executed]
        exact ⟨finalFacts, finalValues, finalForest, finalReturned, finalRepresented, finalEndpoints,
          EqualityLeafProjectionSyntax.progress_trans (forestWeight rank) forest trimmed finalForest passProgress finalProgress, fixed⟩

end MicroCFTA.MergedProjectionTermination
