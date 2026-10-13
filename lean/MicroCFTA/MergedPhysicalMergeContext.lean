import MicroCFTA.MergedPhysicalComparison

/-!
# Prepared comparison reads through ordinary merge construction

The merge can allocate edges, ordinary nodes, and unions between queries.
These effects add no Mu. They preserve the exact prepared unfolding
results. Each later comparison derives its finite inventory from its
current cache and its actual current roots.
-/
namespace MicroCFTA.MergedPhysicalMergeContext
open Cache InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedNestedConstruction InternedNestedFacts InternedNestedProvenance InternedEdgeResidency
open InternedShallowHeap MergedPhysicalWarmup MergedPhysicalComparison

/-- The current source cache retains available results for every complete Mu unfolding. -/
structure Context [DecidableEq (EdgeKey Symbol Guard)] (state : State Symbol Guard)
    (outputs : List (Value Symbol Guard)) : Prop where
  facts : Facts state
  retained : Values state outputs
  ready : Ready state outputs

/-- Finite source preparation constructs an initial comparison context. -/
theorem prepare_context [DecidableEq (EdgeKey Symbol Guard)] (state : State Symbol Guard)
    (facts : Facts state) (prepared : Prepared state) :
    ∃ outputs after, warmup (nodeInventory state) state = .done outputs after ∧
      Grows state after ∧ Context after outputs := by
  obtain ⟨outputs, after, done, afterFacts, growth, _, _, results, ready⟩ := prepare state facts prepared
  exact ⟨outputs, after, done, growth, ⟨afterFacts, results, ready⟩⟩

/-- A finite ordinary constructor effect preserves the prepared context and every retained result. -/
theorem Context.work [DecidableEq (EdgeKey Symbol Guard)] (state : State Symbol Guard)
    (outputs : List (Value Symbol Guard)) (context : Context state outputs) (computation : Work Symbol Guard Result)
    (facts : Facts (run computation state).2) (unchanged : NoNewMu state (run computation state).2) :
    Context (run computation state).2 outputs := by
  refine ⟨facts, ?_, ?_⟩
  · intro value member
    exact available_after_run computation state context.facts.coherent.valid (context.retained value member)
  · exact context.ready.preserve state _ context.facts outputs
      (InternedConstructorTemplates.run_correct computation state context.facts.coherent.valid).2 unchanged

/-- Actual edge construction preserves prepared comparison reads and returns a resident edge. -/
theorem Context.makeEdge [DecidableEq (EdgeKey Symbol Guard)] (state : State Symbol Guard)
    (outputs : List (Value Symbol Guard)) (context : Context state outputs)
    (symbol : Symbol) (guard : Guard) (values : List (Value Symbol Guard)) (inputs : Values state values) :
    Context (run (InternedConstructorTemplates.makeEdge symbol guard values) state).2 outputs ∧
      EdgeResident (run (InternedConstructorTemplates.makeEdge symbol guard values) state).2 (run (InternedConstructorTemplates.makeEdge symbol guard values) state).1 := by
  have verified := edge_verified symbol guard values state context.facts inputs
  refine ⟨context.work state outputs (InternedConstructorTemplates.makeEdge symbol guard values) verified.facts ?_, verified.result _ _ rfl⟩
  intro key entry body depth ordinary stored
  exact stored

/-- Actual ordinary node construction preserves prepared reads and returns an available record. -/
theorem Context.makeNode [DecidableEq (EdgeKey Symbol Guard)] (state : State Symbol Guard)
    (outputs : List (Value Symbol Guard)) (context : Context state outputs)
    (edges : List (EdgeValue Symbol Guard)) (inputs : Edges state edges) :
    Context (run (InternedConstructorTemplates.makeNode edges) state).2 outputs ∧
      Available (run (InternedConstructorTemplates.makeNode edges) state).2 (run (InternedConstructorTemplates.makeNode edges) state).1 := by
  have verified := node_verified edges state context.facts inputs
  exact ⟨context.work state outputs (InternedConstructorTemplates.makeNode edges) verified.facts (makeNode_noNewMu edges state),
    verified.result _ _ rfl⟩

/-- Actual union normalization preserves prepared reads and returns an available record. -/
theorem Context.makeUnion [DecidableEq (EdgeKey Symbol Guard)] (state : State Symbol Guard)
    (outputs : List (Value Symbol Guard)) (context : Context state outputs)
    (values : List (Value Symbol Guard)) (inputs : Values state values) :
    Context (run (InternedConstructorTemplates.makeUnion values) state).2 outputs ∧
      Available (run (InternedConstructorTemplates.makeUnion values) state).2 (run (InternedConstructorTemplates.makeUnion values) state).1 := by
  have verified := union_verified values state context.facts inputs
  exact ⟨context.work state outputs (InternedConstructorTemplates.makeUnion values) verified.facts (makeUnion_noNewMu values state),
    verified.result _ _ rfl⟩

noncomputable section
local instance : DecidableEq (Value Symbol Guard) := Classical.typeDecidableEq _

/-- Every current root has an exact finite epsilon exposure in the current physical cache. -/
theorem Context.expose_exact [DecidableEq (EdgeKey Symbol Guard)] (state : State Symbol Guard)
    (outputs : List (Value Symbol Guard)) (context : Context state outputs)
    (roots : List (Value Symbol Guard)) (inputs : Values state roots) (root : Value Symbol Guard) (member : root ∈ roots)
    (value : Value Symbol Guard) :
    value ∈ visited state roots outputs root ↔ Productivity.Reachable (successors state) [root] value :=
  visited_exact state context.facts roots outputs inputs context.retained context.ready root
    (by simp [inventory, member]) value

/-- Every adaptive comparison has a finite source call tree, whether its answer is true or false. -/
theorem Context.compare_terminates [DecidableEq (EdgeKey Symbol Guard)]
    (state : State Symbol Guard) (outputs : List (Value Symbol Guard)) (context : Context state outputs)
    (roots : List (Value Symbol Guard)) (inputs : Values state roots)
    (meaning : Guard → Language.Term Symbol → Bool)
    (wide narrow : Value Symbol Guard) (wideIn : wide ∈ roots) (narrowIn : narrow ∈ roots) :
    MergedComparisonSource.Terminates (rows state roots outputs meaning)
      (fun value => value.referenceOf == .empty) [] wide narrow :=
  MergedComparisonSource.inventory_terminates (rows state roots outputs meaning) (fun value => value.referenceOf == .empty)
    (inventory state roots outputs) (rows_closed state context.facts roots outputs inputs context.retained meaning)
    wide narrow (by simp [inventory, wideIn]) (by simp [inventory, narrowIn])

/-- Adaptive source comparisons retain an explicit finite pair bound after all earlier ordinary effects. -/
theorem Context.compare_saturated [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Symbol]
    (state : State Symbol Guard) (outputs : List (Value Symbol Guard)) (context : Context state outputs)
    (roots : List (Value Symbol Guard)) (inputs : Values state roots)
    (meaning : Guard → Language.Term Symbol → Bool)
    (unconstrained : Language.Edge (Value Symbol Guard) Symbol → Bool)
    (wide narrow : Value Symbol Guard) (wideIn : wide ∈ roots) (narrowIn : narrow ∈ roots) (extra : Nat) :
    MergedComparisonSource.check (rows state roots outputs meaning) (fun value => value.referenceOf == .empty) unconstrained
        ((inventory state roots outputs).length * (inventory state roots outputs).length + extra) [] wide narrow =
      MergedComparisonSource.check (rows state roots outputs meaning) (fun value => value.referenceOf == .empty) unconstrained
        ((inventory state roots outputs).length * (inventory state roots outputs).length) [] wide narrow :=
  MergedComparisonSource.check_saturated (rows state roots outputs meaning) (fun value => value.referenceOf == .empty) unconstrained
    (inventory state roots outputs) (rows_closed state context.facts roots outputs inputs context.retained meaning)
    wide narrow (by simp [inventory, wideIn]) (by simp [inventory, narrowIn]) extra

end
end MicroCFTA.MergedPhysicalMergeContext
