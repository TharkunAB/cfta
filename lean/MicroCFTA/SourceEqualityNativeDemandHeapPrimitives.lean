import MicroCFTA.SourceEqualityRequiredCache
import MicroCFTA.SourceRecursiveIntersectionOpenDepthEffects

/-!
# Heap preservation for checked native primitive effects

Actual constructor arguments supply availability or edge residency in the
current heap. Ordinary node and union effects need no closedness premise.
An available optional-binder body completes in a ready heap and retains
both histories. These facts do not use eager intersection provenance.
-/
namespace MicroCFTA.SourceEqualityNativeDemandHeapPrimitives
open Cache InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values Edges)
open SourceEqualityRequiredCache (Ready Keeps)

/-- Ordinary node construction retains a ready heap and available output for open resident rows. -/
theorem node [DecidableEq (EdgeKey Symbol Guard)] (edges : List (EdgeValue Symbol Guard))
    (state : State Symbol Guard) (ready : Ready state) (resident : Edges state edges) :
    Keeps state (run (makeNode edges) state).2 ∧ Available (run (makeNode edges) state).2 (run (makeNode edges) state).1 := by
  have facts := ready.semantic.1.normal.facts
  have checked := InternedNestedFacts.node_verified edges state facts resident
  refine ⟨⟨⟨SourceRecursiveIntersectionSemanticHeap.node edges state ready.semantic resident,
    InternedNestedCoverage.run_covered _ state facts.coherent.valid ready.covered,
    InternedOpenDepthReadback.preserve state _ ready.depth (InternedShallowHeap.makeNode_noNewMu edges state)⟩,
    checked.growth, checked.history⟩, checked.result _ _ rfl⟩

/-- Union construction retains a ready heap and available output for open available operands. -/
theorem union [DecidableEq (EdgeKey Symbol Guard)] (values : List (Value Symbol Guard))
    (state : State Symbol Guard) (ready : Ready state) (available : Values state values) :
    Keeps state (run (makeUnion values) state).2 ∧ Available (run (makeUnion values) state).2 (run (makeUnion values) state).1 := by
  have facts := ready.semantic.1.normal.facts
  have checked := InternedNestedFacts.union_verified values state facts available
  refine ⟨⟨⟨SourceRecursiveIntersectionSemanticHeap.union values state ready.semantic available,
    InternedNestedCoverage.run_covered _ state facts.coherent.valid ready.covered,
    InternedOpenDepthReadback.preserve state _ ready.depth (InternedShallowHeap.makeUnion_noNewMu values state)⟩,
    checked.growth, checked.history⟩, checked.result _ _ rfl⟩

/-- An actual available optional-binder body completes with a ready heap and available result. -/
theorem optionalBinder_complete [DecidableEq (EdgeKey Symbol Guard)] (pair : Nat × Nat) (body : Value Symbol Guard)
    (state : State Symbol Guard) (ready : Ready state) (available : Available state body) :
    ∃ value after, SourceRecursiveIntersectionMaybeMu.maybeMu pair body state = .done value after ∧
      Keeps state after ∧ Available after value := by
  obtain ⟨value, after, done, context, depth, covered, valueAvailable, growth, history⟩ :=
    SourceRecursiveIntersectionMaybeMu.complete_decoded pair body state ready.semantic.1 available ready.semantic.2 ready.covered
  have openDepth := SourceRecursiveIntersectionOpenDepthEffects.optionalBinder pair body state ready.semantic ready.depth available
  refine ⟨value, after, done, ⟨⟨⟨context, depth⟩, covered, ?_⟩, growth, history⟩, valueAvailable⟩
  simpa only [done, InternedNestedConstruction.Outcome.state] using openDepth

/-- The actual optional-binder outcome retains the complete ready heap and histories. -/
theorem optionalBinder_keeps [DecidableEq (EdgeKey Symbol Guard)] (pair : Nat × Nat) (body : Value Symbol Guard)
    (state : State Symbol Guard) (ready : Ready state) (available : Available state body) :
    Keeps state (SourceRecursiveIntersectionMaybeMu.maybeMu pair body state).state := by
  obtain ⟨value, after, done, keeps, _⟩ := optionalBinder_complete pair body state ready available
  simpa only [done, InternedNestedConstruction.Outcome.state] using keeps

/-- Every actual optional-binder observation has heap preservation and available completed output. -/
theorem optionalBinder [DecidableEq (EdgeKey Symbol Guard)] (pair : Nat × Nat) (body : Value Symbol Guard)
    (state : State Symbol Guard) (ready : Ready state) (available : Available state body) :
    Keeps state (SourceRecursiveIntersectionMaybeMu.maybeMu pair body state).state ∧
      ∀ value after, SourceRecursiveIntersectionMaybeMu.maybeMu pair body state = .done value after → Available after value :=
  ⟨optionalBinder_keeps pair body state ready available,
    (SourceRecursiveIntersectionMaybeMu.verified pair body state ready.semantic.1.normal.facts available).result⟩

/-- Primitive jobs require only their actual arguments' current physical representation. -/
inductive WorkInputs (state : State Symbol Guard) : {Result : Type} → Work Symbol Guard Result → Prop where
  | pure (value : Result) : WorkInputs state (.pure value)
  | edge (symbol : Symbol) (guard : Guard) (values : List (Value Symbol Guard))
      (available : Values state values) : WorkInputs state (makeEdge symbol guard values)
  | node (edges : List (EdgeValue Symbol Guard)) (resident : Edges state edges) : WorkInputs state (makeNode edges)
  | union (values : List (Value Symbol Guard)) (available : Values state values) : WorkInputs state (makeUnion values)

/-- Current primitive input checks derive actual heap preservation without a future-state premise. -/
theorem work_keeps [DecidableEq (EdgeKey Symbol Guard)] (job : Work Symbol Guard Result)
    (state : State Symbol Guard) (ready : Ready state) (inputs : WorkInputs state job) : Keeps state (run job state).2 := by
  cases inputs with
  | pure value => exact SourceEqualityRequiredCache.pure_keeps state ready
  | edge symbol guard values available => exact (SourceEqualityRequiredCache.edge symbol guard values state ready available).1
  | node edges resident => exact (node edges state ready resident).1
  | union values available => exact (union values state ready available).1

end MicroCFTA.SourceEqualityNativeDemandHeapPrimitives
