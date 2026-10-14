import MicroCFTA.SourceRecursiveIntersectionSemanticHeap
import MicroCFTA.InternedOpenDepthExecution

/-!
# Body/probe open-depth preservation at native source effects

Ordinary jobs add no Mu record. Actual optional binders compile to the
repaired source executor, whose body/probe heap preservation is proved.
The older semantic heap remains a separate premise.
-/
namespace MicroCFTA.SourceRecursiveIntersectionOpenDepthEffects
open Cache InternedConstructorTemplates InternedProbeProvenance
open InternedNestedConstruction (Outcome)
open InternedStoredSubstitution
open InternedOpenDepthReadback (Heap)
open SourceRecursiveIntersectionSemanticHeap (SemanticHeap)

/-- Actual edge construction cannot change a stored Mu body/probe equality. -/
theorem edge [DecidableEq (EdgeKey Symbol Guard)] (symbol : Symbol) (guard : Guard)
    (values : List (Value Symbol Guard)) (state : State Symbol Guard) (heap : Heap state) :
    Heap (run (makeEdge symbol guard values) state).2 := heap

/-- Actual ordinary node construction retains every stored Mu body/probe equality. -/
theorem node [DecidableEq (EdgeKey Symbol Guard)] (edges : List (EdgeValue Symbol Guard))
    (state : State Symbol Guard) (heap : Heap state) : Heap (run (makeNode edges) state).2 :=
  InternedOpenDepthReadback.preserve state _ heap (InternedShallowHeap.makeNode_noNewMu edges state)

/-- Actual union normalization retains every stored Mu body/probe equality. -/
theorem union [DecidableEq (EdgeKey Symbol Guard)] (values : List (Value Symbol Guard))
    (state : State Symbol Guard) (heap : Heap state) : Heap (run (makeUnion values) state).2 :=
  InternedOpenDepthReadback.preserve state _ heap (InternedShallowHeap.makeUnion_noNewMu values state)

/-- Actual optional binders retain the body/probe heap through every probe, canonical hit, and outcome. -/
theorem optionalBinder [DecidableEq (EdgeKey Symbol Guard)] (pair : Nat × Nat) (body : Value Symbol Guard)
    (state : State Symbol Guard) (semantic : SemanticHeap state) (heap : Heap state) (available : Available state body) :
    Heap (SourceRecursiveIntersectionMaybeMu.maybeMu pair body state).state := by
  have context := SourceRecursiveIntersectionSemanticHeap.context state semantic (leaves body)
    (leaves_available body state available)
  rw [SourceRecursiveIntersectionMaybeMu.maybeMu_eq pair body state state semantic.1.normal.facts available]
  split
  · exact (InternedOpenDepthExecution.build_depth _ _ state context semantic.2 heap).heap
  · exact heap

end MicroCFTA.SourceRecursiveIntersectionOpenDepthEffects
