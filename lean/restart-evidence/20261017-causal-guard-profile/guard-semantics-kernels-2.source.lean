import MicroCFTA.SourceCurrentConstrainedCapGuardSemantics

set_option linter.all true
set_option pp.explicit true
set_option pp.proofs true
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000
set_option pp.fullNames true
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

namespace MicroCFTA.GuardSemanticsKernels
open InternedConstructorTemplates InternedNestedConstruction
open SourceCurrentConstrainedCapGuardSemantics

/-- The first row executes a raw recursive subplan but its empty sibling erases the complete row. -/
def mixedPlan : Syntax Nat Bool := .node
  [.mk 0 false [.empty, .binder false (.node [.mk 9 false [.var 0]])],
   .mk 1 true [.var 0, .binder true (.union [.var 0, .node [.mk 2 false []]])]]

/-- Full evaluation retains a deep argument and exact depth two after erasure and smart cleanup. -/
theorem mixed_nested_prediction (argument : Atom) (captures : List (Shape Atom)) :
    evaluate (fun guard : Bool => guard = true) mixedPlan (reference argument :: captures) =
      ⟨⟨[], [argument], true, 0⟩, some 2⟩ := by
  classical
  simp [mixedPlan, evaluate, evaluateMany, evaluateEdges, edge, binder, reference, combineMany, combine,
    Shape.map, InternedDepthSemantics.edge, InternedDepthSemantics.binder,
    InternedDepthSemantics.combineMany, InternedDepthSemantics.combine, InternedDepthSemantics.Shape.free,
    InternedDepthSemantics.Shape.isEmpty, InternedDepthSemantics.Shape.map, InternedDepthSemantics.hasLocal,
    InternedDepthSemantics.lower, InternedFreeNameSemantics.lower,
    SourceCurrentConstrainedCapGuardDepth.join, SourceCurrentConstrainedCapGuardDepth.raise,
    SourceCurrentConstrainedCapGuardDepth.guardCost]

/-- Literal argument substitution changes structural names and retains the full mixed guard prediction. -/
theorem mixed_argument_transport (first second : Atom) (captures : List (Shape Atom)) :
    (evaluate (fun guard : Bool => guard = true) mixedPlan (reference first :: captures)).guardDepth = some 2 ∧
    (evaluate (fun guard : Bool => guard = true) mixedPlan (reference second :: captures)).guardDepth = some 2 ∧
    (evaluate (fun guard : Bool => guard = true) mixedPlan (reference first :: captures)).shape.deep = [first] ∧
    (evaluate (fun guard : Bool => guard = true) mixedPlan (reference second :: captures)).shape.deep = [second] := by
  rw [mixed_nested_prediction, mixed_nested_prediction]
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- A colliding root argument and a fresh argument have different filtered roots but the same guard depth. -/
theorem normalization_collision (first second : Nat) (different : first ≠ second) :
    (normalize first (evaluate (fun guard : Bool => guard = true) (.union [.var 0, .var 1] : Syntax Nat Bool)
      [reference first, reference first])).shape.roots = [first, first] ∧
    (normalize second (evaluate (fun guard : Bool => guard = true) (.union [.var 0, .var 1] : Syntax Nat Bool)
      [reference second, reference first])).shape.roots = [first] ∧
    (normalize first (evaluate (fun guard : Bool => guard = true) (.union [.var 0, .var 1] : Syntax Nat Bool)
      [reference first, reference first])).guardDepth =
    (normalize second (evaluate (fun guard : Bool => guard = true) (.union [.var 0, .var 1] : Syntax Nat Bool)
      [reference second, reference first])).guardDepth := by
  simp [evaluate, evaluateMany, combineMany, combine, normalize, reference,
    InternedDepthSemantics.combine, different,
    SourceCurrentConstrainedCapGuardDepth.join]

#print axioms mixed_nested_prediction
#check @mixed_nested_prediction
#print axioms mixed_argument_transport
#check @mixed_argument_transport
#print axioms normalization_collision
#check @normalization_collision
end MicroCFTA.GuardSemanticsKernels
