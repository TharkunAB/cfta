import MicroCFTA.SourceCurrentRequiredPrimaryOrigins
import MicroCFTA.SourceCurrentMuEndpoint
set_option linter.all true
set_option maxHeartbeats 3000000
set_option maxRecDepth 30000
set_option cbv.maxSteps 100000000

namespace MicroCFTA.RequiredPrimaryRetentionBoundaries
noncomputable section
open InternedConstructorTemplates InternedNestedConstruction
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "Heap" => State Symbol Guard
private instance : DecidableEq FullSyntax.Formula :=
  fun first second => decidable_of_iff (FormulaOrder.compareFormula first second = .eq)
    (FormulaOrder.formula_eq first second)
private instance : DecidableEq (SourceGuards.Guard FullSyntax.Formula) :=
  SourceEqualityPCSNativeEdge.guardDecidableEq
private instance : DecidableEq Guard := fun first second =>
  decidable_of_iff (first.equalities = second.equalities ∧ first.guard = second.guard)
    (by cases first; cases second; simp)

private def plain : Guard := ⟨some [],.top⟩
private def leaf : Syntax Symbol Guard := .node [.mk ("leaf",.top) plain []]
private def recursive : Syntax Symbol Guard := .binder false (.node [.mk ("loop",.top) plain [.var 0]])
private def mixed : Syntax Symbol Guard := .node [.mk ("pair",.top) plain [recursive,leaf]]
private def exposedUnion : Syntax Symbol Guard :=
  .binder false (.node [.mk ("outer",.top) plain [.union [.var 0,leaf]]])
private def built (expression : Syntax Symbol Guard) :=
  InternedFreshOrdinaryConstruction.build expression [] empty
private def value (expression : Syntax Symbol Guard) : Node :=
  match built expression with | .done result _ => result | _ => .empty
private def heap (expression : Syntax Symbol Guard) : Heap := (built expression).state
private def called (expression : Syntax Symbol Guard) (paths : EqualityNormalize.Class) :=
  SourceEqualityRequiredExecution.requireAll 8 8 (paths.map (List.map Int.ofNat)) [value expression] (heap expression)
private def outputs (expression : Syntax Symbol Guard) (paths : EqualityNormalize.Class) : List Node :=
  match called expression paths with | .done result _ => result | _ => []
private def after (expression : Syntax Symbol Guard) (paths : EqualityNormalize.Class) : Heap :=
  match called expression paths with | .done _ final => final | _ => heap expression
private def Checked (expression : Syntax Symbol Guard) (paths : EqualityNormalize.Class) : Prop :=
  built expression = .done (value expression) (heap expression) ∧
  SourceCurrentMuEndpoint.classMeets true SourceMemoGate.unconstrained
    (SourceEndpointReachability.reaches SourceMemoGate.unconstrained) 8
    [value expression] paths (heap expression) = .done (some false) (heap expression) ∧
  called expression paths = .done (outputs expression paths) (after expression paths) ∧
  SourceCurrentMuEndpoint.classMeets true SourceMemoGate.unconstrained
    (SourceEndpointReachability.reaches SourceMemoGate.unconstrained) 8
    (outputs expression paths) paths (after expression paths) = .done (some false) (after expression paths)

/-- Actual Required calls preserve these missing, accepted-Mu, and mixed path certificates. -/
theorem targeted_cases :
    Checked leaf [[0,0]] ∧ Checked recursive [[0,0]] ∧ Checked mixed [[0,0,0],[0,1]] := by
  constructor
  · cbv
  constructor <;> cbv

/-- A closed accepted used Mu can expose a retained union endpoint during Required. -/
theorem exposed_union_changes :
    built exposedUnion = .done (value exposedUnion) (heap exposedUnion) ∧
    SourceCurrentMuEndpoint.classMeets true SourceMemoGate.unconstrained
      (SourceEndpointReachability.reaches SourceMemoGate.unconstrained) 8
      [value exposedUnion] [[0,0]] (heap exposedUnion) = .done (some false) (heap exposedUnion) ∧
    called exposedUnion [[0,0]] = .done (outputs exposedUnion [[0,0]]) (after exposedUnion [[0,0]]) ∧
    SourceCurrentMuEndpoint.classMeets true SourceMemoGate.unconstrained
      (SourceEndpointReachability.reaches SourceMemoGate.unconstrained) 8
      (outputs exposedUnion [[0,0]]) [[0,0]] (after exposedUnion [[0,0]]) =
        .done (some true) (after exposedUnion [[0,0]]) := by
  cbv

end
end MicroCFTA.RequiredPrimaryRetentionBoundaries
