import MicroCFTA.SourceEqualityWarmNativeEdge
import MicroCFTA.MergedOrdinaryHeight

/-!
# Ordinary height can increase before the next recursive source call

Both selected endpoints are ordinary wrappers. Their children are raw
closed binders with constrained bodies. The gate accepts the endpoints.
Native intersection removes the unused binders and exposes their common
constrained ordinary body. The next child exceeds the original root height.
This is a counterexample to a proposed measure, not to termination.
-/
namespace MicroCFTA.SourceEqualityPartialHeightBoundary
open InternedConstructorTemplates InternedNestedConstruction
open SourceObservations SourceSymbolicIndex SourceEqualityClassFoldGraph
local notation "Symbol" => Label FullSyntax.Formula
local notation "Guard" => Constraint FullSyntax.Formula
local notation "top" => SourceEqualityConstraintConstructors.top (Formula := FullSyntax.Formula)

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
set_option cbv.maxSteps 200000000

attribute [local cbv_eval] SourceCompactGuards.arrayNormalize_eq

private instance : DecidableEq FullSyntax.Formula :=
  fun first second => decidable_of_iff (FormulaOrder.compareFormula first second = .eq) (FormulaOrder.formula_eq first second)

private instance : DecidableEq (SourceGuards.Guard FullSyntax.Formula) := SourceEqualityPCSNativeEdge.guardDecidableEq

private instance : DecidableEq Guard := fun first second =>
  decidable_of_iff (first.equalities = second.equalities ∧ first.guard = second.guard)
    (by cases first; cases second; simp)

/-- The same normalized nontrivial class labels the outer and inner binary edges. -/
def equality : Guard := ⟨some [[[0], [1]]], .top⟩

/-- The literal stored class is an actual completed source normal form. -/
theorem equality_cached : SourceEqualityGuardReadback.Cached equality.equalities := by
  have normalized : SourceCompactGuards.normalize [[[0], [1]]] = equality.equalities := by cbv
  rw [← normalized]
  exact SourceEqualityGuardReadback.normalize_cached _

/-- One ordinary leaf has no equality or residual constraint. -/
def leaf (name : String) : Syntax Symbol Guard := .node [.mk (name, .top) top []]

/-- A raw unused binder retains two closed alternatives, including the constrained binary body. -/
def raw (name : String) : Syntax Symbol Guard := .binder false (.node [
  .mk (name, .top) top [], .mk ("p", .top) equality [leaf "a", leaf "a"]])

/-- Ordinary endpoints hide two distinct constrained raw binders below their roots. -/
def expression : Syntax Symbol Guard := .node [.mk ("root", .top) equality [
  .node [.mk ("w", .top) top [raw "left"]], .node [.mk ("w", .top) top [raw "right"]]]]

/-- The source fixture is closed and uses only normalized physical annotations. -/
theorem source_valid : Scoped 0 expression ∧
    SourceEqualityAnnotationConstruction.Allowed SourceEqualityNormalizedEntry.ValidGuard expression := by
  constructor
  · simp [expression, raw, leaf, Scoped, ManyScoped, EdgesScoped]
  · simp only [expression, raw, leaf, SourceEqualityAnnotationConstruction.Allowed,
      SourceEqualityAnnotationConstruction.ManyAllowed, SourceEqualityAnnotationConstruction.EdgesAllowed]
    simp only [SourceEqualityNormalizedEntry.ValidGuard, SourceEqualityConstraintConstructors.top_cached,
      equality_cached, and_self]

/-- Observe the original root and child heights and the actual narrowed child height. -/
noncomputable def heights : Option (Nat × Nat × Nat) :=
  match InternedFreshOrdinaryConstruction.build expression [] empty with
  | .pending .. => none
  | .done root heap => match root with
    | .node _ (edge :: _) _ _ =>
        match SourceEqualityGuardedEdgeWorker.run SourceMemoGate.unconstrained top SourceEqualityPCSNativeEdge.conjoin
            SourceMemoGate.plain top 4 4 2 2 2 64 edge (some []) (SourceEqualityNativeInitial.cold 16 heap) with
        | .done (.ok result) _ => some (MergedOrdinaryHeight.height root,
            MergedOrdinaryHeight.childrenHeight edge.children, MergedOrdinaryHeight.childrenHeight result.children)
        | _ => none
    | _ => none

/-- Kernel evaluation follows closed source construction, actual gate selection, required paths, and native narrowing. -/
theorem actual_heights : heights = some (2, 1, 3) := by
  set_option cbv.maxSteps 200000000 in cbv

/-- The local prefix can return a child strictly taller than its original caller root. -/
theorem child_exceeds_original_root : ∃ parent originalChild narrowedChild,
    heights = some (parent, originalChild, narrowedChild) ∧ originalChild < parent ∧ parent < narrowedChild :=
  ⟨2, 1, 3, actual_heights, by decide, by decide⟩

/-- Original ordinary height cannot bound all children returned by a selected local prefix. -/
theorem not_parent_height_bound : ¬ (∀ parent originalChild narrowedChild,
    heights = some (parent, originalChild, narrowedChild) → narrowedChild < parent) := by
  intro bounded
  have impossible := bounded 2 1 3 actual_heights
  omega

end MicroCFTA.SourceEqualityPartialHeightBoundary
