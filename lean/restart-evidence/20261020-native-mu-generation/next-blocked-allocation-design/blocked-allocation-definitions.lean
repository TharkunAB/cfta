import MicroCFTA.SourceCurrentNativeMuOptionalGeneration

/-!
# Unchecked definitions for one blocked nested-allocation candidate

These definitions are a design draft. No equation is claimed here.
-/
namespace MicroCFTA.NativeBlockedAllocationDesign
open Cache InternedConstructorTemplates InternedProbeProvenance
open InternedNestedConstruction (Syntax)
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceEqualityNativeDemand
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "Heap" => InternedConstructorTemplates.State Symbol Guard
local notation "Checked" => SourceEqualityNativeDemand.State
private instance : DecidableEq FullSyntax.Formula :=
  fun first second => decidable_of_iff (FormulaOrder.compareFormula first second = .eq)
    (FormulaOrder.formula_eq first second)
private instance : DecidableEq (SourceGuards.Guard FullSyntax.Formula) := SourceEqualityPCSNativeEdge.guardDecidableEq
private instance : DecidableEq Guard := fun first second =>
  decidable_of_iff (first.equalities = second.equalities ∧ first.guard = second.guard)
    (by cases first; cases second; simp)

private def pair : Nat × Nat := (0,1)
private def capture : Node := .reference (.intersection pair.1 pair.2)
private def expression : Syntax Symbol Guard :=
  .node [.mk ("outer7",.top) SourceEqualityConstraintConstructors.top
    [.binder false (.node [.mk ("inner8",.top) SourceEqualityConstraintConstructors.top [.var 1,.var 0]])]]
private def built := InternedFreshOrdinaryConstruction.build expression [capture] (empty : Heap)
private def valueOf : InternedNestedConstruction.Outcome Symbol Guard Node → Node
  | .done value _ => value
  | .pending .. => .empty
private def body : Node := valueOf built
private def base : Heap := built.state
private def reserve (heap : Heap) (key : InternedBinderProtocol.NodeKey) : Heap :=
  {heap with nodes := (Cache.intern heap.nodes key).2}
private def oracle : Heap := reserve base .empty
private def oracleDepth := SourceRecursiveIntersectionMaybeMu.callback
  (.intersection pair.1 pair.2) body .depth oracle
private def oracleOrdinary := SourceRecursiveIntersectionMaybeMu.callback
  (.intersection pair.1 pair.2) body
  (.uninterned (InternedFreshOrdinaryConstruction.ordinaryLevel (valueOf oracleDepth))) oracleDepth.state
private def outerKey := muKey (valueOf oracleDepth) (valueOf oracleOrdinary)
private def warm : Heap := reserve base outerKey
private def actualDepth := SourceRecursiveIntersectionMaybeMu.callback
  (.intersection pair.1 pair.2) body .depth warm
private def actualOrdinary := SourceRecursiveIntersectionMaybeMu.callback
  (.intersection pair.1 pair.2) body
  (.uninterned (InternedFreshOrdinaryConstruction.ordinaryLevel (valueOf actualDepth))) actualDepth.state
private def bound := SourceRecursiveIntersectionMaybeMu.maybeMu pair body warm
private def suffix (value : Node) : Code Symbol Guard Node :=
  .work (.pure ()) (fun _ => .pure value)
private def binder : Code Symbol Guard Node := .optionalBinder pair body suffix
private def control : Control Node := .code (.work (.pure ()) (fun _ => binder))
private def before : Checked 64 :=
  ⟨initial 64 ⟨warm,Cache.emptyState⟩,SourceEqualityConstraintMemoAllocation.empty⟩
private def outcome := SourceEqualityNativeDemand.execute 3 control before

end MicroCFTA.NativeBlockedAllocationDesign
