import MicroCFTA.SourceRecursiveIntersectionNative
import MicroCFTA.SourceEqualityPCSNativeEdge
import MicroCFTA.SourceEqualityInheritedPayload
import MicroCFTA.InternedFreshOrdinaryFacts

namespace MicroCFTA.StaggeredNativeConstructed
open Cache InternedConstructorTemplates InternedNestedConstruction InternedProbeProvenance
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Heap" => InternedConstructorTemplates.State Symbol Guard

private instance : DecidableEq FullSyntax.Formula :=
  fun first second => decidable_of_iff (FormulaOrder.compareFormula first second = .eq)
    (FormulaOrder.formula_eq first second)
private instance : DecidableEq (SourceGuards.Guard FullSyntax.Formula) := SourceEqualityPCSNativeEdge.guardDecidableEq
private instance : DecidableEq Guard := fun first second =>
  decidable_of_iff (first.equalities = second.equalities ∧ first.guard = second.guard)
    (by cases first; cases second; simp)

private def top : Guard := ⟨some [], .top⟩
private def equal : Guard := ⟨some [[[0], [1]]], .top⟩
private def leaf : Syntax Symbol Guard := .node [.mk ("leaf", .top) top []]
private def good : Syntax Symbol Guard := .node [.mk ("mid", .top) top [leaf, leaf]]
private def bad : Syntax Symbol Guard := .node [.mk ("mid", .top) equal [leaf, leaf]]
private def leftPlan : Syntax Symbol Guard := .node [.mk ("root", .top) equal [good, good]]
private def rightPlan : Syntax Symbol Guard := .node [.mk ("root", .top) top [bad, bad]]
private def built := InternedFreshOrdinaryConstruction.buildMany [leftPlan, rightPlan] [] empty
private def source := built.state
private def values : List (Value Symbol Guard) := match built with | .done values _ => values | .pending .. => []
private def left := values[0]?.getD .empty
private def right := values[1]?.getD .empty
private def before : SourceRecursiveIntersectionThunks.State 8 Symbol Guard :=
  SourceRecursiveIntersectionThunks.initial 8 ⟨source, Cache.emptyState⟩
private def request : SourceRecursiveIntersectionThunks.NodeRequest Symbol Guard :=
  ⟨IntersectionEmptyDomain.emptyDomain, left, right⟩
private def query := SourceRecursiveIntersectionNative.execute top SourceEqualityPCSNativeEdge.conjoin 64
  (.node request .pure) before
private def result : Value Symbol Guard := match query with | .done value _ => value | _ => .empty
private def after := query.state

private def firstChild (value : Value Symbol Guard) : Value Symbol Guard :=
  match InternedEdgeResidency.nodeEdges value with
  | row :: _ => row.children[0]?.getD .empty
  | [] => .empty
private def own (value : Value Symbol Guard) : Except String (Option EqualityNormalize.Constraints) :=
  match InternedEdgeResidency.nodeEdges value with
  | row :: _ => (SourceEqualityPhysicalPayload.own row.entry.key.constraint).map SourceEqualityInheritedPayload.classes
  | [] => .error "missing row"

private theorem built_done : built = .done [left, right] source := by cbv
private theorem query_done : query = .done result after := by cbv
private theorem own_fields :
    own left = .ok (some [[[0], [1]]]) ∧ own (firstChild left) = .ok (some []) ∧
    own right = .ok (some []) ∧ own (firstChild right) = .ok (some [[[0], [1]]]) ∧
    own result = .ok (some [[[0], [1]]]) ∧ own (firstChild result) = .ok (some [[[0], [1]]]) := by cbv

/-- The actual native product combines constraints that occupy different ordinary depths. -/
theorem actual_staggered_product :
    ∃ (first second output : Value Symbol Guard) (initial : Heap)
        (final : SourceRecursiveIntersectionThunks.State 8 Symbol Guard),
      InternedFreshOrdinaryConstruction.buildMany [leftPlan, rightPlan] [] empty = .done [first, second] initial ∧
      InternedNestedFacts.Facts initial ∧ Available initial first ∧ Available initial second ∧
      first.free = [] ∧ second.free = [] ∧
      SourceRecursiveIntersectionNative.execute top SourceEqualityPCSNativeEdge.conjoin 64
        (.node ⟨IntersectionEmptyDomain.emptyDomain, first, second⟩ .pure)
        (SourceRecursiveIntersectionThunks.initial 8 ⟨initial, Cache.emptyState⟩) = .done output final ∧
      own first = .ok (some [[[0], [1]]]) ∧ own (firstChild first) = .ok (some []) ∧
      own second = .ok (some []) ∧ own (firstChild second) = .ok (some [[[0], [1]]]) ∧
      own output = .ok (some [[[0], [1]]]) ∧ own (firstChild output) = .ok (some [[[0], [1]]]) := by
  have physical := InternedFreshOrdinaryFacts.buildMany_verified [leftPlan, rightPlan] [] empty
    InternedNestedFacts.empty_facts (by intro value absent; cases absent)
  have facts : InternedNestedFacts.Facts source := by simpa only [built_done, Outcome.state] using physical.facts
  have available := physical.result [left, right] source built_done
  exact ⟨left, right, result, source, after, built_done, facts, available left List.mem_cons_self,
    available right (List.mem_cons_of_mem _ List.mem_cons_self), by cbv, by cbv, query_done, own_fields⟩

end MicroCFTA.StaggeredNativeConstructed

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.proofs true
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.proofs.threshold 254
set_option pp.maxSteps 10000000

#check @MicroCFTA.StaggeredNativeConstructed.actual_staggered_product
#print axioms MicroCFTA.StaggeredNativeConstructed.actual_staggered_product
