import MicroCFTA.SourceEqualityNormalizationReceipt
import MicroCFTA.SourceRecursiveIntersectionNative
import MicroCFTA.SourceEqualityPCSNativeEdge
import MicroCFTA.SourceEqualityInheritedPayload
import MicroCFTA.InternedFreshOrdinaryFacts

/-!
# Native product growth of constrained ordinary levels

The actual source product combines nonempty own equality fields at distinct
ordinary depths. Each closed operand has one nonplain ordinary level on any
branch. The returned value has two. All source payloads are built from empty.
The complete native node and edge memo execution is checked literally.
This refutes maximum preservation for this count. It does not refute the
existing distance-based Cap profile or prove an outer recursive cycle.
-/

set_option maxRecDepth 30000
set_option maxHeartbeats 4000000
set_option cbv.maxSteps 100000000

namespace MicroCFTA.SourceCurrentNativeGuardOccurrenceGrowth
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

private theorem array_small (classes : EqualityNormalize.Constraints) :
    SourceCompactGuards.arrayNormalize classes = SourceEqualityNormalizationReceipt.observed 16 classes :=
  SourceEqualityNormalizationReceipt.observed_eq 16 classes
attribute [local cbv_eval] array_small

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
private def before := SourceRecursiveIntersectionThunks.initial 8
  (SourceRecursiveIntersectionKernel.Machine.mk source Cache.emptyState)
private def request : SourceRecursiveIntersectionThunks.NodeRequest Symbol Guard :=
  ⟨IntersectionEmptyDomain.emptyDomain, left, right⟩
private noncomputable def query := SourceRecursiveIntersectionNative.execute top SourceEqualityPCSNativeEdge.conjoin 64
  (.node request .pure) before
private noncomputable def result : Value Symbol Guard := match query with | .done value _ => value | _ => .empty
private noncomputable def after := query.state

private def firstChild (value : Value Symbol Guard) : Value Symbol Guard :=
  match InternedEdgeResidency.nodeEdges value with
  | row :: _ => row.children[0]?.getD .empty
  | [] => .empty
private noncomputable def own (value : Value Symbol Guard) : Except String (Option EqualityNormalize.Constraints) :=
  match InternedEdgeResidency.nodeEdges value with
  | row :: _ => (SourceEqualityPhysicalPayload.own row.entry.key.constraint).map SourceEqualityInheritedPayload.classes
  | [] => .error "missing row"

mutual
/-- Count nonplain ordinary row levels on one literal branch. Mu and references contribute zero. -/
noncomputable def depth : Value Symbol Guard → Nat
  | .node _ rows _ _ => rowsDepth rows
  | .union _ members _ _ => valuesDepth members
  | .empty | .reference _ | .mu .. => 0
termination_by value => sizeOf value
/-- Retain the largest count in the ordered members. -/
noncomputable def valuesDepth : List (Value Symbol Guard) → Nat
  | [] => 0
  | first :: rest => max (depth first) (valuesDepth rest)
termination_by values => sizeOf values
/-- Charge one for a nonplain row and add its greatest child count. -/
noncomputable def rowsDepth : List (EdgeValue Symbol Guard) → Nat
  | [] => 0
  | .mk entry children :: rest =>
      max ((if SourceMemoGate.plain entry.key.constraint then 0 else 1) + valuesDepth children) (rowsDepth rest)
termination_by rows => sizeOf rows
end

private theorem built_done : built = .done [left, right] source := by cbv
private theorem query_done : query = .done result after := by cbv
private theorem counts : depth left = 1 ∧ depth right = 1 ∧ depth result = 2 := by cbv
private theorem own_fields :
    own left = .ok (some [[[0], [1]]]) ∧ own (firstChild left) = .ok (some []) ∧
    own right = .ok (some []) ∧ own (firstChild right) = .ok (some [[[0], [1]]]) ∧
    own result = .ok (some [[[0], [1]]]) ∧ own (firstChild result) = .ok (some [[[0], [1]]]) := by cbv

private theorem witness :
    ∃ (programs : List (Syntax Symbol Guard)) (first second output : Value Symbol Guard) (initial : Heap)
        (final : SourceRecursiveIntersectionThunks.State 8 Symbol Guard),
      InternedFreshOrdinaryConstruction.buildMany programs [] empty = .done [first, second] initial ∧
      InternedNestedFacts.Facts initial ∧ Available initial first ∧ Available initial second ∧
      first.free = [] ∧ second.free = [] ∧
      SourceRecursiveIntersectionNative.execute top SourceEqualityPCSNativeEdge.conjoin 64
        (.node ⟨IntersectionEmptyDomain.emptyDomain, first, second⟩ .pure)
        (SourceRecursiveIntersectionThunks.initial 8 ⟨initial, Cache.emptyState⟩) = .done output final ∧
      depth first = 1 ∧ depth second = 1 ∧ depth output = 2 ∧
      own first = .ok (some [[[0], [1]]]) ∧ own (firstChild first) = .ok (some []) ∧
      own second = .ok (some []) ∧ own (firstChild second) = .ok (some [[[0], [1]]]) ∧
      own output = .ok (some [[[0], [1]]]) ∧ own (firstChild output) = .ok (some [[[0], [1]]]) := by
  have physical := InternedFreshOrdinaryFacts.buildMany_verified [leftPlan, rightPlan] [] empty
    InternedNestedFacts.empty_facts (by intro value absent; cases absent)
  have facts : InternedNestedFacts.Facts source := by change InternedNestedFacts.Facts built.state; exact physical.facts
  have available := physical.result [left, right] source built_done
  exact ⟨[leftPlan,rightPlan],left, right, result, source, after, built_done, facts, available left List.mem_cons_self,
    available right (List.mem_cons_of_mem _ List.mem_cons_self), by cbv, by cbv, query_done, counts.1, counts.2.1, counts.2.2, own_fields⟩

/-- An actual source-built native product raises the count from one in each operand to two. -/
theorem supported_product_growth :
    ∃ (programs : List (Syntax Symbol Guard)) (first second output : Value Symbol Guard) (initial : Heap)
        (final : SourceRecursiveIntersectionThunks.State 8 Symbol Guard),
      InternedFreshOrdinaryConstruction.buildMany programs [] empty = .done [first, second] initial ∧
      InternedNestedFacts.Facts initial ∧ Available initial first ∧ Available initial second ∧
      first.free = [] ∧ second.free = [] ∧
      SourceRecursiveIntersectionNative.execute top SourceEqualityPCSNativeEdge.conjoin 64
        (.node ⟨IntersectionEmptyDomain.emptyDomain, first, second⟩ .pure)
        (SourceRecursiveIntersectionThunks.initial 8 ⟨initial, Cache.emptyState⟩) = .done output final ∧
      depth first = 1 ∧ depth second = 1 ∧ depth output = 2 ∧
      own first = .ok (some [[[0], [1]]]) ∧ own (firstChild first) = .ok (some []) ∧
      own second = .ok (some []) ∧ own (firstChild second) = .ok (some [[[0], [1]]]) ∧
      own output = .ok (some [[[0], [1]]]) ∧ own (firstChild output) = .ok (some [[[0], [1]]]) := witness

end MicroCFTA.SourceCurrentNativeGuardOccurrenceGrowth
