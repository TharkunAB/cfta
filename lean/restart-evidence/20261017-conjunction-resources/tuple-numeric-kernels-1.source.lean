import MicroCFTA.SourceCurrentConjunctionTupleNumeric
import MicroCFTA.SourceCurrentConjunctionExposureResources
import MicroCFTA.SourceCurrentConjunctionRequirementNumeric
import MicroCFTA.SourceCurrentConjunctionClassHistoryEntry
import MicroCFTA.InternedFreshOrdinaryClosedCompletion

set_option linter.all true
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.proofs true
set_option pp.universes true
set_option pp.deepTerms true
set_option pp.maxSteps 10000000
set_option maxHeartbeats 4000000
set_option maxRecDepth 30000

namespace MicroCFTA.ConjunctionTupleNumericIntegration
open Cache InternedConstructorTemplates InternedProbeProvenance
open InternedNestedConstruction (Syntax Outcome)
open InternedNestedProvenance (Values Edges)
open MergedColdReaderClosedInputs (ClosedValues ClosedEdges)
open SourceEqualityRequiredSemanticCache (SemanticReady)
open SourceCurrentMemoMergeResourceControl (Fits)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
private instance : DecidableEq FullSyntax.Formula :=
  fun first second => decidable_of_iff (FormulaOrder.compareFormula first second = .eq) (FormulaOrder.formula_eq first second)
private instance : DecidableEq (SourceGuards.Guard FullSyntax.Formula) := SourceEqualityPCSNativeEdge.guardDecidableEq
private instance : DecidableEq Guard := fun first second =>
  decidable_of_iff (first.equalities = second.equalities ∧ first.guard = second.guard)
    (by cases first; cases second; simp)
private def annotation : Guard := ⟨some [[[0, 0], [1, 0]]], .top⟩
private def top : Guard := SourceEqualityConstraintConstructors.top
private def recursive : Syntax Symbol Guard :=
  .binder false (.node [.mk ("loop", .top) top [.var 0], .mk ("leaf", .top) top []])
private def expression : Syntax Symbol Guard :=
  .node [.mk ("parent", .top) annotation [recursive, recursive]]
private def built := InternedFreshOrdinaryConstruction.build expression [] empty
private def root : Value Symbol Guard := match built with | .done value _ => value | .pending .. => .empty
private def heap := built.state
private def child : Value Symbol Guard := (children root)[0]?.getD .empty
private def parentRow : EdgeValue Symbol Guard := (InternedEdgeResidency.nodeEdges root)[0]?.getD
  (run (makeEdge ("unused", .top) top []) empty).1
private def first := SourceEqualityConstraintAllocation.construct annotation.equalities Cache.emptyState
private def firstValue : SourceEqualityConstraintAllocation.Value := match first.1 with
  | .ok value => value | .error _ => .contradiction
private def last := SourceEqualityConstraintAllocation.construct top.equalities first.2
private def lastValue : SourceEqualityConstraintAllocation.Value := match last.1 with
  | .ok value => value | .error _ => .contradiction
private def operations := SourceEqualityConstraintMemoAllocation.initial last.2
private def physical : SourceCurrentConjunctionRowsAllocation.State Symbol FullSyntax.Formula := ⟨heap, operations⟩
private theorem annotation_cached : SourceEqualityGuardReadback.Cached annotation.equalities := by
  have normalized : EqualityNormalize.mkEqConstraints 2 [[[0, 0], [1, 0]]] = .normalized [[[0, 0], [1, 0]]] := by cbv
  intro classes same
  cases same
  exact SourceEqualityGuardReadback.normalized normalized
private theorem top_cached : SourceEqualityGuardReadback.Cached top.equalities := by
  have normalized : EqualityNormalize.mkEqConstraints 1 [] = .normalized [] := by cbv
  intro classes same
  cases same
  exact SourceEqualityGuardReadback.normalized normalized
private theorem history : SourceEqualityOriginalAllocationHistory.History Cache.emptyState last.2 [annotation, top] := by
  have firstDone : first = (.ok firstValue, first.2) := by cbv
  have lastDone : last = (.ok lastValue, last.2) := by cbv
  exact .construct (.construct (.start Cache.emptyState) annotation_cached firstDone) top_cached lastDone
private theorem constructed : built = .done root heap := by
  obtain ⟨value, after, done⟩ := InternedFreshOrdinaryClosedCompletion.closed_complete expression
  simp only [built, root, heap, done, Outcome.state]
private theorem covered : ∀ guard ∈ SourceEqualityConstraintOrigins.guards expression, guard ∈ [annotation, top] := by
  intro guard member
  simpa only [expression, recursive, SourceEqualityConstraintOrigins.guards, SourceEqualityConstraintOrigins.edgeGuards,
    SourceEqualityConstraintOrigins.childGuards, List.append_nil, List.nil_append, List.mem_append, List.mem_cons,
    List.not_mem_nil, or_false, or_self] using member
private theorem initial : SourceCurrentConjunctionClassScan.Ready
    (⟨SourceRecursiveIntersectionThunks.initial 0 ⟨heap, Cache.emptyState⟩, operations⟩ : SourceEqualityNativeDemand.State 0) ∧
    Available heap root ∧ root.free = [] ∧ SourceRecursiveIntersectionInputView.Original root :=
  SourceCurrentConjunctionClassHistoryEntry.constructed 0 history Cache.empty_valid expression covered root heap constructed
private theorem ready : SourceCurrentConjunctionRowsAllocation.Ready physical :=
  SourceCurrentAllocatedConjunctionMemo.ready _ initial.1.good initial.1.semantic initial.1.costs
private theorem child_available : Available heap child :=
  initial.2.1.children child (by cbv; exact .head _)
private theorem child_closed : child.free = [] := by cbv
private theorem child_mu : ∃ entry body depth ordinary, child = .mu entry body depth ordinary := by
  have kind : (match child with | .mu .. => True | _ => False) := by cbv
  cases found : child with
  | mu entry body depth ordinary => exact ⟨entry, body, depth, ordinary, rfl⟩
  | empty | reference | node | union => simp only [found] at kind
private def q := SourceCurrentMemoMergeResourceControl.initialBound heap.nodes.next heap.edges.next
  (InternedValueMassHeap.initialBound heap)
private theorem fits : Fits q heap := SourceCurrentMemoMergeResourceControl.initial heap _
  (InternedValueMassHeap.initial heap initial.1.good.native.machine.1)
private theorem duplicated_available : Values heap [child, child] := by
  intro value member
  simp only [List.mem_cons, List.not_mem_nil, or_false, or_self] at member
  exact member ▸ child_available
private theorem duplicated_closed : ClosedValues [child, child] := by
  intro value member
  simp only [List.mem_cons, List.not_mem_nil, or_false, or_self] at member
  exact member ▸ child_closed

private def tuple : List (EdgeValue Symbol Guard) := [parentRow, parentRow]
private def constraints : EqualityNormalize.Constraints := [[[0, 0], [1, 0]]]
private theorem children : parentRow.children = [child, child] := by cbv
private theorem resident : Edges heap tuple := by
  intro row member
  have same : row = parentRow := by simpa only [tuple, List.mem_cons, List.not_mem_nil, or_false, or_self] using member
  subst row
  exact InternedEdgeResidency.resident_edges heap initial.1.good.native.machine.1.linked root initial.2.1.resident
    parentRow (by cbv; exact .head _)
private theorem tuple_closed : ClosedEdges tuple := by
  intro row member
  have same : row = parentRow := by simpa only [tuple, List.mem_cons, List.not_mem_nil, or_false, or_self] using member
  subst row
  rw [children]
  exact duplicated_closed
private theorem tuple_same : SourceCurrentConjunctionRequirements.SameArity tuple := by
  intro row member
  have same : row = parentRow := by simpa only [tuple, List.mem_cons, List.not_mem_nil, or_false, or_self] using member
  subst row
  rfl
private theorem tuple_widths : ∀ row ∈ tuple, row.children.length ≤ 2 := by
  intro row member
  have same : row = parentRow := by simpa only [tuple, List.mem_cons, List.not_mem_nil, or_false, or_self] using member
  rw [same, children]
  decide

private theorem carrier : ∀ edge ∈ tuple, edge.entry.key.constraint ∈ [annotation, top] := by
  intro edge member
  have same : edge = parentRow := by simpa only [tuple, List.mem_cons, List.not_mem_nil, or_false, or_self] using member
  subst edge
  have key : parentRow.entry.key.constraint = annotation := by cbv
  rw [key]
  exact List.mem_cons_self
private theorem normalize_fixed (input output : EqualityNormalize.Constraints)
    (prepared : EqualityNormalize.complete (EqualityNormalize.prepare input) = output)
    (fixed : EqualityNormalize.congruenceStep output = some output) :
    SourceCompactGuards.normalize input = some output := by
  simp only [SourceCompactGuards.normalize, SourceCompactGuards.arrayNormalize_eq,
    EqualityNormalize.mkEqConstraints, EqualityTermination.normalizationBound, EqualityTermination.saturationBound,
    prepared, EqualityNormalize.fixMaybe, fixed, ite_true, SymbolicEqualityBridge.resultClasses]
private theorem combined_live : SourceCurrentConjunctionEmptinessRows.combined
    (tuple.map SourceCurrentConjunctionEquality.edgeView) = some constraints := by
  rw [← SourceCurrentConjunctionTupleBounds.combined_edgeView]
  have guards : tuple.map (fun edge => edge.entry.key.constraint) = [annotation, annotation] := by cbv
  rw [guards]
  have fixed : EqualityNormalize.congruenceStep constraints = some constraints := by cbv
  have one := normalize_fixed constraints constraints (by cbv) fixed
  have both := normalize_fixed (constraints ++ constraints) constraints (by cbv) fixed
  change SourceCompactGuards.combineEqualities (some constraints)
    (SourceCompactGuards.combineEqualities (some constraints) (some [])) = some constraints
  have tail : SourceCompactGuards.combineEqualities (some constraints) (some []) = some constraints := by
    simpa only [constraints, SourceCompactGuards.combineEqualities, List.append_nil] using one
  rw [tail]
  simpa only [constraints, SourceCompactGuards.combineEqualities] using both
private theorem live_output {output after} (actual : SourceCurrentConjunctionRowsAllocation.Tuple tuple physical output after) :
    ∃ rows, output = some rows := by
  obtain ⟨observed, done, _valid, _ready, classes, _built, _growth, _fields⟩ :=
    SourceCurrentConjunctionEquality.fold_heap_correct tuple heap operations ready.valid ready.fields resident
  cases actual with
  | contradiction folded empty =>
      have same := Option.some.inj (Except.ok.inj (done.symm.trans folded))
      cases same
      have impossible := empty.symm.trans (classes.trans combined_live)
      cases impossible
  | live _ _ _ => exact ⟨_, rfl⟩

/-- Initial source and equality-field history construct a live full tuple worker with recursive class projections. -/
theorem constructed_live_tuple :
    (∃ entry body depth ordinary, child = .mu entry body depth ordinary) ∧
    ∃ rows after, ∃ actual : SourceCurrentConjunctionRowsAllocation.Tuple tuple physical (some rows) after,
      SourceCurrentConjunctionRowsAllocation.Effects physical after ∧
      SourceCurrentConjunctionRequirements.RowsReady after.heap rows ∧
      after.equality = (SourceCurrentConjunctionEquality.fold tuple operations).2 ∧
      Fits (SourceCurrentConjunctionTupleNumeric.forecast [annotation, top] 2 2 q) after.heap ∧
      SourceCurrentConjunctionTupleNumeric.OptionalBounds
        (SourceCurrentConjunctionTupleBounds.shapeThrough [annotation, top] 2) 2 2 (some rows) ∧
      ∀ work reader,
        SourceCurrentConjunctionProjectionResources.workerFuel
          (SourceCurrentConjunctionTupleBounds.shapeThrough [annotation, top] 2) ≤ work →
        SourceCurrentProjectionUnionResources.readFuel
          (SourceCurrentConjunctionTupleNumeric.forecast [annotation, top] 2 2 q) ≤ reader →
        SourceCurrentConjunctionRowsWorker.tuple work reader tuple physical = .done (some rows) after := by
  obtain ⟨output, after, actual, effects, rowsReady, finalFits, bounds, done⟩ :=
    SourceCurrentConjunctionTupleNumeric.complete tuple physical [annotation, top] 2 2 q ready resident tuple_closed
      tuple_same fits (by decide) tuple_widths carrier
  obtain ⟨rows, rfl⟩ := live_output actual
  have equality : after.equality = (SourceCurrentConjunctionEquality.fold tuple operations).2 := by
    cases actual <;> rfl
  exact ⟨child_mu, rows, after, actual, effects, rowsReady, equality, finalFits, bounds, done⟩
end MicroCFTA.ConjunctionTupleNumericIntegration

#check @MicroCFTA.ConjunctionTupleNumericIntegration.constructed_live_tuple
#print axioms MicroCFTA.ConjunctionTupleNumericIntegration.constructed_live_tuple
#print MicroCFTA.ConjunctionTupleNumericIntegration.constructed_live_tuple
