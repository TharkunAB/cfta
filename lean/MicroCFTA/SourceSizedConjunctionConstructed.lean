import MicroCFTA.SourcePruningEnumerationSelectedSource
import MicroCFTA.SourceColdSharedRowsSizedNative
import MicroCFTA.SourceSizedConjunctionPreparation
import MicroCFTA.SourceEqualityConjoinAllocation

/-!
# Constructed equality fields at the actual conjunction input table

Completed normalization and allocation supply ready equality fields. Selected
preparation and the actual cold worklist retain checked input annotations.
The existing Sized conversion then supplies ActiveOption at every stored row.
No final table, trace, field inventory, or completed preparation is supplied
to the constructed endpoint.

The endpoint retains the existing SyntaxValid input-annotation condition.
Raw Syntax stores arbitrary Constraint values. Its makeEdge call copies those
values; it does not normalize them. Connecting all input annotations to actual
Constraint/equality constructors remains separate. This file does not assert
that arbitrary raw fields are normalized, or close native storage/Int laws.
-/
namespace MicroCFTA.SourceSizedConjunctionConstructed
open Language SourceGuards SourceObservations SourceSymbolicIndex Std
open InternedConstructorTemplates InternedProbeProvenance
open SourceFreshOrdinaryColdSharedRows (Trace keys)
open SourcePreparedSharedRows (encode)
attribute [local instance] lexOrd

variable {Symbol Guard Formula : Type}

/-- The existing Sized conversion preserves exact raw lookup order and fields. -/
theorem sized_lookup
    (raw : List (SourceInternedRows.State × List (SourceInternedRows.Transition Symbol Guard)))
    (key : SourceInternedRows.State) :
    SourceSizedFiniteKeys.lookup (SourceColdSharedRows.sizedTable raw) key =
      (SourceInternedRows.lookup raw key).map
        (fun edge => (⟨edge.label, edge.children, edge.constraint⟩ :
          SourceSizedDecided.Row SourceInternedRows.State Symbol Guard)) := by
  simp only [SourceSizedFiniteKeys.lookup, SourceColdSharedRows.sizedTable,
    SourceInternedRows.lookup, List.flatMap_map, List.map_flatMap]
  apply TablePosition.flatMap_congr
  intro entry _
  cases entry with
  | mk owner edges =>
      by_cases same : owner = key <;> simp [same]

/-- The exact raw map-key inventory survives the existing Sized conversion. -/
theorem sized_keys
    (raw : List (SourceInternedRows.State × List (SourceInternedRows.Transition Symbol Guard))) :
    SourceDenseRows.keys (SourceColdSharedRows.sizedTable raw) = SourceDenseRows.keys raw := by
  have sequence : (SourceColdSharedRows.sizedTable raw).map Prod.fst = raw.map Prod.fst := by
    induction raw with
    | nil => rfl
    | cons entry rest ih =>
        cases entry with
        | mk owner edges =>
            change owner :: (SourceColdSharedRows.sizedTable rest).map Prod.fst = owner :: rest.map Prod.fst
            exact congrArg (List.cons owner) ih
  unfold SourceDenseRows.keys
  rw [sequence]

/-- A resident raw-row invariant transfers to the actual Sized table, not a replacement table. -/
theorem sized_property
    (raw : List (SourceInternedRows.State × List (SourceInternedRows.Transition Symbol Guard)))
    (property : Guard → Prop)
    (checked : ∀ key edge, edge ∈ SourceInternedRows.lookup raw key → property edge.constraint) :
    ∀ key row, row ∈ SourceSizedFiniteKeys.lookup (SourceColdSharedRows.sizedTable raw) key →
      property row.constraint := by
  intro key row member
  rw [sized_lookup] at member
  obtain ⟨edge, present, rfl⟩ := List.mem_map.mp member
  exact checked key edge present

/-- Actual raw child closure also transfers without changing the declared carrier. -/
theorem sized_closed
    (raw : List (SourceInternedRows.State × List (SourceInternedRows.Transition Symbol Guard)))
    (closed : SourceDenseRowsRestrict.Closed raw) :
    SourceSizedFiniteKeys.Closed (SourceColdSharedRows.sizedTable raw) := by
  intro key row member child childIn
  rw [sized_lookup] at member
  obtain ⟨edge, present, rfl⟩ := List.mem_map.mp member
  rw [sized_keys]
  exact closed key edge present child childIn

/-- Actual normalization followed by stored-field construction derives readiness and ActiveOption. -/
theorem normalized_construct (paths : EqualityNormalize.Constraints) (guard : SourceGuards.Guard Formula)
    (before : SourceEqualityConstraintMemoAllocation.State)
    (valid : SourceEqualityConstraintMemoAllocation.Valid before) :
    ∃ value after,
      SourceEqualityConjoinAllocation.construct (SourceCompactGuards.normalize paths) guard before = (.ok value, after) ∧
      SourceEqualityConstraintMemoAllocation.Valid after ∧
      SourceEqualityConstraintAllocation.Ready after.constraints value.stored ∧
      SourceEqualityConjoinAllocation.readback value = ⟨SourceCompactGuards.normalize paths, guard⟩ ∧
      SourceCompactGuards.ActiveOption (SourceEqualityConjoinAllocation.readback value).equalities := by
  obtain ⟨value, after, done, afterValid, ready, readback, cached, _, _⟩ :=
    SourceEqualityConjoinAllocation.construct_complete (SourceCompactGuards.normalize paths)
      (SourceEqualityGuardReadback.normalize_cached paths) guard before valid
  exact ⟨value, after, done, afterValid, ready, readback, SourceEqualityGuardReadback.active cached⟩

/-- A normalized stored constructor supplies the leaf annotation required by selected_table. -/
theorem normalized_leaf (paths : EqualityNormalize.Constraints) (guard : SourceGuards.Guard Formula)
    (symbol : Symbol) (before : SourceEqualityConstraintMemoAllocation.State)
    (valid : SourceEqualityConstraintMemoAllocation.Valid before) :
    ∃ value after,
      SourceEqualityConjoinAllocation.construct (SourceCompactGuards.normalize paths) guard before = (.ok value, after) ∧
      SourceEqualityConstraintMemoAllocation.Valid after ∧
      InternedFreshOrdinaryConstraintHeap.SyntaxValid
        (fun constraint : Constraint Formula => SourceCompactGuards.ActiveOption constraint.equalities)
        (.node [.mk symbol (SourceEqualityConjoinAllocation.readback value) []]) := by
  obtain ⟨value, after, done, afterValid, _, _, active⟩ := normalized_construct paths guard before valid
  exact ⟨value, after, done, afterValid, active, trivial, trivial⟩

/-- An actual successful stored-field conjunction derives its output invariant from ready operands. -/
theorem conjoin_active [DecidableEq (SourceGuards.Guard Formula)]
    (le : SourceGuards.Guard Formula → SourceGuards.Guard Formula → Bool)
    (first second : SourceEqualityConjoinAllocation.Constraint Formula)
    (before : SourceEqualityConstraintMemoAllocation.State)
    (valid : SourceEqualityConstraintMemoAllocation.Valid before)
    (firstReady : SourceEqualityConstraintAllocation.Ready before.constraints first.stored)
    (secondReady : SourceEqualityConstraintAllocation.Ready before.constraints second.stored)
    (result : SourceEqualityConjoinAllocation.Constraint Formula)
    (done : (SourceEqualityConjoinAllocation.conjoin le first second before).1 = .ok result) :
    SourceCompactGuards.ActiveOption (SourceEqualityConjoinAllocation.readback result).equalities :=
  SourceEqualityGuardReadback.active
    (SourceEqualityConjoinAllocation.result_readback le first second before valid firstReady secondReady result done).1

/-- The raw field type alone cannot supply normalized constructor provenance. -/
theorem singleton_not_active :
    ¬SourceCompactGuards.ActiveOption (some ([[[0]]] : EqualityNormalize.Constraints)) := by
  intro active
  obtain ⟨left, leftIn, right, rightIn, different⟩ := active [[[0]]] rfl [[0]] (by simp)
  exact different ((List.mem_singleton.mp leftIn).trans (List.mem_singleton.mp rightIn).symm)

section Selected
variable [DecidableEq Formula] [Ord (Label Formula)]
  [DecidableEq (EdgeKey (Label Formula) (Constraint Formula))]

/-- Actual source construction, selected preparation, and cold collection derive the conjunction table fields.
The only annotation premise is at original Syntax, not the resulting table or worker. -/
theorem selected_table
    (expression : InternedNestedConstruction.Syntax (Label Formula) (Constraint Formula))
    (annotations : InternedFreshOrdinaryConstraintHeap.SyntaxValid
      (fun constraint => SourceCompactGuards.ActiveOption constraint.equalities) expression)
    (width : Nat) (emptyGuard : Constraint Formula)
    (conjoin : Constraint Formula → Constraint Formula → Constraint Formula) :
    ∃ value source bound prepared,
    ∃ middle : SourceRecursiveIntersectionThunks.State width (Label Formula) (Constraint Formula),
    ∃ rows final outer inner,
      InternedFreshOrdinaryConstruction.build expression [] empty = .done value source ∧
      (∀ extra, SourcePruningEnumerationSelectedValue.run (bound + extra) value source =
        .done prepared middle.machine.heap) ∧
      SourceFreshOrdinaryNativeCallback.Ready emptyGuard conjoin middle ∧
      Trace middle.machine.heap (fun _ => none) [prepared] rows final ∧
      (∀ largerOuter largerInner, outer ≤ largerOuter → inner ≤ largerInner →
        SourceFreshOrdinaryColdSharedRows.collect largerOuter largerInner middle.machine.heap
          (fun _ => none) [prepared] = .done rows final) ∧
      (let original := SourceColdSharedRows.sizedTable
          (SourceColdSharedRows.table rows (keys final rows) prepared)
       SourceSizedFiniteKeys.Closed original ∧
       SourceFTAValidation.validateRows (encode prepared) (SourceSizedFiniteKeys.interpreted original (fun _ _ => true)) =
         .ok (SourceSizedFiniteKeys.interpreted original (fun _ _ => true)) ∧
       (∀ owner row, row ∈ SourceSizedFiniteKeys.lookup original owner →
         SourceCompactGuards.ActiveOption row.constraint.equalities) ∧
       (∀ (formulas : Formulas Formula) (solver : Entailment Formula) term,
         Accepts (SourceSizedConjunctionGuarded.originalGraph formulas solver original) (encode prepared) term ↔
           InternedGuardedSyntax.evaluate (acceptsConstraint formulas solver) [] expression term) ∧
       (∀ output, SourceSizedConjunctionPreparation.prepare original (encode prepared) = some output →
         ∀ (formulas : Formulas Formula) (solver : Entailment Formula) term,
           Accepts (SourceSizedConjunctionLanguage.graph (SourceSizedFiniteKeys.lookup output)) [encode prepared] term ↔
             InternedGuardedSyntax.evaluate (acceptsConstraint formulas solver) [] expression term)) := by
  let property := fun constraint : Constraint Formula => SourceCompactGuards.ActiveOption constraint.equalities
  obtain ⟨value, source, bound, prepared, middle, built, running, ready, _, _, _, _, available,
      closedValue, heap, language⟩ :=
    SourcePruningEnumerationSelectedSource.prepare property expression annotations width emptyGuard conjoin
  obtain ⟨rows, final, outer, inner, trace, stable, metadata⟩ :=
    SourceFreshOrdinaryColdNativeTable.collect emptyGuard conjoin middle ready prepared available closedValue
  obtain ⟨_, _, _, _, _, supported, resident, _, _, _, domain, rawClosed, _⟩ := metadata
  have inputs : SourceColdSharedRows.Inputs middle.machine.heap [prepared] := by
    intro child member
    simpa only [List.mem_singleton.mp member] using And.intro available closedValue
  have finalHeap := trace.constraint_heap property ready.semantic ready.covered heap inputs
  let raw := SourceColdSharedRows.table rows (keys final rows) prepared
  let original := SourceColdSharedRows.sizedTable raw
  have active : ∀ owner row, row ∈ SourceSizedFiniteKeys.lookup original owner →
      SourceCompactGuards.ActiveOption row.constraint.equalities :=
    sized_property raw property
      (SourceFreshOrdinaryColdSharedRows.table_constraints property final finalHeap rows resident
        (keys final rows) domain prepared)
  have closed : SourceSizedFiniteKeys.Closed original := sized_closed raw rawClosed
  have present : encode prepared ∈ SourceDenseRows.keys original := by
    change encode prepared ∈ SourceDenseRows.keys (SourceColdSharedRows.sizedTable raw)
    rw [sized_keys]
    exact SourceFreshOrdinaryColdCyclic.root_key rows (keys final rows) prepared domain supported
  have valid := SourceSizedStructuralKeys.validation_of_closed original (encode prepared) present closed
  have exactLanguage (formulas : Formulas Formula) (solver : Entailment Formula)
      (term : Term (Label Formula)) :
      Accepts (SourceSizedConjunctionGuarded.originalGraph formulas solver original) (encode prepared) term ↔
        InternedGuardedSyntax.evaluate (acceptsConstraint formulas solver) [] expression term := by
    let ambient : InternedGuardedLanguage.Env (Label Formula) := fun _ _ => False
    change Accepts (SourceSizedDecided.automaton (SourceSizedFiniteKeys.lookup (SourceColdSharedRows.sizedTable raw))
      (acceptsConstraint formulas solver)) (encode prepared) term ↔ _
    rw [SourceColdSharedRows.sized_graph]
    exact (SourceFreshOrdinaryColdGuardedExact.trace_table_exact
      middle.machine.heap final prepared rows trace ready.semantic ready.covered ready.guarded ready.budget
      available closedValue (keys final rows) domain (acceptsConstraint formulas solver) ambient term).trans
        (language (acceptsConstraint formulas solver) ambient term)
  refine ⟨value, source, bound, prepared, middle, rows, final, outer, inner, built, running,
    ready, trace, stable, closed, valid, active, exactLanguage, ?_⟩
  intro output success formulas solver term
  exact (SourceSizedConjunctionPreparation.root_language formulas solver original active
    (encode prepared) output success term).trans (exactLanguage formulas solver term)

end Selected
end MicroCFTA.SourceSizedConjunctionConstructed
