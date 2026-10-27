import MicroCFTA.SourceEqualityConstraintFieldLookup
import MicroCFTA.SourceCurrentConjunctionEmptinessRows
import MicroCFTA.SourceEqualityAnnotationHeap

/-!
# Allocated equality accessors in source conjunction tuples

The tuple fold demands the head accessor first. Contradiction stops before
any suffix operation. A live head demands the tail before combination.
The empty base uses an actual canonical constructor receipt. Physical
field availability grows with the separate equality-operation cache.
Pending publication, machine allocation, and GHC forcing stay separate.
-/
namespace MicroCFTA.SourceCurrentConjunctionEquality
open SourceEqualityConstraintAllocation
open SourceEqualityConstraintMemoAllocation (State Valid Grows)
local notation "EqValue" => SourceEqualityConstraintAllocation.Value
local notation "Raw" => SourceSymbolicIndex.Constraint
local notation "Allocated" => SourceEqualityConjoinAllocation.Constraint

/-- An original physical field is normalized and has an existing successful load. -/
def FieldAvailable (state : State) (original : Raw Formula) : Prop :=
  SourceEqualityGuardReadback.Cached original.equalities ∧
    ∃ value : Allocated Formula, SourceEqualityConstraintFieldLookup.load original state.constraints = .ok (some value)

/-- Physical edge keys retain field availability in the current equality cache. -/
def Fields (state : State) (heap : InternedConstructorTemplates.State Symbol (Raw Formula)) : Prop :=
  SourceEqualityAnnotationHeap.Heap (FieldAvailable state) heap

/-- Consecutive actual equality operations retain all allocation and completed-table receipts. -/
theorem grows_trans {before middle after : State} (first : Grows before middle) (second : Grows middle after) :
    Grows before after :=
  ⟨steps_trans first.constraints second.constraints, Cache.extends_trans first.combinations second.combinations,
    Cache.extends_trans first.descents second.descents⟩

/-- Existing successful field loads survive canonical cache growth without allocation. -/
theorem load_grows (original : Raw Formula) (before after : State) (growth : Grows before after)
    (value : Allocated Formula)
    (done : SourceEqualityConstraintFieldLookup.load original before.constraints = .ok (some value)) :
    SourceEqualityConstraintFieldLookup.load original after.constraints = .ok (some value) := by
  cases built : SourceEqualityPhysicalPayload.read original.equalities with
  | error message => simp only [SourceEqualityConstraintFieldLookup.load, built] at done; cases done
  | ok payload =>
      cases payload with
      | none => simpa only [SourceEqualityConstraintFieldLookup.load, built] using done
      | some records =>
          cases present : before.constraints.table (SourceEqualityPartialConstraintKey.key records) with
          | none => simp only [SourceEqualityConstraintFieldLookup.load, built, present] at done; cases done
          | some entry =>
              have retained := growth.constraint_growth _ _ present
              simpa only [SourceEqualityConstraintFieldLookup.load, built, present, retained] using done

/-- Field availability is a derived growing annotation, with no future-load premise. -/
theorem FieldAvailable.grows {before after : State} {original : Raw Formula}
    (available : FieldAvailable before original) (growth : Grows before after) : FieldAvailable after original := by
  obtain ⟨cached, value, loaded⟩ := available
  exact ⟨cached, value, load_grows original before after growth value loaded⟩

/-- Equality allocation retains every original physical edge's field availability. -/
theorem Fields.grows {before after : State} {heap : InternedConstructorTemplates.State Symbol (Raw Formula)}
    (fields : Fields before heap) (growth : Grows before after) : Fields after heap := by
  intro key edge present
  exact (fields key edge present).grows growth

/-- Current successful loads derive readiness, exact raw readback, and their original constructor receipt. -/
theorem FieldAvailable.receipts {state : State} {original : Raw Formula}
    (available : FieldAvailable state original) (valid : Valid state) :
    ∃ value : Allocated Formula, SourceEqualityConstraintFieldLookup.load original state.constraints = .ok (some value) ∧
      Ready state.constraints value.stored ∧ SourceEqualityConjoinAllocation.readback value = original ∧
      SourceEqualityPhysicalPayload.read original.equalities = .ok value.stored.payload := by
  obtain ⟨cached, value, loaded⟩ := available
  have checked := SourceEqualityConstraintFieldLookup.load_ready original state.constraints valid.constraints cached value loaded
  exact ⟨value, loaded, checked.1, checked.2,
    SourceEqualityConstraintFieldLookup.load_constructor_receipt original state.constraints cached value loaded⟩

/-- Missing field representation stays separate from the accessor's original checked errors. -/
noncomputable def accessor (original : Raw Formula) (before : State) : Except String (Option EqValue) × State :=
  match SourceEqualityConstraintFieldLookup.load original before.constraints with
  | .error message => (.error message, before)
  | .ok none => (.ok none, before)
  | .ok (some value) =>
      let actual := SourceEqualityAccessorAllocation.equalities value.stored value.guard before
      (actual.1.map some, actual.2)

/-- One available original field derives the actual accessor result and exact physical classes. -/
theorem accessor_correct (original : Raw Formula) (before : State) (valid : Valid before)
    (available : FieldAvailable before original) :
    ∃ result, (accessor original before).1 = .ok (some result) ∧ Valid (accessor original before).2 ∧
      Ready (accessor original before).2.constraints result ∧
      SourceEqualityInheritedPayload.classes result.payload = SourceCompactGuards.sourceEqualities original ∧
      SourceEqualityPhysicalPayload.read (SourceCompactGuards.sourceEqualities original) = .ok result.payload ∧
      Grows before (accessor original before).2 := by
  obtain ⟨value, loaded, valueReady, readback, built⟩ := available.receipts valid
  obtain ⟨result, done, finalValid, resultReady, classes, growth⟩ :=
    SourceEqualityAccessorAllocation.equalities_correct value.stored value.guard before valid valueReady
  have own := SourceEqualityAccessorAllocation.own_of_equalities value.stored value.guard before valid valueReady
    original.equalities available.1 built result done
  have same : SourceEqualityAccessorAllocation.constraint value.stored value.guard = original := readback
  simp only [accessor, loaded, done, Except.map]
  refine ⟨result, rfl, finalValid, resultReady, ?_, ?_, growth⟩
  · simpa only [same] using classes
  · simpa only [SourceEqualityPhysicalPayload.own, same] using own

/-- The reached EmptyConstraints base uses the actual canonical constructor. -/
def canonicalEmpty (before : State) : Except String (Option EqValue) × State :=
  let actual := construct (some []) before.constraints
  (actual.1.map some, {before with constraints := actual.2})

/-- The actual empty constructor derives its canonical identity, readiness, and allocation trace. -/
theorem canonicalEmpty_correct (before : State) (valid : Valid before) :
    ∃ result, (canonicalEmpty before).1 = .ok (some result) ∧ Valid (canonicalEmpty before).2 ∧
      Ready (canonicalEmpty before).2.constraints result ∧
      SourceEqualityInheritedPayload.classes result.payload = some [] ∧
      SourceEqualityPhysicalPayload.read (some []) = .ok result.payload ∧
      Grows before (canonicalEmpty before).2 := by
  obtain ⟨result, cache, done, _, ready, steps, built, classes⟩ :=
    construct_complete (some []) SourceEqualityGuardReadback.empty_cached before.constraints valid.constraints
  simp only [canonicalEmpty, done, Except.map]
  exact ⟨result, rfl, valid.steps cache steps, ready, classes, built,
    ⟨steps, Cache.extends_refl _, Cache.extends_refl _⟩⟩

/-- The semantic edge view uses the complete original source equality accessor. -/
noncomputable def edgeView (edge : InternedConstructorTemplates.EdgeValue Symbol (Raw Formula)) :
    SourceCurrentConjunctionEmptinessRows.Edge (InternedConstructorTemplates.Value Symbol (Raw Formula)) Symbol :=
  ⟨edge.entry.key.symbol, edge.children, SourceCompactGuards.sourceEqualities edge.entry.key.constraint⟩

/-- Demand each head accessor before its tail, and stop at the first head contradiction. -/
noncomputable def fold : List (InternedConstructorTemplates.EdgeValue Symbol (Raw Formula)) →
    State → Except String (Option EqValue) × State
  | [], before => canonicalEmpty before
  | edge :: rest, before =>
      let head := accessor edge.entry.key.constraint before
      match head.1 with
      | .error message => (.error message, head.2)
      | .ok none => (.ok none, head.2)
      | .ok (some .contradiction) => (.ok (some .contradiction), head.2)
      | .ok (some value@(.live _ _)) =>
          let tail := fold rest head.2
          match tail.1 with
          | .error message => (.error message, tail.2)
          | .ok none => (.ok none, tail.2)
          | .ok (some remaining) =>
              let combined := SourceEqualityConstraintMemoAllocation.combine value remaining tail.2
              (combined.1.map some, combined.2)

/-- A contradictory head returns its exact accessor state without any suffix operation. -/
theorem fold_stop (edge : InternedConstructorTemplates.EdgeValue Symbol (Raw Formula)) (rest : List _)
    (before : State) (done : (accessor edge.entry.key.constraint before).1 = .ok (some .contradiction)) :
    fold (edge :: rest) before = (.ok (some .contradiction), (accessor edge.entry.key.constraint before).2) := by
  simp only [fold, done]

/-- Actual tuple folding derives all ready allocation receipts and the exact source combined classes. -/
theorem fold_correct (tuple : List (InternedConstructorTemplates.EdgeValue Symbol (Raw Formula)))
    (before : State) (valid : Valid before)
    (available : ∀ edge ∈ tuple, FieldAvailable before edge.entry.key.constraint) :
    ∃ result, (fold tuple before).1 = .ok (some result) ∧ Valid (fold tuple before).2 ∧
      Ready (fold tuple before).2.constraints result ∧
      SourceEqualityInheritedPayload.classes result.payload = SourceCurrentConjunctionEmptinessRows.combined (tuple.map edgeView) ∧
      SourceEqualityPhysicalPayload.read (SourceCurrentConjunctionEmptinessRows.combined (tuple.map edgeView)) = .ok result.payload ∧
      Grows before (fold tuple before).2 := by
  induction tuple generalizing before with
  | nil => exact canonicalEmpty_correct before valid
  | cons edge rest ih =>
      obtain ⟨head, headDone, headValid, headReady, headClasses, headRead, headGrowth⟩ :=
        accessor_correct edge.entry.key.constraint before valid (available edge List.mem_cons_self)
      cases head with
      | contradiction =>
          rw [fold_stop edge rest before headDone]
          have classes : SourceCurrentConjunctionEmptinessRows.combined ((edge :: rest).map edgeView) = none := by
            change SourceCompactGuards.combineEqualities (SourceCompactGuards.sourceEqualities edge.entry.key.constraint)
              (SourceCurrentConjunctionEmptinessRows.combined (rest.map edgeView)) = none
            rw [← headClasses]
            rfl
          exact ⟨.contradiction, rfl, headValid, headReady, classes.symm, by rw [classes]; rfl, headGrowth⟩
      | live identity records =>
          obtain ⟨tail, tailDone, tailValid, tailReady, tailClasses, tailRead, tailGrowth⟩ :=
            ih (accessor edge.entry.key.constraint before).2 headValid
              (fun value member => (available value (List.mem_cons_of_mem _ member)).grows headGrowth)
          obtain ⟨result, done, finalValid, resultReady, payload, finalGrowth⟩ :=
            SourceEqualityConstraintMemoAllocation.combine_correct (.live identity records) tail (fold rest (accessor edge.entry.key.constraint before).2).2
              tailValid (headReady.grows tailGrowth.constraint_growth) tailReady
          have actual : fold (edge :: rest) before =
              ((SourceEqualityConstraintMemoAllocation.combine (.live identity records) tail (fold rest (accessor edge.entry.key.constraint before).2).2).1.map some,
                (SourceEqualityConstraintMemoAllocation.combine (.live identity records) tail (fold rest (accessor edge.entry.key.constraint before).2).2).2) := by
            simp only [fold, headDone, tailDone]
          rw [actual]
          refine ⟨result, by simp only [done, Except.map], finalValid, resultReady, ?_, ?_,
            grows_trans headGrowth (grows_trans tailGrowth finalGrowth)⟩
          · have resultClasses := read_classes _ (SourceEqualityGuardReadback.combine_cached _ _) result.payload payload
            change SourceEqualityInheritedPayload.classes result.payload =
              SourceCompactGuards.combineEqualities (SourceCompactGuards.sourceEqualities edge.entry.key.constraint)
                (SourceCurrentConjunctionEmptinessRows.combined (rest.map edgeView))
            simpa only [headClasses, tailClasses] using resultClasses
          · change SourceEqualityPhysicalPayload.read
              (SourceCompactGuards.combineEqualities (SourceCompactGuards.sourceEqualities edge.entry.key.constraint)
                (SourceCurrentConjunctionEmptinessRows.combined (rest.map edgeView))) = .ok result.payload
            simpa only [SourceEqualityInheritedPayload.combine, headClasses, tailClasses] using payload

/-- Actual resident tuple edges supply all field premises from the physical heap annotation. -/
theorem fold_heap_correct (tuple : List (InternedConstructorTemplates.EdgeValue Symbol (Raw Formula)))
    (heap : InternedConstructorTemplates.State Symbol (Raw Formula)) (before : State) (valid : Valid before)
    (fields : Fields before heap)
    (resident : ∀ edge ∈ tuple, InternedEdgeResidency.EdgeResident heap edge) :
    ∃ result, (fold tuple before).1 = .ok (some result) ∧ Valid (fold tuple before).2 ∧
      Ready (fold tuple before).2.constraints result ∧
      SourceEqualityInheritedPayload.classes result.payload = SourceCurrentConjunctionEmptinessRows.combined (tuple.map edgeView) ∧
      SourceEqualityPhysicalPayload.read (SourceCurrentConjunctionEmptinessRows.combined (tuple.map edgeView)) = .ok result.payload ∧
      Grows before (fold tuple before).2 ∧ Fields (fold tuple before).2 heap := by
  obtain ⟨result, done, finalValid, ready, classes, built, growth⟩ :=
    fold_correct tuple before valid (fun edge member => fields edge.entry.key edge (resident edge member))
  exact ⟨result, done, finalValid, ready, classes, built, growth, fields.grows growth⟩

end MicroCFTA.SourceCurrentConjunctionEquality
