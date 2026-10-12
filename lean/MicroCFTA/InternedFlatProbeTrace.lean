import MicroCFTA.InternedFlatProbeHeap

/-!
# Derived body/probe costs for complete source constructor histories

The history starts with empty actual caches. Each callback can capture any
earlier available record. Nested captured Mu depth is unrestricted. Source
construction derives all cache facts and the body/probe cost relation.
-/
namespace MicroCFTA.InternedFlatProbeTrace
open InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedConstructionProvenance InternedTemplateProvenance
open InternedNestedFacts InternedNestedProvenance
open InternedFlatProbeCosts InternedFlatProbeHeap

/-- Fixed captured leaves are exactly the inputs required by the existing template compiler. -/
theorem captured_inputs (values : List (Value Symbol Guard)) :
    manyCaptures (values.map Template.captured) = values := by
  induction values with
  | nil => simp [manyCaptures]
  | cons first rest ih => simp [manyCaptures, captures, ih]

/-- The ordinary callback declares precisely its original captured records. -/
theorem template_inputs (symbol : Symbol) (constraint : Guard) (values : List (Value Symbol Guard)) :
    captures (template symbol constraint values) = values := by
  simp [template, captures, edgeCaptures, manyCaptures, captured_inputs]

/-- Actual source calls use only available captures from the preceding canonical cache. -/
inductive History {Symbol Guard : Type} [DecidableEq (EdgeKey Symbol Guard)] : State Symbol Guard → Prop where
  | empty : History empty
  | binder {state : State Symbol Guard} (before : History state) (symbol : Symbol) (constraint : Guard)
      (captured : List (Value Symbol Guard)) (available : Values state captured) :
      History (internMu (template symbol constraint captured) state).2

/-- Every finite actual source history derives the stored relation together with full cache provenance. -/
theorem history_correct [DecidableEq (EdgeKey Symbol Guard)] {state : State Symbol Guard} (history : History state) :
    Facts state ∧ Covered [] state ∧ Heap state := by
  induction history with
  | empty => exact ⟨empty_facts, empty_correct.2, empty_heap⟩
  | @binder beforeState before symbol constraint captured inputs ih =>
      have declared : ∀ value ∈ captures (template symbol constraint captured), Available beforeState value := by
        simpa only [template_inputs, Values] using inputs
      have checked := internMu_available (template symbol constraint captured) beforeState ih.1.coherent ih.2.1 ih.1.cached declared
      have retained := internMu_properties symbol constraint captured beforeState ih.1 inputs ih.2.2
      have covered := (InternedRecordCoherence.internMu_correct (template symbol constraint captured) beforeState ih.1.coherent ih.2.1).2
      exact ⟨⟨checked.1, checked.2.1, retained.2⟩, covered, retained.1⟩

/-- An actual canonical payload read from a generated history has the derived body/probe cost relation. -/
theorem stored_related [DecidableEq (EdgeKey Symbol Guard)] {state : State Symbol Guard} (history : History state)
    (key : InternedBinderProtocol.NodeKey) (value : Value Symbol Guard) (stored : state.nodeRecords key = some value) :
    Related value := (history_correct history).2.2 key value stored

/-- A later source call inherits the same result law on both cache hits and fresh construction. -/
theorem next_related [DecidableEq (EdgeKey Symbol Guard)] {state : State Symbol Guard} (history : History state)
    (symbol : Symbol) (constraint : Guard) (captured : List (Value Symbol Guard)) (inputs : Values state captured) :
    Related (internMu (template symbol constraint captured) state).1 :=
  internMu_related symbol constraint captured state (history_correct history).1 inputs (history_correct history).2.2

end MicroCFTA.InternedFlatProbeTrace
