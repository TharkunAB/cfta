import MicroCFTA.InternedFreshOrdinaryStoredCosts
import MicroCFTA.InternedOccurrenceCostSupport

/-!
# Lexical inputs for positive stored-plan retention

Closed captures keep their original empty test. Each reference slot keeps
its supplied occurrence costs. A fresh symbolic local shadows the original
binder name and leaves every other supplied occurrence external.
-/
namespace MicroCFTA.InternedStoredCostInputs
open InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedStoredSubstitution
open InternedDepthSemantics (Shape)
open InternedOccurrenceCostSemantics (rename)
open InternedBinderProtocol (Reference)

/-- The positive occurrence costs supplied for each original reference. -/
abbrev Meanings (Atom : Type) := Reference → List (Atom × Nat)

/-- The prepared lexical slots retain closed shapes and reference meanings. -/
structure Inputs (context : List (Value Symbol Guard)) (locals : List Reference)
    (shapes : List (Shape Atom)) (costs : List (List (Atom × Nat))) (meanings : Meanings Atom) : Prop where
  coherent : InternedDepthSemanticProjections.CoherentMany shapes
  support : InternedOccurrenceCostSupport.Inputs shapes costs
  closed : ∀ value ∈ context, value.free = [] →
    (shapes[locals.length + slot context value]?.getD {}).isEmpty = (value.referenceOf == .empty)
  reference : ∀ name, Value.reference name ∈ context →
    InternedOccurrenceCostSemantics.evaluate (encode context locals (.reference name)) shapes costs = meanings name
  positive : ∀ name, meanings name ≠ []

/-- A fresh local has one zero-cost occurrence; captures use distinct external names. -/
def bindMeanings (own : Reference) (meanings : Meanings Atom) : Meanings (Sum Unit Atom) :=
  fun name => if name = own then [(Sum.inl (), 0)] else rename Sum.inr (meanings name)

/-- Renamed optional shape slots retain the empty fallback. -/
theorem map_shape_slot (function : Atom → Other) (shapes : List (Shape Atom)) (index : Nat) :
    ((shapes.map (Shape.map function))[index]?.getD {}) = (shapes[index]?.getD {}).map function := by
  cases found : shapes[index]? <;> simp [List.getElem?_map, found, Shape.map]

/-- Renamed optional cost slots retain the empty fallback. -/
theorem map_cost_slot (function : Atom → Other) (costs : List (List (Atom × Nat))) (index : Nat) :
    ((costs.map (rename function))[index]?.getD []) = rename function (costs[index]?.getD []) := by
  cases found : costs[index]? <;> simp [List.getElem?_map, found, rename]

/-- Extending the prepared lexical prefix preserves every required input fact. -/
theorem local_inputs (context : List (Value Symbol Guard)) (locals : List Reference)
    (shapes : List (Shape Atom)) (costs : List (List (Atom × Nat))) (meanings : Meanings Atom)
    (inputs : Inputs context locals shapes costs meanings) (own : Reference) :
    Inputs context (own :: locals)
      (⟨[Sum.inl ()], [], false, 0⟩ :: shapes.map (Shape.map Sum.inr))
      ([(Sum.inl (), 0)] :: costs.map (rename Sum.inr)) (bindMeanings own meanings) := by
  refine ⟨InternedDepthSemanticProjections.local_coherent shapes inputs.coherent,
    InternedOccurrenceCostSupport.local_inputs shapes costs inputs.support, ?_, ?_, ?_⟩
  · intro value member closed
    simpa only [List.length_cons, Nat.add_right_comm locals.length 1, List.getElem?_cons_succ, map_shape_slot,
      InternedDepthSemantics.isEmpty_map] using inputs.closed value member closed
  · intro name member
    have original := inputs.reference name member
    by_cases same : name = own
    · subst name
      simp [encode, Value.free, List.findIdx?_cons, InternedOccurrenceCostSemantics.evaluate, bindMeanings]
    · cases found : locals.findIdx? (· == name) with
      | none =>
          simp only [encode, Value.free, List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte, found,
            InternedOccurrenceCostSemantics.evaluate] at original
          simp only [encode, Value.free, List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte,
            List.findIdx?_cons, beq_eq_false_iff_ne.mpr (Ne.symm same), found, Option.map_none,
            bindMeanings, same, InternedOccurrenceCostSemantics.evaluate, List.length_cons,
            Nat.add_right_comm locals.length 1, List.getElem?_cons_succ, map_cost_slot, original]
      | some index =>
          simp only [encode, Value.free, List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte, found,
            InternedOccurrenceCostSemantics.evaluate] at original
          simp only [encode, Value.free, List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte,
            List.findIdx?_cons, beq_eq_false_iff_ne.mpr (Ne.symm same), found, Option.map_some,
            bindMeanings, same, InternedOccurrenceCostSemantics.evaluate,
            List.getElem?_cons_succ, map_cost_slot, original]
  · intro name
    by_cases same : name = own
    · simp [bindMeanings, same]
    · simpa [bindMeanings, same, rename] using inputs.positive name

end MicroCFTA.InternedStoredCostInputs
