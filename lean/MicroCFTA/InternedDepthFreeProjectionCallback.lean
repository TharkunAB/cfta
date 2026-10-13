import MicroCFTA.InternedDepthFreeProjectionSource
import MicroCFTA.InternedFreshOrdinaryDepthHeap

/-!
# Derived deep observations for full ordinary-root callbacks

One symbolic full-syntax evaluation determines fixed deep captures and
the supplied local contribution. The actual callback theorem discharges
the deep observation field for ordinary-root bodies with arbitrary nested
children. It assumes no recursive depth/deep observation equation.
-/
namespace MicroCFTA.InternedDepthFreeProjectionCallback
open InternedConstructorTemplates InternedProbeProvenance
open InternedNestedConstruction (Syntax EdgeSyntax Outcome)
open InternedBinderProtocol (Reference)
open InternedDepthSemantics
open InternedDepthFreeProjectionSource (literal)
open InternedFreshOrdinaryContext

/-- Evaluate the complete body with a local distinct from all captured references. -/
def symbolic (body : Syntax Symbol Guard) (names : List Reference) : Shape (Sum Unit Reference) :=
  evaluate body (literal (.inl ()) :: (names.map literal).map (Shape.map Sum.inr))

/-- Substituting any literal argument preserves the complete computed shape. -/
theorem evaluate_supplied (body : Syntax Symbol Guard) (names : List Reference) (argument : Reference) :
    evaluate body ((argument :: names).map literal) =
      (symbolic body names).map (InternedProfileCallbackForm.supply argument) := by
  have mapped := evaluate_map (InternedProfileCallbackForm.supply argument) body
    (literal (Sum.inl ()) :: (names.map literal).map (Shape.map Sum.inr))
  have inputs : (literal (Sum.inl ()) :: (names.map literal).map (Shape.map Sum.inr)).map
      (Shape.map (InternedProfileCallbackForm.supply argument)) = (argument :: names).map literal := by
    simp [literal, Shape.map, InternedProfileCallbackForm.supply, List.map_map, Function.comp_def]
  simpa only [inputs, symbolic] using mapped

/-- The syntax determines all fixed deep captures. -/
def captured (body : Syntax Symbol Guard) (names : List Reference) : List Reference :=
  InternedProfileCallbackForm.captures (symbolic body names).deep

/-- The syntax determines whether its supplied argument occurs below a constructor boundary. -/
def uses (body : Syntax Symbol Guard) (names : List Reference) : Bool :=
  InternedProfileCallbackForm.usesArgument (symbolic body names).deep

/-- The pure deep observation has the exact captured-or-supplied membership form. -/
theorem deep_form (body : Syntax Symbol Guard) (names : List Reference) (argument name : Reference) :
    name ∈ (evaluate body ((argument :: names).map literal)).deep ↔
      name ∈ InternedRootProfile.response (captured body names) (uses body names) argument := by
  rw [evaluate_supplied]
  simp only [Shape.map, captured, uses, InternedProfileCallbackForm.supplied_member,
    InternedProfileCallbackForm.response_member]

/-- Actual normalized node callbacks derive the depth heap's required deep observation. -/
theorem callback_observed [DecidableEq (EdgeKey Symbol Guard)] (edges : List (EdgeSyntax Symbol Guard))
    (names : List Reference) (argument : Reference) (state : State Symbol Guard)
    (context : Context state (names.map Value.reference)) (available : Available state (.reference argument))
    (value : Value Symbol Guard) (after : State Symbol Guard)
    (completed : InternedFreshOrdinaryFacts.callback (.node edges) (names.map Value.reference) argument state = .done value after) :
    InternedFreshOrdinaryDepthHeap.Observed (captured (.node edges) names) (uses (.node edges) names) argument value := by
  intro name
  exact (InternedDepthFreeProjectionSource.callback_node_deep edges names argument state context available
    value after completed name).trans (deep_form (.node edges) names argument name)

end MicroCFTA.InternedDepthFreeProjectionCallback
