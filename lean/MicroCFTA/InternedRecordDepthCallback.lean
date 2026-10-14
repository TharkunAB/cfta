import MicroCFTA.InternedRecordDepthSource

/-!
# Callback observations with captured records

The symbolic local is distinct from all names in the captured records.
Substitution supplies its actual argument. The captured records retain
their root alternatives, deep names, and cached depths.
-/
namespace MicroCFTA.InternedRecordDepthCallback
open InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedNestedConstruction (Syntax Outcome)
open InternedFreshOrdinaryContext InternedFreshOrdinaryDepthComposition
open InternedRecordDepthShape InternedDepthSemantics
open InternedBinderProtocol (Reference)

/-- Evaluate the body with one distinct local and the complete decoded captures. -/
def symbolic (body : Syntax Symbol Guard) (environment : List (Value Symbol Guard)) : Shape (Sum Unit Reference) :=
  evaluate body (⟨[.inl ()], [], false, 0⟩ :: (environment.map shape).map (Shape.map Sum.inr))

/-- The symbolic body determines its fixed deep captures. -/
def captured (body : Syntax Symbol Guard) (environment : List (Value Symbol Guard)) : List Reference :=
  InternedProfileCallbackForm.captures (symbolic body environment).deep

/-- The symbolic body determines whether its local occurs below a constructor. -/
def uses (body : Syntax Symbol Guard) (environment : List (Value Symbol Guard)) : Bool :=
  InternedProfileCallbackForm.usesArgument (symbolic body environment).deep

/-- Supplying a reference retains the complete shape of every captured record. -/
theorem evaluate_supplied (body : Syntax Symbol Guard) (environment : List (Value Symbol Guard)) (argument : Reference) :
    evaluate body ((Value.reference argument :: environment).map shape) =
      (symbolic body environment).map (InternedProfileCallbackForm.supply argument) := by
  have mapped := evaluate_map (InternedProfileCallbackForm.supply argument) body
    (⟨[Sum.inl ()], [], false, 0⟩ :: (environment.map shape).map (Shape.map Sum.inr))
  have inputs : (⟨[Sum.inl ()], [], false, 0⟩ :: (environment.map shape).map (Shape.map Sum.inr)).map
      (Shape.map (InternedProfileCallbackForm.supply argument)) = (Value.reference argument :: environment).map shape := by
    simp [shape, Shape.map, InternedProfileCallbackForm.supply, List.map_map, Function.comp_def]
  simpa only [inputs, symbolic] using mapped

/-- The supplied deep names are exactly the fixed captures and the selected local. -/
theorem deep_form (body : Syntax Symbol Guard) (environment : List (Value Symbol Guard)) (argument name : Reference) :
    name ∈ (evaluate body ((Value.reference argument :: environment).map shape)).deep ↔
      name ∈ InternedRootProfile.response (captured body environment) (uses body environment) argument := by
  rw [evaluate_supplied]
  simp only [Shape.map, captured, uses, InternedProfileCallbackForm.supplied_member,
    InternedProfileCallbackForm.response_member]

/-- Symbolic free captures agree with the independent actual-record free-name interpreter. -/
theorem captures_free (body : Syntax Symbol Guard) (environment : List (Value Symbol Guard))
    (state : State Symbol Guard) (coherent : Coherent state) (available : ∀ value ∈ environment, Available state value)
    (name : Reference) :
    name ∈ InternedProfileCallbackForm.captures (symbolic body environment).free ↔
      name ∈ InternedProfileCallbackForm.captures (InternedFreeNameForm.symbolic body
        (environment.map InternedRootProfile.profile) (environment.map Value.free)) := by
  have projected := InternedRecordDepthSource.evaluate_free (.binder true body) environment state coherent available name
  rw [evaluate, InternedDepthFreeProjection.binder_free, InternedFreeNameForm.binder_captures, lower_captures] at projected
  exact projected

/-- Actual normalized callbacks retain exactly the symbolic free captures away from their argument. -/
theorem callback_free [DecidableEq (EdgeKey Symbol Guard)] (body : Syntax Symbol Guard)
    (environment : List (Value Symbol Guard)) (argument : Reference) (state : State Symbol Guard)
    (context : Context state environment) (available : Available state (.reference argument))
    (value : Value Symbol Guard) (after : State Symbol Guard)
    (done : InternedFreshOrdinaryFacts.callback body environment argument state = .done value after)
    (name : Reference) (different : name ≠ argument) :
    name ∈ value.free ↔ name ∈ InternedProfileCallbackForm.captures (symbolic body environment).free :=
  (InternedFreshOrdinarySourceFreeNames.callback_other body environment argument state context.normal
    (context.local argument available).inputs context.freeNames context.profiles value after done name different).trans
      (captures_free body environment state context.normal.facts.coherent context.inputs name).symm

/-- A checked raw body supplies the exact normalized callback observations. -/
theorem callback_checked [DecidableEq (EdgeKey Symbol Guard)] (body : Syntax Symbol Guard)
    (environment : List (Value Symbol Guard)) (argument : Reference) (state : State Symbol Guard)
    (context : Context state environment) (argumentAvailable : Available state (.reference argument))
    (checked : InternedFreshOrdinaryDepthRequest.Checked
      (InternedFreshOrdinaryConstruction.build body (.reference argument :: environment) state)
      (fun value => Observed value (evaluate body ((Value.reference argument :: environment).map shape)))) :
    InternedFreshOrdinaryDepthRequest.Checked (InternedFreshOrdinaryFacts.callback body environment argument state)
      (fun value => value.depth = (symbolic body environment).depth ∧
        InternedFreshOrdinaryDepthHeap.Observed (captured body environment) (uses body environment) argument value) := by
  have localContext := context.local argument argumentAvailable
  have verified := InternedFreshOrdinaryFacts.build_verified body _ state localContext.normal.facts localContext.inputs
  unfold InternedFreshOrdinaryFacts.callback
  apply InternedFreshOrdinaryDepthRequest.bind_checked _ _ _ _ checked
  intro value after returned heap observed
  have afterContext : Context after (.reference argument :: environment) := by
    simpa only [returned, Outcome.state] using localContext.build body
  have available := verified.result _ _ returned
  apply InternedFreshOrdinaryDepthRequest.done_checked
  · exact InternedFreshOrdinaryDepthHeap.preserve after _ heap (InternedStoredMuOrigins.filter_noNewMu argument value after)
  · constructor
    · have pure := congrArg Shape.depth (evaluate_supplied body environment argument)
      exact (InternedNormalizationDepthExact.filter_depth argument value after afterContext.normal.facts.coherent
        afterContext.normal.facts.cached afterContext.normal.facts.linked afterContext.normal.live available).trans (observed.depth.trans pure)
    · intro name
      exact (InternedDeepFreeNormalization.filter_deep argument name value after afterContext.normal available).trans
        ((observed.deep name).trans (deep_form body environment argument name))

end MicroCFTA.InternedRecordDepthCallback
