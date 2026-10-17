import MicroCFTA.SourceCurrentNativeNormalizationFreshness
import MicroCFTA.SourceCurrentNativeStrippedAlternatives
import MicroCFTA.InternedRecordDepthExecution

/-!
# Symbolic observations for normalized original-input comparison

The two source executions can assign different references to each varying
lexical slot. Fixed captures remain complete available records.
-/
namespace MicroCFTA.SourceCurrentNativeNormalizedComparison
open Cache InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedNestedConstruction (Syntax Outcome)
open InternedFreshOrdinaryConstruction InternedFreshOrdinaryFacts
open InternedFreshOrdinaryContext InternedFreshOrdinaryLiveInputs
open InternedDeepFreeDepth InternedRecordDepthShape InternedDepthSemantics
open InternedBinderProtocol (Reference)
variable {Atom : Type}

/-- Fixed records retain their decoded shape and varying slots remain distinct roots. -/
def inputShape : Sum (Value Symbol Guard) Atom → Shape (Sum Reference Atom)
  | .inl value => (shape value).map Sum.inl
  | .inr atom => ⟨[.inr atom], [], false, 0⟩

/-- One symbolic execution retains fixed names separately from all varying slots. -/
def symbolic (expression : Syntax Symbol Guard) (inputs : List (Sum (Value Symbol Guard) Atom)) :
    Shape (Sum Reference Atom) := evaluate expression (inputs.map inputShape)

private theorem input_shape (names : Atom → Reference) (selected : Sum (Value Symbol Guard) Atom) :
    shape (input names selected) = (inputShape selected).map (Sum.elim id names) := by
  cases selected with
  | inl value => simp [input, inputShape, Shape.map, List.map_map, Function.comp_def]
  | inr atom => simp [input, inputShape, shape, Shape.map]

private theorem input_shapes (names : Atom → Reference) (inputs : List (Sum (Value Symbol Guard) Atom)) :
    (inputs.map (input names)).map shape = (inputs.map inputShape).map (Shape.map (Sum.elim id names)) := by
  simp only [List.map_map]
  apply List.map_congr_left
  intro selected member
  exact input_shape names selected

/-- Renaming varying slots commutes with the complete shape interpreter. -/
theorem instantiated (expression : Syntax Symbol Guard) (inputs : List (Sum (Value Symbol Guard) Atom))
    (names : Atom → Reference) :
    evaluate expression ((inputs.map (input names)).map shape) =
      (symbolic expression inputs).map (Sum.elim id names) := by
  rw [input_shapes, evaluate_map]
  rfl

/-- Actual full source execution has exactly the instantiated symbolic deep occurrences. -/
theorem actual_deep [DecidableEq (EdgeKey Symbol Guard)]
    (expression : Syntax Symbol Guard) (inputs : List (Sum (Value Symbol Guard) Atom))
    (names : Atom → Reference) (before after : State Symbol Guard)
    (context : Context before (inputs.map (input names)))
    (heap : InternedFreshOrdinaryDepthHeap.Heap before) (value : Value Symbol Guard)
    (actual : build expression (inputs.map (input names)) before = .done value after)
    (name : Reference) :
    name ∈ deepNames value ↔ name ∈ ((symbolic expression inputs).deep.map (Sum.elim id names)) := by
  have observed := (InternedRecordDepthExecution.build_depth expression _ before context heap).result value after actual
  simpa only [instantiated, Shape.map] using observed.deep name

private theorem symbolic_callback (body : Syntax Symbol Guard)
    (inputs : List (Sum (Value Symbol Guard) Atom)) (names : Atom → Reference) :
    InternedRecordDepthCallback.symbolic body (inputs.map (input names)) =
      (evaluate body (⟨[Sum.inl ()], [], false, 0⟩ ::
        (inputs.map inputShape).map (Shape.map Sum.inr))).map (Sum.map id (Sum.elim id names)) := by
  unfold InternedRecordDepthCallback.symbolic
  rw [input_shapes, ← local_map, evaluate_map]

private theorem uses_mapped (function : First → Reference) (names : List (Sum Unit First)) :
    InternedProfileCallbackForm.usesArgument (names.map (Sum.map id function)) =
      hasLocal names := by
  induction names with
  | nil => rfl
  | cons name names ih =>
      cases name <;> simp [InternedProfileCallbackForm.usesArgument, hasLocal] at ih ⊢
      exact ih

/-- The syntax-local occurrence decision does not depend on the assigned reference names. -/
theorem uses_same (body : Syntax Symbol Guard) (inputs : List (Sum (Value Symbol Guard) Atom))
    (firstNames secondNames : Atom → Reference) :
    InternedRecordDepthCallback.uses body (inputs.map (input firstNames)) =
      InternedRecordDepthCallback.uses body (inputs.map (input secondNames)) := by
  simp only [InternedRecordDepthCallback.uses, symbolic_callback, Shape.map, uses_mapped]

/-- Both actual probes recover the syntax-local decision at their actual chosen ordinary level. -/
theorem probes_use [DecidableEq (EdgeKey Symbol Guard)]
    (body : Syntax Symbol Guard) (environment : List (Value Symbol Guard))
    (before afterDepth afterOrdinary : State Symbol Guard)
    (context : Context before environment) (heap : InternedFreshOrdinaryDepthHeap.Heap before)
    (depth ordinary : Value Symbol Guard)
    (depthActual : callback body environment .depth before = .done depth afterDepth)
    (ordinaryActual : callback body environment (.uninterned (ordinaryLevel depth)) afterDepth =
      .done ordinary afterOrdinary) :
    InternedFreshOrdinaryDepthHeap.usesLocal depth ordinary = InternedRecordDepthCallback.uses body environment := by
  have depthChecked := InternedRecordDepthCallback.callback_checked body environment .depth before context
    (InternedNestedProvenance.depth_available before)
    (InternedRecordDepthExecution.build_depth body _ before
      (context.local .depth (InternedNestedProvenance.depth_available before)) heap)
  have depthObservation := (depthChecked.result depth afterDepth depthActual).2
  have depthContext : Context afterDepth environment := by
    simpa only [depthActual, Outcome.state] using
      context.callback body .depth (InternedNestedProvenance.depth_available before)
  have afterHeap : InternedFreshOrdinaryDepthHeap.Heap afterDepth := by
    simpa only [depthActual, Outcome.state] using depthChecked.heap
  have ordinaryChecked := InternedRecordDepthCallback.callback_checked body environment
    (.uninterned (ordinaryLevel depth)) afterDepth depthContext
    (InternedNestedProvenance.ordinary_available afterDepth _)
    (InternedRecordDepthExecution.build_depth body _ afterDepth
      (depthContext.local _ (InternedNestedProvenance.ordinary_available afterDepth _)) afterHeap)
  have ordinaryObservation := (ordinaryChecked.result ordinary afterOrdinary ordinaryActual).2
  have depthAvailable := (callback_verified body environment .depth before context.normal.facts
    (context.local .depth (InternedNestedProvenance.depth_available before)).inputs).result _ _ depthActual
  have fresh : .uninterned (ordinaryLevel depth) ∉ InternedRecordDepthCallback.captured body environment := by
    intro present
    have named := (InternedFreshOrdinaryDepthHeap.observed_other _ _ .depth depth depthObservation _
      (by intro impossible; cases impossible)).mpr present
    exact ordinary_fresh depth (InternedDeepFreeNormalization.deep_free depth afterDepth
      depthContext.normal.facts.coherent depthAvailable _ named)
  apply Bool.eq_iff_iff.mpr
  simpa only [InternedFreshOrdinaryDepthHeap.usesLocal, decide_eq_true_eq] using
    InternedFreshOrdinaryDepthHeap.observed_own _ _ _ ordinary ordinaryObservation fresh

end MicroCFTA.SourceCurrentNativeNormalizedComparison
