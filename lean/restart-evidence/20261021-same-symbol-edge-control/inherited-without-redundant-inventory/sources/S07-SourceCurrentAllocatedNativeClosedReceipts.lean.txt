import MicroCFTA.SourceCurrentAllocatedNativeContextCache
import MicroCFTA.SourceCurrentAllocatedNativeMuMeaning

/-!
# Closed checked receipts from contextual result laws

The input interpretation and its finite ranks describe only original inputs.
The contextual result law gives exact meaning at the empty source domain.
An actual checked body trace then supplies its own completion receipt.
This construction needs no final native validity assumption.

The recursive body law, physical effects, and completion remain explicit
component obligations. This module does not prove general checked completion.
-/
namespace MicroCFTA.SourceCurrentAllocatedNativeClosedReceipts
open Language BinderLanguage InternedConstructorTemplates InternedProbeProvenance
open InternedNestedFacts
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionCode
open SourceCurrentAllocatedNativePairContexts SourceCurrentAllocatedNativeContextCache
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State

/-- Local unfolded-body laws construct the contextual law stored by a Mu completion. -/
theorem mu_node_law [DecidableEq (EdgeKey Symbol Guard)]
    (view : IntersectSchedule.View Symbol) (model : IntersectSchedule.InputMeaning view)
    (ranked : IntersectSchedule.RankedInput view model.valid) (holds : Guard → Term Symbol → Bool)
    (request : NodeRequest Symbol Guard) (body value : Value Symbol Guard)
    (before after : InternedConstructorTemplates.State Symbol Guard)
    (semantic : SourceRecursiveIntersectionSemanticHeap.SemanticHeap before)
    (heap : InternedGuardedProbeHeap.Heap before) (available : Available before body)
    (leftNonempty : SourceRecursiveIntersectionInputView.inputOf request.left ≠ .empty)
    (rightNonempty : SourceRecursiveIntersectionInputView.inputOf request.right ≠ .empty)
    (recursive : (∃ name, SourceRecursiveIntersectionInputView.inputOf request.left = .mu name) ∨
      ∃ name, SourceRecursiveIntersectionInputView.inputOf request.right = .mu name)
    (bindings : List Nat)
    (fresh : IntersectSchedule.pair (SourceRecursiveIntersectionInputView.inputOf request.left)
      (SourceRecursiveIntersectionInputView.inputOf request.right) ∉ request.domain.key.seen)
    (done : SourceRecursiveIntersectionMaybeMu.maybeMu
      (IntersectSchedule.pair (SourceRecursiveIntersectionInputView.inputOf request.left)
        (SourceRecursiveIntersectionInputView.inputOf request.right)) body before = .done value after)
    (bodySound : ∀ inner, SoundPairs model.languages
      (SourceRecursiveIntersectionDomain.extend request.domain.key bindings
        (IntersectSchedule.pair (SourceRecursiveIntersectionInputView.inputOf request.left)
          (SourceRecursiveIntersectionInputView.inputOf request.right))) inner →
      Included (InternedGuardedLanguage.meaning holds inner body) (fun term =>
        IntersectSchedule.inputLanguage model.languages
          (SourceCurrentAllocatedNativeMuMeaning.unfolded view (SourceRecursiveIntersectionInputView.inputOf request.left)) term ∧
        IntersectSchedule.inputLanguage model.languages
          (SourceCurrentAllocatedNativeMuMeaning.unfolded view (SourceRecursiveIntersectionInputView.inputOf request.right)) term))
    (bodyComplete : ∀ bound inner, CompletePairs ranked.languages bound
      (SourceRecursiveIntersectionDomain.extend request.domain.key bindings
        (IntersectSchedule.pair (SourceRecursiveIntersectionInputView.inputOf request.left)
          (SourceRecursiveIntersectionInputView.inputOf request.right))) inner →
      ∀ first second, first + second ≤ bound → ∀ term,
      IntersectSchedule.inputAt ranked.languages
        (SourceCurrentAllocatedNativeMuMeaning.unfolded view (SourceRecursiveIntersectionInputView.inputOf request.left)) first term →
      IntersectSchedule.inputAt ranked.languages
        (SourceCurrentAllocatedNativeMuMeaning.unfolded view (SourceRecursiveIntersectionInputView.inputOf request.right)) second term →
      InternedGuardedLanguage.meaning holds inner body term) :
    NodeLaw view model ranked holds request value := by
  constructor
  · intro inputs output sound
    exact SourceCurrentAllocatedNativeMuMeaning.optionalBinder_mu_sound view model _ _ inputs.2.2.1 inputs.2.2.2
      leftNonempty rightNonempty body before semantic heap available value after done holds request.domain.key bindings fresh
      bodySound output sound
  · intro inputs bound output complete first second bounded term left right
    exact SourceCurrentAllocatedNativeMuMeaning.optionalBinder_mu_complete view model ranked _ _
      inputs.2.2.1 inputs.2.2.2 leftNonempty rightNonempty recursive body before semantic heap available value after done
      holds request.domain.key bindings fresh bodyComplete bound output complete first second bounded term left right

/-- Erasing original derivation ranks also applies to the tagged empty input. -/
theorem input_finite (languages : Nat → Lang Symbol) (ranks : Nat → Nat → Lang Symbol)
    (finite : ∀ name term, languages name term ↔ ∃ rank, ranks name rank term)
    (input : IntersectSchedule.Input) (term : Term Symbol)
    (accepted : IntersectSchedule.inputLanguage languages input term) :
    ∃ rank, IntersectSchedule.inputAt ranks input rank term := by
  cases input with
  | empty => cases accepted
  | node name | mu name | union name | ref name => exact (finite name term).mp accepted

/-- A contextual node law at the empty domain gives exact original input meaning. -/
theorem node_closed_exact (view : IntersectSchedule.View Symbol) (model : IntersectSchedule.InputMeaning view)
    (ranked : IntersectSchedule.RankedInput view model.valid) (holds : Guard → Term Symbol → Bool)
    (finite : ∀ name term, model.languages name term ↔ ∃ rank, ranked.languages name rank term)
    (request : NodeRequest Symbol Guard) (value : Value Symbol Guard)
    (inputs : NodeInputs view model request) (law : NodeLaw view model ranked holds request value)
    (domain : request.domain = IntersectionEmptyDomain.emptyDomain)
    (output : InternedGuardedLanguage.Env Symbol) (term : Term Symbol) :
    InternedGuardedLanguage.meaning holds output value term ↔
      IntersectSchedule.inputLanguage model.languages (SourceRecursiveIntersectionInputView.inputOf request.left) term ∧
      IntersectSchedule.inputLanguage model.languages (SourceRecursiveIntersectionInputView.inputOf request.right) term := by
  have sound : SoundPairs model.languages request.domain.key output := by
    rw [domain]
    exact sound_empty_domain model.languages output
  constructor
  · exact law.sound inputs output sound term
  · intro common
    obtain ⟨first, left⟩ := input_finite model.languages ranked.languages finite _ term common.1
    obtain ⟨second, right⟩ := input_finite model.languages ranked.languages finite _ term common.2
    have complete : CompletePairs ranked.languages (first + second) request.domain.key output := by
      rw [domain]
      exact complete_empty_domain ranked.languages (first + second) output
    exact law.complete inputs (first + second) output complete first second (Nat.le_refl _) term left right

/-- Original physical input readback turns the contextual law into the closed receipt law. -/
theorem node_meaning (view : IntersectSchedule.View Symbol) (model : IntersectSchedule.InputMeaning view)
    (ranked : IntersectSchedule.RankedInput view model.valid) (holds : Guard → Term Symbol → Bool)
    (finite : ∀ name term, model.languages name term ↔ ∃ rank, ranked.languages name rank term)
    (request : NodeRequest Symbol Guard) (value : Value Symbol Guard)
    (inputs : NodeInputs view model request) (law : NodeLaw view model ranked holds request value)
    (left : request.left.free = [] → ∀ output term,
      InternedGuardedLanguage.meaning holds output request.left term ↔
        IntersectSchedule.inputLanguage model.languages (SourceRecursiveIntersectionInputView.inputOf request.left) term)
    (right : request.right.free = [] → ∀ output term,
      InternedGuardedLanguage.meaning holds output request.right term ↔
        IntersectSchedule.inputLanguage model.languages (SourceRecursiveIntersectionInputView.inputOf request.right) term) :
    SourceEqualityNativeDemandProvenance.NodeMeaning holds request value := by
  intro domain leftClosed rightClosed output term
  rw [node_closed_exact view model ranked holds finite request value inputs law domain output term,
    left leftClosed output term, right rightClosed output term]

/-- An actual checked body and its physical effects construct a new closed node receipt. -/
theorem node_produced [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (view : IntersectSchedule.View Symbol) (model : IntersectSchedule.InputMeaning view)
    (ranked : IntersectSchedule.RankedInput view model.valid) (holds : Guard → Term Symbol → Bool)
    (finite : ∀ name term, model.languages name term ↔ ∃ rank, ranked.languages name rank term)
    (request : NodeRequest Symbol Guard) (value : Value Symbol Guard)
    (inputs : NodeInputs view model request) (law : NodeLaw view model ranked holds request value)
    (left : request.left.free = [] → ∀ output term,
      InternedGuardedLanguage.meaning holds output request.left term ↔
        IntersectSchedule.inputLanguage model.languages (SourceRecursiveIntersectionInputView.inputOf request.left) term)
    (right : request.right.free = [] → ∀ output term,
      InternedGuardedLanguage.meaning holds output request.right term ↔
        IntersectSchedule.inputLanguage model.languages (SourceRecursiveIntersectionInputView.inputOf request.right) term)
    (before after : Checked width) (fuel : Nat)
    (ready : NodeReady before.native.machine request)
    (done : SourceEqualityNativeDemand.execute fuel (.code (compileNode request)) before = .done value after)
    (growth : Extension before.native.machine after.native.machine)
    (available : Available after.native.machine.heap value) :
    SourceEqualityNativeDemandProvenance.NodeProduced (width := width) holds after.native.machine request value :=
  ⟨before, after, fuel, ready, done, growth, available, .refl _,
    node_meaning view model ranked holds finite request value inputs law left right⟩

/-- Closed original inputs derive a fixed model that can discharge new result receipts. -/
theorem source_models (source : InternedConstructorTemplates.State Symbol Guard) (facts : Facts source)
    (holds : Guard → Term Symbol → Bool) (request : NodeRequest Symbol Guard)
    (leftOriginal : SourceRecursiveIntersectionInputView.Original request.left)
    (rightOriginal : SourceRecursiveIntersectionInputView.Original request.right)
    (leftAvailable : Available source request.left) (rightAvailable : Available source request.right)
    (leftClosed : request.left.free = []) (rightClosed : request.right.free = []) :
    ∃ (model : IntersectSchedule.InputMeaning (SourceRecursiveIntersectionInputView.view source holds))
      (ranked : IntersectSchedule.RankedInput (SourceRecursiveIntersectionInputView.view source holds) model.valid),
      NodeInputs (SourceRecursiveIntersectionInputView.view source holds) model request ∧
      (∀ value, NodeLaw (SourceRecursiveIntersectionInputView.view source holds) model ranked holds request value →
        SourceEqualityNativeDemandProvenance.NodeMeaning holds request value) := by
  obtain ⟨model, ranked, leftValid, rightValid, finite, left, right⟩ :=
    source_input_models source facts holds request.left request.right leftOriginal rightOriginal leftAvailable rightAvailable
      leftClosed rightClosed
  have inputs : NodeInputs (SourceRecursiveIntersectionInputView.view source holds) model request :=
    ⟨leftOriginal, rightOriginal, leftValid, rightValid⟩
  exact ⟨model, ranked, inputs, fun value law =>
    node_meaning _ model ranked holds finite request value inputs law (fun _ => left) (fun _ => right)⟩

end MicroCFTA.SourceCurrentAllocatedNativeClosedReceipts
