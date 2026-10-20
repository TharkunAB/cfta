import MicroCFTA.SourceCurrentAllocatedNativeClosedReceipts
import MicroCFTA.SourceRecursiveIntersectionCompileMuBounds

/-!
# Contextual Mu meaning at the actual source domain entry

Original codecs identify the physical pair and stored body inputs.
The real domain allocation supplies its literal source binding list.
A contextual child law then discharges the local binder body laws.
The actual checked trace must still derive that child law and completion.
-/
namespace MicroCFTA.SourceCurrentAllocatedNativeMuSource
open Language BinderLanguage InternedConstructorTemplates InternedProbeProvenance InternedNestedFacts
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionInputView
open SourceCurrentAllocatedNativePairContexts SourceCurrentAllocatedNativeContextCache
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula

/-- The actual checked Mu prefix enters the literal child domain and retains its binder continuation. -/
theorem enter_prefix [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (request : NodeRequest Symbol Guard) (before : SourceEqualityNativeDemand.State width) (first second : Nat)
    (leftIdentity : SourceRecursiveIntersectionControl.identity request.left = some first)
    (rightIdentity : SourceRecursiveIntersectionControl.identity request.right = some second) :
    let entered := SourceRecursiveIntersectionEnvironment.enter before.native.machine.domains request.domain.key
      request.left request.right first second
    SourceEqualityNativeDemand.step
      (.code (SourceRecursiveIntersectionCode.compileMu request.domain request.left request.right)) before =
      .yielded (.code (.node ⟨entered.1, SourceRecursiveIntersectionKernel.body request.left,
        SourceRecursiveIntersectionKernel.body request.right⟩ (fun value =>
          .optionalBinder (SourceRecursiveIntersectionControl.pair first second) value .pure)))
        {before with native := advance before.native {before.native.machine with domains := entered.2}} := by
  simp only [SourceRecursiveIntersectionCode.compileMu, leftIdentity, rightIdentity,
    SourceEqualityNativeDemand.step, SourceRecursiveIntersectionNative.step, SourceEqualityNativeDemand.lift]

/-- Removing an actual Mu constructor retains original input syntax. -/
theorem original_body (value : Value Symbol Guard) (original : Original value) :
    Original (SourceRecursiveIntersectionKernel.body value) := by
  cases value with
  | empty | reference | node | union => exact original
  | mu entry stored depth ordinary =>
      cases original with
      | mu _ _ _ _ bodyOriginal => exact bodyOriginal

/-- The fixed input model also validates each unfolded input. -/
theorem unfolded_valid (view : IntersectSchedule.View Symbol) (model : IntersectSchedule.InputMeaning view)
    (input : IntersectSchedule.Input) (valid : model.valid input) :
    model.valid (SourceCurrentAllocatedNativeMuMeaning.unfolded view input) := by
  cases input with
  | mu name => exact model.body_valid name valid
  | empty | node | union | ref => exact valid

/-- Literal source entry and original body readback derive the parent contextual Mu law. -/
theorem mu_source_law [DecidableEq (EdgeKey Symbol Guard)]
    (source : InternedConstructorTemplates.State Symbol Guard) (facts : Facts source)
    (holds : Guard → Term Symbol → Bool)
    (model : IntersectSchedule.InputMeaning (view source holds))
    (ranked : IntersectSchedule.RankedInput (view source holds) model.valid)
    (request : NodeRequest Symbol Guard) (inputs : NodeInputs (view source holds) model request)
    (leftAvailable : Available source request.left) (rightAvailable : Available source request.right)
    (cache : Cache.State IntersectionFlatMemoKeyDomain.DomainKey) (cacheValid : Cache.Valid cache)
    (first second : Nat)
    (leftIdentity : SourceRecursiveIntersectionControl.identity request.left = some first)
    (rightIdentity : SourceRecursiveIntersectionControl.identity request.right = some second)
    (leftNonempty : inputOf request.left ≠ .empty) (rightNonempty : inputOf request.right ≠ .empty)
    (recursive : (∃ name, inputOf request.left = .mu name) ∨ ∃ name, inputOf request.right = .mu name)
    (fresh : SourceRecursiveIntersectionControl.pair first second ∉ request.domain.key.seen)
    (bodyValue value : Value Symbol Guard)
    (bodyLaw : NodeLaw (view source holds) model ranked holds
      ⟨(SourceRecursiveIntersectionEnvironment.enter cache request.domain.key request.left request.right first second).1,
        SourceRecursiveIntersectionKernel.body request.left, SourceRecursiveIntersectionKernel.body request.right⟩ bodyValue)
    (before after : InternedConstructorTemplates.State Symbol Guard)
    (semantic : SourceRecursiveIntersectionSemanticHeap.SemanticHeap before)
    (heap : InternedGuardedProbeHeap.Heap before) (available : Available before bodyValue)
    (done : SourceRecursiveIntersectionMaybeMu.maybeMu
      (SourceRecursiveIntersectionControl.pair first second) bodyValue before = .done value after) :
    NodeLaw (view source holds) model ranked holds request value := by
  have pairEq := SourceRecursiveIntersectionSchedule.pair_encoded request.left request.right
    (inputOf request.left) (inputOf request.right) (inputs.1.codec request.left) (inputs.2.1.codec request.right)
    first second leftIdentity rightIdentity
  have entered := SourceRecursiveIntersectionSchedule.entered_key cache cacheValid request.domain.key
    request.left request.right first second
  rw [pairEq] at entered fresh done
  have leftBody := SourceRecursiveIntersectionCode.body_encoded source facts holds request.left inputs.1 leftAvailable
  have rightBody := SourceRecursiveIntersectionCode.body_encoded source facts holds request.right inputs.2.1 rightAvailable
  change inputOf (SourceRecursiveIntersectionKernel.body request.left) =
    SourceCurrentAllocatedNativeMuMeaning.unfolded (view source holds) (inputOf request.left) at leftBody
  change inputOf (SourceRecursiveIntersectionKernel.body request.right) =
    SourceCurrentAllocatedNativeMuMeaning.unfolded (view source holds) (inputOf request.right) at rightBody
  have childInputs : NodeInputs (view source holds) model
      ⟨(SourceRecursiveIntersectionEnvironment.enter cache request.domain.key request.left request.right first second).1,
        SourceRecursiveIntersectionKernel.body request.left, SourceRecursiveIntersectionKernel.body request.right⟩ := by
    refine ⟨original_body request.left inputs.1, original_body request.right inputs.2.1, ?_, ?_⟩
    · rw [leftBody]
      exact unfolded_valid _ model _ inputs.2.2.1
    · rw [rightBody]
      exact unfolded_valid _ model _ inputs.2.2.2
  apply SourceCurrentAllocatedNativeClosedReceipts.mu_node_law (view source holds) model ranked holds request bodyValue value
    before after semantic heap available leftNonempty rightNonempty recursive
    ((SourceRecursiveIntersectionEnvironment.bindings request.left request.right).map Prod.fst) fresh done
  · intro output context term accepted
    have actualContext : SoundPairs model.languages
        (SourceRecursiveIntersectionEnvironment.enter cache request.domain.key request.left request.right first second).1.key output := by
      rw [entered]
      exact context
    have common := bodyLaw.sound childInputs output actualContext term accepted
    simpa only [leftBody, rightBody] using common
  · intro bound output context one two bounded term left right
    have actualContext : CompletePairs ranked.languages bound
        (SourceRecursiveIntersectionEnvironment.enter cache request.domain.key request.left request.right first second).1.key output := by
      rw [entered]
      exact context
    apply bodyLaw.complete childInputs bound output actualContext one two bounded term
    · simpa only [leftBody] using left
    · simpa only [rightBody] using right

end MicroCFTA.SourceCurrentAllocatedNativeMuSource
