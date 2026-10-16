import MicroCFTA.SourceCurrentAllocatedNativeContextualCode
import MicroCFTA.SourceCurrentAllocatedNativeMuSource

/-!
# Local contextual certificates for actual Mu branches

The selected source branch derives its fresh pair and recursive operands.
The actual domain entry fixes the child request. Its local child law and
the actual optional-binder result derive the parent law before memo finish.
-/
namespace MicroCFTA.SourceCurrentAllocatedNativeContextualMuCertificates
open Language Cache InternedConstructorTemplates InternedProbeProvenance InternedNestedFacts
open SourceRecursiveIntersectionKernel SourceRecursiveIntersectionThunks SourceRecursiveIntersectionInputView
open SourceRecursiveIntersectionCode SourceCurrentAllocatedNativeContextCache
open SourceCurrentAllocatedNativeContextualCode
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula

/-- A complete source identity excludes the empty semantic input. -/
theorem identity_nonempty (value : Value Symbol Guard) (original : Original value) (name : Nat)
    (identity : SourceRecursiveIntersectionControl.identity value = some name) : inputOf value ≠ .empty := by
  cases original <;> simp_all [SourceRecursiveIntersectionControl.identity, inputOf,
    Value.referenceOf, IntersectionFlatMemoKey.input]

/-- A selected Mu payload contains an actual original Mu operand. -/
theorem payload_recursive (left right : Value Symbol Guard)
    (selected : SourceRecursiveIntersectionControl.payload left right = .bothMu ∨
      SourceRecursiveIntersectionControl.payload left right = .leftMu ∨
      SourceRecursiveIntersectionControl.payload left right = .rightMu) :
    (∃ name, inputOf left = .mu name) ∨ ∃ name, inputOf right = .mu name := by
  cases left <;> cases right <;>
    simp_all [SourceRecursiveIntersectionControl.payload, inputOf,
      Value.referenceOf, IntersectionFlatMemoKey.input]

/-- Selected Mu branches pass every earlier guard and use a pair absent from seen. -/
theorem selected_fresh [DecidableEq Symbol] (request : NodeRequest Symbol Guard) (first second : Nat)
    (leftIdentity : SourceRecursiveIntersectionControl.identity request.left = some first)
    (rightIdentity : SourceRecursiveIntersectionControl.identity request.right = some second)
    (selected : SourceRecursiveIntersectionControl.decision request.domain.key request.left request.right = .bothMu ∨
      SourceRecursiveIntersectionControl.decision request.domain.key request.left request.right = .leftMu ∨
      SourceRecursiveIntersectionControl.decision request.domain.key request.left request.right = .rightMu) :
    SourceRecursiveIntersectionControl.pair first second ∉ request.domain.key.seen ∧
      (SourceRecursiveIntersectionControl.payload request.left request.right = .bothMu ∨
        SourceRecursiveIntersectionControl.payload request.left request.right = .leftMu ∨
        SourceRecursiveIntersectionControl.payload request.left request.right = .rightMu) := by
  unfold SourceRecursiveIntersectionControl.decision at selected
  split at selected <;> try rcases selected with impossible | impossible | impossible <;> cases impossible
  split at selected <;> try rcases selected with impossible | impossible | impossible <;> cases impossible
  split at selected <;> try rcases selected with impossible | impossible | impossible <;> cases impossible
  split at selected <;> try rcases selected with impossible | impossible | impossible <;> cases impossible
  simp only [leftIdentity, rightIdentity] at selected
  split at selected
  · rcases selected with impossible | impossible | impossible <;> cases impossible
  · exact ⟨by assumption, selected⟩

/-- Actual optional-binder completion derives a local law conditional only on original input validity. -/
theorem optional_law [DecidableEq (EdgeKey Symbol Guard)]
    (source : InternedConstructorTemplates.State Symbol Guard) (facts : Facts source)
    (holds : Guard → Term Symbol → Bool) (model : IntersectSchedule.InputMeaning (view source holds))
    (ranked : IntersectSchedule.RankedInput (view source holds) model.valid)
    (request : NodeRequest Symbol Guard) (scope : NodeScope source request)
    (cache : Cache.State IntersectionFlatMemoKeyDomain.DomainKey) (cacheValid : Cache.Valid cache)
    (first second : Nat)
    (leftIdentity : SourceRecursiveIntersectionControl.identity request.left = some first)
    (rightIdentity : SourceRecursiveIntersectionControl.identity request.right = some second)
    (leftNonempty : inputOf request.left ≠ .empty) (rightNonempty : inputOf request.right ≠ .empty)
    (recursive : (∃ name, inputOf request.left = .mu name) ∨ ∃ name, inputOf request.right = .mu name)
    (fresh : SourceRecursiveIntersectionControl.pair first second ∉ request.domain.key.seen)
    (bodyValue value : Value Symbol Guard) (before after : Machine Symbol Guard)
    (semantic : SourceEqualityRequiredSemanticCache.SemanticReady before.heap)
    (available : Available before.heap bodyValue)
    (childLaw : NodeLaw (view source holds) model ranked holds
      ⟨(SourceRecursiveIntersectionEnvironment.enter cache request.domain.key request.left request.right first second).1,
        SourceRecursiveIntersectionKernel.body request.left, SourceRecursiveIntersectionKernel.body request.right⟩ bodyValue)
    (done : construction (SourceRecursiveIntersectionMaybeMu.maybeMu
      (SourceRecursiveIntersectionControl.pair first second) bodyValue before.heap) before = .done value after) :
    NodeLaw (view source holds) model ranked holds request value := by
  cases actual : SourceRecursiveIntersectionMaybeMu.maybeMu
      (SourceRecursiveIntersectionControl.pair first second) bodyValue before.heap with
  | pending => simp only [actual, construction] at done; cases done
  | done result heap =>
      have same := Result.done.inj (by simpa only [actual, construction] using done)
      rcases same.1 with rfl
      have localLaw : NodeInputs (view source holds) model request →
          NodeLaw (view source holds) model ranked holds request result := fun inputs =>
        SourceCurrentAllocatedNativeMuSource.mu_source_law source facts holds model ranked request inputs
          scope.leftAvailable scope.rightAvailable cache cacheValid first second leftIdentity rightIdentity
          leftNonempty rightNonempty recursive fresh bodyValue result childLaw before.heap heap
          semantic.ready.semantic semantic.guarded available actual
      exact ⟨fun inputs => (localLaw inputs).sound inputs, fun inputs => (localLaw inputs).complete inputs⟩

/-- The actual selected Mu body has a local contextual certificate with no execution premise. -/
theorem mu_certified [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (source : InternedConstructorTemplates.State Symbol Guard) (facts : Facts source)
    (holds : Guard → Term Symbol → Bool) (model : IntersectSchedule.InputMeaning (view source holds))
    (ranked : IntersectSchedule.RankedInput (view source holds) model.valid)
    (request : NodeRequest Symbol Guard) (scope : NodeScope source request)
    (state : Machine Symbol Guard) (valid : SourceRecursiveIntersectionKernel.Valid state)
    (ready : NodeReady state request)
    (selected : SourceRecursiveIntersectionControl.decision request.domain.key request.left request.right = .bothMu ∨
      SourceRecursiveIntersectionControl.decision request.domain.key request.left request.right = .leftMu ∨
      SourceRecursiveIntersectionControl.decision request.domain.key request.left request.right = .rightMu) :
    Certified (view source holds) model ranked holds (compileMu request.domain request.left request.right) state
      (fun _ value => NodeLaw (view source holds) model ranked holds request value) := by
  obtain ⟨first, second, leftIdentity, rightIdentity⟩ := mu_identities request selected
  obtain ⟨fresh, payload⟩ := selected_fresh request first second leftIdentity rightIdentity selected
  have recursive := payload_recursive request.left request.right payload
  have leftNonempty := identity_nonempty request.left scope.left first leftIdentity
  have rightNonempty := identity_nonempty request.right scope.right second rightIdentity
  have entered := SourceRecursiveIntersectionKernel.entered state valid request.domain ready.1
    request.left request.right ready.2.1 ready.2.2 first second
  simp only [compileMu, leftIdentity, rightIdentity, Certified]
  refine ⟨entered.1, entered.2.1, ?_⟩
  intro bodyValue middle _ _ middleSemantic available childLaw value after done _ _ _
  exact optional_law source facts holds model ranked request scope state.domains valid.2 first second
    leftIdentity rightIdentity leftNonempty rightNonempty recursive fresh bodyValue value middle after
    middleSemantic available childLaw done

end MicroCFTA.SourceCurrentAllocatedNativeContextualMuCertificates
