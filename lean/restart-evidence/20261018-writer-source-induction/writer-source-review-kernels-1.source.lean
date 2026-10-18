import MicroCFTA.SourceCurrentReaderFiniteOrdinaryStep
import MicroCFTA.InternedFreshOrdinarySourceFreeNames
import MicroCFTA.SourceCurrentStoredUnionObservations
import MicroCFTA.SourceCurrentRetainedMuWriterAlignment

set_option linter.all true
set_option maxHeartbeats 3000000
set_option maxRecDepth 30000

namespace MicroCFTA.WriterSourceReviewKernels
open Cache Language InternedConstructorTemplates InternedProbeProvenance
open InternedNestedConstruction (Syntax EdgeSyntax Outcome work request finish)
open InternedFreshOrdinaryConstruction InternedFreshOrdinaryFacts
open InternedFreshOrdinaryStoredSubstitution (execute)
open SourceEqualityRequiredCache (Ready Keeps)
open SourceCurrentNativeMuPublication (Publication History)
open SourceCurrentRetainedMuWriterAlignment (Writer)
open SourceCurrentReaderFiniteOrdinaryStep (RelatedAt AlignedAt)
open InternedBinderProtocol (Reference)

private def nested : Syntax Nat Bool :=
  .binder true (.node [.mk 7 true [], .mk 9 false [.var 0]])

private theorem nested_aligned (depth : Nat) (reader : State Nat Bool) :
    AlignedAt depth reader nested := by
  intro leftInputs rightInputs first second paired ready firstInputs secondInputs
    firstReplacements secondReplacements rawFirst rawSecond firstRaw secondRaw result other firstDone secondDone
  have independent (inputs : List (Value Nat Bool)) : build nested inputs reader = build nested [] reader := by
    apply InternedFreshOrdinaryDependencies.build_congr
    intro index member
    have noInputs : InternedNestedDependencies.inputs nested = [] := by cbv
    rw [noInputs] at member
    cases member
  have same : rawFirst = rawSecond :=
    (Outcome.done.inj (firstRaw.symm.trans ((independent leftInputs).trans
      ((independent rightInputs).symm.trans secondRaw)))).1
  subst rawSecond
  have closed : rawFirst.free = [] := by
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro name member
    have raw : build nested [] reader = .done rawFirst reader := (independent leftInputs).symm.trans firstRaw
    obtain ⟨value,impossible,_⟩ := InternedFreshOrdinarySourceFreeNames.build_free_origins nested [] reader
      ready.semantic.1.normal (by intro value impossible; cases impossible) ready.semantic.1.freeNames
      ready.semantic.1.profiles rawFirst reader raw name member
    cases impossible
  have firstClosed := SourceCurrentStoredUnionObservations.closed rawFirst first reader closed
  have secondClosed := SourceCurrentStoredUnionObservations.closed rawFirst second reader closed
  have left : result = rawFirst := (Outcome.done.inj (firstDone.symm.trans firstClosed)).1
  have right : other = rawFirst := (Outcome.done.inj (secondDone.symm.trans secondClosed)).1
  subst result
  subst other
  exact ⟨Iff.rfl,SourceCurrentOpenObservations.Same.refl depth reader [rawFirst]⟩

end MicroCFTA.WriterSourceReviewKernels
