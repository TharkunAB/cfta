import MicroCFTA.SourceRecursiveIntersectionInputExact
import MicroCFTA.InternedGuardedLanguage

/-!
# Independent guarded meaning agrees with actual original input derivations

Original payloads use only interned recursive names. Their copied lexical
meaning equals the independent meaning of the complete stored records.
Closed available original records therefore have exact finite input runs.
-/
namespace MicroCFTA.SourceRecursiveIntersectionGuardedInput
open Cache Language InternedConstructorTemplates InternedProbeProvenance InternedNestedFacts
open SourceRecursiveIntersectionInputView
open InternedBinderProtocol (Reference)

/-- Restrict an actual reference environment to the original interned-name inputs. -/
def internedEnv (ambient : InternedGuardedLanguage.Env Symbol) : BinderLanguage.Env Symbol :=
  fun name => ambient (.interned name)

/-- An actual interned binder has the same local override in the original input copy. -/
theorem internedEnv_bind (ambient : InternedGuardedLanguage.Env Symbol) (name : Nat) (candidate : BinderLanguage.Lang Symbol) :
    internedEnv (InternedGuardedLanguage.bind ambient (.interned name) candidate) = BinderLanguage.bind (internedEnv ambient) name candidate := by
  funext other
  simp only [internedEnv, InternedGuardedLanguage.bind, Reference.interned.injEq, BinderLanguage.bind]

/-- Original stored payloads and their actual lexical copies have equal independent guarded meanings. -/
theorem original_meaning (holds : Guard → Term Symbol → Bool) (value : Value Symbol Guard) (original : Original value)
    (ambient : InternedGuardedLanguage.Env Symbol) :
    InternedGuardedLanguage.meaning holds ambient value = BinderLanguage.meaning (internedEnv ambient) (shape holds value) := by
  induction original generalizing ambient with
  | empty => rw [InternedGuardedLanguage.meaning, shape, BinderLanguage.meaning]
  | reference name => rw [InternedGuardedLanguage.meaning, shape, BinderLanguage.meaning]; rfl
  | node entry edges depth free children ih =>
      funext term
      apply propext
      rw [(InternedGuardedLanguage.laws holds ambient).node, shape_node_meaning]
      apply exists_congr
      intro edge
      apply and_congr_right
      intro member
      simp only [MergedColdInterpretation.EdgeMeaning]
      apply exists_congr
      intro terms
      apply and_congr_right
      intro shape
      apply and_congr_left
      intro guard
      constructor
      · intro runs
        apply SourcePhysicalSharedRows.all₂_both_imp _ _ _ _ runs
        intro child childIn term termIn accepted
        exact (ih edge member child childIn ambient) ▸ accepted
      · intro runs
        apply SourcePhysicalSharedRows.all₂_both_imp _ _ _ _ runs
        intro child childIn term termIn accepted
        exact (ih edge member child childIn ambient).symm ▸ accepted
  | union entry members depth free children ih =>
      funext term
      apply propext
      rw [(InternedGuardedLanguage.laws holds ambient).union, shape_union_meaning]
      apply exists_congr
      intro member
      apply and_congr_right
      intro included
      exact iff_of_eq (congrFun (ih member included ambient) term)
  | mu entry body depth ordinary original ih =>
      rw [InternedGuardedLanguage.meaning, shape, BinderLanguage.meaning]
      apply BinderLanguage.least_congr
      intro candidate term
      have same := ih (InternedGuardedLanguage.bind ambient (.interned entry.identity) candidate)
      rw [internedEnv_bind] at same
      exact iff_of_eq (congrFun same term)

/-- Every closed available original record has exactly the finite derivations of the actual tagged input view. -/
theorem input_exact (state : State Symbol Guard) (facts : Facts state) (holds : Guard → Term Symbol → Bool)
    (value : Value Symbol Guard) (original : Original value) (available : Available state value)
    (closed : value.free = []) (ambient : InternedGuardedLanguage.Env Symbol) :
    InternedGuardedLanguage.meaning holds ambient value = InputLanguage state holds (inputOf value) := by
  have viewClosed : IntersectSchedule.closed (view state holds) (inputOf value) = true := by
    rw [closed_readback state facts holds value original available, closed]
    rfl
  have originalInput : OriginalInput state (inputOf value) := ⟨value, original, available, original.codec value⟩
  have copied := copy_exact_original state facts holds (inputOf value) originalInput viewClosed (internedEnv ambient)
  rw [copy_readback state facts holds value available _ (original.codec value)] at copied
  exact (original_meaning holds value original ambient).trans copied

end MicroCFTA.SourceRecursiveIntersectionGuardedInput
