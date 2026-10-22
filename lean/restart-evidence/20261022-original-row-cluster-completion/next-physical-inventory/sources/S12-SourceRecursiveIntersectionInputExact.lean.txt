import MicroCFTA.SourceRecursiveIntersectionInputSoundness
import MicroCFTA.SourceRecursiveIntersectionInputCompleteness

/-!
# Exact independent language of copied original physical inputs

Copied closed syntax has exactly the independent finite input derivations.
Soundness and completeness derive this equation from actual payloads and
least binders. No copy-language contract is supplied.
-/
namespace MicroCFTA.SourceRecursiveIntersectionInputView
open Cache Binding BinderLanguage InternedConstructorTemplates InternedProbeProvenance
open InternedFreshProbeKeys InternedBinderProtocol InternedNestedFacts IntersectSchedule Language

/-- Closed original physical copies have exactly their independent finite input language. -/
theorem copy_exact_original (state : InternedConstructorTemplates.State Symbol Guard) (facts : Facts state)
    (holds : Guard → Term Symbol → Bool) (input : Input) (originalInput : OriginalInput state input)
    (isClosed : closed (view state holds) input = true) (environment : Env Symbol) :
    meaning environment ((view state holds).copy input) = InputLanguage state holds input := by
  obtain ⟨value, original, available, complete⟩ := originalInput
  have inputExact := inputOf_codec value input complete
  have empty : freeNames value = [] := by
    have empty : (view state holds).free input = [] := List.isEmpty_iff.mp isClosed
    rw [← inputExact, free_readback state facts holds value available] at empty
    exact empty
  rw [copy_readback state facts holds value available input complete, ← inputExact]
  funext term
  apply propext
  constructor
  · apply original.copy_sound state facts holds value available environment
    intro name member
    simp [empty] at member
  · rintro ⟨rank, accepted⟩
    apply original.copy_complete state facts holds value available rank environment ?_ term accepted
    intro name member
    simp [empty] at member

/-- The reachable domain of closed original roots retains actual original physical records. -/
theorem reachable_original (state : InternedConstructorTemplates.State Symbol Guard) (facts : Facts state)
    (holds : Guard → Term Symbol → Bool) (leftRoot rightRoot : Input)
    (leftOriginal : OriginalInput state leftRoot) (rightOriginal : OriginalInput state rightRoot)
    (leftClosed : closed (view state holds) leftRoot = true) (rightClosed : closed (view state holds) rightRoot = true)
    (input : Input) (reachable : Reachable state holds leftRoot rightRoot input) : OriginalInput state input := by
  rcases reachable with left | right
  · exact closed_reach_original state facts holds leftRoot input leftOriginal leftClosed left
  · exact closed_reach_original state facts holds rightRoot input rightOriginal rightClosed right

/-- Actual closed original roots supply every structural and semantic field of the finite input interface. -/
def finiteInput (state : InternedConstructorTemplates.State Symbol Guard) (facts : Facts state)
    (holds : Guard → Term Symbol → Bool) (leftRoot rightRoot : Input)
    (leftOriginal : OriginalInput state leftRoot) (rightOriginal : OriginalInput state rightRoot)
    (leftClosed : closed (view state holds) leftRoot = true) (rightClosed : closed (view state holds) rightRoot = true) :
    FiniteInput (view state holds) where
  valid := Reachable state holds leftRoot rightRoot
  representative := representative state
  identity_exact := reachable_identity state facts holds leftRoot rightRoot leftOriginal rightOriginal leftClosed rightClosed
  body_valid := Reachable.body state holds leftRoot rightRoot
  reference_valid := Reachable.reference state holds leftRoot rightRoot
  row_valid := Reachable.child state holds leftRoot rightRoot
  union_valid := Reachable.member state holds leftRoot rightRoot
  copy_exact input reachable isClosed environment :=
    copy_exact_original state facts holds input
      (reachable_original state facts holds leftRoot rightRoot leftOriginal rightOriginal leftClosed rightClosed input reachable)
      isClosed environment

/-- The actual finite carrier and physical payload rank supply every finite schedule bound. -/
noncomputable def inputBounds (state : InternedConstructorTemplates.State Symbol Guard) (facts : Facts state)
    (holds : Guard → Term Symbol → Bool) (leftRoot rightRoot : Input)
    (leftOriginal : OriginalInput state leftRoot) (rightOriginal : OriginalInput state rightRoot)
    (leftClosed : closed (view state holds) leftRoot = true) (rightClosed : closed (view state holds) rightRoot = true) :
    InputBounds (view state holds) (finiteInput state facts holds leftRoot rightRoot leftOriginal rightOriginal leftClosed rightClosed) where
  pairs := inputPairs (inventory state)
  pair_mem left right leftValid rightValid _ _ := input_pair_mem (inventory state) left right
    ((reachable_original state facts holds leftRoot rightRoot leftOriginal rightOriginal leftClosed rightClosed left leftValid).inventory state facts left)
    ((reachable_original state facts holds leftRoot rightRoot leftOriginal rightOriginal leftClosed rightClosed right rightValid).inventory state facts right)
  localWeight := localWeight state facts holds
  size := weight state
  body name valid := (reachable_original state facts holds leftRoot rightRoot leftOriginal rightOriginal leftClosed rightClosed (.mu name) valid).body_weight state facts holds name
  child name _ := rows_weight state facts holds name
  member name _ := members_weight state facts holds name
  closed_reach root valid isClosed input reachable := closed_reach_below state facts holds root input
    (reachable_original state facts holds leftRoot rightRoot leftOriginal rightOriginal leftClosed rightClosed root valid) isClosed reachable

/-- The semantic schedule terminates with exact product language for actual closed original physical inputs. -/
theorem schedule_total [DecidableEq Symbol] (state : InternedConstructorTemplates.State Symbol Guard) (facts : Facts state)
    (holds : Guard → Term Symbol → Bool) (leftRoot rightRoot : Input)
    (leftOriginal : OriginalInput state leftRoot) (rightOriginal : OriginalInput state rightRoot)
    (leftClosed : closed (view state holds) leftRoot = true) (rightClosed : closed (view state holds) rightRoot = true) :
    ∃ bound result,
      (∀ fuel, bound ≤ fuel → IntersectSchedule.run (view state holds) fuel {} leftRoot rightRoot = .ok result) ∧
      ∀ environment term, meaning environment result term ↔
        InputLanguage state holds leftRoot term ∧ InputLanguage state holds rightRoot term :=
  finite_intersection_total (view state holds)
    (finiteInput state facts holds leftRoot rightRoot leftOriginal rightOriginal leftClosed rightClosed)
    (free_correct state facts holds)
    (inputBounds state facts holds leftRoot rightRoot leftOriginal rightOriginal leftClosed rightClosed)
    leftRoot rightRoot (.inl .root) (.inr .root) leftClosed rightClosed

/-- Actual closed original records give finite semantic execution and their exact copied product language. -/
theorem source_schedule_total [DecidableEq Symbol] (state : InternedConstructorTemplates.State Symbol Guard) (facts : Facts state)
    (holds : Guard → Term Symbol → Bool) (left right : Value Symbol Guard)
    (leftOriginal : Original left) (rightOriginal : Original right)
    (leftAvailable : Available state left) (rightAvailable : Available state right)
    (leftClosed : left.free = []) (rightClosed : right.free = []) :
    ∃ bound result,
      (∀ fuel, bound ≤ fuel → IntersectSchedule.run (view state holds) fuel {} (inputOf left) (inputOf right) = .ok result) ∧
      ∀ environment term, meaning environment result term ↔
        meaning environment (shape holds left) term ∧ meaning environment (shape holds right) term := by
  have leftViewClosed : closed (view state holds) (inputOf left) = true := by
    rw [closed_readback state facts holds left leftOriginal leftAvailable, leftClosed]; rfl
  have rightViewClosed : closed (view state holds) (inputOf right) = true := by
    rw [closed_readback state facts holds right rightOriginal rightAvailable, rightClosed]; rfl
  let leftInput : OriginalInput state (inputOf left) := ⟨left, leftOriginal, leftAvailable, leftOriginal.codec left⟩
  let rightInput : OriginalInput state (inputOf right) := ⟨right, rightOriginal, rightAvailable, rightOriginal.codec right⟩
  obtain ⟨bound, result, completed, exactResult⟩ := schedule_total state facts holds (inputOf left) (inputOf right)
    leftInput rightInput leftViewClosed rightViewClosed
  refine ⟨bound, result, completed, ?_⟩
  intro environment term
  have leftLanguage := copy_exact_original state facts holds (inputOf left) leftInput leftViewClosed environment
  have rightLanguage := copy_exact_original state facts holds (inputOf right) rightInput rightViewClosed environment
  rw [copy_readback state facts holds left leftAvailable _ (leftOriginal.codec left)] at leftLanguage
  rw [copy_readback state facts holds right rightAvailable _ (rightOriginal.codec right)] at rightLanguage
  rw [exactResult environment term, leftLanguage, rightLanguage]

end MicroCFTA.SourceRecursiveIntersectionInputView
