import MicroCFTA.SourcePruningEnumerationRendering
import MicroCFTA.EnumerationPendingDomainAssignment

/-!
# Assignment construction for actual recursive-marker rendering

One fixed marker term belongs to each present pending domain.
Empty pending buckets and the existing evaluator construct one assignment.
The actual renderer retains that assignment through reads and residual checks.
Original-root and removed-obligation soundness remain separate obligations.
-/
namespace MicroCFTA.SourcePruningEnumerationPendingRendering
open Language Fragments EnumerationState EnumerationCorrectness EnumerationSchedule
open EnumerationDriver EnumerationCompressionFrame SourcePruningEnumerationNodes
open SourcePruningEnumerationRendering (expandFragment expandUVar render)
local notation "Symbol" => SourcePruningTemplates.Symbol
variable {NativeGuard EnumGuard : Type}

local instance : Monad List where
  pure value := [value]
  bind values continuation := values.flatMap continuation

private def Valid (language : NodeLanguage Symbol) (assignment : Nat → Term Symbol) (marker : Symbol)
    (state : EnumerationState.State Symbol EnumGuard) : Prop :=
  UnionFind.Total state.representatives ∧
    stateSatisfies state.representatives (EnumerationCorrectness.heap language state.values) assignment ∧
      ∀ (uv : Nat) (node : Option Nat) (scs : List Suspended),
        state.values[uv]? = some (.unenumerated node scs) → assignment uv = .node marker []

private theorem read_sound (language : NodeLanguage Symbol) (assignment : Nat → Term Symbol) (marker : Symbol)
    (fuel uv : Nat) (before after : EnumerationState.State Symbol EnumGuard) (value : UVarValue Symbol)
    (valid : Valid language assignment marker before) (success : Success (getValue fuel uv) before value after) :
    Valid language assignment marker after ∧ Frame before after ∧ slotSatisfies assignment uv (slot language value) ∧
      (∀ node scs, value = .unenumerated node scs → assignment uv = .node marker []) := by
  obtain ⟨frame, root, size, path, _afterPath, stored⟩ := getValue_frame fuel uv before after value valid.1 success
  have satisfied : Satisfies language (fun _ _ => True) assignment before :=
    ⟨valid.2.1, by simp [guardsHold]⟩
  have final := (EnumerationFrame.getValue_assignment language (fun _ _ => True) assignment
    fuel uv before after value valid.1 success).mpr satisfied
  have assigned := valid.2.1.1 uv root (UnionFind.sameClass_root path)
  have storedHolds : slotSatisfies assignment root (slot language value) := by
    simpa only [EnumerationCorrectness.heap, stored, Option.getD_some] using valid.2.1.2 root
  refine ⟨⟨frame.total valid.1, final.1, ?_⟩, frame, ?_, ?_⟩
  · intro held node scs found
    exact valid.2.2 held node scs (by simpa only [frame.values] using found)
  · cases value <;> simp_all [slot, slotSatisfies]
  · intro node scs same
    exact assigned.trans (valid.2.2 root node scs (by simpa only [same] using stored))

private theorem fragment_sound (heap : InternedConstructorTemplates.State Symbol NativeGuard)
    (language : NodeLanguage Symbol) (assignment : Nat → Term Symbol) (marker : Symbol)
    (fuel : Nat) (fragment : Fragment Symbol) (before after : EnumerationState.State Symbol EnumGuard)
    (term : Term Symbol) (valid : Valid language assignment marker before)
    (success : Success (expandFragment heap marker fuel fragment) before term after) :
    Valid language assignment marker after ∧ Frame before after ∧ term = fill assignment fragment := by
  induction fuel generalizing fragment before after term with
  | zero => exact (success_failure .fuelExhausted before after term success).elim
  | succ fuel ih =>
      cases fragment with
      | node symbol children =>
          obtain ⟨terms, middle, traversed, final⟩ := (success_bind _ _ _ _ _).mp success
          obtain ⟨invariant, related⟩ := mapM_sound (expandFragment heap marker fuel)
            (fun state => Valid language assignment marker state ∧ Frame before state)
            (fun child output => output = fill assignment child)
            (fun child previous output next stateValid step => by
              obtain ⟨nextValid, frame, same⟩ := ih child previous next output stateValid.1 step
              exact ⟨⟨nextValid, stateValid.2.trans frame⟩, same⟩)
            children before middle terms ⟨valid, .refl before⟩ traversed
          obtain ⟨rfl, rfl⟩ := (success_pure (.node symbol terms) term middle after).mp final
          exact ⟨invariant.1, invariant.2, by simp [fill, all₂_map_eq (fill assignment) children terms related]⟩
      | hole uv =>
          obtain ⟨value, middle, reading, continued⟩ := (success_bind _ _ _ _ _).mp success
          obtain ⟨readValid, frame, equation, free⟩ := read_sound language assignment marker
            (fuel + 1) uv before middle value valid reading
          cases value with
          | eliminated => exact (success_failure .unfinishedFragment middle after term continued).elim
          | unenumerated node scs =>
              have chosen := free node scs rfl
              cases node with
              | none => exact (success_failure .unfinishedFragment middle after term continued).elim
              | some handle =>
                  cases decoded : lookupNode heap handle with
                  | none =>
                      simp only [decoded] at continued
                      exact (success_failure .unresolvedReference middle after term continued).elim
                  | some value =>
                      simp only [decoded] at continued
                      by_cases boundary : MergedOrdinaryHeight.recursiveBoundary value = true
                      · simp only [ite_eq_left boundary] at continued
                        obtain ⟨rfl, rfl⟩ := (success_pure (.node marker []) term middle after).mp continued
                        exact ⟨readValid, frame, by simpa only [fill] using chosen.symm⟩
                      · simp only [ite_eq_right boundary] at continued
                        exact (success_failure .unfinishedFragment middle after term continued).elim
          | enumerated storedFragment =>
              obtain ⟨afterValid, afterFrame, same⟩ := ih storedFragment middle after term readValid continued
              exact ⟨afterValid, frame.trans afterFrame, by simpa only [fill, slot, slotSatisfies] using same.trans equation⟩

private theorem root_sound (heap : InternedConstructorTemplates.State Symbol NativeGuard)
    (language : NodeLanguage Symbol) (assignment : Nat → Term Symbol) (marker : Symbol)
    (fuel uv : Nat) (before after : EnumerationState.State Symbol EnumGuard) (term : Term Symbol)
    (valid : Valid language assignment marker before)
    (success : Success (expandUVar heap marker fuel uv) before term after) :
    Valid language assignment marker after ∧ Frame before after ∧ term = assignment uv := by
  obtain ⟨value, middle, reading, continued⟩ := (success_bind _ _ _ _ _).mp success
  obtain ⟨readValid, frame, equation, free⟩ := read_sound language assignment marker
    (fuel + 1) uv before middle value valid reading
  cases value with
  | eliminated => exact (reject_unsuccessful middle after term continued).elim
  | unenumerated node scs =>
      have chosen := free node scs rfl
      cases node with
      | none => exact (reject_unsuccessful middle after term continued).elim
      | some handle =>
          cases decoded : lookupNode heap handle with
          | none =>
              simp only [decoded] at continued
              exact (success_failure .unresolvedReference middle after term continued).elim
          | some value =>
              simp only [decoded] at continued
              by_cases boundary : MergedOrdinaryHeight.recursiveBoundary value = true
              · simp only [ite_eq_left boundary] at continued
                obtain ⟨rfl, rfl⟩ := (success_pure (.node marker []) term middle after).mp continued
                exact ⟨readValid, frame, chosen.symm⟩
              · simp only [ite_eq_right boundary] at continued
                exact (reject_unsuccessful middle after term continued).elim
  | enumerated fragment =>
      obtain ⟨afterValid, afterFrame, same⟩ := fragment_sound heap language assignment marker fuel fragment
        middle after term readValid continued
      exact ⟨afterValid, frame.trans afterFrame, same.trans equation⟩

/-- Actual recursive-marker rendering and checked residuals construct one current native assignment. -/
theorem render_assignment (heap : InternedConstructorTemplates.State Symbol NativeGuard)
    (holds : NativeGuard → Term Symbol → Bool) (ambient : InternedGuardedLanguage.Env Symbol)
    (meaning : EnumGuard → Term Symbol → Prop) (marker : Symbol) (fuel uv : Nat)
    (before after : EnumerationState.State Symbol EnumGuard) (term : Term Symbol)
    (pending : List (EnumGuard × Term Symbol)) (safe : Safe before)
    (level : Nat → Nat) (frontier : Nat) (ordered : EnumerationOrder.Stratified before level frontier)
    (choices : ∀ (slot : Nat) (node : Option Nat) (scs : List Suspended),
      before.values[slot]? = some (.unenumerated node scs) →
      scs = [] ∧ ∀ handle, node = some handle →
        SourcePruningEnumerationNativeLanguage.handles holds ambient heap handle (.node marker []))
    (success : Success (render heap marker fuel uv) before (term, pending) after)
    (checked : ∀ obligation ∈ pending, meaning obligation.1 obligation.2) :
    ∃ assignment : Nat → Term Symbol,
      Satisfies (SourcePruningEnumerationNativeLanguage.handles holds ambient heap) meaning assignment before ∧
      term = assignment uv ∧ Frame before after ∧
      Satisfies (SourcePruningEnumerationNativeLanguage.handles holds ambient heap) meaning assignment after
 := by
  let language := SourcePruningEnumerationNativeLanguage.handles holds ambient heap
  obtain ⟨assignment, equations, chosen⟩ := EnumerationPendingAssignment.stratified_pending_assignment before safe level frontier
    ordered (.node marker []) language choices
  unfold render at success
  obtain ⟨rendered, middle, rendering, afterRoot⟩ := (success_bind _ _ _ _ _).mp success
  obtain ⟨middleValid, rootFrame, sameTerm⟩ := root_sound heap language assignment marker fuel uv
    before middle rendered ⟨safe.1.total, equations, chosen⟩ rendering
  obtain ⟨current, readAfter, reading, afterRead⟩ := (success_bind _ _ _ _ _).mp afterRoot
  obtain ⟨currentSame, readSame⟩ := (get_success middle readAfter current).mp reading
  subst current
  subst readAfter
  obtain ⟨obligations, guarded, traversal, final⟩ := (success_bind _ _ _ _ _).mp afterRead
  obtain ⟨samePair, afterSame⟩ := (success_pure (rendered, obligations) (term, pending) guarded after).mp final
  have termSame : term = rendered := congrArg Prod.fst samePair
  have pendingSame : pending = obligations := congrArg Prod.snd samePair
  subst term
  subst obligations
  subst guarded
  let action : EnumGuard × Fragment Symbol → EnumerateM Symbol EnumGuard (EnumGuard × Term Symbol) :=
    fun obligation => do
    pure (obligation.1, ← expandFragment heap marker fuel obligation.2)
  have step : ∀ obligation previous output next,
      (Valid language assignment marker previous ∧ Frame middle previous) →
      Success (action obligation) previous output next →
      (Valid language assignment marker next ∧ Frame middle next) ∧
        output = (obligation.1, fill assignment obligation.2) := by
    intro obligation previous output next valid observed
    obtain ⟨subterm, reached, rendering, final⟩ := (success_bind _ _ _ _ _).mp observed
    obtain ⟨nextValid, frame, exactTerm⟩ := fragment_sound heap language assignment marker fuel
      obligation.2 previous reached subterm valid.1 rendering
    obtain ⟨rfl, rfl⟩ := (success_pure (obligation.1, subterm) output reached next).mp final
    exact ⟨⟨nextValid, valid.2.trans frame⟩, by simp only [exactTerm]⟩
  obtain ⟨guardedValid, related⟩ := mapM_sound action
    (fun state => Valid language assignment marker state ∧ Frame middle state)
    (fun obligation output => output = (obligation.1, fill assignment obligation.2)) step
    middle.obligations middle after pending ⟨middleValid, .refl middle⟩ traversal
  have exactPending := all₂_map_eq (fun obligation => (obligation.1, fill assignment obligation.2))
    middle.obligations pending related
  have satisfied : Satisfies language meaning assignment before := by
    refine ⟨equations, ?_⟩
    intro obligation member
    apply checked (obligation.1, fill assignment obligation.2)
    rw [exactPending]
    exact List.mem_map.mpr ⟨obligation, by simpa only [rootFrame.obligations] using member, rfl⟩
  have frame := rootFrame.trans guardedValid.2
  exact ⟨assignment, satisfied, sameTerm, frame,
    (SourcePruningEnumerationNativeLanguage.satisfies_frame language meaning assignment before after frame).mpr satisfied⟩


end MicroCFTA.SourcePruningEnumerationPendingRendering

#check MicroCFTA.SourcePruningEnumerationPendingRendering.render_assignment
#print axioms MicroCFTA.SourcePruningEnumerationPendingRendering.render_assignment
