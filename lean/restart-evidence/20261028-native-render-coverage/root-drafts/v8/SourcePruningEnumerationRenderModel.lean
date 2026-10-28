import MicroCFTA.SourcePruningEnumerationRendering

/-!
# Exact residual checks at the actual native renderer

The original assignment fixes the actual rendered root and every residual.
This observer does not assume that any returned residual check succeeds.
-/
namespace MicroCFTA.SourcePruningEnumerationRendering
open Language Fragments EnumerationState EnumerationCorrectness EnumerationSchedule
open EnumerationDriver EnumerationCompressionFrame SourcePruningEnumerationNodes
local notation "Symbol" => SourcePruningTemplates.Symbol
variable {NativeGuard EnumGuard : Type}

local instance nativeRenderModelMonadList : Monad List where
  pure value := [value]
  bind values continuation := values.flatMap continuation

private def Valid (language : NodeLanguage Symbol) (assignment : Nat → Term Symbol)
    (state : EnumerationState.State Symbol EnumGuard) : Prop :=
  UnionFind.Total state.representatives ∧
    stateSatisfies state.representatives (EnumerationCorrectness.heap language state.values) assignment ∧ Discharged state

private theorem read_sound (language : NodeLanguage Symbol) (assignment : Nat → Term Symbol)
    (fuel uv : Nat) (before after : EnumerationState.State Symbol EnumGuard) (value : UVarValue Symbol)
    (valid : Valid language assignment before) (success : Success (getValue fuel uv) before value after) :
    Valid language assignment after ∧ Frame before after ∧ slotSatisfies assignment uv (slot language value) ∧
      (∀ node scs, value = .unenumerated node scs → node = none ∧ scs = []) := by
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
    exact valid.2.2 root node scs (by simpa only [same] using stored)

private theorem fragment_sound (heap : InternedConstructorTemplates.State Symbol NativeGuard)
    (language : NodeLanguage Symbol) (assignment : Nat → Term Symbol) (marker : Symbol)
    (fuel : Nat) (fragment : Fragment Symbol) (before after : EnumerationState.State Symbol EnumGuard)
    (term : Term Symbol) (valid : Valid language assignment before)
    (success : Success (expandFragment heap marker fuel fragment) before term after) :
    Valid language assignment after ∧ Frame before after ∧ term = fill assignment fragment := by
  induction fuel generalizing fragment before after term with
  | zero => exact (success_failure .fuelExhausted before after term success).elim
  | succ fuel ih =>
      cases fragment with
      | node symbol children =>
          obtain ⟨terms, middle, traversed, final⟩ := (success_bind _ _ _ _ _).mp success
          obtain ⟨invariant, related⟩ := mapM_sound (expandFragment heap marker fuel)
            (fun state => Valid language assignment state ∧ Frame before state)
            (fun child output => output = fill assignment child)
            (fun child previous output next stateValid step => by
              obtain ⟨nextValid, frame, same⟩ := ih child previous next output stateValid.1 step
              exact ⟨⟨nextValid, stateValid.2.trans frame⟩, same⟩)
            children before middle terms ⟨valid, .refl before⟩ traversed
          obtain ⟨rfl, rfl⟩ := (success_pure (.node symbol terms) term middle after).mp final
          exact ⟨invariant.1, invariant.2, by simp [fill, all₂_map_eq (fill assignment) children terms related]⟩
      | hole uv =>
          obtain ⟨value, middle, reading, continued⟩ := (success_bind _ _ _ _ _).mp success
          obtain ⟨readValid, frame, equation, free⟩ := read_sound language assignment
            (fuel + 1) uv before middle value valid reading
          cases value with
          | eliminated => exact (success_failure .unfinishedFragment middle after term continued).elim
          | unenumerated node scs =>
              obtain ⟨rfl, rfl⟩ := free node scs rfl
              exact (success_failure .unfinishedFragment middle after term continued).elim
          | enumerated storedFragment =>
              obtain ⟨afterValid, afterFrame, same⟩ := ih storedFragment middle after term readValid continued
              exact ⟨afterValid, frame.trans afterFrame, by simpa only [fill, slot, slotSatisfies] using same.trans equation⟩

private theorem root_sound (heap : InternedConstructorTemplates.State Symbol NativeGuard)
    (language : NodeLanguage Symbol) (assignment : Nat → Term Symbol) (marker : Symbol)
    (fuel uv : Nat) (before after : EnumerationState.State Symbol EnumGuard) (term : Term Symbol)
    (valid : Valid language assignment before)
    (success : Success (expandUVar heap marker fuel uv) before term after) :
    Valid language assignment after ∧ Frame before after ∧ term = assignment uv := by
  obtain ⟨value, middle, reading, continued⟩ := (success_bind _ _ _ _ _).mp success
  obtain ⟨readValid, frame, equation, free⟩ := read_sound language assignment
    (fuel + 1) uv before middle value valid reading
  cases value with
  | eliminated => exact (reject_unsuccessful middle after term continued).elim
  | unenumerated node scs =>
      obtain ⟨rfl, rfl⟩ := free node scs rfl
      exact (reject_unsuccessful middle after term continued).elim
  | enumerated fragment =>
      obtain ⟨afterValid, afterFrame, same⟩ := fragment_sound heap language assignment marker fuel fragment
        middle after term readValid continued
      exact ⟨afterValid, frame.trans afterFrame, same.trans equation⟩

/-- An original model determines the actual root and all actual residual checks. -/
theorem render_model (heap : InternedConstructorTemplates.State Symbol NativeGuard)
    (language : NodeLanguage Symbol) (meaning : EnumGuard → Term Symbol → Prop)
    (assignment : Nat → Term Symbol) (marker : Symbol) (fuel uv : Nat)
    (before after : EnumerationState.State Symbol EnumGuard) (term : Term Symbol)
    (pending : List (EnumGuard × Term Symbol)) (total : UnionFind.Total before.representatives)
    (discharged : Discharged before) (satisfied : Satisfies language meaning assignment before)
    (success : Success (render heap marker fuel uv) before (term, pending) after) :
    term = assignment uv ∧
      pending = before.obligations.map (fun obligation => (obligation.1, fill assignment obligation.2)) ∧
      (∀ obligation ∈ pending, meaning obligation.1 obligation.2) ∧
      Frame before after ∧ Satisfies language meaning assignment after := by
  unfold render at success
  obtain ⟨rendered, middle, rendering, afterRoot⟩ := (success_bind _ _ _ _ _).mp success
  obtain ⟨middleValid, rootFrame, sameTerm⟩ := root_sound heap language assignment marker fuel uv
    before middle rendered ⟨total, satisfied.1, discharged⟩ rendering
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
      (Valid language assignment previous ∧ Frame middle previous) →
      Success (action obligation) previous output next →
      (Valid language assignment next ∧ Frame middle next) ∧
        output = (obligation.1, fill assignment obligation.2) := by
    intro obligation previous output next valid observed
    obtain ⟨subterm, reached, rendering, final⟩ := (success_bind _ _ _ _ _).mp observed
    obtain ⟨nextValid, frame, exactTerm⟩ := fragment_sound heap language assignment marker fuel
      obligation.2 previous reached subterm valid.1 rendering
    obtain ⟨rfl, rfl⟩ := (success_pure (obligation.1, subterm) output reached next).mp final
    exact ⟨⟨nextValid, valid.2.trans frame⟩, by simp only [exactTerm]⟩
  obtain ⟨guardedValid, related⟩ := mapM_sound action
    (fun state => Valid language assignment state ∧ Frame middle state)
    (fun obligation output => output = (obligation.1, fill assignment obligation.2)) step
    middle.obligations middle after pending ⟨middleValid, .refl middle⟩ traversal
  have exactPending := all₂_map_eq (fun obligation => (obligation.1, fill assignment obligation.2))
    middle.obligations pending related
  have originalPending : pending =
      before.obligations.map (fun obligation => (obligation.1, fill assignment obligation.2)) := by
    rw [exactPending, rootFrame.obligations]
  have checked : ∀ obligation ∈ pending, meaning obligation.1 obligation.2 := by
    intro obligation member
    rw [originalPending] at member
    obtain ⟨original, present, same⟩ := List.mem_map.mp member
    subst obligation
    exact satisfied.2 original present
  have frame := rootFrame.trans guardedValid.2
  exact ⟨sameTerm, originalPending, checked, frame,
    (SourcePruningEnumerationNativeLanguage.satisfies_frame language meaning assignment before after frame).mpr satisfied⟩

end MicroCFTA.SourcePruningEnumerationRendering
