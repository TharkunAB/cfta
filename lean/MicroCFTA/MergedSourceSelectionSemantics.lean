import MicroCFTA.MergedSourceSelection
import MicroCFTA.MergedComparisonSoundnessReplay
import MicroCFTA.MergedComparisonSoundness

/-!
# Replay and coverage of ordered source child selection

Selection retains its exact input records and actual comparison effects.
Every removed input has a successful comparison with a retained original
closed Mu. Completed selection replays exactly in later source caches.
-/
namespace MicroCFTA.MergedSourceSelectionSemantics
open InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedNestedFacts InternedNestedProvenance InternedFreshProbeKeys
open MergedPhysicalWarmup MergedSourceComparison MergedComparisonFacts MergedComparisonCompletion
open MergedSourceSelection MergedColdReaderClosedInputs MergedPhysicalGroupColumns

/-- Ordered cover search replays its exact Boolean and all earlier failed comparisons without effects. -/
theorem any_replay [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Symbol]
    (clear : Guard → Bool) (fuel : Nat) (narrow : Value Symbol Guard) (wides : List (Value Symbol Guard))
    (state : State Symbol Guard) (facts : Facts state) (prepared : Prepared state)
    (narrowInput : Available state narrow) (wideInputs : Values state wides) (wideClosed : ClosedValues wides)
    (accepted : Bool) (after view : State Symbol Guard)
    (done : anyAccepts clear fuel narrow wides state = .done accepted after) (growth : Grows after view) :
    anyAccepts clear fuel narrow wides view = .done accepted view := by
  induction wides generalizing state with
  | nil => cases done; rfl
  | cons wide rest ih =>
      by_cases closed : narrow.free = []
      · have verified := check_verified clear fuel [] wide narrow state facts prepared
          (wideInputs wide List.mem_cons_self) narrowInput (wideClosed wide List.mem_cons_self) closed
        cases first : check clear fuel [] wide narrow state with
        | failed => simp only [anyAccepts, ite_eq_left closed, first, Result.bind, reduceCtorEq] at done
        | done answer middle =>
            have effect := verified.effect first
            have restInputs : Values middle rest := fun value member =>
              (wideInputs value (List.mem_cons_of_mem _ member)).grows state middle effect.growth effect.history
            have restClosed : ClosedValues rest := fun value member => wideClosed value (List.mem_cons_of_mem _ member)
            cases answer with
            | true =>
                have equal : true = accepted ∧ middle = after := by
                  simpa only [anyAccepts, ite_eq_left closed, first, Result.bind, ↓reduceIte, Result.done.injEq] using done
                rcases equal with ⟨rfl, rfl⟩
                simp only [anyAccepts, ite_eq_left closed,
                  MergedComparisonReplay.check_replay clear fuel [] wide narrow state facts prepared
                    (wideInputs wide List.mem_cons_self) narrowInput (wideClosed wide List.mem_cons_self) closed
                    true middle view first growth, Result.bind, ↓reduceIte]
            | false =>
                have tail : anyAccepts clear fuel narrow rest middle = .done accepted after := by
                  simpa only [anyAccepts, ite_eq_left closed, first, Result.bind, Bool.false_eq_true, ↓reduceIte] using done
                have narrowMiddle := narrowInput.grows state middle effect.growth effect.history
                have tailEffect := (any_verified clear fuel narrow rest middle effect.facts
                  (prepared.preserve effect.unchanged) narrowMiddle restInputs restClosed).effect tail
                simp only [anyAccepts, ite_eq_left closed,
                  MergedComparisonReplay.check_replay clear fuel [] wide narrow state facts prepared
                    (wideInputs wide List.mem_cons_self) narrowInput (wideClosed wide List.mem_cons_self) closed
                    false middle view first (grows_trans tailEffect.growth growth), Result.bind, Bool.false_eq_true, ↓reduceIte]
                exact ih middle effect.facts (prepared.preserve effect.unchanged) narrowMiddle restInputs restClosed tail
      · simp only [anyAccepts, ite_eq_right closed] at done ⊢
        cases done
        rfl

/-- The complete filter replays the original retained list in any later cache without allocation. -/
theorem retain_replay [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Symbol]
    (clear : Guard → Bool) (fuel : Nat) (recursive inputs : List (Value Symbol Guard))
    (state : State Symbol Guard) (facts : Facts state) (prepared : Prepared state)
    (recInputs : Values state recursive) (recClosed : ClosedValues recursive) (available : Values state inputs)
    (retained : List (Value Symbol Guard)) (after view : State Symbol Guard)
    (done : retain clear fuel recursive inputs state = .done retained after) (growth : Grows after view) :
    retain clear fuel recursive inputs view = .done retained view := by
  induction inputs generalizing state retained with
  | nil => cases done; rfl
  | cons child rest ih =>
      have restInputs : Values state rest := fun value member => available value (List.mem_cons_of_mem _ member)
      by_cases recursiveChild : closedMu child = true
      · cases tail : retain clear fuel recursive rest state with
        | failed => simp only [retain, ite_eq_left recursiveChild, tail, Result.bind, reduceCtorEq] at done
        | done values final =>
            have equal : child :: values = retained ∧ final = after := by
              simpa only [retain, ite_eq_left recursiveChild, tail, Result.bind, Result.done.injEq] using done
            rcases equal with ⟨rfl, rfl⟩
            simp only [retain, ite_eq_left recursiveChild,
              ih state facts prepared recInputs restInputs values tail, Result.bind]
      · cases first : anyAccepts clear fuel child recursive state with
        | failed => simp only [retain, ite_eq_right recursiveChild, first, Result.bind, reduceCtorEq] at done
        | done covered middle =>
            have effect := (any_verified clear fuel child recursive state facts prepared
              (available child List.mem_cons_self) recInputs recClosed).effect first
            have middleRec : Values middle recursive := fun value member =>
              (recInputs value member).grows state middle effect.growth effect.history
            have middleInputs : Values middle rest := fun value member =>
              (restInputs value member).grows state middle effect.growth effect.history
            cases tail : retain clear fuel recursive rest middle with
            | failed => simp only [retain, ite_eq_right recursiveChild, first, Result.bind, tail, reduceCtorEq] at done
            | done values final =>
                have equal : (if covered then values else child :: values) = retained ∧ final = after := by
                  simpa only [retain, ite_eq_right recursiveChild, first, Result.bind, tail, Result.done.injEq] using done
                rcases equal with ⟨rfl, rfl⟩
                have tailEffect := (retain_verified clear fuel recursive rest middle effect.facts
                  (prepared.preserve effect.unchanged) middleRec recClosed middleInputs).effect tail
                simp only [retain, ite_eq_right recursiveChild,
                  any_replay clear fuel child recursive state facts prepared (available child List.mem_cons_self)
                    recInputs recClosed covered middle view first (grows_trans tailEffect.growth growth), Result.bind,
                  ih middle effect.facts (prepared.preserve effect.unchanged) middleRec middleInputs values tail]

/-- Successful source selection replays the same canonical retained records without effects in a later cache. -/
theorem select_replay [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Symbol]
    (clear : Guard → Bool) (fuel : Nat) (inputs : List (Value Symbol Guard))
    (state : State Symbol Guard) (facts : Facts state) (prepared : Prepared state) (available : Values state inputs)
    (retained : List (Value Symbol Guard)) (after view : State Symbol Guard)
    (done : select clear fuel inputs state = .done retained after) (growth : Grows after view) :
    select clear fuel inputs view = .done retained view := by
  cases filtered : retain clear fuel (inputs.filter closedMu) inputs state with
  | failed => simp only [select, filtered, Result.bind, reduceCtorEq] at done
  | done values final =>
      have equal : distinctNodes values = retained ∧ final = after := by
        simpa only [select, filtered, Result.bind, Result.done.injEq] using done
      rcases equal with ⟨rfl, rfl⟩
      simp only [select, retain_replay clear fuel (inputs.filter closedMu) inputs state facts prepared
        (fun value member => available value (List.mem_filter.mp member).1) (recursive_closed inputs)
        available values final view filtered growth, Result.bind]

/-- A successful ordered cover search has an original wide witness and an exact true comparison in a later cache. -/
theorem any_witness [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Symbol]
    (clear : Guard → Bool) (fuel : Nat) (narrow : Value Symbol Guard) (wides : List (Value Symbol Guard))
    (state : State Symbol Guard) (facts : Facts state) (prepared : Prepared state)
    (narrowInput : Available state narrow) (wideInputs : Values state wides) (wideClosed : ClosedValues wides)
    (after view : State Symbol Guard)
    (done : anyAccepts clear fuel narrow wides state = .done true after) (growth : Grows after view) :
    narrow.free = [] ∧ ∃ wide ∈ wides, check clear fuel [] wide narrow view = .done true view := by
  induction wides generalizing state with
  | nil => cases done
  | cons wide rest ih =>
      by_cases closed : narrow.free = []
      · have verified := check_verified clear fuel [] wide narrow state facts prepared
          (wideInputs wide List.mem_cons_self) narrowInput (wideClosed wide List.mem_cons_self) closed
        cases first : check clear fuel [] wide narrow state with
        | failed => simp only [anyAccepts, ite_eq_left closed, first, Result.bind, reduceCtorEq] at done
        | done answer middle =>
            have effect := verified.effect first
            cases answer with
            | true =>
                have equal : middle = after := by
                  simpa only [anyAccepts, ite_eq_left closed, first, Result.bind, ↓reduceIte, Result.done.injEq, true_and] using done
                subst middle
                exact ⟨closed, wide, List.mem_cons_self,
                  MergedComparisonReplay.check_replay clear fuel [] wide narrow state facts prepared
                    (wideInputs wide List.mem_cons_self) narrowInput (wideClosed wide List.mem_cons_self) closed
                    true after view first growth⟩
            | false =>
                have tail : anyAccepts clear fuel narrow rest middle = .done true after := by
                  simpa only [anyAccepts, ite_eq_left closed, first, Result.bind, Bool.false_eq_true, ↓reduceIte] using done
                obtain ⟨closed, wide, member, compared⟩ := ih middle effect.facts (prepared.preserve effect.unchanged)
                  (narrowInput.grows state middle effect.growth effect.history)
                  (fun value member => (wideInputs value (List.mem_cons_of_mem _ member)).grows state middle effect.growth effect.history)
                  (fun value member => wideClosed value (List.mem_cons_of_mem _ member)) tail
                exact ⟨closed, wide, List.mem_cons_of_mem _ member, compared⟩
      · simp only [anyAccepts, ite_eq_right closed] at done
        cases done

/-- The ordered filter preserves every original closed Mu regardless of comparison answers. -/
theorem retain_recursive [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Symbol]
    (clear : Guard → Bool) (fuel : Nat) (recursive inputs : List (Value Symbol Guard))
    (state : State Symbol Guard) (retained : List (Value Symbol Guard)) (after : State Symbol Guard)
    (done : retain clear fuel recursive inputs state = .done retained after)
    (value : Value Symbol Guard) (member : value ∈ inputs) (marked : closedMu value = true) : value ∈ retained := by
  induction inputs generalizing state retained with
  | nil => cases member
  | cons child rest ih =>
      by_cases recursiveChild : closedMu child = true
      · cases tail : retain clear fuel recursive rest state with
        | failed => simp only [retain, ite_eq_left recursiveChild, tail, Result.bind, reduceCtorEq] at done
        | done values final =>
            have equal : child :: values = retained ∧ final = after := by
              simpa only [retain, ite_eq_left recursiveChild, tail, Result.bind, Result.done.injEq] using done
            rcases equal with ⟨rfl, rfl⟩
            rcases List.mem_cons.mp member with same | member
            · exact List.mem_cons.mpr (Or.inl same)
            · exact List.mem_cons_of_mem _ (ih state values tail member)
      · have tailMember : value ∈ rest := (List.mem_cons.mp member).resolve_left (fun same => recursiveChild (same ▸ marked))
        cases first : anyAccepts clear fuel child recursive state with
        | failed => simp only [retain, ite_eq_right recursiveChild, first, Result.bind, reduceCtorEq] at done
        | done covered middle =>
            cases tail : retain clear fuel recursive rest middle with
            | failed => simp only [retain, ite_eq_right recursiveChild, first, Result.bind, tail, reduceCtorEq] at done
            | done values final =>
                have equal : (if covered then values else child :: values) = retained ∧ final = after := by
                  simpa only [retain, ite_eq_right recursiveChild, first, Result.bind, tail, Result.done.injEq] using done
                rcases equal with ⟨rfl, rfl⟩
                have present := ih middle values tail tailMember
                cases covered with
                | true => exact present
                | false => exact List.mem_cons_of_mem _ present

/-- Every discarded source record has a successful original recursive cover in each later cache. -/
theorem retain_coverage [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Symbol]
    (clear : Guard → Bool) (fuel : Nat) (recursive inputs : List (Value Symbol Guard))
    (state : State Symbol Guard) (facts : Facts state) (prepared : Prepared state)
    (recInputs : Values state recursive) (recClosed : ClosedValues recursive) (available : Values state inputs)
    (retained : List (Value Symbol Guard)) (after view : State Symbol Guard)
    (done : retain clear fuel recursive inputs state = .done retained after) (growth : Grows after view)
    (value : Value Symbol Guard) (member : value ∈ inputs) :
    value ∈ retained ∨ (value.free = [] ∧ ∃ wide ∈ recursive, check clear fuel [] wide value view = .done true view) := by
  induction inputs generalizing state retained with
  | nil => cases member
  | cons child rest ih =>
      have restInputs : Values state rest := fun value member => available value (List.mem_cons_of_mem _ member)
      by_cases recursiveChild : closedMu child = true
      · cases tail : retain clear fuel recursive rest state with
        | failed => simp only [retain, ite_eq_left recursiveChild, tail, Result.bind, reduceCtorEq] at done
        | done values final =>
            have equal : child :: values = retained ∧ final = after := by
              simpa only [retain, ite_eq_left recursiveChild, tail, Result.bind, Result.done.injEq] using done
            rcases equal with ⟨rfl, rfl⟩
            rcases List.mem_cons.mp member with same | member
            · exact Or.inl (List.mem_cons.mpr (Or.inl same))
            · rcases ih state facts prepared recInputs restInputs values tail member with kept | covered
              · exact Or.inl (List.mem_cons_of_mem _ kept)
              · exact Or.inr covered
      · cases first : anyAccepts clear fuel child recursive state with
        | failed => simp only [retain, ite_eq_right recursiveChild, first, Result.bind, reduceCtorEq] at done
        | done covered middle =>
            have effect := (any_verified clear fuel child recursive state facts prepared
              (available child List.mem_cons_self) recInputs recClosed).effect first
            have middleRec : Values middle recursive := fun value member =>
              (recInputs value member).grows state middle effect.growth effect.history
            have middleInputs : Values middle rest := fun value member =>
              (restInputs value member).grows state middle effect.growth effect.history
            cases tail : retain clear fuel recursive rest middle with
            | failed => simp only [retain, ite_eq_right recursiveChild, first, Result.bind, tail, reduceCtorEq] at done
            | done values final =>
                have equal : (if covered then values else child :: values) = retained ∧ final = after := by
                  simpa only [retain, ite_eq_right recursiveChild, first, Result.bind, tail, Result.done.injEq] using done
                rcases equal with ⟨rfl, rfl⟩
                rcases List.mem_cons.mp member with same | member
                · subst value
                  cases covered with
                  | false => exact Or.inl List.mem_cons_self
                  | true =>
                      have tailEffect := (retain_verified clear fuel recursive rest middle effect.facts
                        (prepared.preserve effect.unchanged) middleRec recClosed middleInputs).effect tail
                      exact Or.inr (any_witness clear fuel child recursive state facts prepared
                        (available child List.mem_cons_self) recInputs recClosed middle view first
                        (grows_trans tailEffect.growth growth))
                · rcases ih middle effect.facts (prepared.preserve effect.unchanged) middleRec middleInputs values tail member with kept | witness
                  · left
                    cases covered with
                    | true => exact kept
                    | false => exact List.mem_cons_of_mem _ kept
                  · exact Or.inr witness

/-- Every original input is retained or covered by a retained original closed Mu with an exact true comparison. -/
theorem select_coverage [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Symbol]
    (clear : Guard → Bool) (fuel : Nat) (inputs : List (Value Symbol Guard))
    (state : State Symbol Guard) (facts : Facts state) (prepared : Prepared state) (available : Values state inputs)
    (retained : List (Value Symbol Guard)) (after view : State Symbol Guard)
    (done : select clear fuel inputs state = .done retained after) (growth : Grows after view)
    (value : Value Symbol Guard) (member : value ∈ inputs) :
    value ∈ retained ∨ (value.free = [] ∧ ∃ wide ∈ retained, closedMu wide = true ∧
      check clear fuel [] wide value view = .done true view) := by
  cases filtered : retain clear fuel (inputs.filter closedMu) inputs state with
  | failed => simp only [select, filtered, Result.bind, reduceCtorEq] at done
  | done values final =>
      have equal : distinctNodes values = retained ∧ final = after := by
        simpa only [select, filtered, Result.bind, Result.done.injEq] using done
      rcases equal with ⟨rfl, rfl⟩
      have effect := (retain_verified clear fuel (inputs.filter closedMu) inputs state facts prepared
        (fun value member => available value (List.mem_filter.mp member).1) (recursive_closed inputs) available).effect filtered
      have resident : ∀ value ∈ values, Resident final value := fun value member =>
        ((available value (retain_subset clear fuel _ inputs state values final filtered value member)).grows
          state final effect.growth effect.history).resident
      have kept (value : Value Symbol Guard) (member : value ∈ values) : value ∈ distinctNodes values :=
        InternedUnionRetention.distinctNodes_retains final effect.facts.coherent values resident value member
      rcases retain_coverage clear fuel (inputs.filter closedMu) inputs state facts prepared
        (fun value member => available value (List.mem_filter.mp member).1) (recursive_closed inputs)
        available values final view filtered growth value member with member | ⟨closed, wide, recursive, covered⟩
      · exact Or.inl (kept value member)
      · have original := (List.mem_filter.mp recursive).1
        have marked := (List.mem_filter.mp recursive).2
        exact Or.inr ⟨closed, wide, kept wide (retain_recursive clear fuel _ inputs state values final filtered wide original marked),
          marked, covered⟩

/-- Actual selection preserves exactly the union language in any later retained source cache. -/
theorem select_exact [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Symbol]
    (clear : Guard → Bool) (fuel : Nat) (inputs : List (Value Symbol Guard))
    (state : State Symbol Guard) (facts : Facts state) (prepared : Prepared state) (available : Values state inputs)
    (retained : List (Value Symbol Guard)) (after view : State Symbol Guard)
    (done : select clear fuel inputs state = .done retained after) (growth : Grows after view)
    (viewFacts : Facts view) (viewPrepared : Prepared view) (viewInputs : Values view inputs)
    (meaning : Guard → Language.Term Symbol → Bool)
    (clearTrue : ∀ guard, clear guard = true → ∀ term, meaning guard term = true)
    (term : Language.Term Symbol) :
    (∃ value ∈ retained, EpsilonUnion.Accepts (MergedPhysicalLanguage.graph view meaning) value term) ↔
      ∃ value ∈ inputs, EpsilonUnion.Accepts (MergedPhysicalLanguage.graph view meaning) value term := by
  constructor
  · rintro ⟨value, member, accepted⟩
    exact ⟨value, select_subset clear fuel inputs state retained after done value member, accepted⟩
  · rintro ⟨value, member, accepted⟩
    rcases select_coverage clear fuel inputs state facts prepared available retained after view done growth value member with
      kept | ⟨closed, wide, kept, marked, compared⟩
    · exact ⟨value, kept, accepted⟩
    · have wideInput := viewInputs wide (select_subset clear fuel inputs state retained after done wide kept)
      have wideClosed : wide.free = [] := by
        cases wide with
        | empty | reference | node | union => simp [closedMu] at marked
        | mu entry body depth ordinary => exact List.isEmpty_iff.mp marked
      exact ⟨wide, kept, MergedComparisonSoundness.check_fixed_sound view viewFacts viewPrepared
        clear meaning clearTrue fuel wide value wideInput (viewInputs value member) wideClosed closed compared term accepted⟩

/-- A completed cold selection preserves the exact union language in its actual returned cache. -/
theorem select_actual_exact [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Symbol]
    (clear : Guard → Bool) (fuel : Nat) (inputs : List (Value Symbol Guard))
    (state : State Symbol Guard) (facts : Facts state) (prepared : Prepared state) (available : Values state inputs)
    (retained : List (Value Symbol Guard)) (after : State Symbol Guard)
    (done : select clear fuel inputs state = .done retained after)
    (meaning : Guard → Language.Term Symbol → Bool)
    (clearTrue : ∀ guard, clear guard = true → ∀ term, meaning guard term = true)
    (term : Language.Term Symbol) :
    (∃ value ∈ retained, EpsilonUnion.Accepts (MergedPhysicalLanguage.graph after meaning) value term) ↔
      ∃ value ∈ inputs, EpsilonUnion.Accepts (MergedPhysicalLanguage.graph after meaning) value term := by
  have effect := (select_verified clear fuel inputs state facts prepared available).effect done
  exact select_exact clear fuel inputs state facts prepared available retained after after done (grows_refl after)
    effect.facts (prepared.preserve effect.unchanged)
    (fun value member => (available value member).grows state after effect.growth effect.history) meaning clearTrue term

/-- Source facts derive complete stable selection and exact actual-cache language without recursive premises. -/
theorem select_complete_exact [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Symbol]
    (clear : Guard → Bool) (inputs : List (Value Symbol Guard))
    (state : State Symbol Guard) (facts : Facts state) (prepared : Prepared state) (available : Values state inputs)
    (meaning : Guard → Language.Term Symbol → Bool)
    (clearTrue : ∀ guard, clear guard = true → ∀ term, meaning guard term = true) :
    ∃ bound retained after,
      (∀ fuel, bound ≤ fuel → select clear fuel inputs state = .done retained after) ∧
      Verified state (.done retained after) ∧ Prepared after ∧
      (∀ fuel, bound ≤ fuel → select clear fuel inputs after = .done retained after) ∧
      ∀ term, (∃ value ∈ retained, EpsilonUnion.Accepts (MergedPhysicalLanguage.graph after meaning) value term) ↔
        ∃ value ∈ inputs, EpsilonUnion.Accepts (MergedPhysicalLanguage.graph after meaning) value term := by
  obtain ⟨bound, retained, after, stable, verified, afterPrepared⟩ :=
    select_complete clear inputs state facts prepared available
  exact ⟨bound, retained, after, stable, verified, afterPrepared,
    fun fuel enough => select_replay clear fuel inputs state facts prepared available retained after after (stable fuel enough) (grows_refl after),
    select_actual_exact clear bound inputs state facts prepared available retained after (stable bound (Nat.le_refl _)) meaning clearTrue⟩

end MicroCFTA.MergedSourceSelectionSemantics
