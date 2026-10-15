import MicroCFTA.SourceMergedSelection

/-!
# Exact independent union language of general repaired child selection

Only actual successful comparisons remove a child. Their independent
language law identifies an original recursive cover. The source retains
that recursive operand and then removes only repeated coherent identities.
-/
namespace MicroCFTA.SourceMergedSelectionLanguage
open Language InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open MergedColdReaderClosedInputs (ClosedValues)
open MergedPhysicalGroupColumns (closedMu)
open MergedSourceComparison (Result)
open SourceEqualityRequiredCache SourceEqualityRequiredSemanticCache SourceMergedComparisonEffects SourceMergedSelection
open InternedGuardedLanguage (meaning)

/-- A true actual recursive-cover scan supplies an original operand that accepts each narrow term. -/
theorem any_cover [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] (clear : Guard → Bool) (fuel : Nat)
    (holds : Guard → Term Symbol → Bool) (ambient : InternedGuardedLanguage.Env Symbol)
    (clearTrue : ∀ guard, clear guard = true → ∀ term, holds guard term = true)
    (narrow : Value Symbol Guard) (wides : List (Value Symbol Guard)) (before : State Symbol Guard) (semantic : SemanticReady before)
    (narrowInput : Available before narrow) (wideInputs : Values before wides) (narrowClosed : narrow.free = []) (wideClosed : ClosedValues wides)
    (after : State Symbol Guard) (done : anyAccepts clear fuel narrow wides before = .done true after) :
    ∀ term, meaning holds ambient narrow term → ∃ wide ∈ wides, meaning holds ambient wide term := by
  induction wides generalizing before with
  | nil => cases done
  | cons wide wides ih =>
      simp only [anyAccepts, narrowClosed, ite_true] at done
      obtain ⟨accepted, middle, first, later⟩ := (bind_done _ _ true after).mp done
      cases accepted with
      | true =>
          intro term accepted
          exact ⟨wide, List.mem_cons_self, SourceMergedComparisonSoundness.check_sound clear holds ambient clearTrue fuel wide narrow before semantic
            (wideInputs _ List.mem_cons_self) narrowInput (wideClosed _ List.mem_cons_self) narrowClosed middle first term accepted⟩
      | false =>
          have effects := check_effect clear fuel [] wide narrow before semantic (wideInputs _ List.mem_cons_self) narrowInput
            (wideClosed _ List.mem_cons_self) narrowClosed false middle first
          intro term accepted
          obtain ⟨chosen, member, run⟩ := ih middle effects.2 (effects.1.available narrow narrowInput)
            (fun value member => effects.1.available value (wideInputs value (List.mem_cons_of_mem _ member)))
            (fun value member => wideClosed value (List.mem_cons_of_mem _ member)) later term accepted
          exact ⟨chosen, List.mem_cons_of_mem _ member, run⟩

/-- Every original term remains in a retained child or in one of its original recursive covers. -/
theorem retain_coverage [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] (clear : Guard → Bool) (fuel : Nat)
    (holds : Guard → Term Symbol → Bool) (ambient : InternedGuardedLanguage.Env Symbol)
    (clearTrue : ∀ guard, clear guard = true → ∀ term, holds guard term = true)
    (recursive inputs : List (Value Symbol Guard)) (before : State Symbol Guard) (semantic : SemanticReady before)
    (recInputs : Values before recursive) (recClosed : ClosedValues recursive) (available : Values before inputs) (closed : ClosedValues inputs)
    (retained : List (Value Symbol Guard)) (after : State Symbol Guard)
    (done : retain clear fuel recursive inputs before = .done retained after) :
    ∀ value ∈ inputs, ∀ term, meaning holds ambient value term → ∃ kept, (kept ∈ retained ∨ kept ∈ recursive) ∧ meaning holds ambient kept term := by
  induction inputs generalizing before retained after with
  | nil => simp
  | cons child inputs ih =>
      rw [retain] at done
      split at done
      · obtain ⟨rest, final, tail, returned⟩ := (bind_done _ _ retained after).mp done
        have parts := Result.done.inj returned
        cases parts.1; cases parts.2
        intro value member term accepted
        rcases List.mem_cons.mp member with rfl | member
        · exact ⟨_, Or.inl List.mem_cons_self, accepted⟩
        · obtain ⟨kept, present, run⟩ := ih before semantic recInputs
            (fun value member => available value (List.mem_cons_of_mem _ member))
            (fun value member => closed value (List.mem_cons_of_mem _ member)) rest after tail value member term accepted
          exact ⟨kept, present.imp (List.mem_cons_of_mem _) id, run⟩
      · obtain ⟨covered, middle, first, later⟩ := (bind_done _ _ retained after).mp done
        have effects := any_effect clear fuel child recursive before semantic (available _ List.mem_cons_self) recInputs
          (closed _ List.mem_cons_self) recClosed covered middle first
        obtain ⟨rest, final, tail, returned⟩ := (bind_done _ _ retained after).mp later
        have remaining := ih middle effects.2 (fun value member => effects.1.available value (recInputs value member))
          (fun value member => effects.1.available value (available value (List.mem_cons_of_mem _ member)))
          (fun value member => closed value (List.mem_cons_of_mem _ member)) rest final tail
        cases covered with
        | true =>
            have parts := Result.done.inj returned
            cases parts.1; cases parts.2
            intro value member term accepted
            rcases List.mem_cons.mp member with rfl | member
            · obtain ⟨wide, member, run⟩ := any_cover clear fuel holds ambient clearTrue _ recursive before semantic
                (available _ List.mem_cons_self) recInputs (closed _ List.mem_cons_self) recClosed middle first term accepted
              exact ⟨wide, Or.inr member, run⟩
            · exact remaining value member term accepted
        | false =>
            have parts := Result.done.inj returned
            cases parts.1; cases parts.2
            intro value member term accepted
            rcases List.mem_cons.mp member with rfl | member
            · exact ⟨_, Or.inl List.mem_cons_self, accepted⟩
            · obtain ⟨kept, present, run⟩ := remaining value member term accepted
              exact ⟨kept, present.imp (List.mem_cons_of_mem _) id, run⟩

/-- Any completed actual general selection retains semantic caches and exactly the independent union language. -/
theorem select_exact [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] (clear : Guard → Bool) (fuel : Nat)
    (holds : Guard → Term Symbol → Bool) (ambient : InternedGuardedLanguage.Env Symbol)
    (clearTrue : ∀ guard, clear guard = true → ∀ term, holds guard term = true)
    (inputs : List (Value Symbol Guard)) (before : State Symbol Guard) (semantic : SemanticReady before)
    (available : Values before inputs) (closed : ClosedValues inputs)
    (selected : List (Value Symbol Guard)) (after : State Symbol Guard)
    (done : select clear fuel inputs before = .done selected after) :
    Effect before after ∧ Values after selected ∧ ClosedValues selected ∧
      (∀ value ∈ selected, value ∈ inputs) ∧
      ∀ term, (∃ value ∈ selected, meaning holds ambient value term) ↔ ∃ value ∈ inputs, meaning holds ambient value term := by
  obtain ⟨retained, final, filtered, returned⟩ := (bind_done _ _ selected after).mp done
  have parts := Result.done.inj returned
  cases parts.1; cases parts.2
  have recInputs : Values before (inputs.filter closedMu) := fun value member => available value (List.mem_filter.mp member).1
  have recClosed : ClosedValues (inputs.filter closedMu) := fun value member => closed value (List.mem_filter.mp member).1
  have effects := retain_effect clear fuel (inputs.filter closedMu) inputs before semantic recInputs recClosed available closed retained after filtered
  have members := retain_members clear fuel (inputs.filter closedMu) inputs before retained after filtered
  have retainedInputs : Values after retained := fun value member => effects.1.available value (available value (members.1 value member))
  have subset : ∀ value ∈ distinctNodes retained, value ∈ inputs := fun value member => members.1 value (distinctNodes_member _ _ member)
  refine ⟨effects, (fun value member => effects.1.available value (available value (subset value member))),
    (fun value member => closed value (subset value member)), subset, ?_⟩
  intro term
  constructor
  · rintro ⟨value, member, accepted⟩
    exact ⟨value, subset value member, accepted⟩
  · rintro ⟨value, member, accepted⟩
    obtain ⟨kept, present, run⟩ := retain_coverage clear fuel holds ambient clearTrue (inputs.filter closedMu) inputs before semantic
      recInputs recClosed available closed retained after filtered value member term accepted
    have keptIn : kept ∈ retained := by
      rcases present with retained | recursive
      · exact retained
      · exact members.2 kept (List.mem_filter.mp recursive).1 (List.mem_filter.mp recursive).2
    exact ⟨kept, InternedUnionRetention.distinctNodes_retains after effects.2.ready.semantic.1.normal.facts.coherent retained
      (fun value member => (retainedInputs value member).resident) kept keptIn, run⟩

end MicroCFTA.SourceMergedSelectionLanguage
