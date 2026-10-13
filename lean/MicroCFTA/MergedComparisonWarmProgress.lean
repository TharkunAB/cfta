import MicroCFTA.MergedSourceComparison

/-!
# Cold-record progress of actual physical edge reads

A warm value unfolds without changing its current cache. Warmth persists
under actual cache growth. Each reader either leaves its cache unchanged
or warms a previously cold Mu already available before that read.
-/
namespace MicroCFTA.MergedComparisonWarmProgress
open Cache InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedNestedConstruction InternedNestedFacts InternedNestedProvenance
open MergedPhysicalWarmup MergedSourceExposure
open InternedBinderProtocol (NodeKey)

/-- An actual stored unfolding returns a result without any cache effect. -/
def Warm [DecidableEq (EdgeKey Symbol Guard)] (state : State Symbol Guard) (value : Value Symbol Guard) : Prop :=
  ∃ result, InternedStoredSubstitution.unfold value state = .done result state

/-- A completed allocation-free unfolding remains allocation-free after cache growth. -/
theorem Warm.grows [DecidableEq (EdgeKey Symbol Guard)] (before after : State Symbol Guard)
    (valid : Valid before) (growth : Grows before after) (value : Value Symbol Guard) (warm : Warm before value) : Warm after value := by
  obtain ⟨result, done⟩ := warm
  exact ⟨result, unfold_replay value before after result before valid done growth⟩

/-- The actual returned cache can replay its own completed unfolding without allocation. -/
theorem unfolded_warm [DecidableEq (EdgeKey Symbol Guard)] (before after : State Symbol Guard)
    (valid : Valid before) (value result : Value Symbol Guard)
    (done : InternedStoredSubstitution.unfold value before = .done result after) : Warm after value :=
  ⟨result, unfold_replay value before after result after valid done (grows_refl after)⟩

/-- A changed reader cache has completed one previously cold, already available Mu. -/
def Gain [DecidableEq (EdgeKey Symbol Guard)] (before after : State Symbol Guard) : Prop :=
  ∃ entry body depth ordinary, Available before (.mu entry body depth ordinary) ∧
    ¬ Warm before (.mu entry body depth ordinary) ∧ Warm after (.mu entry body depth ordinary)

/-- Each exact effect is unchanged or makes one original recursive value warm. -/
def Progress [DecidableEq (EdgeKey Symbol Guard)] (before after : State Symbol Guard) : Prop :=
  after = before ∨ Gain before after

/-- Progress from an earlier source stage persists through every later verified effect. -/
theorem Progress.trans [DecidableEq (EdgeKey Symbol Guard)]
    {before middle after : State Symbol Guard} (first : Progress before middle) (second : Progress middle after)
    (valid : Valid middle) (growth : Grows middle after) : Progress before after := by
  rcases first with same | ⟨entry, body, depth, ordinary, available, cold, warm⟩
  · subst middle; exact second
  · exact Or.inr ⟨entry, body, depth, ordinary, available, cold, warm.grows middle after valid growth _⟩

/-- Every actual completed Mu call is unchanged or warms that same previously cold value. -/
theorem unfold_progress [DecidableEq (EdgeKey Symbol Guard)] (before after : State Symbol Guard)
    (valid : Valid before) (entry : Interned NodeKey) (body depth ordinary result : Value Symbol Guard)
    (available : Available before (.mu entry body depth ordinary))
    (done : InternedStoredSubstitution.unfold (.mu entry body depth ordinary) before = .done result after) :
    Progress before after := by
  by_cases same : after = before
  · exact Or.inl same
  refine Or.inr ⟨entry, body, depth, ordinary, available, ?_, unfolded_warm before after valid _ result done⟩
  rintro ⟨old, warm⟩
  exact same (Outcome.done.inj (done.symm.trans warm)).2

/-- Prepending stored ordinary edges does not alter the reader's returned cache. -/
theorem prepend_state (result : Result Symbol Guard) (edges : List (EdgeValue Symbol Guard)) :
    (result.prepend edges).state = result.state := by cases result <;> rfl

/-- Canonical edge ordering does not alter the reader's returned cache. -/
theorem canonical_state (result : Result Symbol Guard) : result.canonical.state = result.state := by cases result <;> rfl

/-- Every actual ordered worklist run is unchanged or warms one earlier available Mu. -/
theorem collect_progress [DecidableEq (EdgeKey Symbol Guard)] (fuel : Nat) (state : State Symbol Guard)
    (facts : Facts state) (prepared : Prepared state) (seen : List Nat) (pending : List (Value Symbol Guard))
    (inputs : Values state pending) : Progress state (collect fuel state seen pending).state := by
  induction fuel generalizing state seen pending with
  | zero => cases pending <;> exact Or.inl rfl
  | succ fuel ih =>
      cases pending with
      | nil => exact Or.inl rfl
      | cons value rest =>
          have available := inputs value List.mem_cons_self
          have restInputs : Values state rest := fun child member => inputs child (List.mem_cons_of_mem _ member)
          cases value with
          | empty => exact ih state facts prepared seen rest restInputs
          | reference => exact Or.inl rfl
          | node => simpa only [collect, prepend_state] using ih state facts prepared seen rest restInputs
          | union entry members depth free =>
              by_cases visited : entry.identity ∈ seen
              · simpa only [collect, ite_eq_left visited] using ih state facts prepared seen rest restInputs
              · have nextInputs : Values state (members ++ rest) := by
                  intro child member
                  rcases List.mem_append.mp member with first | later
                  · exact available.children child first
                  · exact restInputs child later
                simpa only [collect, ite_eq_right visited] using ih state facts prepared (entry.identity :: seen) (members ++ rest) nextInputs
          | mu entry body depth ordinary =>
              by_cases visited : entry.identity ∈ seen
              · simpa only [collect, ite_eq_left visited] using ih state facts prepared seen rest restInputs
              · obtain ⟨result, after, done⟩ := unfold_complete (.mu entry body depth ordinary) state prepared available
                have verified := InternedStoredSubstitution.unfold_verified (.mu entry body depth ordinary) state facts available
                have afterFacts : Facts after := by simpa only [done, Outcome.state] using verified.facts
                have afterPrepared : Prepared after := by
                  simpa only [done, Outcome.state] using prepared.preserve (unfold_noNewMu (.mu entry body depth ordinary) state prepared available)
                have nextInputs : Values after (result :: rest) := by
                  intro child member
                  rcases List.mem_cons.mp member with same | member
                  · rw [same]; exact verified.result result after done
                  · simpa only [done, Outcome.state] using verified.available child (restInputs child member)
                have next := ih after afterFacts afterPrepared (entry.identity :: seen) (result :: rest) nextInputs
                have nextVerified := MergedColdReaderFacts.collect_verified fuel after afterFacts afterPrepared (entry.identity :: seen) (result :: rest) nextInputs
                simpa only [collect, ite_eq_right visited, done] using
                  (unfold_progress state after facts.coherent.valid entry body depth ordinary result available done).trans
                    next afterFacts.coherent.valid nextVerified.growth

/-- Every actual top-level read is unchanged or warms one earlier available Mu. -/
theorem nodeEdges_progress [DecidableEq (EdgeKey Symbol Guard)] (fuel : Nat) (value : Value Symbol Guard)
    (state : State Symbol Guard) (facts : Facts state) (prepared : Prepared state)
    (available : Available state value) : Progress state (MergedSourceExposure.nodeEdges fuel value state).state := by
  have fallback (root : Value Symbol Guard) (current : State Symbol Guard) (currentFacts : Facts current)
      (currentPrepared : Prepared current) (rootAvailable : Available current root) :
      Progress current (collect fuel current [] [root]).canonical.state := by
    rw [canonical_state]
    exact collect_progress fuel current currentFacts currentPrepared [] [root]
      (by intro value member; simpa only [List.mem_singleton.mp member] using rootAvailable)
  cases value with
  | empty | reference | node => exact Or.inl rfl
  | union entry members depth free => exact fallback _ state facts prepared available
  | mu entry body depth ordinary =>
      obtain ⟨result, after, done⟩ := unfold_complete (.mu entry body depth ordinary) state prepared available
      have verified := InternedStoredSubstitution.unfold_verified (.mu entry body depth ordinary) state facts available
      have afterFacts : Facts after := by simpa only [done, Outcome.state] using verified.facts
      have afterPrepared : Prepared after := by
        simpa only [done, Outcome.state] using prepared.preserve (unfold_noNewMu (.mu entry body depth ordinary) state prepared available)
      have rootAvailable : Available after (.mu entry body depth ordinary) := by
        simpa only [done, Outcome.state] using verified.available _ available
      have first := unfold_progress state after facts.coherent.valid entry body depth ordinary result available done
      have next := fallback _ after afterFacts afterPrepared rootAvailable
      have nextVerified := (MergedColdReaderFacts.collect_verified fuel after afterFacts afterPrepared [] [.mu entry body depth ordinary]
        (by intro value member; simpa only [List.mem_singleton.mp member] using rootAvailable)).canonical _
      cases result with
      | node => simpa only [MergedSourceExposure.nodeEdges, done, Result.state] using first
      | empty | reference | union | mu =>
          simpa only [MergedSourceExposure.nodeEdges, done] using first.trans next afterFacts.coherent.valid nextVerified.growth

end MicroCFTA.MergedComparisonWarmProgress
