import MicroCFTA.SourceColdUnfoldBudget

/-!
# Cache progress of actual cold row reads

The finite unfolding budget cannot increase through any reader effect.
If a completed read retains that budget, it retains the identical cache.
This includes repeated Mu requests inside ordered union closures.
-/
namespace MicroCFTA.SourceColdReaderBudget
open Cache InternedConstructorTemplates InternedProbeProvenance InternedNestedFacts
open InternedNestedProvenance InternedShallowHeap MergedPhysicalWarmup MergedSourceExposure
open InternedNestedConstruction (Outcome)
open SourceColdUnfoldBudget

/-- An ordered cold closure with unchanged unfolding budget has no cache effect. -/
theorem collect_unchanged [DecidableEq (EdgeKey Symbol Guard)] (fuel : Nat) (before : State Symbol Guard)
    (facts : Facts before) (prepared : Prepared before) (inventory : List (Value Symbol Guard))
    (covered : Covers before inventory) (seen : List Nat) (pending : List (Value Symbol Guard))
    (inputs : Values before pending) (edges : List (EdgeValue Symbol Guard)) (after : State Symbol Guard)
    (done : collect fuel before seen pending = .done edges after)
    (sameBudget : remaining after inventory = remaining before inventory) : after = before := by
  induction fuel generalizing before seen pending edges after with
  | zero =>
      cases pending with
      | nil => exact (Result.done.inj done).2.symm
      | cons => cases done
  | succ fuel ih =>
      cases pending with
      | nil => exact (Result.done.inj done).2.symm
      | cons value rest =>
          have available := inputs value List.mem_cons_self
          have tailInputs : Values before rest := fun child member => inputs child (List.mem_cons_of_mem _ member)
          cases value with
          | empty => exact ih before facts prepared covered seen rest tailInputs edges after done sameBudget
          | reference => cases done
          | node entry own depth free =>
              cases tail : collect fuel before seen rest with
              | unresolved | pending | exhausted =>
                  simp only [collect, tail, Result.prepend] at done
                  cases done
              | done rows final =>
                  have equal : own ++ rows = edges ∧ final = after := by
                    simpa only [collect, tail, Result.prepend, Result.done.injEq] using done
                  obtain ⟨_, rfl⟩ := equal
                  exact ih before facts prepared covered seen rest tailInputs rows final tail sameBudget
          | union entry members depth free =>
              by_cases visited : entry.identity ∈ seen
              · exact ih before facts prepared covered seen rest tailInputs edges after
                  (by simpa only [collect, ite_eq_left visited] using done) sameBudget
              · have nextInputs : Values before (members ++ rest) := by
                  intro child member
                  rcases List.mem_append.mp member with first | later
                  · exact available.children child first
                  · exact tailInputs child later
                exact ih before facts prepared covered (entry.identity :: seen) (members ++ rest) nextInputs edges after
                  (by simpa only [collect, ite_eq_right visited] using done) sameBudget
          | mu entry body depth ordinary =>
              by_cases visited : entry.identity ∈ seen
              · exact ih before facts prepared covered seen rest tailInputs edges after
                  (by simpa only [collect, ite_eq_left visited] using done) sameBudget
              · obtain ⟨result, middle, unfolded⟩ := unfold_complete (.mu entry body depth ordinary) before prepared available
                have checked := InternedStoredSubstitution.unfold_verified (.mu entry body depth ordinary) before facts available
                have middleFacts : Facts middle := by simpa only [unfolded, Outcome.state] using checked.facts
                have growth : Grows before middle := by simpa only [unfolded, Outcome.state] using checked.growth
                have unchanged : NoNewMu before middle := by
                  simpa only [unfolded, Outcome.state] using unfold_noNewMu (.mu entry body depth ordinary) before prepared available
                have middlePrepared := prepared.preserve unchanged
                have middleCovered := covered.preserve before middle facts inventory unchanged
                have nextInputs : Values middle (result :: rest) := by
                  intro child member
                  rcases List.mem_cons.mp member with same | later
                  · rw [same]; exact checked.result result middle unfolded
                  · simpa only [unfolded, Outcome.state] using checked.available child (tailInputs child later)
                have tail : collect fuel middle (entry.identity :: seen) (result :: rest) = .done edges after := by
                  simpa only [collect, ite_eq_right visited, unfolded] using done
                have tailGrowth : Grows middle after := by
                  simpa only [tail, Result.state] using
                    (MergedColdReaderFacts.collect_verified fuel middle middleFacts middlePrepared (entry.identity :: seen)
                      (result :: rest) nextInputs).growth
                have firstBudget := remaining_mono before middle facts.coherent.valid growth inventory
                have tailBudget := remaining_mono middle after middleFacts.coherent.valid tailGrowth inventory
                have middleSame : remaining middle inventory = remaining before inventory := by omega
                have afterSame : remaining after inventory = remaining middle inventory := by omega
                exact (ih middle middleFacts middlePrepared middleCovered (entry.identity :: seen) (result :: rest)
                  nextInputs edges after tail afterSame).trans
                  (unfold_unchanged before middle facts inventory covered _ available result unfolded middleSame)

/-- Canonical edge ordering does not hide a cache effect from the unfolding budget. -/
theorem canonical_unchanged [DecidableEq (EdgeKey Symbol Guard)] (fuel : Nat) (before : State Symbol Guard)
    (facts : Facts before) (prepared : Prepared before) (inventory : List (Value Symbol Guard))
    (covered : Covers before inventory) (value : Value Symbol Guard) (available : Available before value)
    (edges : List (EdgeValue Symbol Guard)) (after : State Symbol Guard)
    (done : (collect fuel before [] [value]).canonical = .done edges after)
    (sameBudget : remaining after inventory = remaining before inventory) : after = before := by
  cases read : collect fuel before [] [value] with
  | unresolved | pending | exhausted => simp only [read, Result.canonical] at done; cases done
  | done rows final =>
      have equal : canonicalEdges rows = edges ∧ final = after := by
        simpa only [read, Result.canonical, Result.done.injEq] using done
      obtain ⟨_, rfl⟩ := equal
      exact collect_unchanged fuel before facts prepared inventory covered [] [value]
        (by simpa [Values] using available) rows final read sameBudget

/-- A completed cold row read with unchanged finite Mu budget retains the exact cache. -/
theorem nodeEdges_unchanged [DecidableEq (EdgeKey Symbol Guard)] (fuel : Nat) (before : State Symbol Guard)
    (facts : Facts before) (prepared : Prepared before) (inventory : List (Value Symbol Guard))
    (covered : Covers before inventory) (value : Value Symbol Guard) (available : Available before value)
    (edges : List (EdgeValue Symbol Guard)) (after : State Symbol Guard)
    (done : MergedSourceExposure.nodeEdges fuel value before = .done edges after)
    (sameBudget : remaining after inventory = remaining before inventory) : after = before := by
  cases value with
  | empty | reference | node => exact (Result.done.inj done).2.symm
  | union entry members depth free => exact canonical_unchanged fuel before facts prepared inventory covered _ available edges after done sameBudget
  | mu entry body depth ordinary =>
      obtain ⟨result, middle, unfolded⟩ := unfold_complete (.mu entry body depth ordinary) before prepared available
      have checked := InternedStoredSubstitution.unfold_verified (.mu entry body depth ordinary) before facts available
      have middleFacts : Facts middle := by simpa only [unfolded, Outcome.state] using checked.facts
      have growth : Grows before middle := by simpa only [unfolded, Outcome.state] using checked.growth
      have unchanged : NoNewMu before middle := by
        simpa only [unfolded, Outcome.state] using unfold_noNewMu (.mu entry body depth ordinary) before prepared available
      have middlePrepared := prepared.preserve unchanged
      have middleCovered := covered.preserve before middle facts inventory unchanged
      have middleAvailable : Available middle (.mu entry body depth ordinary) := by
        simpa only [unfolded, Outcome.state] using checked.available _ available
      have finish (current : State Symbol Guard) (tailGrowth : Grows middle current)
          (tail : remaining current inventory = remaining middle inventory → current = middle)
          (same : remaining current inventory = remaining before inventory) : current = before := by
        have firstBudget := remaining_mono before middle facts.coherent.valid growth inventory
        have tailBudget := remaining_mono middle current middleFacts.coherent.valid tailGrowth inventory
        exact (tail (by omega)).trans
          (unfold_unchanged before middle facts inventory covered _ available result unfolded (by omega))
      cases result with
      | node actual own depth free =>
          have equal : own = edges ∧ middle = after := by
            simpa only [MergedSourceExposure.nodeEdges, unfolded, Result.done.injEq] using done
          obtain ⟨_, rfl⟩ := equal
          exact unfold_unchanged before middle facts inventory covered _ available _ unfolded sameBudget
      | empty | reference | union | mu =>
          have fallback : (collect fuel middle [] [.mu entry body depth ordinary]).canonical = .done edges after := by
            simpa only [MergedSourceExposure.nodeEdges, unfolded] using done
          have tailGrowth : Grows middle after := by
            have verified := (MergedColdReaderFacts.collect_verified fuel middle middleFacts middlePrepared []
              [.mu entry body depth ordinary] (by simpa [Values] using middleAvailable)).canonical _
            simpa only [fallback, Result.state] using verified.growth
          exact finish after tailGrowth
            (canonical_unchanged fuel middle middleFacts middlePrepared inventory middleCovered _ middleAvailable edges after fallback) sameBudget

end MicroCFTA.SourceColdReaderBudget
