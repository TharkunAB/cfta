import MicroCFTA.MergedFreshOrdinaryColdEffects
import MicroCFTA.InternedFreshOrdinaryReplay
import MicroCFTA.MergedPreparedReaderEffects

/-!
# Exact replay of general repaired cold reads

Every bounded repaired read preserves valid caches and completed records.
A successful read replays the same ordered edges after its final cache has
grown. Replay adds no record. These laws do not require preparation or closed
inputs. They do not supply a finite successful bound for an unfinished read.
-/
namespace MicroCFTA.InternedFreshOrdinaryStoredSubstitution
open InternedConstructorTemplates
open InternedNestedConstruction (Outcome)
open InternedStoredSubstitution (Environment)

/-- Arbitrary repaired stored execution preserves valid caches and completed records at every outcome. -/
theorem execute_correct [DecidableEq (EdgeKey Symbol Guard)] (value : Value Symbol Guard)
    (environment : Environment Symbol Guard) (state : State Symbol Guard) (valid : Valid state) :
    Valid (execute value environment state).state ∧ Grows state (execute value environment state).state :=
  InternedFreshOrdinaryGrowth.build_correct _ _ state valid

/-- A completed repaired stored plan replays its exact value without further allocation after growth. -/
theorem execute_replay [DecidableEq (EdgeKey Symbol Guard)] (value : Value Symbol Guard)
    (environment : Environment Symbol Guard) (before after : State Symbol Guard) (result : Value Symbol Guard)
    (final : State Symbol Guard) (valid : Valid before)
    (done : execute value environment before = .done result final) (growth : Grows final after) :
    execute value environment after = .done result after :=
  InternedFreshOrdinaryReplay.build_replay _ _ before after result final valid done growth

/-- Single repaired unfolding preserves valid caches and completed records at every outcome. -/
theorem unfold_correct [DecidableEq (EdgeKey Symbol Guard)] (value : Value Symbol Guard)
    (state : State Symbol Guard) (valid : Valid state) :
    Valid (unfold value state).state ∧ Grows state (unfold value state).state := by
  cases value with
  | empty | reference | node | union => exact ⟨valid, grows_refl _⟩
  | mu => exact execute_correct _ _ state valid

/-- A completed repaired unfolding replays the identical record in every later cache. -/
theorem unfold_replay [DecidableEq (EdgeKey Symbol Guard)] (value : Value Symbol Guard)
    (before after : State Symbol Guard) (result : Value Symbol Guard) (final : State Symbol Guard)
    (valid : Valid before) (done : unfold value before = .done result final) (growth : Grows final after) :
    unfold value after = .done result after := by
  cases value with
  | empty | reference | node | union => cases done; rfl
  | mu => exact execute_replay _ _ before after result final valid done growth

end MicroCFTA.InternedFreshOrdinaryStoredSubstitution

namespace MicroCFTA.MergedFreshOrdinaryColdReplay
open Cache InternedConstructorTemplates
open MergedSourceExposure (Result)
open MergedFreshOrdinaryExposure
open MergedPreparedReaderEffects (prepend_state canonical_state)

/-- Every bounded repaired worklist preserves valid caches and all completed records, including on failure. -/
theorem collect_correct [DecidableEq (EdgeKey Symbol Guard)] (fuel : Nat) (state : State Symbol Guard)
    (valid : Valid state) (seen : List Nat) (pending : List (Value Symbol Guard)) :
    Valid (collect fuel state seen pending).state ∧ Grows state (collect fuel state seen pending).state := by
  induction fuel generalizing state seen pending with
  | zero => cases pending <;> exact ⟨valid, grows_refl _⟩
  | succ fuel ih =>
      cases pending with
      | nil => exact ⟨valid, grows_refl _⟩
      | cons value rest =>
          cases value with
          | empty => exact ih state valid seen rest
          | reference => exact ⟨valid, grows_refl _⟩
          | node entry edges depth free => simpa only [collect, prepend_state] using ih state valid seen rest
          | union entry members depth free =>
              by_cases visited : entry.identity ∈ seen
              · simpa only [collect, ite_eq_left visited] using ih state valid seen rest
              · simpa only [collect, ite_eq_right visited] using ih state valid (entry.identity :: seen) (members ++ rest)
          | mu entry body depth ordinary =>
              by_cases visited : entry.identity ∈ seen
              · simpa only [collect, ite_eq_left visited] using ih state valid seen rest
              · have checked := InternedFreshOrdinaryStoredSubstitution.unfold_correct (.mu entry body depth ordinary) state valid
                cases done : InternedFreshOrdinaryStoredSubstitution.unfold (.mu entry body depth ordinary) state with
                | pending key after => simpa only [collect, ite_eq_right visited, done, InternedNestedConstruction.Outcome.state, Result.state] using checked
                | done result after =>
                    have middle : Valid after ∧ Grows state after := by
                      simpa only [done, InternedNestedConstruction.Outcome.state] using checked
                    have next := ih after middle.1 (entry.identity :: seen) (result :: rest)
                    simpa only [collect, ite_eq_right visited, done] using
                      (show Valid (collect fuel after (entry.identity :: seen) (result :: rest)).state ∧
                        Grows state (collect fuel after (entry.identity :: seen) (result :: rest)).state from
                        ⟨next.1, grows_trans middle.2 next.2⟩)

/-- Completed ordered worklists replay their exact edge list after all original effects have grown. -/
theorem collect_replay [DecidableEq (EdgeKey Symbol Guard)] (fuel : Nat) (before after : State Symbol Guard)
    (valid : Valid before) (seen : List Nat) (pending : List (Value Symbol Guard))
    (edges : List (EdgeValue Symbol Guard)) (final : State Symbol Guard)
    (done : collect fuel before seen pending = .done edges final) (growth : Grows final after) :
    collect fuel after seen pending = .done edges after := by
  induction fuel generalizing before after seen pending edges final with
  | zero =>
      cases pending with
      | nil => cases done; rfl
      | cons => cases done
  | succ fuel ih =>
      cases pending with
      | nil => cases done; rfl
      | cons value rest =>
          cases value with
          | empty => exact ih before after valid seen rest edges final done growth
          | reference => cases done
          | node entry ordinaryEdges depth free =>
              cases tail : collect fuel before seen rest with
              | unresolved | pending | exhausted => simp only [collect, tail, Result.prepend] at done; cases done
              | done values middle =>
                  have equal : ordinaryEdges ++ values = edges ∧ middle = final := by
                    simpa only [collect, tail, Result.prepend, Result.done.injEq] using done
                  have again := ih before after valid seen rest values middle tail (by simpa only [equal.2] using growth)
                  simp only [collect, again, Result.prepend, equal.1]
          | union entry members depth free =>
              by_cases visited : entry.identity ∈ seen
              · simpa only [collect, ite_eq_left visited] using ih before after valid seen rest edges final
                  (by simpa only [collect, ite_eq_left visited] using done) growth
              · simpa only [collect, ite_eq_right visited] using ih before after valid (entry.identity :: seen) (members ++ rest) edges final
                  (by simpa only [collect, ite_eq_right visited] using done) growth
          | mu entry body depth ordinary =>
              by_cases visited : entry.identity ∈ seen
              · simpa only [collect, ite_eq_left visited] using ih before after valid seen rest edges final
                  (by simpa only [collect, ite_eq_left visited] using done) growth
              · cases unfolded : InternedFreshOrdinaryStoredSubstitution.unfold (.mu entry body depth ordinary) before with
                | pending => simp only [collect, ite_eq_right visited, unfolded] at done; cases done
                | done result middle =>
                    have tail : collect fuel middle (entry.identity :: seen) (result :: rest) = .done edges final := by
                      simpa only [collect, ite_eq_right visited, unfolded] using done
                    have middleValid : Valid middle := by
                      simpa only [unfolded, InternedNestedConstruction.Outcome.state] using
                        (InternedFreshOrdinaryStoredSubstitution.unfold_correct (.mu entry body depth ordinary) before valid).1
                    have finalGrowth : Grows middle final := by
                      simpa only [tail, Result.state] using (collect_correct fuel middle middleValid (entry.identity :: seen) (result :: rest)).2
                    have repeated := InternedFreshOrdinaryStoredSubstitution.unfold_replay (.mu entry body depth ordinary)
                      before after result middle valid unfolded (grows_trans finalGrowth growth)
                    simpa only [collect, ite_eq_right visited, repeated] using
                      ih middle after middleValid (entry.identity :: seen) (result :: rest) edges final tail growth

/-- Completed repaired edge reads replay their exact ordered rows with no cache effect after growth. -/
theorem nodeEdges_replay [DecidableEq (EdgeKey Symbol Guard)] (fuel : Nat) (value : Value Symbol Guard)
    (before after : State Symbol Guard) (valid : Valid before) (edges : List (EdgeValue Symbol Guard))
    (final : State Symbol Guard) (done : nodeEdges fuel value before = .done edges final) (growth : Grows final after) :
    nodeEdges fuel value after = .done edges after := by
  have fallback (current : State Symbol Guard) (currentValid : Valid current) (root : Value Symbol Guard)
      (complete : (collect fuel current [] [root]).canonical = .done edges final) :
      (collect fuel after [] [root]).canonical = .done edges after := by
    cases actual : collect fuel current [] [root] with
    | unresolved | pending | exhausted => simp only [actual, Result.canonical] at complete; cases complete
    | done values middle =>
        have equal : canonicalEdges values = edges ∧ middle = final := by
          simpa only [actual, Result.canonical, Result.done.injEq] using complete
        have again := collect_replay fuel current after currentValid [] [root] values middle actual
          (by simpa only [equal.2] using growth)
        simp only [again, Result.canonical, equal.1]
  cases value with
  | empty | reference | node => cases done; rfl
  | union => exact fallback before valid _ done
  | mu entry body depth ordinary =>
      cases unfolded : InternedFreshOrdinaryStoredSubstitution.unfold (.mu entry body depth ordinary) before with
      | pending => simp only [nodeEdges, unfolded] at done; cases done
      | done result middle =>
          have middleValid : Valid middle := by
            simpa only [unfolded, InternedNestedConstruction.Outcome.state] using
              (InternedFreshOrdinaryStoredSubstitution.unfold_correct (.mu entry body depth ordinary) before valid).1
          have middleGrowth : Grows middle final := by
            cases result with
            | node =>
                have equal := Result.done.inj (by simpa only [nodeEdges, unfolded] using done)
                rw [← equal.2]
                exact grows_refl middle
            | empty | reference | union | mu =>
                have complete : (collect fuel middle [] [.mu entry body depth ordinary]).canonical = .done edges final := by
                  simpa only [nodeEdges, unfolded] using done
                have same : (collect fuel middle [] [.mu entry body depth ordinary]).state = final := by
                  have states := congrArg Result.state complete
                  rw [canonical_state] at states
                  exact states
                simpa only [same] using
                  (collect_correct fuel middle middleValid [] [.mu entry body depth ordinary]).2
          have repeated := InternedFreshOrdinaryStoredSubstitution.unfold_replay (.mu entry body depth ordinary)
            before after result middle valid unfolded (grows_trans middleGrowth growth)
          cases result with
          | node =>
              have equal := Result.done.inj (by simpa only [nodeEdges, unfolded] using done)
              simp only [nodeEdges, repeated, equal.1]
          | empty | reference | union | mu =>
              simpa only [nodeEdges, repeated] using fallback middle middleValid (.mu entry body depth ordinary)
                (by simpa only [nodeEdges, unfolded] using done)

/-- Increasing the proof bound retains every completed ordered read and its exact cache. -/
theorem collect_stable [DecidableEq (EdgeKey Symbol Guard)] (fuel extra : Nat)
    (state : State Symbol Guard) (seen : List Nat) (pending : List (Value Symbol Guard))
    (finished : MergedSourceExposure.Finished (collect fuel state seen pending)) :
    collect (fuel + extra) state seen pending = collect fuel state seen pending := by
  induction fuel generalizing state seen pending with
  | zero =>
      cases pending with
      | nil => simp [collect]
      | cons value rest => simp [collect, MergedSourceExposure.Finished] at finished
  | succ fuel ih =>
      cases pending with
      | nil => simp [collect]
      | cons value rest =>
          cases value with
          | empty => simpa only [Nat.succ_add, collect] using ih state seen rest finished
          | reference => simp only [Nat.succ_add, collect]
          | node entry edges depth free =>
              simp only [collect, MergedSourceExposure.finished_prepend] at finished
              simp only [Nat.succ_add, collect, ih state seen rest finished]
          | union entry members depth free =>
              by_cases visited : entry.identity ∈ seen
              · simpa only [Nat.succ_add, collect, ite_eq_left visited] using ih state seen rest
                  (by simpa only [collect, ite_eq_left visited] using finished)
              · simpa only [Nat.succ_add, collect, ite_eq_right visited] using ih state (entry.identity :: seen) (members ++ rest)
                  (by simpa only [collect, ite_eq_right visited] using finished)
          | mu entry body depth ordinary =>
              by_cases visited : entry.identity ∈ seen
              · simpa only [Nat.succ_add, collect, ite_eq_left visited] using ih state seen rest
                  (by simpa only [collect, ite_eq_left visited] using finished)
              · cases done : InternedFreshOrdinaryStoredSubstitution.unfold (.mu entry body depth ordinary) state with
                | pending => simp only [collect, ite_eq_right visited, done, MergedSourceExposure.Finished] at finished
                | done result after =>
                    simpa only [Nat.succ_add, collect, ite_eq_right visited, done] using ih after (entry.identity :: seen) (result :: rest)
                      (by simpa only [collect, ite_eq_right visited, done] using finished)

/-- Every finished repaired edge read retains its exact result and effects at all larger bounds. -/
theorem nodeEdges_stable [DecidableEq (EdgeKey Symbol Guard)] (fuel extra : Nat)
    (value : Value Symbol Guard) (state : State Symbol Guard)
    (finished : MergedSourceExposure.Finished (nodeEdges fuel value state)) :
    nodeEdges (fuel + extra) value state = nodeEdges fuel value state := by
  have fallback (current : State Symbol Guard) (root : Value Symbol Guard)
      (complete : MergedSourceExposure.Finished (collect fuel current [] [root]).canonical) :
      (collect (fuel + extra) current [] [root]).canonical = (collect fuel current [] [root]).canonical :=
    congrArg Result.canonical (collect_stable fuel extra current [] [root]
      ((MergedSourceExposure.finished_canonical _).mp complete))
  cases value with
  | empty | reference | node => rfl
  | union => exact fallback state _ finished
  | mu entry body depth ordinary =>
      cases done : InternedFreshOrdinaryStoredSubstitution.unfold (.mu entry body depth ordinary) state with
      | pending => simp only [nodeEdges, done]
      | done result after =>
          cases result <;> simp only [nodeEdges, done] at finished ⊢ <;>
            first | rfl | exact fallback after _ finished

/-- Successful cold reads replay the same rows without allocation at every larger bound and later cache. -/
theorem nodeEdges_replay_stable [DecidableEq (EdgeKey Symbol Guard)] (fuel extra : Nat) (value : Value Symbol Guard)
    (before after : State Symbol Guard) (valid : Valid before) (edges : List (EdgeValue Symbol Guard))
    (final : State Symbol Guard) (done : nodeEdges fuel value before = .done edges final) (growth : Grows final after) :
    nodeEdges (fuel + extra) value after = .done edges after := by
  have repeated := nodeEdges_replay fuel value before after valid edges final done growth
  rw [nodeEdges_stable fuel extra value after (by rw [repeated]; trivial)]
  exact repeated

end MicroCFTA.MergedFreshOrdinaryColdReplay
