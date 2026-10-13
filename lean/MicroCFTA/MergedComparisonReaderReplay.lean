import MicroCFTA.MergedComparisonWarmProgress

/-!
# Exact cold edge-reader replay after later physical effects

Every unfolding reuses its own earlier completed result. The ordered
visited traversal then returns the same exact edge list. Replay leaves
the later cache unchanged and compares no alternative allocation order.
-/
namespace MicroCFTA.MergedComparisonReaderReplay
open Cache InternedConstructorTemplates InternedProbeProvenance
open InternedNestedConstruction InternedNestedFacts InternedNestedProvenance
open MergedPhysicalWarmup MergedSourceExposure

/-- A completed ordered worklist replays with identical edges and no effects in any later cache. -/
theorem collect_replay [DecidableEq (EdgeKey Symbol Guard)] (fuel : Nat)
    (before : State Symbol Guard) (facts : Facts before) (prepared : Prepared before)
    (seen : List Nat) (pending : List (Value Symbol Guard)) (inputs : Values before pending)
    (edges : List (EdgeValue Symbol Guard)) (final later : State Symbol Guard)
    (done : collect fuel before seen pending = .done edges final) (growth : Grows final later) :
    collect fuel later seen pending = .done edges later := by
  induction fuel generalizing before seen pending edges final with
  | zero =>
      cases pending with
      | nil => cases done; rfl
      | cons => cases done
  | succ fuel ih =>
      cases pending with
      | nil => cases done; rfl
      | cons value rest =>
          have available := inputs value List.mem_cons_self
          have restInputs : Values before rest := fun child member => inputs child (List.mem_cons_of_mem _ member)
          cases value with
          | empty => exact ih before facts prepared seen rest restInputs edges final done growth
          | reference => cases done
          | node entry own depth free =>
              cases tail : collect fuel before seen rest with
              | unresolved | pending | exhausted => simp only [collect, tail, Result.prepend, reduceCtorEq] at done
              | done rows after =>
                  have equal : own ++ rows = edges ∧ after = final := by
                    simpa only [collect, tail, Result.prepend, Result.done.injEq] using done
                  rcases equal with ⟨rfl, rfl⟩
                  simp only [collect, ih before facts prepared seen rest restInputs rows after tail growth, Result.prepend]
          | union entry members depth free =>
              by_cases visited : entry.identity ∈ seen
              · simpa only [collect, ite_eq_left visited] using ih before facts prepared seen rest restInputs edges final
                  (by simpa only [collect, ite_eq_left visited] using done) growth
              · have nextInputs : Values before (members ++ rest) := by
                  intro child member
                  rcases List.mem_append.mp member with first | other
                  · exact available.children child first
                  · exact restInputs child other
                simpa only [collect, ite_eq_right visited] using ih before facts prepared (entry.identity :: seen) (members ++ rest)
                  nextInputs edges final (by simpa only [collect, ite_eq_right visited] using done) growth
          | mu entry body depth ordinary =>
              by_cases visited : entry.identity ∈ seen
              · simpa only [collect, ite_eq_left visited] using ih before facts prepared seen rest restInputs edges final
                  (by simpa only [collect, ite_eq_left visited] using done) growth
              · obtain ⟨result, middle, unfolded⟩ := unfold_complete (.mu entry body depth ordinary) before prepared available
                have verified := InternedStoredSubstitution.unfold_verified (.mu entry body depth ordinary) before facts available
                have middleFacts : Facts middle := by simpa only [unfolded, Outcome.state] using verified.facts
                have middlePrepared : Prepared middle := by
                  simpa only [unfolded, Outcome.state] using prepared.preserve (unfold_noNewMu (.mu entry body depth ordinary) before prepared available)
                have nextInputs : Values middle (result :: rest) := by
                  intro child member
                  rcases List.mem_cons.mp member with same | member
                  · rw [same]; exact verified.result result middle unfolded
                  · simpa only [unfolded, Outcome.state] using verified.available child (restInputs child member)
                have tail : collect fuel middle (entry.identity :: seen) (result :: rest) = .done edges final := by
                  simpa only [collect, ite_eq_right visited, unfolded] using done
                have middleGrowth : Grows middle final := by
                  simpa only [tail, Result.state] using (MergedColdReaderFacts.collect_verified fuel middle middleFacts middlePrepared
                    (entry.identity :: seen) (result :: rest) nextInputs).growth
                have replay := unfold_replay (.mu entry body depth ordinary) before later result middle facts.coherent.valid unfolded
                  (grows_trans middleGrowth growth)
                have tailReplay := ih middle middleFacts middlePrepared (entry.identity :: seen) (result :: rest) nextInputs edges final tail growth
                simp only [collect, ite_eq_right visited, replay, tailReplay]

/-- Canonicalized closure replays its exact edge list after later cache growth. -/
theorem canonical_replay [DecidableEq (EdgeKey Symbol Guard)] (fuel : Nat)
    (before : State Symbol Guard) (facts : Facts before) (prepared : Prepared before)
    (seen : List Nat) (pending : List (Value Symbol Guard)) (inputs : Values before pending)
    (edges : List (EdgeValue Symbol Guard)) (final later : State Symbol Guard)
    (done : (collect fuel before seen pending).canonical = .done edges final) (growth : Grows final later) :
    (collect fuel later seen pending).canonical = .done edges later := by
  cases original : collect fuel before seen pending with
  | unresolved | pending | exhausted => simp only [original, Result.canonical, reduceCtorEq] at done
  | done rows after =>
      have equal : canonicalEdges rows = edges ∧ after = final := by
        simpa only [original, Result.canonical, Result.done.injEq] using done
      rcases equal with ⟨rfl, rfl⟩
      simp only [collect_replay fuel before facts prepared seen pending inputs rows after later original growth, Result.canonical]

/-- Each completed physical source reader returns its exact original edges in a later cache without allocation. -/
theorem nodeEdges_replay [DecidableEq (EdgeKey Symbol Guard)] (fuel : Nat) (value : Value Symbol Guard)
    (before : State Symbol Guard) (facts : Facts before) (prepared : Prepared before) (available : Available before value)
    (edges : List (EdgeValue Symbol Guard)) (final later : State Symbol Guard)
    (done : MergedSourceExposure.nodeEdges fuel value before = .done edges final) (growth : Grows final later) :
    MergedSourceExposure.nodeEdges fuel value later = .done edges later := by
  have singleton (root : Value Symbol Guard) (state : State Symbol Guard) (available : Available state root) : Values state [root] := by
    intro value member
    simpa only [List.mem_singleton.mp member] using available
  cases value with
  | empty | reference | node => cases done; rfl
  | union entry members depth free => exact canonical_replay fuel before facts prepared [] _ (singleton _ before available) edges final later done growth
  | mu entry body depth ordinary =>
      obtain ⟨result, middle, unfolded⟩ := unfold_complete (.mu entry body depth ordinary) before prepared available
      have verified := InternedStoredSubstitution.unfold_verified (.mu entry body depth ordinary) before facts available
      have middleFacts : Facts middle := by simpa only [unfolded, Outcome.state] using verified.facts
      have middlePrepared : Prepared middle := by
        simpa only [unfolded, Outcome.state] using prepared.preserve (unfold_noNewMu (.mu entry body depth ordinary) before prepared available)
      have middleAvailable : Available middle (.mu entry body depth ordinary) := by
        simpa only [unfolded, Outcome.state] using verified.available _ available
      have fallback {result : Value Symbol Guard}
          (source : InternedStoredSubstitution.unfold (.mu entry body depth ordinary) before = .done result middle)
          (finished : (collect fuel middle [] [.mu entry body depth ordinary]).canonical = .done edges final) :
          InternedStoredSubstitution.unfold (.mu entry body depth ordinary) later = .done result later ∧
          (collect fuel later [] [.mu entry body depth ordinary]).canonical = .done edges later := by
        have middleGrowth : Grows middle final := by
          simpa only [finished, Result.state] using (MergedColdReaderFacts.collect_verified fuel middle middleFacts middlePrepared []
            [.mu entry body depth ordinary] (singleton _ middle middleAvailable)).canonical _ |>.growth
        exact ⟨unfold_replay (.mu entry body depth ordinary) before later result middle facts.coherent.valid source
            (grows_trans middleGrowth growth),
          canonical_replay fuel middle middleFacts middlePrepared [] _ (singleton _ middle middleAvailable) edges final later finished growth⟩
      cases result with
      | node actual own level free =>
          have equal : own = edges ∧ middle = final := by simpa only [MergedSourceExposure.nodeEdges, unfolded, Result.done.injEq] using done
          rcases equal with ⟨rfl, rfl⟩
          have replay := unfold_replay (.mu entry body depth ordinary) before later (.node actual own level free) middle facts.coherent.valid unfolded growth
          simp only [MergedSourceExposure.nodeEdges, replay]
      | empty | reference | union | mu =>
          obtain ⟨replay, resultDone⟩ := fallback unfolded (by simpa only [MergedSourceExposure.nodeEdges, unfolded] using done)
          simpa only [MergedSourceExposure.nodeEdges, replay] using resultDone

end MicroCFTA.MergedComparisonReaderReplay
