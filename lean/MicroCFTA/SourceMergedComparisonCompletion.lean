import MicroCFTA.SourceMergedComparisonStages

/-!
# Finite general repaired comparison with exact stable caches

An allocating prefix reduces unfinished Mu degrees. An unchanged prefix
lets the new ancestor pair reduce the finite issued-pair allowance. This
order derives actual recursive completion without prepared Mu bodies.
-/
namespace MicroCFTA.SourceMergedComparisonCompletion
open InternedConstructorTemplates InternedProbeProvenance
open SourceEqualityRequiredCache SourceEqualityRequiredSemanticCache
open SourceMergedComparisonEffects (Effect read_graph)
open SourceMergedComparisonBudget SourceMergedComparisonStages
open MergedSourceComparison (Result)
open MergedFreshOrdinaryComparison (check allRows)
open MergedComparisonCompletion (EventuallyDone eventually_bind identity_closed remainingPairs remaining_mem remaining_cons_lt)
open InternedMuDepthInventory (Bounded)
variable {Symbol Guard : Type} [DecidableEq (EdgeKey Symbol Guard)]

noncomputable section

local instance (limit : Nat) : WellFoundedRelation (Fin limit → Nat) :=
  ⟨HeightOrder.VectorBelow limit, HeightOrder.vector_wellFounded limit⟩

/-- General closed comparisons have a stable exact result and cache at all sufficiently large bounds. -/
theorem check_eventually [DecidableEq Symbol] (limit : Nat) (clear : Guard → Bool)
    (state : State Symbol Guard) (semantic : SemanticReady state) (bounded : Bounded state limit)
    (above : List (Nat × Nat)) (wide narrow : Value Symbol Guard)
    (wideInput : Available state wide) (narrowInput : Available state narrow) (wideClosed : wide.free = []) (narrowClosed : narrow.free = []) :
    EventuallyDone (fun fuel => check clear fuel above wide narrow state) := by
  classical
  by_cases narrowEmpty : narrow.referenceOf = .empty
  · refine ⟨0, true, state, ?_⟩
    intro fuel enough
    change check clear fuel above wide narrow state = .done true state
    rw [check, ite_eq_left narrowEmpty]
  by_cases wideEmpty : wide.referenceOf = .empty
  · refine ⟨0, false, state, ?_⟩
    intro fuel enough
    change check clear fuel above wide narrow state = .done false state
    rw [check, ite_eq_right narrowEmpty, ite_eq_left wideEmpty]
  by_cases same : wide.referenceOf = narrow.referenceOf
  · refine ⟨0, true, state, ?_⟩
    intro fuel enough
    change check clear fuel above wide narrow state = .done true state
    rw [check, ite_eq_right narrowEmpty, ite_eq_right wideEmpty, ite_eq_left same]
  have facts := semantic.ready.semantic.1.normal.facts
  obtain ⟨wideId, wideIdentity, wideBound⟩ := identity_closed wide state facts wideInput wideClosed wideEmpty
  obtain ⟨narrowId, narrowIdentity, narrowBound⟩ := identity_closed narrow state facts narrowInput narrowClosed narrowEmpty
  by_cases visited : (wideId, narrowId) ∈ above
  · refine ⟨0, true, state, ?_⟩
    intro fuel enough
    change check clear fuel above wide narrow state = .done true state
    simp only [check, ite_eq_right narrowEmpty, ite_eq_right wideEmpty, ite_eq_right same,
      wideIdentity, narrowIdentity, ite_eq_left visited]
  have callbacks : ∀ fuel, Callback (Symbol := Symbol) limit (check clear fuel ((wideId, narrowId) :: above)) :=
    fun fuel => check_budget limit clear fuel ((wideId, narrowId) :: above)
  have complete : CompleteCallback limit state (fun fuel => check clear fuel ((wideId, narrowId) :: above)) := by
    intro left right current currentSemantic currentBounded leftInput rightInput leftClosed rightClosed reached
    have decrease : Prod.Lex (HeightOrder.VectorBelow limit) Nat.lt
        ((fun index => InternedFreshMuUnfoldBudget.count current index), (remainingPairs current.nodes.next ((wideId, narrowId) :: above)).length)
        ((fun index => InternedFreshMuUnfoldBudget.count state index), (remainingPairs state.nodes.next above).length) := by
      by_cases unchanged : current = state
      · subst current
        apply Prod.Lex.right
        exact remaining_cons_lt state.nodes.next above (wideId, narrowId)
          (remaining_mem state.nodes.next above wideId narrowId wideBound narrowBound visited)
      · apply Prod.Lex.left
        exact reached.progress.resolve_right unchanged
    exact check_eventually limit clear current currentSemantic currentBounded _ left right leftInput rightInput leftClosed rightClosed
  have rows : EventuallyDone (fun fuel => (MergedFreshOrdinaryExposure.read (fuel + 1) narrow state).bind
      (fun narrows after => allRows (fuel + 1) clear (check clear fuel ((wideId, narrowId) :: above)) wide narrows after)) := by
    apply eventually_bind
    · exact read_eventually narrow state semantic narrowInput narrowClosed
    · intro fuel narrows after done
      have readFacts := (read_graph (fuel + 1) narrow state narrows after done).verified semantic narrowInput narrowClosed
      have readBudget := read_budget limit (fuel + 1) narrow state semantic bounded narrowInput narrowClosed narrows after done
      exact allRows_eventually limit state clear _ callbacks complete wide narrows after readFacts.2.1 readBudget.bounded
        (readFacts.1.available wide wideInput) readFacts.2.2.1 wideClosed readFacts.2.2.2 readBudget
  obtain ⟨bound, accepted, after, rowsDone⟩ := rows
  refine ⟨bound + 1, accepted, after, ?_⟩
  intro fuel enough
  cases fuel with
  | zero => omega
  | succ fuel =>
      simpa only [check, ite_eq_right narrowEmpty, ite_eq_right wideEmpty, ite_eq_right same,
        wideIdentity, narrowIdentity, ite_eq_right visited] using rowsDone fuel (by omega)
termination_by ((fun index : Fin limit => InternedFreshMuUnfoldBudget.count state index), (remainingPairs state.nodes.next above).length)
decreasing_by exact decrease

/-- The actual initial finite Mu inventory derives general comparison completion and complete semantic effects. -/
theorem check_complete [DecidableEq Symbol] (clear : Guard → Bool)
    (state : State Symbol Guard) (semantic : SemanticReady state) (above : List (Nat × Nat)) (wide narrow : Value Symbol Guard)
    (wideInput : Available state wide) (narrowInput : Available state narrow) (wideClosed : wide.free = []) (narrowClosed : narrow.free = []) :
    ∃ bound accepted after, (∀ fuel, bound ≤ fuel → check clear fuel above wide narrow state = .done accepted after) ∧ Effect state after := by
  obtain ⟨bound, accepted, after, done⟩ := check_eventually (maximumDepth (InternedRecordCoherence.nodeInventory state) + 1)
    clear state semantic (InternedMuDepthInventory.initial_bounded state semantic.ready.semantic.1.normal.facts)
    above wide narrow wideInput narrowInput wideClosed narrowClosed
  exact ⟨bound, accepted, after, done, SourceMergedComparisonEffects.check_effect clear bound above wide narrow state semantic
    wideInput narrowInput wideClosed narrowClosed accepted after (done bound (Nat.le_refl _))⟩

end
end MicroCFTA.SourceMergedComparisonCompletion
