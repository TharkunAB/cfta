import MicroCFTA.MergedComparisonCompletion

/-!
# No nontrivial cycles of verified comparison effects

A changed source effect warms a previously cold Mu. Cache growth cannot
make that record cold again. Thus a verified effect with growth back to
its starting cache must have left that cache unchanged.
-/
namespace MicroCFTA.MergedComparisonEffectOrder
open InternedConstructorTemplates InternedProbeProvenance InternedNestedProvenance InternedNestedFacts
open InternedEdgeResidency MergedPhysicalWarmup MergedSourceComparison MergedComparisonFacts
open MergedComparisonWarmProgress
open MergedColdReaderClosedInputs

/-- A verified effect cannot change the cache and then grow back to its original state. -/
theorem verified_antisymm [DecidableEq (EdgeKey Symbol Guard)]
    (before after : State Symbol Guard) (effect : Verified before (Result.done () after))
    (back : Grows after before) : after = before := by
  rcases effect.progress with same | ⟨entry, body, depth, ordinary, available, cold, warm⟩
  · exact same
  · exact False.elim (cold (warm.grows after before effect.facts.coherent.valid back _))

/-- Every successful prefix of a cache-preserving complete source trace is cache-preserving. -/
theorem prefix_unchanged [DecidableEq (EdgeKey Symbol Guard)]
    (before : State Symbol Guard) (first : Result Symbol Guard First)
    (next : First → State Symbol Guard → Result Symbol Guard Output)
    (verified : Verified before first)
    (continues : ∀ value after, first = .done value after → Verified after (next value after))
    (value : Output) (done : first.bind next = .done value before) : first.state = before := by
  cases first with
  | failed fault after => cases done
  | done initial after =>
      have later := continues initial after rfl
      change next initial after = .done value before at done
      rw [done] at later
      exact verified_antisymm before after (verified.effect rfl) later.growth

/-- A cache-preserving initial read and row search both run in the original cache. -/
theorem read_allRows_fixed [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Symbol]
    (fuel : Nat) (clear : Guard → Bool)
    (compare : Value Symbol Guard → Value Symbol Guard → State Symbol Guard → Result Symbol Guard Bool)
    (callback : Callback compare) (wide narrow : Value Symbol Guard)
    (state : State Symbol Guard) (facts : Facts state) (prepared : Prepared state)
    (wideInput : Available state wide) (narrowInput : Available state narrow)
    (wideClosed : wide.free = []) (narrowClosed : narrow.free = []) (accepted : Bool)
    (done : (MergedSourceComparison.read fuel narrow state).bind
      (fun rows after => allRows fuel clear compare wide rows after) = .done accepted state) :
    ∃ rows, MergedSourceComparison.read fuel narrow state = .done rows state ∧
      allRows fuel clear compare wide rows state = .done accepted state := by
  cases readDone : MergedSourceComparison.read fuel narrow state with
  | failed fault after => simp only [readDone, Result.bind, reduceCtorEq] at done
  | done rows after =>
      have reader := (read_verified fuel narrow state facts prepared narrowInput).effect readDone
      have tailDone : allRows fuel clear compare wide rows after = .done accepted state := by
        simpa only [readDone, Result.bind] using done
      have tail := allRows_verified fuel clear compare callback wide rows after reader.facts
        (prepared.preserve reader.unchanged) (wideInput.grows state after reader.growth reader.history)
        (read_edges fuel narrow state facts prepared narrowInput rows after readDone) wideClosed
        (read_closed fuel narrow state facts prepared narrowInput narrowClosed rows after readDone)
      have same := verified_antisymm state after reader (tail.effect tailDone).growth
      subst after
      exact ⟨rows, rfl, tailDone⟩

/-- Every stage of a successful cache-preserving nonempty row loop uses that same cache. -/
theorem allRows_fixed [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Symbol]
    (fuel : Nat) (clear : Guard → Bool)
    (compare : Value Symbol Guard → Value Symbol Guard → State Symbol Guard → Result Symbol Guard Bool)
    (callback : Callback compare) (wide : Value Symbol Guard)
    (narrow : EdgeValue Symbol Guard) (rest : List (EdgeValue Symbol Guard))
    (state : State Symbol Guard) (facts : Facts state) (prepared : Prepared state)
    (wideInput : Available state wide) (narrowInputs : Edges state (narrow :: rest))
    (wideClosed : wide.free = []) (narrowClosed : ClosedEdges (narrow :: rest))
    (done : allRows fuel clear compare wide (narrow :: rest) state = .done true state) :
    ∃ rows, MergedSourceComparison.read fuel wide state = .done rows state ∧
      anyCover clear compare narrow rows state = .done true state ∧
      allRows fuel clear compare wide rest state = .done true state := by
  cases readDone : MergedSourceComparison.read fuel wide state with
  | failed fault after => simp only [allRows, readDone, Result.bind, reduceCtorEq] at done
  | done rows middle =>
      have reader := (read_verified fuel wide state facts prepared wideInput).effect readDone
      have middlePrepared := prepared.preserve reader.unchanged
      have middleWide := wideInput.grows state middle reader.growth reader.history
      have middleNarrows : Edges middle (narrow :: rest) :=
        fun edge member => edge_grows state middle reader.growth edge (narrowInputs edge member)
      have rowInputs := read_edges fuel wide state facts prepared wideInput rows middle readDone
      have rowClosed := read_closed fuel wide state facts prepared wideInput wideClosed rows middle readDone
      cases coverDone : anyCover clear compare narrow rows middle with
      | failed fault after => simp only [allRows, readDone, coverDone, Result.bind, reduceCtorEq] at done
      | done covered after =>
          have checked := (anyCover_verified clear compare callback narrow rows middle reader.facts middlePrepared
            (middleNarrows narrow List.mem_cons_self) rowInputs (narrowClosed narrow List.mem_cons_self) rowClosed).effect coverDone
          cases covered with
          | false =>
              simp only [allRows, readDone, coverDone, Result.bind, Bool.false_eq_true, ↓reduceIte, Result.done.injEq] at done
              exact False.elim done.1
          | true =>
              have tailDone : allRows fuel clear compare wide rest after = .done true state := by
                simpa only [allRows, readDone, coverDone, Result.bind, ↓reduceIte] using done
              have tail := allRows_verified fuel clear compare callback wide rest after checked.facts
                (middlePrepared.preserve checked.unchanged) (middleWide.grows middle after checked.growth checked.history)
                (fun edge member => edge_grows middle after checked.growth edge (middleNarrows edge (List.mem_cons_of_mem _ member)))
                wideClosed (fun edge member => narrowClosed edge (List.mem_cons_of_mem _ member))
              have firstSame := verified_antisymm state middle reader
                (grows_trans checked.growth (tail.effect tailDone).growth)
              subst middle
              have secondSame := verified_antisymm state after checked (tail.effect tailDone).growth
              subst after
              exact ⟨rows, rfl, coverDone, tailDone⟩

end MicroCFTA.MergedComparisonEffectOrder
