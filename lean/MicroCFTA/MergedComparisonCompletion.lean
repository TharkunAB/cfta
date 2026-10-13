import MicroCFTA.MergedComparisonFacts

/-!
# Completion of the ordered stateful comparator

Actual cache changes consume cold original Mu records. Without a cache
change, a new ancestor pair consumes one issued pair. Finite ordered
lists compose the resulting stable recursive bounds.
-/
namespace MicroCFTA.MergedComparisonCompletion
open Cache InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedNestedFacts InternedNestedProvenance InternedShallowHeap InternedEdgeResidency InternedFreshProbeKeys
open MergedPhysicalWarmup MergedSourceComparison MergedComparisonFacts
open MergedComparisonColdMeasure MergedColdReaderClosedInputs

/-- All sufficiently large bounds return the same value and exact cache. -/
def EventuallyDone (run : Nat → Result Symbol Guard Output) : Prop :=
  ∃ bound value after, ∀ fuel, bound ≤ fuel → run fuel = .done value after

/-- A constant successful effect has a stable bound of zero. -/
theorem eventually_done (value : Output) (state : State Symbol Guard) :
    EventuallyDone (fun _ => Result.done value state) := ⟨0, value, state, fun _ _ => rfl⟩

/-- Ordered effect sequencing combines two stable bounds without changing either trace. -/
theorem eventually_bind (first : Nat → Result Symbol Guard First)
    (next : Nat → First → State Symbol Guard → Result Symbol Guard Output)
    (complete : EventuallyDone first)
    (continues : ∀ fuel value after, first fuel = .done value after →
      EventuallyDone (fun later => next later value after)) :
    EventuallyDone (fun fuel => (first fuel).bind (next fuel)) := by
  obtain ⟨bound, value, middle, done⟩ := complete
  obtain ⟨later, output, final, nextDone⟩ := continues bound value middle (done bound (Nat.le_refl _))
  refine ⟨max bound later, output, final, ?_⟩
  intro fuel enough
  simp only [done fuel (Nat.le_trans (Nat.le_max_left _ _) enough), Result.bind,
    nextDone fuel (Nat.le_trans (Nat.le_max_right _ _) enough)]

/-- The closed physical reader supplies an exact stable successful bound. -/
theorem read_eventually [DecidableEq (EdgeKey Symbol Guard)] (value : Value Symbol Guard)
    (state : State Symbol Guard) (facts : Facts state) (prepared : Prepared state)
    (available : Available state value) (closed : value.free = []) :
    EventuallyDone (fun fuel => read (fuel + 1) value state) := by
  obtain ⟨bound, edges, after, done, _, _, _, _, _, _, _, stable⟩ :=
    MergedColdReaderFacts.read_closed value state facts prepared available closed
  refine ⟨bound, edges, after, ?_⟩
  intro fuel enough
  have extra : bound + (fuel + 1 - bound) = fuel + 1 := by omega
  have later := stable (fuel + 1 - bound)
  rw [extra] at later
  simp only [MergedSourceComparison.read, later]

/-- Discarding a successful answer retains its verified cache effects. -/
theorem _root_.MicroCFTA.MergedComparisonFacts.Verified.effect [DecidableEq (EdgeKey Symbol Guard)]
    (verified : Verified before (result : Result Symbol Guard Output))
    (done : result = .done value after) : Verified before (.done () after) := by
  rw [done] at verified
  exact ⟨verified.facts, verified.growth, verified.history, verified.unchanged, verified.progress⟩

/-- Two successful source effects compose their original warming progress. -/
theorem effect_trans [DecidableEq (EdgeKey Symbol Guard)]
    {before middle after : State Symbol Guard}
    (first : Verified before (Result.done () middle)) (second : Verified middle (Result.done () after)) :
    Verified before (Result.done () after) :=
  ⟨second.facts, grows_trans first.growth second.growth, extends_trans first.history second.history,
    noNewMu_trans first.unchanged second.unchanged,
    first.progress.trans second.progress first.facts.coherent.valid second.growth⟩

/-- Closed nonempty source operands have an issued numeric identity. -/
theorem identity_closed (value : Value Symbol Guard) (state : State Symbol Guard)
    (facts : Facts state) (available : Available state value) (closed : value.free = [])
    (nonempty : value.referenceOf ≠ .empty) :
    ∃ number, identity value = some number ∧ number < state.nodes.next := by
  cases value with
  | empty => exact False.elim (nonempty rfl)
  | reference name => simp [Value.free] at closed
  | node entry edges depth free | union entry members depth free | mu entry body depth ordinary =>
      refine ⟨entry.identity, rfl, ?_⟩
      have stored := resident_entry state facts.coherent _ available.resident entry rfl
      exact facts.coherent.valid.2.1 entry.identity entry.key
        (facts.coherent.valid.2.2 entry.key entry stored).2

/-- Numeric pairs not yet present in the source ancestor list. -/
def remainingPairs (limit : Nat) (above : List (Nat × Nat)) : List (Nat × Nat) :=
  ((List.range limit).flatMap fun left => (List.range limit).map (left, ·)).filter
    (fun pair => decide (pair ∉ above))

/-- Every available fresh pair belongs to the finite current allowance. -/
theorem remaining_mem (limit : Nat) (above : List (Nat × Nat)) (left right : Nat)
    (leftBound : left < limit) (rightBound : right < limit) (fresh : (left, right) ∉ above) :
    (left, right) ∈ remainingPairs limit above := by
  simp only [remainingPairs, List.mem_filter, decide_eq_true_eq]
  exact ⟨List.mem_flatMap.mpr ⟨left, List.mem_range.mpr leftBound,
    List.mem_map.mpr ⟨right, List.mem_range.mpr rightBound, rfl⟩⟩, fresh⟩

/-- Adding a fresh ancestor pair strictly decreases its current finite allowance. -/
theorem remaining_cons_lt (limit : Nat) (above : List (Nat × Nat)) (pair : Nat × Nat)
    (member : pair ∈ remainingPairs limit above) :
    (remainingPairs limit (pair :: above)).length < (remainingPairs limit above).length := by
  have equal : remainingPairs limit (pair :: above) =
      (remainingPairs limit above).filter (fun other => decide (other ≠ pair)) := by
    simp only [remainingPairs, List.filter_filter]
    apply List.filter_congr
    intro other member
    simp only [List.mem_cons, not_or]
    by_cases same : other = pair <;> by_cases present : other ∈ above <;> simp [same, present]
  rw [equal]
  exact List.length_filter_lt_length_iff_exists.mpr ⟨pair, member, by simp⟩

/-- Smaller recursive calls complete at every cache reached by earlier source effects. -/
def CompleteCallback [DecidableEq (EdgeKey Symbol Guard)] (before : State Symbol Guard)
    (compare : Nat → Value Symbol Guard → Value Symbol Guard → State Symbol Guard → Result Symbol Guard Bool) : Prop :=
  ∀ wide narrow state, Facts state → Prepared state → Available state wide → Available state narrow →
    wide.free = [] → narrow.free = [] → Verified before (.done () state) →
    EventuallyDone (fun fuel => compare fuel wide narrow state)

/-- Finite ordered children combine stable recursive bounds along their actual effects. -/
theorem children_eventually [DecidableEq (EdgeKey Symbol Guard)]
    (before : State Symbol Guard)
    (compare : Nat → Value Symbol Guard → Value Symbol Guard → State Symbol Guard → Result Symbol Guard Bool)
    (callbacks : ∀ fuel, Callback (compare fuel)) (complete : CompleteCallback before compare)
    (wides narrows : List (Value Symbol Guard)) (state : State Symbol Guard)
    (facts : Facts state) (prepared : Prepared state) (wideInputs : Values state wides) (narrowInputs : Values state narrows)
    (wideClosed : ClosedValues wides) (narrowClosed : ClosedValues narrows)
    (reached : Verified before (.done () state)) :
    EventuallyDone (fun fuel => children (compare fuel) wides narrows state) := by
  induction wides generalizing narrows state with
  | nil => exact eventually_done true state
  | cons wide wides ih =>
      cases narrows with
      | nil => exact eventually_done true state
      | cons narrow narrows =>
          apply eventually_bind
          · exact complete wide narrow state facts prepared (wideInputs wide List.mem_cons_self)
              (narrowInputs narrow List.mem_cons_self) (wideClosed wide List.mem_cons_self)
              (narrowClosed narrow List.mem_cons_self) reached
          · intro fuel accepted after done
            have checked := (callbacks fuel wide narrow state facts prepared
              (wideInputs wide List.mem_cons_self) (narrowInputs narrow List.mem_cons_self)
              (wideClosed wide List.mem_cons_self) (narrowClosed narrow List.mem_cons_self)).effect done
            cases accepted with
            | false => exact eventually_done false after
            | true =>
                apply ih narrows after checked.facts (prepared.preserve checked.unchanged)
                · exact fun value member => (wideInputs value (List.mem_cons_of_mem _ member)).grows
                    state after checked.growth checked.history
                · exact fun value member => (narrowInputs value (List.mem_cons_of_mem _ member)).grows
                    state after checked.growth checked.history
                · exact fun value member => wideClosed value (List.mem_cons_of_mem _ member)
                · exact fun value member => narrowClosed value (List.mem_cons_of_mem _ member)
                · exact effect_trans reached checked

/-- Ordered candidate search retains failed candidates' effects while combining finite bounds. -/
theorem anyCover_eventually [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Symbol]
    (before : State Symbol Guard) (clear : Guard → Bool)
    (compare : Nat → Value Symbol Guard → Value Symbol Guard → State Symbol Guard → Result Symbol Guard Bool)
    (callbacks : ∀ fuel, Callback (compare fuel)) (complete : CompleteCallback before compare)
    (narrow : EdgeValue Symbol Guard) (wides : List (EdgeValue Symbol Guard))
    (state : State Symbol Guard) (facts : Facts state) (prepared : Prepared state)
    (narrowInput : EdgeResident state narrow) (wideInputs : Edges state wides)
    (narrowClosed : ClosedValues narrow.children) (wideClosed : ClosedEdges wides)
    (reached : Verified before (.done () state)) :
    EventuallyDone (fun fuel => anyCover clear (compare fuel) narrow wides state) := by
  induction wides generalizing state with
  | nil => exact eventually_done false state
  | cons wide rest ih =>
      by_cases header : wide.entry.key.symbol = narrow.entry.key.symbol ∧
          wide.children.length = narrow.children.length ∧ clear wide.entry.key.constraint = true
      · simp only [anyCover, ite_eq_left header]
        apply eventually_bind
        · exact children_eventually before compare callbacks complete wide.children narrow.children state facts prepared
            (facts.cached.edges wide.entry.key wide (wideInputs wide List.mem_cons_self))
            (facts.cached.edges narrow.entry.key narrow narrowInput) (wideClosed wide List.mem_cons_self) narrowClosed reached
        · intro fuel accepted after done
          have checked := (children_verified (compare fuel) (callbacks fuel) wide.children narrow.children state facts prepared
            (facts.cached.edges wide.entry.key wide (wideInputs wide List.mem_cons_self))
            (facts.cached.edges narrow.entry.key narrow narrowInput) (wideClosed wide List.mem_cons_self) narrowClosed).effect done
          cases accepted with
          | true => exact eventually_done true after
          | false =>
              exact ih after checked.facts (prepared.preserve checked.unchanged)
                (edge_grows state after checked.growth narrow narrowInput)
                (fun edge member => edge_grows state after checked.growth edge (wideInputs edge (List.mem_cons_of_mem _ member)))
                (fun edge member => wideClosed edge (List.mem_cons_of_mem _ member)) (effect_trans reached checked)
      · simpa only [anyCover, ite_eq_right header] using ih state facts prepared narrowInput
          (fun edge member => wideInputs edge (List.mem_cons_of_mem _ member))
          (fun edge member => wideClosed edge (List.mem_cons_of_mem _ member)) reached

/-- Each demanded narrow row composes its physical read and ordered cover search. -/
theorem allRows_eventually [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Symbol]
    (before : State Symbol Guard) (clear : Guard → Bool)
    (compare : Nat → Value Symbol Guard → Value Symbol Guard → State Symbol Guard → Result Symbol Guard Bool)
    (callbacks : ∀ fuel, Callback (compare fuel)) (complete : CompleteCallback before compare)
    (wide : Value Symbol Guard) (narrows : List (EdgeValue Symbol Guard))
    (state : State Symbol Guard) (facts : Facts state) (prepared : Prepared state)
    (wideInput : Available state wide) (narrowInputs : Edges state narrows)
    (wideClosed : wide.free = []) (narrowClosed : ClosedEdges narrows)
    (reached : Verified before (.done () state)) :
    EventuallyDone (fun fuel => allRows (fuel + 1) clear (compare fuel) wide narrows state) := by
  induction narrows generalizing state with
  | nil => exact eventually_done true state
  | cons narrow rest ih =>
      apply eventually_bind
      · exact read_eventually wide state facts prepared wideInput wideClosed
      · intro fuel wides middle readDone
        have reader := (read_verified (fuel + 1) wide state facts prepared wideInput).effect readDone
        have middlePrepared := prepared.preserve reader.unchanged
        have middleWide := wideInput.grows state middle reader.growth reader.history
        have middleNarrows : Edges middle (narrow :: rest) :=
          fun edge member => edge_grows state middle reader.growth edge (narrowInputs edge member)
        have wideEdges := read_edges (fuel + 1) wide state facts prepared wideInput wides middle readDone
        have closedEdges := read_closed (fuel + 1) wide state facts prepared wideInput wideClosed wides middle readDone
        have middleReached := effect_trans reached reader
        apply eventually_bind
        · exact anyCover_eventually before clear compare callbacks complete narrow wides middle reader.facts middlePrepared
            (middleNarrows narrow List.mem_cons_self) wideEdges (narrowClosed narrow List.mem_cons_self) closedEdges middleReached
        · intro bound accepted after done
          have checked := (anyCover_verified clear (compare bound) (callbacks bound) narrow wides middle reader.facts middlePrepared
            (middleNarrows narrow List.mem_cons_self) wideEdges (narrowClosed narrow List.mem_cons_self) closedEdges).effect done
          cases accepted with
          | false => exact eventually_done false after
          | true =>
              exact ih after checked.facts (middlePrepared.preserve checked.unchanged)
                (middleWide.grows middle after checked.growth checked.history)
                (fun edge member => edge_grows middle after checked.growth edge (middleNarrows edge (List.mem_cons_of_mem _ member)))
                (fun edge member => narrowClosed edge (List.mem_cons_of_mem _ member)) (effect_trans middleReached checked)

/-- The exact ordered comparator has a stable successful bound on available closed inputs. -/
theorem check_eventually [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Symbol]
    (originals : List (Value Symbol Guard)) (clear : Guard → Bool)
    (state : State Symbol Guard) (facts : Facts state) (prepared : Prepared state)
    (covers : CoversMu originals state) (above : List (Nat × Nat)) (wide narrow : Value Symbol Guard)
    (wideInput : Available state wide) (narrowInput : Available state narrow)
    (wideClosed : wide.free = []) (narrowClosed : narrow.free = []) :
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
  obtain ⟨wideId, wideIdentity, wideBound⟩ := identity_closed wide state facts wideInput wideClosed wideEmpty
  obtain ⟨narrowId, narrowIdentity, narrowBound⟩ := identity_closed narrow state facts narrowInput narrowClosed narrowEmpty
  by_cases visited : (wideId, narrowId) ∈ above
  · refine ⟨0, true, state, ?_⟩
    intro fuel enough
    change check clear fuel above wide narrow state = .done true state
    simp only [check, ite_eq_right narrowEmpty, ite_eq_right wideEmpty, ite_eq_right same,
      wideIdentity, narrowIdentity, ite_eq_left visited]
  have callbacks : ∀ fuel, Callback (Symbol := Symbol) (check clear fuel ((wideId, narrowId) :: above)) := by
    intro fuel left right current currentFacts currentPrepared leftInput rightInput leftClosed rightClosed
    exact check_verified clear fuel _ left right current currentFacts currentPrepared leftInput rightInput leftClosed rightClosed
  have complete : CompleteCallback state (fun fuel => check clear fuel ((wideId, narrowId) :: above)) := by
    intro left right current currentFacts currentPrepared leftInput rightInput leftClosed rightClosed reached
    have decrease : Prod.Lex (· < ·) (· < ·)
        (coldCount originals current, (remainingPairs current.nodes.next ((wideId, narrowId) :: above)).length)
        (coldCount originals state, (remainingPairs state.nodes.next above).length) := by
      by_cases unchanged : current = state
      · subst current
        apply Prod.Lex.right
        exact remaining_cons_lt state.nodes.next above (wideId, narrowId)
          (remaining_mem state.nodes.next above wideId narrowId wideBound narrowBound visited)
      · apply Prod.Lex.left
        exact progress_lt originals state current facts.coherent.valid reached.growth covers reached.progress unchanged
    exact check_eventually originals clear current currentFacts currentPrepared
      (covers.preserve state current facts originals reached.unchanged) _ left right
      leftInput rightInput leftClosed rightClosed
  have rows : EventuallyDone (fun fuel => (MergedSourceComparison.read (fuel + 1) narrow state).bind
      (fun narrows after => allRows (fuel + 1) clear (check clear fuel ((wideId, narrowId) :: above)) wide narrows after)) := by
    apply eventually_bind
    · exact read_eventually narrow state facts prepared narrowInput narrowClosed
    · intro fuel narrows after done
      have reader := (read_verified (fuel + 1) narrow state facts prepared narrowInput).effect done
      exact allRows_eventually state clear _ callbacks complete wide narrows after reader.facts
        (prepared.preserve reader.unchanged) (wideInput.grows state after reader.growth reader.history)
        (read_edges (fuel + 1) narrow state facts prepared narrowInput narrows after done) wideClosed
        (read_closed (fuel + 1) narrow state facts prepared narrowInput narrowClosed narrows after done) reader
  obtain ⟨bound, accepted, after, rowsDone⟩ := rows
  refine ⟨bound + 1, accepted, after, ?_⟩
  intro fuel enough
  cases fuel with
  | zero => omega
  | succ fuel =>
      simpa only [check, ite_eq_right narrowEmpty, ite_eq_right wideEmpty, ite_eq_right same,
        wideIdentity, narrowIdentity, ite_eq_right visited] using rowsDone fuel (by omega)
termination_by (coldCount originals state, (remainingPairs state.nodes.next above).length)
decreasing_by exact decrease

/-- The initial issued inventory derives comparator completion with no recursive law premise. -/
theorem check_complete [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Symbol]
    (clear : Guard → Bool) (state : State Symbol Guard) (facts : Facts state) (prepared : Prepared state)
    (above : List (Nat × Nat)) (wide narrow : Value Symbol Guard)
    (wideInput : Available state wide) (narrowInput : Available state narrow)
    (wideClosed : wide.free = []) (narrowClosed : narrow.free = []) :
    ∃ bound accepted after, (∀ fuel, bound ≤ fuel → check clear fuel above wide narrow state = .done accepted after) ∧
      Verified state (.done accepted after) ∧ Prepared after := by
  obtain ⟨bound, accepted, after, done⟩ := check_eventually (nodeInventory state) clear state facts prepared
    (covers_initial state facts) above wide narrow wideInput narrowInput wideClosed narrowClosed
  have verified := check_verified clear bound above wide narrow state facts prepared wideInput narrowInput wideClosed narrowClosed
  dsimp only at done
  rw [done bound (Nat.le_refl _)] at verified
  exact ⟨bound, accepted, after, done, verified, prepared.preserve verified.unchanged⟩

end MicroCFTA.MergedComparisonCompletion
