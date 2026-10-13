import MicroCFTA.MergedComparisonFacts
import MicroCFTA.MergedComparisonReaderReplay

/-!
# Exact comparison replay in a common later cache

A completed ordered comparison replays its exact Boolean after later cache
growth. Every reader and recursive comparison retains its original trace.
The replay leaves the later cache unchanged, including after failed covers.
-/
namespace MicroCFTA.MergedComparisonReplay
open Cache InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance InternedNestedFacts
open InternedNestedProvenance InternedEdgeResidency InternedShallowHeap
open MergedPhysicalWarmup MergedSourceComparison MergedComparisonFacts
open MergedColdReaderClosedInputs

/-- A completed lifted edge read replays without effects in every later cache. -/
theorem read_replay [DecidableEq (EdgeKey Symbol Guard)] (fuel : Nat) (value : Value Symbol Guard)
    (state : State Symbol Guard) (facts : Facts state) (prepared : Prepared state)
    (available : Available state value) (edges : List (EdgeValue Symbol Guard)) (after later : State Symbol Guard)
    (done : read fuel value state = .done edges after) (growth : Grows after later) :
    read fuel value later = .done edges later := by
  have replay := MergedComparisonReaderReplay.nodeEdges_replay fuel value state facts prepared available edges after later
    (read_done fuel value state edges after done) growth
  simp only [MergedSourceComparison.read, replay]

/-- Recursive comparisons replay completed traces after later physical cache growth. -/
def CallbackReplay [DecidableEq (EdgeKey Symbol Guard)]
    (compare : Value Symbol Guard → Value Symbol Guard → State Symbol Guard → Result Symbol Guard Bool) : Prop :=
  ∀ wide narrow state, Facts state → Prepared state → Available state wide → Available state narrow →
    wide.free = [] → narrow.free = [] → ∀ accepted after later,
    compare wide narrow state = .done accepted after → Grows after later →
    compare wide narrow later = .done accepted later

/-- Ordered child comparisons replay every completed child and preserve short-circuit results. -/
theorem children_replay [DecidableEq (EdgeKey Symbol Guard)]
    (compare : Value Symbol Guard → Value Symbol Guard → State Symbol Guard → Result Symbol Guard Bool)
    (callback : Callback compare) (replay : CallbackReplay compare)
    (wides narrows : List (Value Symbol Guard)) (state : State Symbol Guard)
    (facts : Facts state) (prepared : Prepared state) (wideInputs : Values state wides) (narrowInputs : Values state narrows)
    (wideClosed : ClosedValues wides) (narrowClosed : ClosedValues narrows)
    (accepted : Bool) (after later : State Symbol Guard)
    (done : children compare wides narrows state = .done accepted after) (growth : Grows after later) :
    children compare wides narrows later = .done accepted later := by
  induction wides generalizing narrows state with
  | nil => cases done; rfl
  | cons wide wides ih =>
      cases narrows with
      | nil => cases done; rfl
      | cons narrow narrows =>
          have wideInput := wideInputs wide List.mem_cons_self
          have narrowInput := narrowInputs narrow List.mem_cons_self
          have wideFree := wideClosed wide List.mem_cons_self
          have narrowFree := narrowClosed narrow List.mem_cons_self
          have verified := callback wide narrow state facts prepared wideInput narrowInput wideFree narrowFree
          cases first : compare wide narrow state with
          | failed fault middle => simp only [MergedSourceComparison.children, first, Result.bind, reduceCtorEq] at done
          | done answer middle =>
              have middleFacts : Facts middle := by simpa only [first, Result.state] using verified.facts
              have middlePrepared : Prepared middle := by simpa only [first, Result.state] using prepared.preserve verified.unchanged
              have tailWide : Values middle wides := fun value member => by
                simpa only [first, Result.state] using verified.available _ value (wideInputs value (List.mem_cons_of_mem _ member))
              have tailNarrow : Values middle narrows := fun value member => by
                simpa only [first, Result.state] using verified.available _ value (narrowInputs value (List.mem_cons_of_mem _ member))
              have tailWideClosed : ClosedValues wides := fun value member => wideClosed value (List.mem_cons_of_mem _ member)
              have tailNarrowClosed : ClosedValues narrows := fun value member => narrowClosed value (List.mem_cons_of_mem _ member)
              cases answer with
              | false =>
                  have equal : accepted = false ∧ after = middle := by
                    simpa only [MergedSourceComparison.children, first, Result.bind, Bool.false_eq_true, ↓reduceIte, Result.done.injEq, eq_comm] using done
                  rcases equal with ⟨rfl, rfl⟩
                  simp only [MergedSourceComparison.children, replay wide narrow state facts prepared wideInput narrowInput wideFree narrowFree
                    false _ later first growth, Result.bind, Bool.false_eq_true, ↓reduceIte]
              | true =>
                  have tailDone : children compare wides narrows middle = .done accepted after := by
                    simpa only [MergedSourceComparison.children, first, Result.bind, ↓reduceIte] using done
                  have tailVerified := children_verified compare callback wides narrows middle middleFacts middlePrepared
                    tailWide tailNarrow tailWideClosed tailNarrowClosed
                  have tailGrowth : Grows middle after := by simpa only [tailDone, Result.state] using tailVerified.growth
                  simp only [MergedSourceComparison.children, replay wide narrow state facts prepared wideInput narrowInput wideFree narrowFree
                    true middle later first (grows_trans tailGrowth growth), Result.bind, ↓reduceIte]
                  exact ih narrows middle middleFacts middlePrepared tailWide tailNarrow tailWideClosed tailNarrowClosed tailDone

/-- Cover search replays unsuccessful candidates before the same final cover or rejection. -/
theorem anyCover_replay [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Symbol] (clear : Guard → Bool)
    (compare : Value Symbol Guard → Value Symbol Guard → State Symbol Guard → Result Symbol Guard Bool)
    (callback : Callback compare) (replay : CallbackReplay compare)
    (narrow : EdgeValue Symbol Guard) (wides : List (EdgeValue Symbol Guard)) (state : State Symbol Guard)
    (facts : Facts state) (prepared : Prepared state) (narrowInput : EdgeResident state narrow) (wideInputs : Edges state wides)
    (narrowClosed : ClosedValues narrow.children) (wideClosed : ClosedEdges wides)
    (accepted : Bool) (after later : State Symbol Guard)
    (done : anyCover clear compare narrow wides state = .done accepted after) (growth : Grows after later) :
    anyCover clear compare narrow wides later = .done accepted later := by
  induction wides generalizing state with
  | nil => cases done; rfl
  | cons wide rest ih =>
      rw [anyCover] at done ⊢
      split at done
      · rename_i header
        simp only [header, and_self, ↓reduceIte]
        have wideChildren := facts.cached.edges wide.entry.key wide (wideInputs wide List.mem_cons_self)
        have narrowChildren := facts.cached.edges narrow.entry.key narrow narrowInput
        have childrenClosed := wideClosed wide List.mem_cons_self
        have verified := children_verified compare callback wide.children narrow.children state facts prepared
          wideChildren narrowChildren childrenClosed narrowClosed
        cases first : MergedSourceComparison.children compare wide.children narrow.children state with
        | failed fault middle => simp only [first, Result.bind, reduceCtorEq] at done
        | done answer middle =>
            have middleFacts : Facts middle := by simpa only [first, Result.state] using verified.facts
            have middlePrepared : Prepared middle := by simpa only [first, Result.state] using prepared.preserve verified.unchanged
            have tailNarrow : EdgeResident middle narrow := by simpa only [first, Result.state] using verified.edge _ narrow narrowInput
            have tailWide : Edges middle rest := fun edge member => by
              simpa only [first, Result.state] using verified.edge _ edge (wideInputs edge (List.mem_cons_of_mem _ member))
            have tailWideClosed : ClosedEdges rest := fun edge member => wideClosed edge (List.mem_cons_of_mem _ member)
            cases answer with
            | true =>
                have equal : accepted = true ∧ after = middle := by
                  simpa only [first, Result.bind, ↓reduceIte, Result.done.injEq, eq_comm] using done
                rcases equal with ⟨rfl, rfl⟩
                simp only [children_replay compare callback replay wide.children narrow.children state facts prepared
                  wideChildren narrowChildren childrenClosed narrowClosed true _ later first growth,
                  Result.bind, ↓reduceIte]
            | false =>
                have tailDone : anyCover clear compare narrow rest middle = .done accepted after := by
                  simpa only [first, Result.bind, Bool.false_eq_true, ↓reduceIte] using done
                have tailVerified := anyCover_verified clear compare callback narrow rest middle middleFacts middlePrepared
                  tailNarrow tailWide narrowClosed tailWideClosed
                have tailGrowth : Grows middle after := by simpa only [tailDone, Result.state] using tailVerified.growth
                simp only [children_replay compare callback replay wide.children narrow.children state facts prepared
                  wideChildren narrowChildren childrenClosed narrowClosed false middle later first (grows_trans tailGrowth growth),
                  Result.bind, Bool.false_eq_true, ↓reduceIte]
                exact ih middle middleFacts middlePrepared tailNarrow tailWide tailWideClosed tailDone
      · rename_i header
        simp only [header, ↓reduceIte]
        exact ih state facts prepared narrowInput (fun edge member => wideInputs edge (List.mem_cons_of_mem _ member))
          (fun edge member => wideClosed edge (List.mem_cons_of_mem _ member)) done

/-- Every demanded row replays its wide read, failed covers, and successful continuation in order. -/
theorem allRows_replay [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Symbol] (fuel : Nat) (clear : Guard → Bool)
    (compare : Value Symbol Guard → Value Symbol Guard → State Symbol Guard → Result Symbol Guard Bool)
    (callback : Callback compare) (replay : CallbackReplay compare)
    (wide : Value Symbol Guard) (narrows : List (EdgeValue Symbol Guard)) (state : State Symbol Guard)
    (facts : Facts state) (prepared : Prepared state) (wideInput : Available state wide) (narrowInputs : Edges state narrows)
    (wideClosed : wide.free = []) (narrowClosed : ClosedEdges narrows)
    (accepted : Bool) (after later : State Symbol Guard)
    (done : allRows fuel clear compare wide narrows state = .done accepted after) (growth : Grows after later) :
    allRows fuel clear compare wide narrows later = .done accepted later := by
  induction narrows generalizing state with
  | nil => cases done; rfl
  | cons narrow rest ih =>
      have reader := read_verified fuel wide state facts prepared wideInput
      cases first : read fuel wide state with
      | failed fault middle => simp only [allRows, first, Result.bind, reduceCtorEq] at done
      | done wides middle =>
          have middleFacts : Facts middle := by simpa only [first, Result.state] using reader.facts
          have middlePrepared : Prepared middle := by simpa only [first, Result.state] using prepared.preserve reader.unchanged
          have middleWide : Available middle wide := by simpa only [first, Result.state] using reader.available _ wide wideInput
          have middleNarrow : Edges middle (narrow :: rest) := fun edge member => by
            simpa only [first, Result.state] using reader.edge _ edge (narrowInputs edge member)
          have wideRows := read_edges fuel wide state facts prepared wideInput wides middle first
          have wideRowsClosed := read_closed fuel wide state facts prepared wideInput wideClosed wides middle first
          have narrowRow := middleNarrow narrow List.mem_cons_self
          have narrowRowClosed := narrowClosed narrow List.mem_cons_self
          have covered := anyCover_verified clear compare callback narrow wides middle middleFacts middlePrepared
            narrowRow wideRows narrowRowClosed wideRowsClosed
          cases second : anyCover clear compare narrow wides middle with
          | failed fault next => simp only [allRows, first, Result.bind, second, reduceCtorEq] at done
          | done answer next =>
              have nextFacts : Facts next := by simpa only [second, Result.state] using covered.facts
              have nextPrepared : Prepared next := by simpa only [second, Result.state] using middlePrepared.preserve covered.unchanged
              have nextWide : Available next wide := by simpa only [second, Result.state] using covered.available _ wide middleWide
              have nextNarrow : Edges next rest := fun edge member => by
                simpa only [second, Result.state] using covered.edge _ edge (middleNarrow edge (List.mem_cons_of_mem _ member))
              have tailClosed : ClosedEdges rest := fun edge member => narrowClosed edge (List.mem_cons_of_mem _ member)
              have coveredGrowth : Grows middle next := by simpa only [second, Result.state] using covered.growth
              cases answer with
              | false =>
                  have equal : accepted = false ∧ after = next := by
                    simpa only [allRows, first, Result.bind, second, Bool.false_eq_true, ↓reduceIte, Result.done.injEq, eq_comm] using done
                  rcases equal with ⟨rfl, rfl⟩
                  simp only [allRows, read_replay fuel wide state facts prepared wideInput wides middle later first
                    (grows_trans coveredGrowth growth), Result.bind,
                    anyCover_replay clear compare callback replay narrow wides middle middleFacts middlePrepared
                      narrowRow wideRows narrowRowClosed wideRowsClosed false _ later second growth,
                    Bool.false_eq_true, ↓reduceIte]
              | true =>
                  have tailDone : allRows fuel clear compare wide rest next = .done accepted after := by
                    simpa only [allRows, first, Result.bind, second, ↓reduceIte] using done
                  have tailVerified := allRows_verified fuel clear compare callback wide rest next nextFacts nextPrepared
                    nextWide nextNarrow wideClosed tailClosed
                  have tailGrowth : Grows next after := by simpa only [tailDone, Result.state] using tailVerified.growth
                  simp only [allRows, read_replay fuel wide state facts prepared wideInput wides middle later first
                    (grows_trans coveredGrowth (grows_trans tailGrowth growth)), Result.bind,
                    anyCover_replay clear compare callback replay narrow wides middle middleFacts middlePrepared
                      narrowRow wideRows narrowRowClosed wideRowsClosed true next later second (grows_trans tailGrowth growth),
                    ↓reduceIte]
                  exact ih next nextFacts nextPrepared nextWide nextNarrow tailClosed tailDone

/-- Every completed physical comparison replays its exact Boolean without effects in any later cache. -/
theorem check_replay [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Symbol]
    (clear : Guard → Bool) (fuel : Nat) (above : List (Nat × Nat)) (wide narrow : Value Symbol Guard)
    (state : State Symbol Guard) (facts : Facts state) (prepared : Prepared state)
    (wideInput : Available state wide) (narrowInput : Available state narrow)
    (wideClosed : wide.free = []) (narrowClosed : narrow.free = [])
    (accepted : Bool) (after later : State Symbol Guard)
    (done : check clear fuel above wide narrow state = .done accepted after) (growth : Grows after later) :
    check clear fuel above wide narrow later = .done accepted later := by
  rw [check] at done ⊢
  by_cases narrowEmpty : narrow.referenceOf = .empty
  · simp only [narrowEmpty, ↓reduceIte] at done ⊢; cases done; rfl
  simp only [narrowEmpty, ↓reduceIte] at done ⊢
  by_cases wideEmpty : wide.referenceOf = .empty
  · simp only [wideEmpty, ↓reduceIte] at done ⊢; cases done; rfl
  simp only [wideEmpty, ↓reduceIte] at done ⊢
  by_cases same : wide.referenceOf = narrow.referenceOf
  · simp only [same, ↓reduceIte] at done ⊢; cases done; rfl
  simp only [same, ↓reduceIte] at done ⊢
  cases wideFound : identity wide with
  | none => simp only [wideFound] at done; cases done
  | some wideId =>
      cases narrowFound : identity narrow with
      | none => simp only [wideFound, narrowFound] at done; cases done
      | some narrowId =>
          simp only [wideFound, narrowFound] at done ⊢
          by_cases visited : (wideId, narrowId) ∈ above
          · simp only [visited, ↓reduceIte] at done ⊢; cases done; rfl
          simp only [visited, ↓reduceIte] at done ⊢
          cases fuel with
          | zero => cases done
          | succ fuel =>
              have callback : Callback (check (Symbol := Symbol) clear fuel ((wideId, narrowId) :: above)) :=
                check_verified clear fuel ((wideId, narrowId) :: above)
              have replay : CallbackReplay (check (Symbol := Symbol) clear fuel ((wideId, narrowId) :: above)) :=
                fun left right current currentFacts currentPrepared leftInput rightInput leftClosed rightClosed
                  answer final view finished extended =>
                    check_replay clear fuel ((wideId, narrowId) :: above) left right current currentFacts currentPrepared
                      leftInput rightInput leftClosed rightClosed answer final view finished extended
              have reader := read_verified (fuel + 1) narrow state facts prepared narrowInput
              cases first : read (fuel + 1) narrow state with
              | failed fault middle => simp only [first, Result.bind, reduceCtorEq] at done
              | done narrows middle =>
                  have middleFacts : Facts middle := by simpa only [first, Result.state] using reader.facts
                  have middlePrepared : Prepared middle := by simpa only [first, Result.state] using prepared.preserve reader.unchanged
                  have middleWide : Available middle wide := by simpa only [first, Result.state] using reader.available _ wide wideInput
                  have narrowRows := read_edges (fuel + 1) narrow state facts prepared narrowInput narrows middle first
                  have narrowRowsClosed := read_closed (fuel + 1) narrow state facts prepared narrowInput narrowClosed narrows middle first
                  have tailDone : allRows (fuel + 1) clear (check clear fuel ((wideId, narrowId) :: above)) wide narrows middle =
                      .done accepted after := by simpa only [first, Result.bind] using done
                  have tailVerified := allRows_verified (fuel + 1) clear _ callback wide narrows middle middleFacts middlePrepared
                    middleWide narrowRows wideClosed narrowRowsClosed
                  have tailGrowth : Grows middle after := by simpa only [tailDone, Result.state] using tailVerified.growth
                  simp only [read_replay (fuel + 1) narrow state facts prepared narrowInput narrows middle later first
                    (grows_trans tailGrowth growth), Result.bind]
                  exact allRows_replay (fuel + 1) clear _ callback replay wide narrows middle middleFacts middlePrepared
                    middleWide narrowRows wideClosed narrowRowsClosed accepted after later tailDone growth
termination_by fuel

/-- One prepared observation of the actual final cache replays the whole comparison without effects. -/
theorem check_observation [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Symbol]
    (clear : Guard → Bool) (fuel : Nat) (above : List (Nat × Nat)) (wide narrow : Value Symbol Guard)
    (state : State Symbol Guard) (facts : Facts state) (prepared : Prepared state)
    (wideInput : Available state wide) (narrowInput : Available state narrow)
    (wideClosed : wide.free = []) (narrowClosed : narrow.free = [])
    (accepted : Bool) (after : State Symbol Guard)
    (done : check clear fuel above wide narrow state = .done accepted after) :
    ∃ outputs view, warmup (nodeInventory after) after = .done outputs view ∧
      Grows after view ∧ Facts view ∧ Prepared view ∧ Values view outputs ∧ Ready view outputs ∧
      Available view wide ∧ Available view narrow ∧
      check clear fuel above wide narrow view = .done accepted view := by
  have verified := check_verified clear fuel above wide narrow state facts prepared wideInput narrowInput wideClosed narrowClosed
  have afterFacts : Facts after := by simpa only [done, Result.state] using verified.facts
  have afterPrepared : Prepared after := by simpa only [done, Result.state] using prepared.preserve verified.unchanged
  have afterWide : Available after wide := by simpa only [done, Result.state] using verified.available _ wide wideInput
  have afterNarrow : Available after narrow := by simpa only [done, Result.state] using verified.available _ narrow narrowInput
  obtain ⟨outputs, view, warmed, viewFacts, growth, history, unchanged, retained, ready⟩ := prepare after afterFacts afterPrepared
  exact ⟨outputs, view, warmed, growth, viewFacts, afterPrepared.preserve unchanged, retained, ready,
    afterWide.grows after view growth history, afterNarrow.grows after view growth history,
    check_replay clear fuel above wide narrow state facts prepared wideInput narrowInput wideClosed narrowClosed
      accepted after view done growth⟩

end MicroCFTA.MergedComparisonReplay
