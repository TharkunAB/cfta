import MicroCFTA.MergedComparisonColdMeasure

/-!
# Exact cache effects of ordered physical comparison

Every comparison stage preserves source facts and both histories. Each
changed cache warms an original recursive record. Successful edge reads
supply resident closed children to the ordered recursive comparisons.
-/
namespace MicroCFTA.MergedComparisonFacts
open Cache InternedConstructorTemplates InternedRecordCoherence InternedProbeProvenance
open InternedNestedFacts InternedNestedProvenance InternedEdgeResidency InternedShallowHeap
open MergedPhysicalWarmup MergedSourceComparison MergedComparisonWarmProgress
open MergedColdReaderClosedInputs

/-- An ordered physical result preserves source invariants and records its cold progress. -/
structure Verified [DecidableEq (EdgeKey Symbol Guard)] (before : State Symbol Guard) (result : Result Symbol Guard Output) : Prop where
  facts : Facts result.state
  growth : Grows before result.state
  history : Extends before.nodes.issued result.state.nodes.issued
  unchanged : NoNewMu before result.state
  progress : Progress before result.state

/-- Returning an answer preserves its current cache exactly. -/
theorem done_verified [DecidableEq (EdgeKey Symbol Guard)] (state : State Symbol Guard) (facts : Facts state) (value : Output) :
    Verified state (.done value state) :=
  ⟨facts, grows_refl _, extends_refl _, noNewMu_refl _, Or.inl rfl⟩

/-- An explicit source failure retains its exact current cache. -/
theorem failed_verified [DecidableEq (EdgeKey Symbol Guard)] (state : State Symbol Guard) (facts : Facts state) (fault : Fault) :
    Verified state (Result.failed (Output := Output) fault state) :=
  ⟨facts, grows_refl _, extends_refl _, noNewMu_refl _, Or.inl rfl⟩

/-- Completed stages compose all actual effects and preserve their first cold progress. -/
theorem bind_verified [DecidableEq (EdgeKey Symbol Guard)] (before : State Symbol Guard) (first : Result Symbol Guard First)
    (next : First → State Symbol Guard → Result Symbol Guard Output) (verified : Verified before first)
    (later : ∀ value after, first = .done value after → Verified after (next value after)) :
    Verified before (first.bind next) := by
  cases first with
  | failed fault after => exact ⟨verified.facts, verified.growth, verified.history, verified.unchanged, verified.progress⟩
  | done value after =>
      have continuation := later value after rfl
      exact ⟨continuation.facts, grows_trans verified.growth continuation.growth,
        extends_trans verified.history continuation.history, noNewMu_trans verified.unchanged continuation.unchanged,
        verified.progress.trans continuation.progress verified.facts.coherent.valid continuation.growth⟩

/-- An earlier physical input remains available after any verified comparison stage. -/
theorem Verified.available [DecidableEq (EdgeKey Symbol Guard)] (result : Result Symbol Guard Output) (verified : Verified state result)
    (value : Value Symbol Guard) (available : Available state value) : Available result.state value :=
  available.grows state result.state verified.growth verified.history

/-- Earlier edge records retain their residency after ordered comparison effects. -/
theorem Verified.edge [DecidableEq (EdgeKey Symbol Guard)] (result : Result Symbol Guard Output) (verified : Verified state result)
    (edge : EdgeValue Symbol Guard) (resident : EdgeResident state edge) : EdgeResident result.state edge :=
  edge_grows state result.state verified.growth edge resident

/-- Reader lifting retains the exact source state for every outcome. -/
theorem read_state [DecidableEq (EdgeKey Symbol Guard)] (fuel : Nat) (value : Value Symbol Guard) (state : State Symbol Guard) :
    (read fuel value state).state = (MergedSourceExposure.nodeEdges fuel value state).state := by
  unfold MergedSourceComparison.read
  cases MergedSourceExposure.nodeEdges fuel value state <;> rfl

/-- A successful lifted read is the exact successful physical edge read. -/
theorem read_done [DecidableEq (EdgeKey Symbol Guard)] (fuel : Nat) (value : Value Symbol Guard) (state : State Symbol Guard)
    (edges : List (EdgeValue Symbol Guard)) (after : State Symbol Guard) (done : read fuel value state = .done edges after) :
    MergedSourceExposure.nodeEdges fuel value state = .done edges after := by
  unfold MergedSourceComparison.read at done
  cases original : MergedSourceExposure.nodeEdges fuel value state <;> simp only [original] at done
  · cases done; rfl
  all_goals cases done

/-- Every lifted source read preserves facts and its exact cold progress. -/
theorem read_verified [DecidableEq (EdgeKey Symbol Guard)] (fuel : Nat) (value : Value Symbol Guard) (state : State Symbol Guard)
    (facts : Facts state) (prepared : Prepared state) (available : Available state value) : Verified state (read fuel value state) := by
  have source := MergedColdReaderFacts.nodeEdges_verified fuel value state facts prepared available
  exact ⟨by simpa only [read_state] using source.facts, by simpa only [read_state] using source.growth,
    by simpa only [read_state] using source.history, by simpa only [read_state] using source.unchanged,
    by simpa only [read_state] using nodeEdges_progress fuel value state facts prepared available⟩

/-- A successful lifted read supplies exact resident edge records. -/
theorem read_edges [DecidableEq (EdgeKey Symbol Guard)] (fuel : Nat) (value : Value Symbol Guard) (state : State Symbol Guard)
    (facts : Facts state) (prepared : Prepared state) (available : Available state value)
    (edges : List (EdgeValue Symbol Guard)) (after : State Symbol Guard) (done : read fuel value state = .done edges after) :
    Edges after edges :=
  (MergedColdReaderFacts.nodeEdges_verified fuel value state facts prepared available).edges edges after (read_done fuel value state edges after done)

/-- Any successful fuel bound for a closed read supplies closed children. -/
theorem read_closed [DecidableEq (EdgeKey Symbol Guard)] (fuel : Nat) (value : Value Symbol Guard) (state : State Symbol Guard)
    (facts : Facts state) (prepared : Prepared state) (available : Available state value) (closed : value.free = [])
    (edges : List (EdgeValue Symbol Guard)) (after : State Symbol Guard) (done : read fuel value state = .done edges after) :
    ClosedEdges edges := by
  have original := read_done fuel value state edges after done
  obtain ⟨bound, sourceEdges, final, sourceDone, children⟩ := MergedColdReaderClosed.nodeEdges_closed value state facts prepared available closed
  have first := (MergedColdReaderTermination.nodeEdges_stable fuel bound value state (by rw [original]; trivial)).trans original
  have second := (MergedColdReaderTermination.nodeEdges_stable bound fuel value state (by rw [sourceDone]; trivial)).trans sourceDone
  rw [Nat.add_comm bound fuel] at second
  have same := (MergedSourceExposure.Result.done.inj (first.symm.trans second)).1
  exact same ▸ children

/-- Recursive callbacks preserve source facts on available closed child pairs. -/
def Callback [DecidableEq (EdgeKey Symbol Guard)]
    (compare : Value Symbol Guard → Value Symbol Guard → State Symbol Guard → Result Symbol Guard Bool) : Prop :=
  ∀ wide narrow state, Facts state → Prepared state → Available state wide → Available state narrow →
    wide.free = [] → narrow.free = [] → Verified state (compare wide narrow state)

/-- Ordered child conjunction composes the exact effects of all demanded recursive comparisons. -/
theorem children_verified [DecidableEq (EdgeKey Symbol Guard)]
    (compare : Value Symbol Guard → Value Symbol Guard → State Symbol Guard → Result Symbol Guard Bool)
    (callback : Callback compare) (wides narrows : List (Value Symbol Guard)) (state : State Symbol Guard)
    (facts : Facts state) (prepared : Prepared state) (wideInputs : Values state wides) (narrowInputs : Values state narrows)
    (wideClosed : ClosedValues wides) (narrowClosed : ClosedValues narrows) :
    Verified state (children compare wides narrows state) := by
  induction wides generalizing narrows state with
  | nil => exact done_verified state facts true
  | cons wide wides ih =>
      cases narrows with
      | nil => exact done_verified state facts true
      | cons narrow narrows =>
          have checked := callback wide narrow state facts prepared (wideInputs wide List.mem_cons_self) (narrowInputs narrow List.mem_cons_self)
            (wideClosed wide List.mem_cons_self) (narrowClosed narrow List.mem_cons_self)
          apply bind_verified state _ _ checked
          intro accepted after done
          have afterFacts : Facts after := by simpa only [done, Result.state] using checked.facts
          have afterPrepared : Prepared after := by simpa only [done, Result.state] using prepared.preserve checked.unchanged
          cases accepted with
          | false => exact done_verified after afterFacts false
          | true =>
              exact ih narrows after afterFacts afterPrepared
                (fun value member => by simpa only [done, Result.state] using checked.available _ value (wideInputs value (List.mem_cons_of_mem _ member)))
                (fun value member => by simpa only [done, Result.state] using checked.available _ value (narrowInputs value (List.mem_cons_of_mem _ member)))
                (fun value member => wideClosed value (List.mem_cons_of_mem _ member))
                (fun value member => narrowClosed value (List.mem_cons_of_mem _ member))

/-- Ordered cover search preserves effects even when a candidate's recursive comparison fails. -/
theorem anyCover_verified [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Symbol] (clear : Guard → Bool)
    (compare : Value Symbol Guard → Value Symbol Guard → State Symbol Guard → Result Symbol Guard Bool)
    (callback : Callback compare) (narrow : EdgeValue Symbol Guard) (wides : List (EdgeValue Symbol Guard))
    (state : State Symbol Guard) (facts : Facts state) (prepared : Prepared state)
    (narrowInput : EdgeResident state narrow) (wideInputs : Edges state wides)
    (narrowClosed : ClosedValues narrow.children) (wideClosed : ClosedEdges wides) :
    Verified state (anyCover clear compare narrow wides state) := by
  induction wides generalizing state with
  | nil => exact done_verified state facts false
  | cons wide rest ih =>
      rw [anyCover]
      split
      · have checked := children_verified compare callback wide.children narrow.children state facts prepared
          (facts.cached.edges wide.entry.key wide (wideInputs wide List.mem_cons_self))
          (facts.cached.edges narrow.entry.key narrow narrowInput) (wideClosed wide List.mem_cons_self) narrowClosed
        apply bind_verified state _ _ checked
        intro accepted after done
        have afterFacts : Facts after := by simpa only [done, Result.state] using checked.facts
        have afterPrepared : Prepared after := by simpa only [done, Result.state] using prepared.preserve checked.unchanged
        cases accepted with
        | true => exact done_verified after afterFacts true
        | false =>
            exact ih after afterFacts afterPrepared (by simpa only [done, Result.state] using checked.edge _ narrow narrowInput)
              (fun edge member => by simpa only [done, Result.state] using checked.edge _ edge (wideInputs edge (List.mem_cons_of_mem _ member)))
              (fun edge member => wideClosed edge (List.mem_cons_of_mem _ member))
      · exact ih state facts prepared narrowInput (fun edge member => wideInputs edge (List.mem_cons_of_mem _ member))
          (fun edge member => wideClosed edge (List.mem_cons_of_mem _ member))

/-- Ordered narrow-row conjunction preserves the cache from every demanded read and failed cover. -/
theorem allRows_verified [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Symbol] (fuel : Nat) (clear : Guard → Bool)
    (compare : Value Symbol Guard → Value Symbol Guard → State Symbol Guard → Result Symbol Guard Bool)
    (callback : Callback compare) (wide : Value Symbol Guard) (narrows : List (EdgeValue Symbol Guard))
    (state : State Symbol Guard) (facts : Facts state) (prepared : Prepared state)
    (wideInput : Available state wide) (narrowInputs : Edges state narrows)
    (wideClosed : wide.free = []) (narrowClosed : ClosedEdges narrows) :
    Verified state (allRows fuel clear compare wide narrows state) := by
  induction narrows generalizing state with
  | nil => exact done_verified state facts true
  | cons narrow rest ih =>
      have reader := read_verified fuel wide state facts prepared wideInput
      apply bind_verified state _ _ reader
      intro wides middle readDone
      have middleFacts : Facts middle := by simpa only [readDone, Result.state] using reader.facts
      have middlePrepared : Prepared middle := by simpa only [readDone, Result.state] using prepared.preserve reader.unchanged
      have middleWide : Available middle wide := by simpa only [readDone, Result.state] using reader.available _ wide wideInput
      have middleNarrows : Edges middle (narrow :: rest) := by
        intro edge member
        simpa only [readDone, Result.state] using reader.edge _ edge (narrowInputs edge member)
      have checked := anyCover_verified clear compare callback narrow wides middle middleFacts middlePrepared
        (middleNarrows narrow List.mem_cons_self) (read_edges fuel wide state facts prepared wideInput wides middle readDone)
        (narrowClosed narrow List.mem_cons_self) (read_closed fuel wide state facts prepared wideInput wideClosed wides middle readDone)
      apply bind_verified middle _ _ checked
      intro accepted after done
      have afterFacts : Facts after := by simpa only [done, Result.state] using checked.facts
      have afterPrepared : Prepared after := by simpa only [done, Result.state] using middlePrepared.preserve checked.unchanged
      cases accepted with
      | false => exact done_verified after afterFacts false
      | true =>
          exact ih after afterFacts afterPrepared
            (by simpa only [done, Result.state] using checked.available _ wide middleWide)
            (fun edge member => by simpa only [done, Result.state] using checked.edge _ edge (middleNarrows edge (List.mem_cons_of_mem _ member)))
            (fun edge member => narrowClosed edge (List.mem_cons_of_mem _ member))

/-- The full fuelled physical comparator preserves cache facts and derives cold progress on closed inputs. -/
theorem check_verified [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Symbol] (clear : Guard → Bool)
    (fuel : Nat) (above : List (Nat × Nat)) (wide narrow : Value Symbol Guard) (state : State Symbol Guard)
    (facts : Facts state) (prepared : Prepared state) (wideInput : Available state wide) (narrowInput : Available state narrow)
    (wideClosed : wide.free = []) (narrowClosed : narrow.free = []) :
    Verified state (check clear fuel above wide narrow state) := by
  rw [check]
  split
  · exact done_verified state facts true
  · split
    · exact done_verified state facts false
    · split
      · exact done_verified state facts true
      · cases wideFound : identity wide with
        | none => exact failed_verified state facts _
        | some wideId =>
            cases narrowFound : identity narrow with
            | none => exact failed_verified state facts _
            | some narrowId =>
                dsimp only
                split
                · exact done_verified state facts true
                · cases fuel with
                  | zero => exact failed_verified state facts _
                  | succ fuel =>
                      have reader := read_verified (fuel + 1) narrow state facts prepared narrowInput
                      apply bind_verified state _ _ reader
                      intro narrows after done
                      have afterFacts : Facts after := by simpa only [done, Result.state] using reader.facts
                      have afterPrepared : Prepared after := by simpa only [done, Result.state] using prepared.preserve reader.unchanged
                      apply allRows_verified (fuel + 1) clear _ ?_ wide narrows after afterFacts afterPrepared
                        (by simpa only [done, Result.state] using reader.available _ wide wideInput)
                        (read_edges (fuel + 1) narrow state facts prepared narrowInput narrows after done) wideClosed
                        (read_closed (fuel + 1) narrow state facts prepared narrowInput narrowClosed narrows after done)
                      intro left right current currentFacts currentPrepared leftInput rightInput leftClosed rightClosed
                      exact check_verified clear fuel ((wideId, narrowId) :: above) left right current currentFacts currentPrepared
                        leftInput rightInput leftClosed rightClosed
termination_by fuel

end MicroCFTA.MergedComparisonFacts
