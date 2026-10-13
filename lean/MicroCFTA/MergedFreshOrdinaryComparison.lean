import MicroCFTA.MergedFreshOrdinaryExposure
import MicroCFTA.MergedComparisonFacts

/-!
# Exact comparison correspondence after the constructor repair

The comparison uses repaired stored reconstruction for every demanded read.
Its ordered child and cover stages retain the original intermediate caches.
Closed available operands and prepared records make the full result identical.
-/
namespace MicroCFTA.MergedFreshOrdinaryComparison
open InternedConstructorTemplates InternedEdgeResidency
open InternedProbeProvenance (Available)
open InternedNestedFacts InternedNestedProvenance InternedShallowHeap
open MergedPhysicalWarmup MergedColdReaderClosedInputs
open MergedSourceComparison (Result identity children anyCover)
open MergedComparisonFacts (Callback Verified check_verified children_verified anyCover_verified read_verified read_edges read_closed)

/-- Each demanded narrow edge reads and searches the wide alternatives before the next narrow edge. -/
def allRows [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Symbol] (fuel : Nat) (clear : Guard → Bool)
    (compare : Value Symbol Guard → Value Symbol Guard → State Symbol Guard → Result Symbol Guard Bool)
    (wide : Value Symbol Guard) : List (EdgeValue Symbol Guard) → State Symbol Guard → Result Symbol Guard Bool
  | [], state => .done true state
  | narrow :: rest, state =>
      (MergedFreshOrdinaryExposure.read fuel wide state).bind fun wides afterRead =>
        (anyCover clear compare narrow wides afterRead).bind fun accepted after =>
          if accepted then allRows fuel clear compare wide rest after else .done false after

/-- Follow the complete source comparison branch order and actual ordered cache effects. -/
def check [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Symbol] (clear : Guard → Bool) :
    Nat → List (Nat × Nat) → Value Symbol Guard → Value Symbol Guard → State Symbol Guard → Result Symbol Guard Bool
  | fuel, above, wide, narrow, state =>
      if narrow.referenceOf = .empty then .done true state
      else if wide.referenceOf = .empty then .done false state
      else if wide.referenceOf = narrow.referenceOf then .done true state
      else match identity wide, identity narrow with
        | none, _ => .failed (.identity wide.referenceOf) state
        | _, none => .failed (.identity narrow.referenceOf) state
        | some wideId, some narrowId =>
            if (wideId, narrowId) ∈ above then .done true state
            else match fuel with
              | 0 => .failed .exhausted state
              | fuel + 1 =>
                  (MergedFreshOrdinaryExposure.read (fuel + 1) narrow state).bind fun narrows after =>
                    allRows (fuel + 1) clear (check clear fuel ((wideId, narrowId) :: above)) wide narrows after

/-- Two recursive callbacks agree at every prepared closed source call. -/
def Agree
    (first second : Value Symbol Guard → Value Symbol Guard → State Symbol Guard → Result Symbol Guard Bool) : Prop :=
  ∀ wide narrow state, Facts state → Prepared state → Available state wide → Available state narrow →
    wide.free = [] → narrow.free = [] → first wide narrow state = second wide narrow state

/-- Callback equality transfers every ordered child conjunction, including failure effects. -/
theorem children_eq [DecidableEq (EdgeKey Symbol Guard)]
    (first second : Value Symbol Guard → Value Symbol Guard → State Symbol Guard → Result Symbol Guard Bool)
    (checked : Callback second) (agree : Agree first second)
    (wides narrows : List (Value Symbol Guard)) (state : State Symbol Guard)
    (facts : Facts state) (prepared : Prepared state) (wideInputs : Values state wides) (narrowInputs : Values state narrows)
    (wideClosed : ClosedValues wides) (narrowClosed : ClosedValues narrows) :
    children first wides narrows state = children second wides narrows state := by
  induction wides generalizing narrows state with
  | nil => rfl
  | cons wide wides ih =>
      cases narrows with
      | nil => rfl
      | cons narrow narrows =>
          have valid := checked wide narrow state facts prepared (wideInputs wide List.mem_cons_self)
            (narrowInputs narrow List.mem_cons_self) (wideClosed wide List.mem_cons_self) (narrowClosed narrow List.mem_cons_self)
          simp only [children]
          rw [agree wide narrow state facts prepared (wideInputs wide List.mem_cons_self)
            (narrowInputs narrow List.mem_cons_self) (wideClosed wide List.mem_cons_self) (narrowClosed narrow List.mem_cons_self)]
          cases done : second wide narrow state with
          | failed => rfl
          | done accepted after =>
              have afterFacts : Facts after := by simpa only [done, Result.state] using valid.facts
              have afterPrepared : Prepared after := by simpa only [done, Result.state] using prepared.preserve valid.unchanged
              cases accepted with
              | false => rfl
              | true =>
                  exact ih narrows after afterFacts afterPrepared
                    (fun value member => by simpa only [done, Result.state] using valid.available _ value (wideInputs value (List.mem_cons_of_mem _ member)))
                    (fun value member => by simpa only [done, Result.state] using valid.available _ value (narrowInputs value (List.mem_cons_of_mem _ member)))
                    (fun value member => wideClosed value (List.mem_cons_of_mem _ member))
                    (fun value member => narrowClosed value (List.mem_cons_of_mem _ member))

/-- Ordered cover search retains every failed candidate's exact effects under callback equality. -/
theorem anyCover_eq [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Symbol] (clear : Guard → Bool)
    (first second : Value Symbol Guard → Value Symbol Guard → State Symbol Guard → Result Symbol Guard Bool)
    (checked : Callback second) (agree : Agree first second)
    (narrow : EdgeValue Symbol Guard) (wides : List (EdgeValue Symbol Guard)) (state : State Symbol Guard)
    (facts : Facts state) (prepared : Prepared state) (narrowInput : EdgeResident state narrow) (wideInputs : Edges state wides)
    (narrowClosed : ClosedValues narrow.children) (wideClosed : ClosedEdges wides) :
    anyCover clear first narrow wides state = anyCover clear second narrow wides state := by
  induction wides generalizing state with
  | nil => rfl
  | cons wide rest ih =>
      simp only [anyCover]
      split
      · have wideChildren := facts.cached.edges wide.entry.key wide (wideInputs wide List.mem_cons_self)
        have narrowChildren := facts.cached.edges narrow.entry.key narrow narrowInput
        have childClosed := wideClosed wide List.mem_cons_self
        have valid := children_verified second checked wide.children narrow.children state facts prepared
          wideChildren narrowChildren childClosed narrowClosed
        rw [children_eq first second checked agree wide.children narrow.children state facts prepared
          wideChildren narrowChildren childClosed narrowClosed]
        cases done : children second wide.children narrow.children state with
        | failed => rfl
        | done accepted after =>
            have afterFacts : Facts after := by simpa only [done, Result.state] using valid.facts
            have afterPrepared : Prepared after := by simpa only [done, Result.state] using prepared.preserve valid.unchanged
            cases accepted with
            | true => rfl
            | false =>
                exact ih after afterFacts afterPrepared
                  (by simpa only [done, Result.state] using valid.edge _ narrow narrowInput)
                  (fun edge member => by simpa only [done, Result.state] using valid.edge _ edge (wideInputs edge (List.mem_cons_of_mem _ member)))
                  (fun edge member => wideClosed edge (List.mem_cons_of_mem _ member))
      · exact ih state facts prepared narrowInput (fun edge member => wideInputs edge (List.mem_cons_of_mem _ member))
          (fun edge member => wideClosed edge (List.mem_cons_of_mem _ member))

/-- Repaired ordered row reads and equal child callbacks give exactly the old source result. -/
theorem allRows_eq [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Symbol] (fuel : Nat) (clear : Guard → Bool)
    (first second : Value Symbol Guard → Value Symbol Guard → State Symbol Guard → Result Symbol Guard Bool)
    (checked : Callback second) (agree : Agree first second) (wide : Value Symbol Guard)
    (narrows : List (EdgeValue Symbol Guard)) (state : State Symbol Guard)
    (facts : Facts state) (prepared : Prepared state) (wideInput : Available state wide) (narrowInputs : Edges state narrows)
    (wideClosed : wide.free = []) (narrowClosed : ClosedEdges narrows) :
    allRows fuel clear first wide narrows state = MergedSourceComparison.allRows fuel clear second wide narrows state := by
  induction narrows generalizing state with
  | nil => rfl
  | cons narrow rest ih =>
      simp only [allRows, MergedSourceComparison.allRows]
      rw [MergedFreshOrdinaryExposure.read_eq fuel wide state facts prepared wideInput]
      have reader := read_verified fuel wide state facts prepared wideInput
      cases readDone : MergedSourceComparison.read fuel wide state with
      | failed => rfl
      | done wides middle =>
          have middleFacts : Facts middle := by simpa only [readDone, Result.state] using reader.facts
          have middlePrepared : Prepared middle := by simpa only [readDone, Result.state] using prepared.preserve reader.unchanged
          have middleWide : Available middle wide := by simpa only [readDone, Result.state] using reader.available _ wide wideInput
          have middleNarrows : Edges middle (narrow :: rest) := by
            intro edge member
            simpa only [readDone, Result.state] using reader.edge _ edge (narrowInputs edge member)
          have middleWides := read_edges fuel wide state facts prepared wideInput wides middle readDone
          have closedWides := read_closed fuel wide state facts prepared wideInput wideClosed wides middle readDone
          have valid := anyCover_verified clear second checked narrow wides middle middleFacts middlePrepared
            (middleNarrows narrow List.mem_cons_self) middleWides (narrowClosed narrow List.mem_cons_self) closedWides
          simp only [Result.bind]
          rw [anyCover_eq clear first second checked agree narrow wides middle middleFacts middlePrepared
            (middleNarrows narrow List.mem_cons_self) middleWides (narrowClosed narrow List.mem_cons_self) closedWides]
          cases done : anyCover clear second narrow wides middle with
          | failed => rfl
          | done accepted after =>
              have afterFacts : Facts after := by simpa only [done, Result.state] using valid.facts
              have afterPrepared : Prepared after := by simpa only [done, Result.state] using middlePrepared.preserve valid.unchanged
              cases accepted with
              | false => rfl
              | true =>
                  exact ih after afterFacts afterPrepared
                    (by simpa only [done, Result.state] using valid.available _ wide middleWide)
                    (fun edge member => by simpa only [done, Result.state] using valid.edge _ edge (middleNarrows edge (List.mem_cons_of_mem _ member)))
                    (fun edge member => narrowClosed edge (List.mem_cons_of_mem _ member))

/-- One demanded narrow read and its complete cover sequence transfer before recursive induction. -/
theorem readRows_eq [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Symbol]
    (fuel : Nat) (clear : Guard → Bool)
    (first second : Value Symbol Guard → Value Symbol Guard → State Symbol Guard → Result Symbol Guard Bool)
    (checked : Callback second) (agree : Agree first second)
    (wide narrow : Value Symbol Guard) (state : State Symbol Guard)
    (facts : Facts state) (prepared : Prepared state) (wideInput : Available state wide) (narrowInput : Available state narrow)
    (wideClosed : wide.free = []) (narrowClosed : narrow.free = []) :
    ((MergedFreshOrdinaryExposure.read fuel narrow state).bind fun narrows after => allRows fuel clear first wide narrows after) =
      ((MergedSourceComparison.read fuel narrow state).bind fun narrows after => MergedSourceComparison.allRows fuel clear second wide narrows after) := by
  rw [MergedFreshOrdinaryExposure.read_eq fuel narrow state facts prepared narrowInput]
  have reader := read_verified fuel narrow state facts prepared narrowInput
  cases done : MergedSourceComparison.read fuel narrow state with
  | failed => rfl
  | done narrows after =>
      have afterFacts : Facts after := by simpa only [done, Result.state] using reader.facts
      have afterPrepared : Prepared after := by simpa only [done, Result.state] using prepared.preserve reader.unchanged
      exact allRows_eq fuel clear first second checked agree wide narrows after afterFacts afterPrepared
        (by simpa only [done, Result.state] using reader.available _ wide wideInput)
        (read_edges fuel narrow state facts prepared narrowInput narrows after done) wideClosed
        (read_closed fuel narrow state facts prepared narrowInput narrowClosed narrows after done)

/-- Every complete or failing comparison has its original answer and exact cache after the repair. -/
theorem check_eq [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Symbol] (clear : Guard → Bool)
    (fuel : Nat) (above : List (Nat × Nat)) (wide narrow : Value Symbol Guard) (state : State Symbol Guard)
    (facts : Facts state) (prepared : Prepared state) (wideInput : Available state wide) (narrowInput : Available state narrow)
    (wideClosed : wide.free = []) (narrowClosed : narrow.free = []) :
    check clear fuel above wide narrow state = MergedSourceComparison.check clear fuel above wide narrow state := by
  induction fuel generalizing above wide narrow state with
  | zero =>
      rw [check, MergedSourceComparison.check]
      split
      · rfl
      · split
        · rfl
        · split
          · rfl
          · cases wideFound : identity wide with
            | none => rfl
            | some wideId =>
                cases narrowFound : identity narrow with
                | none => rfl
                | some narrowId =>
                    dsimp only
  | succ fuel ih =>
      rw [check, MergedSourceComparison.check]
      split
      · rfl
      · split
        · rfl
        · split
          · rfl
          · cases wideFound : identity wide with
            | none => rfl
            | some wideId =>
                cases narrowFound : identity narrow with
                | none => rfl
                | some narrowId =>
                    dsimp only
                    split
                    · rfl
                    · exact readRows_eq (fuel + 1) clear
                        (check clear fuel ((wideId, narrowId) :: above))
                        (MergedSourceComparison.check clear fuel ((wideId, narrowId) :: above))
                        (fun left right current => check_verified clear fuel ((wideId, narrowId) :: above) left right current)
                        (fun left right current => ih ((wideId, narrowId) :: above) left right current)
                        wide narrow state facts prepared wideInput narrowInput wideClosed narrowClosed

end MicroCFTA.MergedFreshOrdinaryComparison
