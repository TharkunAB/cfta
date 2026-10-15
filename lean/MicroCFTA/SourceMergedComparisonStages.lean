import MicroCFTA.SourceMergedComparisonBudget
import MicroCFTA.MergedComparisonCompletion

/-!
# Finite ordered stages of general repaired comparison

General cold reads supply stable exact bounds. Finite ordered child and
cover scans combine locally derived recursive bounds at their actual
returned caches. The degree budget retains all prefix progress.
-/
namespace MicroCFTA.SourceMergedComparisonStages
open InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values Edges)
open MergedColdReaderClosedInputs (ClosedValues ClosedEdges)
open SourceEqualityRequiredCache SourceEqualityRequiredSemanticCache
open SourceMergedComparisonEffects (read_graph)
open SourceMergedComparisonBudget
open MergedSourceComparison (Result children anyCover)
open MergedFreshOrdinaryComparison (allRows)
open MergedComparisonCompletion (EventuallyDone eventually_done eventually_bind)
open InternedMuDepthInventory (Bounded)
variable {Symbol Guard : Type} [DecidableEq (EdgeKey Symbol Guard)]

/-- Every actual general closed row read has a stable finite bound and identical final cache. -/
theorem read_eventually (value : Value Symbol Guard) (before : State Symbol Guard) (semantic : SemanticReady before)
    (available : Available before value) (closed : value.free = []) :
    EventuallyDone (fun fuel => MergedFreshOrdinaryExposure.read (fuel + 1) value before) := by
  obtain ⟨edges, after, trace, _⟩ := SourceEqualityProjectionRead.complete value before semantic available closed
  cases trace with
  | done bound actual =>
      refine ⟨bound, edges, after, ?_⟩
      intro fuel enough
      have stable := MergedFreshOrdinaryColdReplay.nodeEdges_stable bound (fuel + 1 - bound) value before (by rw [actual]; trivial)
      have same : bound + (fuel + 1 - bound) = fuel + 1 := by omega
      rw [same, actual] at stable
      simp only [MergedFreshOrdinaryExposure.read, stable]

/-- Recursive completion is local to caches reached by actual prefixes from one original cache. -/
def CompleteCallback (limit : Nat) (before : State Symbol Guard)
    (compare : Nat → Value Symbol Guard → Value Symbol Guard → State Symbol Guard → Result Symbol Guard Bool) : Prop :=
  ∀ wide narrow state, SemanticReady state → Bounded state limit → Available state wide → Available state narrow →
    wide.free = [] → narrow.free = [] → Budget limit before state → EventuallyDone (fun fuel => compare fuel wide narrow state)

/-- A finite ordered child conjunction combines all demanded stable local bounds. -/
theorem children_eventually (limit : Nat) (before : State Symbol Guard)
    (compare : Nat → Value Symbol Guard → Value Symbol Guard → State Symbol Guard → Result Symbol Guard Bool)
    (callbacks : ∀ fuel, Callback limit (compare fuel)) (complete : CompleteCallback limit before compare)
    (wides narrows : List (Value Symbol Guard)) (state : State Symbol Guard) (semantic : SemanticReady state) (bounded : Bounded state limit)
    (wideInputs : Values state wides) (narrowInputs : Values state narrows) (wideClosed : ClosedValues wides) (narrowClosed : ClosedValues narrows)
    (reached : Budget limit before state) : EventuallyDone (fun fuel => children (compare fuel) wides narrows state) := by
  induction wides generalizing narrows state with
  | nil => exact eventually_done true state
  | cons wide wides ih =>
      cases narrows with
      | nil => exact eventually_done true state
      | cons narrow narrows =>
          apply eventually_bind
          · exact complete wide narrow state semantic bounded (wideInputs _ List.mem_cons_self) (narrowInputs _ List.mem_cons_self)
              (wideClosed _ List.mem_cons_self) (narrowClosed _ List.mem_cons_self) reached
          · intro fuel accepted after done
            have checked := callbacks fuel wide narrow state semantic bounded (wideInputs _ List.mem_cons_self) (narrowInputs _ List.mem_cons_self)
              (wideClosed _ List.mem_cons_self) (narrowClosed _ List.mem_cons_self) accepted after done
            cases accepted with
            | false => exact eventually_done false after
            | true =>
                exact ih narrows after checked.effect.2 checked.bounded
                  (fun value member => checked.effect.1.available value (wideInputs value (List.mem_cons_of_mem _ member)))
                  (fun value member => checked.effect.1.available value (narrowInputs value (List.mem_cons_of_mem _ member)))
                  (fun value member => wideClosed value (List.mem_cons_of_mem _ member))
                  (fun value member => narrowClosed value (List.mem_cons_of_mem _ member)) (reached.trans checked)

/-- A finite cover search combines bounds while retaining every actual failed candidate's effects. -/
theorem anyCover_eventually [DecidableEq Symbol] (limit : Nat) (before : State Symbol Guard) (clear : Guard → Bool)
    (compare : Nat → Value Symbol Guard → Value Symbol Guard → State Symbol Guard → Result Symbol Guard Bool)
    (callbacks : ∀ fuel, Callback limit (compare fuel)) (complete : CompleteCallback limit before compare)
    (narrow : EdgeValue Symbol Guard) (wides : List (EdgeValue Symbol Guard)) (state : State Symbol Guard)
    (semantic : SemanticReady state) (bounded : Bounded state limit)
    (narrowInput : Values state narrow.children) (wideInputs : Edges state wides)
    (narrowClosed : ClosedValues narrow.children) (wideClosed : ClosedEdges wides) (reached : Budget limit before state) :
    EventuallyDone (fun fuel => anyCover clear (compare fuel) narrow wides state) := by
  induction wides generalizing state with
  | nil => exact eventually_done false state
  | cons wide wides ih =>
      by_cases header : wide.entry.key.symbol = narrow.entry.key.symbol ∧ wide.children.length = narrow.children.length ∧ clear wide.entry.key.constraint = true
      · simp only [anyCover, ite_eq_left header]
        apply eventually_bind
        · exact children_eventually limit before compare callbacks complete wide.children narrow.children state semantic bounded
            (semantic.ready.semantic.1.normal.facts.cached.edges wide.entry.key wide (wideInputs _ List.mem_cons_self)) narrowInput
            (wideClosed _ List.mem_cons_self) narrowClosed reached
        · intro fuel accepted after done
          have checked := children_budget limit (compare fuel) (callbacks fuel) wide.children narrow.children state semantic bounded
            (semantic.ready.semantic.1.normal.facts.cached.edges wide.entry.key wide (wideInputs _ List.mem_cons_self)) narrowInput
            (wideClosed _ List.mem_cons_self) narrowClosed accepted after done
          cases accepted with
          | true => exact eventually_done true after
          | false =>
              exact ih after checked.effect.2 checked.bounded
                (fun value member => checked.effect.1.available value (narrowInput value member))
                (fun edge member => InternedEdgeResidency.edge_grows state after checked.effect.1.growth edge (wideInputs edge (List.mem_cons_of_mem _ member)))
                (fun edge member => wideClosed edge (List.mem_cons_of_mem _ member)) (reached.trans checked)
      · simpa only [anyCover, ite_eq_right header] using ih state semantic bounded narrowInput
          (fun edge member => wideInputs edge (List.mem_cons_of_mem _ member))
          (fun edge member => wideClosed edge (List.mem_cons_of_mem _ member)) reached

/-- Every demanded row completes after its actual stable read and complete finite cover search. -/
theorem allRows_eventually [DecidableEq Symbol] (limit : Nat) (before : State Symbol Guard) (clear : Guard → Bool)
    (compare : Nat → Value Symbol Guard → Value Symbol Guard → State Symbol Guard → Result Symbol Guard Bool)
    (callbacks : ∀ fuel, Callback limit (compare fuel)) (complete : CompleteCallback limit before compare)
    (wide : Value Symbol Guard) (narrows : List (EdgeValue Symbol Guard)) (state : State Symbol Guard)
    (semantic : SemanticReady state) (bounded : Bounded state limit)
    (wideInput : Available state wide) (narrowInputs : Edges state narrows) (wideClosed : wide.free = []) (narrowClosed : ClosedEdges narrows)
    (reached : Budget limit before state) : EventuallyDone (fun fuel => allRows (fuel + 1) clear (compare fuel) wide narrows state) := by
  induction narrows generalizing state with
  | nil => exact eventually_done true state
  | cons narrow narrows ih =>
      apply eventually_bind
      · exact read_eventually wide state semantic wideInput wideClosed
      · intro fuel wides middle readDone
        have readFacts := (read_graph (fuel + 1) wide state wides middle readDone).verified semantic wideInput wideClosed
        have readBudget := read_budget limit (fuel + 1) wide state semantic bounded wideInput wideClosed wides middle readDone
        have middleNarrow : Values middle narrow.children := fun value member => readFacts.1.available value
          (semantic.ready.semantic.1.normal.facts.cached.edges narrow.entry.key narrow (narrowInputs _ List.mem_cons_self) value member)
        apply eventually_bind
        · exact anyCover_eventually limit before clear compare callbacks complete narrow wides middle readFacts.2.1 readBudget.bounded
            middleNarrow readFacts.2.2.1 (narrowClosed _ List.mem_cons_self) readFacts.2.2.2 (reached.trans readBudget)
        · intro bound accepted after done
          have checked := anyCover_budget limit clear (compare bound) (callbacks bound) narrow wides middle readFacts.2.1 readBudget.bounded
            middleNarrow readFacts.2.2.1 (narrowClosed _ List.mem_cons_self) readFacts.2.2.2 accepted after done
          have stages :=  readBudget.trans checked
          cases accepted with
          | false => exact eventually_done false after
          | true =>
              exact ih after checked.effect.2 checked.bounded (stages.effect.1.available wide wideInput)
                (fun edge member => InternedEdgeResidency.edge_grows state after stages.effect.1.growth edge (narrowInputs edge (List.mem_cons_of_mem _ member)))
                (fun edge member => narrowClosed edge (List.mem_cons_of_mem _ member)) (reached.trans stages)

end MicroCFTA.SourceMergedComparisonStages
