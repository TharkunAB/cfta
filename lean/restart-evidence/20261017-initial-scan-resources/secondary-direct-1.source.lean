import MicroCFTA.SourceCurrentPrimaryGateResources
import MicroCFTA.SourceCurrentClassGateCompletion

/-!
# Initial numeric resources for the current secondary gate

Actual open Mu prefixes use their decreasing free-occurrence rank. Each
ordinary row retains its original position and returned heap. The same
initial forecasts bound both the heap and the literal completed worker.
Inputs need no closedness, Cap, or desired output law.
-/
namespace MicroCFTA.SourceCurrentSecondaryGateResources
open Cache InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open InternedNestedConstruction (Outcome)
open SourceEqualityRequiredSemanticCache (SemanticReady)
open SourceCurrentMemoMergeResourceControl (Fits)
open SourceCurrentPrimaryGateResources
open SourceCurrentSecondaryTrace
open InternedFreshOrdinaryStatefulGate (child anyKnown)
open InternedFreeOccurrenceRank (rank)
open HeightOrderControlled (iterate)
open SourceCurrentAllocatedReaderControl (g)
local notation "CostHeap" => InternedFreshOrdinaryCostHeap.Heap
variable {Symbol Guard : Type} [DecidableEq (EdgeKey Symbol Guard)]

private def NodeControl (unconstrained : Value Symbol Guard → Bool) (path : List Nat)
    (value : Value Symbol Guard) (before : State Symbol Guard) (answer : Bool) (after : State Symbol Guard) : Prop :=
  SemanticReady before → CostHeap before → Available before value →
    ∀ height, path.length ≤ height → ∀ remaining bound, rank value < remaining → Fits bound before →
      Fits (ordinaryBound height (muPrefix remaining bound)) after ∧
        ∀ fuel, remaining + ordinaryFuel height (muPrefix remaining bound) ≤ fuel →
          nodeMeets unconstrained fuel path value before = .done (some answer) after

private def ChildControl (unconstrained : Value Symbol Guard → Bool) (values : List (Value Symbol Guard))
    (index : Nat) (path : List Nat) (before : State Symbol Guard) (answer : Bool) (after : State Symbol Guard) : Prop :=
  SemanticReady before → CostHeap before → Values before values → ∀ height, path.length ≤ height →
    ∀ bound, Fits bound before → Fits (nodeBound height bound) after ∧
      ∀ fuel, nodeFuel height bound ≤ fuel →
        child (nodeMeets unconstrained fuel) values index path before = .done (some answer) after

private def EdgesControl (unconstrained : Value Symbol Guard → Bool) (index : Nat) (path : List Nat)
    (edges : List (EdgeValue Symbol Guard)) (before : State Symbol Guard) (answer : Bool) (after : State Symbol Guard) : Prop :=
  SemanticReady before → CostHeap before →
    (∀ value ∈ edges.flatMap EdgeValue.children, Available before value) →
      ∀ height, path.length ≤ height → ∀ bound, Fits bound before →
        Fits (iterate (nodeBound height) edges.length bound) after ∧
          ∀ fuel, nodeFuel height (iterate (nodeBound height) edges.length bound) ≤ fuel →
            anyKnown (fun edge current => child (nodeMeets unconstrained fuel) edge.children index path current)
              edges before = .done (some answer) after

private theorem unfolded {value result : Value Symbol Guard} {before after : State Symbol Guard}
    (actual : InternedFreshOrdinaryStoredSubstitution.unfold value before = .done result after)
    (semantic : SemanticReady before) (costs : CostHeap before) (available : Available before value) :
    SemanticReady after ∧ CostHeap after ∧ Available after result := by
  obtain ⟨produced, heap, done, _, returned, resident, _⟩ :=
    SourceEqualityOpenOrdinaryHead.unfold_complete value before semantic available
  obtain ⟨rfl, rfl⟩ := Outcome.done.inj (done.symm.trans actual)
  have kept := InternedFreshOrdinaryStoredSubstitution.unfold_cost_heap value before
    semantic.ready.semantic.1 semantic.ready.semantic.2 costs available
  exact ⟨returned, by simpa only [actual, Outcome.state] using kept, resident⟩

private theorem node_control (unconstrained : Value Symbol Guard → Bool)
    {path : List Nat} {value : Value Symbol Guard} {before after : State Symbol Guard} {answer : Bool}
    (actual : NodeTrace unconstrained path value before answer after) :
    NodeControl unconstrained path value before answer after := by
  induction actual using NodeTrace.rec
      (motive_2 := fun values index path before answer after _ => ChildControl unconstrained values index path before answer after)
      (motive_3 := fun index path edges before answer after _ => EdgesControl unconstrained index path edges before answer after) with
  | empty =>
      intro _ _ _ height _ remaining bound _ fits
      refine ⟨fits.mono (Nat.le_trans (muPrefix_ge _ _) (ordinaryBound_ge _ _)), ?_⟩
      intro fuel enough
      cases fuel with
      | zero => have := ordinaryFuel_pos height (muPrefix remaining bound); omega
      | succ fuel => simp [nodeMeets, SourceCurrentMuEndpoint.nodeMeets, SourceCurrentMuEndpoint.dispatch, Value.depth, Value.free]
  | reference =>
      intro _ _ _ height _ remaining bound _ fits
      refine ⟨fits.mono (Nat.le_trans (muPrefix_ge _ _) (ordinaryBound_ge _ _)), ?_⟩
      intro fuel enough
      cases fuel with
      | zero => have := ordinaryFuel_pos height (muPrefix remaining bound); omega
      | succ fuel => simp [nodeMeets, SourceCurrentMuEndpoint.nodeMeets, SourceCurrentMuEndpoint.dispatch]
  | union =>
      intro _ _ _ height _ remaining bound _ fits
      refine ⟨fits.mono (Nat.le_trans (muPrefix_ge _ _) (ordinaryBound_ge _ _)), ?_⟩
      intro fuel enough
      cases fuel with
      | zero => have := ordinaryFuel_pos height (muPrefix remaining bound); omega
      | succ fuel => simp [nodeMeets, SourceCurrentMuEndpoint.nodeMeets, SourceCurrentMuEndpoint.dispatch]
  | finite fast =>
      intro _ _ _ height _ remaining bound _ fits
      refine ⟨fits.mono (Nat.le_trans (muPrefix_ge _ _) (ordinaryBound_ge _ _)), ?_⟩
      intro fuel enough
      cases fuel with
      | zero => have := ordinaryFuel_pos height (muPrefix remaining bound); omega
      | succ fuel => simp only [nodeMeets, SourceCurrentMuEndpoint.nodeMeets, SourceCurrentMuEndpoint.dispatch, Value.depth, Value.free, fast, ↓reduceIte]
  | endpoint slow =>
      intro _ _ _ height _ remaining bound _ fits
      refine ⟨fits.mono (Nat.le_trans (muPrefix_ge _ _) (ordinaryBound_ge _ _)), ?_⟩
      intro fuel enough
      cases fuel with
      | zero => have := ordinaryFuel_pos height (muPrefix remaining bound); omega
      | succ fuel => simp only [nodeMeets, SourceCurrentMuEndpoint.nodeMeets, SourceCurrentMuEndpoint.dispatch,
          Value.depth, Value.free, slow, Bool.false_and, Bool.or_false, Bool.false_eq_true, ↓reduceIte]
  | @branches entry edges depth free index rest before answer after slow trace ih =>
      intro semantic costs available height length remaining bound _ fits
      cases height with
      | zero => simp only [List.length_cons] at length; omega
      | succ height =>
          let start := muPrefix remaining bound
          have startFits : Fits start before := fits.mono (muPrefix_ge _ _)
          have rows := ih semantic costs (fun value member => available.children value member)
            height (by simp only [List.length_cons] at length; omega) start startFits
          have mass := InternedValueMassHeap.available before startFits.stored _ available
          have width := InternedStoredEncodingWidth.edges_length edges
          have count : edges.length ≤ start := by simp only [InternedValueMass.value] at mass; omega
          have pad : iterate (nodeBound height) edges.length start ≤ ordinaryBound (height + 1) start :=
            iterate_count_mono _ (nodeBound_ge height) count start
          refine ⟨rows.1.mono pad, ?_⟩
          intro fuel enough
          cases fuel with
          | zero => have := ordinaryFuel_pos (height + 1) start; omega
          | succ fuel =>
              have worker := rows.2 fuel (Nat.le_trans (nodeFuel_mono height pad) (by
                change remaining + (1 + nodeFuel height (ordinaryBound (height + 1) start)) ≤ fuel + 1 at enough
                omega))
              simpa only [nodeMeets, SourceCurrentMuEndpoint.nodeMeets, SourceCurrentMuEndpoint.dispatch,
                Value.depth, Value.free, slow, Bool.false_eq_true, ↓reduceIte] using worker
  | constrained blocked =>
      intro _ _ _ height _ remaining bound _ fits
      refine ⟨fits.mono (Nat.le_trans (muPrefix_ge _ _) (ordinaryBound_ge _ _)), ?_⟩
      intro fuel enough
      cases fuel with
      | zero => have := ordinaryFuel_pos height (muPrefix remaining bound); omega
      | succ fuel => exact constrained_result unconstrained fuel _ _ _ _ _ _ blocked
  | closed plain closed =>
      intro _ _ _ height _ remaining bound _ fits
      refine ⟨fits.mono (Nat.le_trans (muPrefix_ge _ _) (ordinaryBound_ge _ _)), ?_⟩
      intro fuel enough
      cases fuel with
      | zero => have := ordinaryFuel_pos height (muPrefix remaining bound); omega
      | succ fuel => simp [nodeMeets, SourceCurrentMuEndpoint.nodeMeets, SourceCurrentMuEndpoint.dispatch, Value.depth, plain, closed]
  | @unfold entry body depth ordinary before next middle path answer after plain opened actual trace ih =>
      intro semantic costs available height length remaining bound rankBound fits
      have progress := InternedFreshOrdinaryUnfoldRank.unfold_decreases entry body depth ordinary before
        semantic.ready.semantic.1 semantic.ready.semantic.2 costs available
        (by intro none; simp [none] at opened) next middle actual
      have effects := unfolded actual semantic costs available
      cases remaining with
      | zero => omega
      | succ remaining =>
          have nextFits := unfold_fits actual fits available
          have result := ih effects.1 effects.2.1 effects.2.2 height length remaining (g bound)
            (by omega) nextFits
          refine ⟨by simpa only [muPrefix_succ] using result.1, ?_⟩
          intro fuel enough
          cases fuel with
          | zero => omega
          | succ fuel =>
              have done := result.2 fuel (by rw [muPrefix_succ] at enough; omega)
              simpa [nodeMeets, SourceCurrentMuEndpoint.nodeMeets, SourceCurrentMuEndpoint.dispatch,
                Value.depth, plain, opened, actual, Outcome.bind] using done
  | missing absent =>
      intro _ _ _ height _ bound fits
      exact ⟨fits.mono (nodeBound_ge _ _), fun _ _ => by simp only [child, absent]⟩
  | present found trace ih =>
      intro semantic costs available height length bound fits
      have selected := available _ (List.mem_of_getElem? found)
      have result := ih semantic costs selected height length (bound + 1) bound (by have := rank_le fits selected; omega) fits
      refine ⟨by simpa only [nodeBound_eq, unfoldPrefix] using result.1, ?_⟩
      intro fuel enough
      have done := result.2 fuel (by simpa only [nodeFuel_eq, unfoldPrefix] using enough)
      simpa only [child, found] using done
  | nil =>
      intro _ _ _ height _ bound fits
      exact ⟨fits, fun _ _ => rfl⟩
  | @stop index path edge rest before after head ih =>
      intro semantic costs available height length bound fits
      have first := ih semantic costs (fun value member => available value (by simp [member])) height length bound fits
      have pad : nodeBound height bound ≤ iterate (nodeBound height) (edge :: rest).length bound := by
        simpa only [List.length_cons, iterate] using iterate_ge _ (nodeBound_ge height) rest.length (nodeBound height bound)
      refine ⟨first.1.mono pad, ?_⟩
      intro fuel enough
      have done := first.2 fuel (Nat.le_trans (nodeFuel_mono height (iterate_ge _ (nodeBound_ge height) _ _)) enough)
      simp only [anyKnown, done, Outcome.bind]
  | @next index path edge rest before middle answer after head tail headIH tailIH =>
      intro semantic costs available height length bound fits
      have first := headIH semantic costs (fun value member => available value (by simp [member])) height length bound fits
      have effects := SourceCurrentSecondaryEffects.child_effects (fun _ => True) unconstrained head semantic costs
        (fun value member => available value (by simp [member])) (by intro _ _ _; trivial)
      have last := tailIH effects.1 effects.2.2.1
        (fun value member => effects.2.1.available value (available value (by simp [member])))
        height length (nodeBound height bound) first.1
      refine ⟨last.1, ?_⟩
      intro fuel enough
      have grow : bound ≤ iterate (nodeBound height) rest.length (nodeBound height bound) :=
        Nat.le_trans (nodeBound_ge _ _) (iterate_ge _ (nodeBound_ge height) _ _)
      have firstDone := first.2 fuel (Nat.le_trans (nodeFuel_mono height grow) enough)
      have lastDone := last.2 fuel enough
      simp only [anyKnown, firstDone, Outcome.bind, lastDone]

/-- Every supplied actual node graph fits its original path and scalar forecasts. -/
theorem node (unconstrained : Value Symbol Guard → Bool)
    {path : List Nat} {value : Value Symbol Guard} {before after : State Symbol Guard} {answer : Bool}
    (actual : NodeTrace unconstrained path value before answer after)
    (semantic : SemanticReady before) (costs : CostHeap before) (available : Available before value)
    (bound : Nat) (fits : Fits bound before) :
    Fits (nodeBound path.length bound) after ∧
      ∀ fuel, nodeFuel path.length bound ≤ fuel → nodeMeets unconstrained fuel path value before = .done (some answer) after := by
  have result := node_control unconstrained actual semantic costs available path.length (Nat.le_refl _)
    (bound + 1) bound (by have := rank_le fits available; omega) fits
  exact ⟨by simpa only [nodeBound_eq, unfoldPrefix] using result.1,
    fun fuel enough => result.2 fuel (by simpa only [nodeFuel_eq, unfoldPrefix] using enough)⟩

/-- An actual forest path selects the original root and retains its exact return. -/
theorem path (unconstrained : Value Symbol Guard → Bool)
    {values : List (Value Symbol Guard)} {selected : List Nat} {before after : State Symbol Guard} {answer : Bool}
    (actual : PathTrace unconstrained values selected before answer after)
    (semantic : SemanticReady before) (costs : CostHeap before) (available : Values before values)
    (bound : Nat) (fits : Fits bound before) :
    Fits (pathBound selected bound) after ∧
      ∀ fuel, pathFuel selected bound ≤ fuel → meets unconstrained fuel values selected before = .done (some answer) after := by
  cases actual with
  | empty => exact ⟨fits, fun _ _ => rfl⟩
  | child selected =>
      cases selected with
      | missing absent => exact ⟨fits.mono (nodeBound_ge _ _), fun _ _ => by simp only [meets, SourceCurrentMuEndpoint.meets, child, absent]⟩
      | present found actual =>
          have result := node unconstrained actual semantic costs (available _ (List.mem_of_getElem? found)) bound fits
          exact ⟨result.1, fun fuel enough => by simpa only [meets, SourceCurrentMuEndpoint.meets, child, found] using result.2 fuel enough⟩

/-- Ordered actual classes use their original path list and no whole-forest closure. -/
theorem classes (unconstrained : Value Symbol Guard → Bool)
    {values : List (Value Symbol Guard)} {paths : List (List Nat)} {before after : State Symbol Guard} {answer : Bool}
    (actual : ClassTrace unconstrained values paths before answer after)
    (semantic : SemanticReady before) (costs : CostHeap before) (available : Values before values)
    (bound : Nat) (fits : Fits bound before) :
    Fits (classBound paths bound) after ∧
      ∀ fuel, classFuel paths bound ≤ fuel → classMeets unconstrained fuel values paths before = .done (some answer) after := by
  induction actual generalizing bound with
  | nil => exact ⟨fits, fun _ _ => rfl⟩
  | @stop selected rest before after head =>
      have first := path unconstrained head semantic costs available bound fits
      have pad := classBound_ge rest (pathBound selected bound)
      exact ⟨first.1.mono pad, fun fuel enough => by
        have done := first.2 fuel (Nat.le_trans (Nat.le_max_left _ _) enough)
        simp only [classMeets, SourceCurrentMuEndpoint.classMeets, anyKnown, done, Outcome.bind]⟩
  | @next selected rest before middle answer after head tail ih =>
      have first := path unconstrained head semantic costs available bound fits
      have effects := SourceCurrentSecondaryEffects.path_effects (fun _ => True) unconstrained head semantic costs available
        (by intro _ _ _; trivial)
      have remaining := ih effects.1 effects.2.2.1
        (fun value member => effects.2.1.available value (available value member)) (pathBound selected bound) first.1
      exact ⟨remaining.1, fun fuel enough => by
        have firstDone := first.2 fuel (Nat.le_trans (Nat.le_max_left _ _) enough)
        have restDone := remaining.2 fuel (Nat.le_trans (Nat.le_max_right _ _) enough)
        simp only [classMeets, SourceCurrentMuEndpoint.classMeets, anyKnown, firstDone, Outcome.bind, restDone]⟩

/-- Initial physical invariants construct their own exact secondary class return at the initial bounds. -/
theorem class_complete (unconstrained : Value Symbol Guard → Bool) (values : List (Value Symbol Guard))
    (paths : List (List Nat)) (before : State Symbol Guard) (semantic : SemanticReady before)
    (costs : CostHeap before) (available : Values before values) (bound : Nat) (fits : Fits bound before) :
    ∃ answer after, ClassTrace unconstrained values paths before answer after ∧
      SemanticReady after ∧ CostHeap after ∧ SourceEqualityRequiredCache.Keeps before after ∧ Values after values ∧
      Fits (classBound paths bound) after ∧
      ∀ fuel, classFuel paths bound ≤ fuel → classMeets unconstrained fuel values paths before = .done (some answer) after := by
  obtain ⟨_, answer, after, actual, returned, returnedCosts, kept, retained, _⟩ :=
    SourceCurrentClassGateCompletion.secondary_class_complete unconstrained (fun _ => false) values paths before semantic costs available
  have numeric := classes unconstrained actual semantic costs available bound fits
  exact ⟨answer, after, actual, returned, returnedCosts, kept, retained, numeric⟩

end MicroCFTA.SourceCurrentSecondaryGateResources
