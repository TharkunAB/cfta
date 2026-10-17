import MicroCFTA.SourceCurrentPrimaryGateResources
import MicroCFTA.SourceCurrentClassGateCompletion
import MicroCFTA.SourceCurrentAllocatedGateWorker

/-!
# Initial primary class resources and exact worker replay

The original path length controls ordinary child descent. At each path,
initial structural mass bounds all consecutive open Mu unfolds. Ordered
siblings receive the actual returned heap. Class completion constructs its
own graph from initial physical facts. Unrelated open siblings remain valid.
-/
namespace MicroCFTA.SourceCurrentPrimaryGateNumericReplay
open InternedConstructorTemplates InternedProbeProvenance EqualityNormalize
open InternedNestedConstruction (Outcome)
open InternedNestedProvenance (Values)
open EndpointStatefulGateTrace EndpointStatefulGate
open InternedFreshOrdinaryStatefulGate (anyKnown child)
open SourceEqualityRequiredSemanticCache (SemanticReady)
open SourceCurrentMemoMergeResourceControl (Fits)
open InternedFreeOccurrenceRank (rank)
open HeightOrderControlled (iterate)
open SourceCurrentPrimaryGateResources
local notation "CostHeap" => InternedFreshOrdinaryCostHeap.Heap
variable {Symbol Guard : Type} [DecidableEq (EdgeKey Symbol Guard)]

private def NodeSpec (unconstrained reaches : Value Symbol Guard → Bool) (height : Nat) : Prop :=
  ∀ {path : Path} {value : Value Symbol Guard} {before after : State Symbol Guard} {answer : Bool},
    NodeTrace unconstrained reaches path value before answer after → path.length ≤ height →
    SemanticReady before → CostHeap before → Available before value →
    ∀ bound, Fits bound before → Fits (nodeBound height bound) after ∧
      ∀ fuel, nodeFuel height bound ≤ fuel → nodeMeets unconstrained reaches fuel path value before = .done (some answer) after

private theorem child_resources (unconstrained reaches : Value Symbol Guard → Bool) (height : Nat)
    (node : NodeSpec unconstrained reaches height)
    {values : List (Value Symbol Guard)} {index : Nat} {path : Path} {before after : State Symbol Guard} {answer : Bool}
    (actual : ChildTrace unconstrained reaches values index path before answer after) (length : path.length ≤ height)
    (semantic : SemanticReady before) (costs : CostHeap before) (available : Values before values)
    (bound : Nat) (fits : Fits bound before) : Fits (nodeBound height bound) after ∧
      ∀ fuel, nodeFuel height bound ≤ fuel →
        child (nodeMeets unconstrained reaches fuel) values index path before = .done (some answer) after := by
  cases actual with
  | missing absent => exact ⟨fits.mono (nodeBound_ge _ _), fun _ _ => by simp only [child, absent]⟩
  | present found actual =>
      have checked := node actual length semantic costs (available _ (List.mem_of_getElem? found)) bound fits
      exact ⟨checked.1, fun fuel enough => by simpa only [child, found] using checked.2 fuel enough⟩

private theorem edges_resources (unconstrained reaches : Value Symbol Guard → Bool) (height : Nat)
    (node : NodeSpec unconstrained reaches height)
    {edges : List (EdgeValue Symbol Guard)} {index : Nat} {path : Path} {before after : State Symbol Guard} {answer : Bool}
    (actual : EdgesTrace unconstrained reaches index path edges before answer after) (length : path.length ≤ height)
    (semantic : SemanticReady before) (costs : CostHeap before)
    (available : Values before (edges.flatMap EdgeValue.children)) (bound : Nat) (fits : Fits bound before) :
    Fits (iterate (nodeBound height) edges.length bound) after ∧
      ∀ fuel, nodeFuel height (iterate (nodeBound height) edges.length bound) ≤ fuel →
        anyKnown (fun edge current => child (nodeMeets unconstrained reaches fuel) edge.children index path current)
          edges before = .done (some answer) after := by
  induction edges generalizing before after answer bound with
  | nil => cases actual; exact ⟨fits, fun _ _ => rfl⟩
  | cons edge edges ih =>
      have headAvailable : Values before edge.children :=
        fun value member => available value (List.mem_flatMap.mpr ⟨edge, List.mem_cons_self, member⟩)
      cases actual with
      | stop head =>
          have first := child_resources unconstrained reaches height node head length semantic costs headAvailable bound fits
          have padding := iterate_ge _ (nodeBound_ge height) edges.length (nodeBound height bound)
          exact ⟨first.1.mono padding, fun fuel enough => by
            simp only [anyKnown, first.2 fuel (Nat.le_trans (nodeFuel_mono height (Nat.le_trans (nodeBound_ge _ _) padding)) enough), Outcome.bind]⟩
      | next head tail =>
          have first := child_resources unconstrained reaches height node head length semantic costs headAvailable bound fits
          have effects := SourcePrimaryGateEffects.child_effects (fun _ => True) unconstrained reaches head
            semantic costs headAvailable (by intro _ _ _; trivial)
          have rest := ih tail effects.1 effects.2.2.1
            (fun value member => effects.2.1.available value (available value
              (List.mem_flatMap.mpr (by
                obtain ⟨row, present, child⟩ := List.mem_flatMap.mp member
                exact ⟨row, List.mem_cons_of_mem _ present, child⟩))))
            (nodeBound height bound) first.1
          have padded := iterate_ge _ (nodeBound_ge height) edges.length (nodeBound height bound)
          exact ⟨rest.1, fun fuel enough => by
            simp only [anyKnown, first.2 fuel (Nat.le_trans (nodeFuel_mono height (Nat.le_trans (nodeBound_ge _ _) padded)) enough),
              Outcome.bind, rest.2 fuel enough]⟩

private theorem stopped (unconstrained reaches : Value Symbol Guard → Bool)
    (height remaining bound : Nat) (path : Path) (value : Value Symbol Guard) (before : State Symbol Guard) (answer : Bool)
    (fits : Fits bound before) (done : nodeMeets unconstrained reaches 1 path value before = .done (some answer) before) :
    Fits (ordinaryBound height (muPrefix remaining bound)) before ∧
      ∀ fuel, remaining + ordinaryFuel height (muPrefix remaining bound) ≤ fuel →
        nodeMeets unconstrained reaches fuel path value before = .done (some answer) before := by
  refine ⟨fits.mono (Nat.le_trans (muPrefix_ge _ _) (ordinaryBound_ge _ _)), ?_⟩
  intro fuel enough
  have positive := ordinaryFuel_pos height (muPrefix remaining bound)
  have stable := fuel_stable unconstrained reaches 1 (fuel - 1) path value before answer before done
  simpa only [Nat.add_sub_of_le (by omega : 1 ≤ fuel)] using stable

private theorem node_spec (unconstrained reaches : Value Symbol Guard → Bool) (height : Nat) : NodeSpec unconstrained reaches height := by
  induction height using Nat.strongRecOn with
  | ind height outer =>
      have phase : ∀ remaining, ∀ {path : Path} {value : Value Symbol Guard} {before after : State Symbol Guard} {answer : Bool},
          NodeTrace unconstrained reaches path value before answer after → path.length ≤ height → rank value ≤ remaining →
          SemanticReady before → CostHeap before → Available before value → ∀ bound, Fits bound before →
          Fits (ordinaryBound height (muPrefix remaining bound)) after ∧
            ∀ fuel, remaining + ordinaryFuel height (muPrefix remaining bound) ≤ fuel →
              nodeMeets unconstrained reaches fuel path value before = .done (some answer) after := by
        intro remaining
        induction remaining with
        | zero =>
            intro path value before after answer actual length ranked semantic costs available bound fits
            cases actual with
            | empty => exact stopped unconstrained reaches height 0 bound _ _ _ _ fits (by simp [nodeMeets, dispatch, Value.depth, Value.free])
            | reference => exact stopped unconstrained reaches height 0 bound _ _ _ _ fits (by simp [nodeMeets, dispatch])
            | union => exact stopped unconstrained reaches height 0 bound _ _ _ _ fits (by simp [nodeMeets, dispatch])
            | finite fast => exact stopped unconstrained reaches height 0 bound _ _ _ _ fits (by simp [nodeMeets, dispatch, Value.depth, Value.free, fast])
            | endpoint slow => exact stopped unconstrained reaches height 0 bound _ _ _ _ fits (by simp [nodeMeets, dispatch, Value.depth, Value.free, slow])
            | constrained blocked => exact stopped unconstrained reaches height 0 bound _ _ _ _ fits (by simp [nodeMeets, dispatch, Value.depth, blocked])
            | closed plain closed => exact stopped unconstrained reaches height 0 bound _ _ _ _ fits (by simp [nodeMeets, dispatch, Value.depth, plain, closed])
            | branches slow rows =>
                cases height with
                | zero => simp only [List.length_cons] at length; omega
                | succ smaller =>
                    have checked := edges_resources unconstrained reaches smaller (outer smaller (by omega)) rows
                      (by simp only [List.length_cons] at length; omega) semantic costs
                      (fun child member => available.children child member) bound fits
                    have rowWidth := InternedStoredEncodingWidth.edges_length _
                    have mass := InternedValueMassHeap.available before fits.stored _ available
                    simp only [InternedValueMass.value] at mass
                    have below := iterate_count_mono _ (nodeBound_ge smaller) (by omega) bound
                    refine ⟨checked.1.mono below, ?_⟩
                    intro fuel enough
                    cases fuel with
                    | zero => have positive := ordinaryFuel_pos (smaller + 1) bound; simp only [muPrefix, iterate] at enough; omega
                    | succ fuel =>
                        have worker : nodeFuel smaller (iterate (nodeBound smaller) _ bound) ≤ fuel := by
                          have enough := enough
                          simp only [muPrefix, iterate, ordinaryFuel] at enough
                          exact Nat.le_trans (nodeFuel_mono smaller below) (by omega)
                        simpa only [nodeMeets, dispatch, Value.depth, Value.free, slow, Bool.false_eq_true, ite_false]
                          using checked.2 fuel worker
            | unfold plain opened actual rest =>
                have positive := InternedFreeOccurrenceRank.mu_positive _ _ _ _ before
                  semantic.ready.semantic.1.normal.facts.coherent available (by intro empty; simp [empty] at opened)
                omega
        | succ remaining ih =>
            intro path value before after answer actual length ranked semantic costs available bound fits
            cases actual with
            | unfold plain opened actual rest =>
                have smaller := InternedFreshOrdinaryUnfoldRank.unfold_decreases _ _ _ _ before
                  semantic.ready.semantic.1 semantic.ready.semantic.2 costs available
                  (by intro empty; simp [empty] at opened) _ _ actual
                obtain ⟨next, middle, done, kept, middleSemantic, nextAvailable, ordinary⟩ :=
                  SourceEqualityOpenOrdinaryHead.unfold_complete _ _ semantic available
                obtain ⟨sameValue, sameState⟩ := Outcome.done.inj (done.symm.trans actual)
                cases sameValue
                cases sameState
                have middleCosts := InternedFreshOrdinaryStoredSubstitution.unfold_cost_heap _ _
                  semantic.ready.semantic.1 semantic.ready.semantic.2 costs available
                have checked := ih rest length (by omega) middleSemantic
                  (by simpa only [actual, Outcome.state] using middleCosts) nextAvailable _ (unfold_fits actual fits available)
                refine ⟨checked.1, ?_⟩
                intro fuel enough
                have positive := ordinaryFuel_pos height (muPrefix (remaining + 1) bound)
                cases fuel with
                | zero => omega
                | succ fuel =>
                    have tail := checked.2 fuel (by simpa only [muPrefix_succ] using (show remaining + ordinaryFuel height (muPrefix (remaining + 1) bound) ≤ fuel by omega))
                    simpa only [nodeMeets, dispatch, Value.depth, plain, opened, Bool.not_true, Bool.false_eq_true, ite_false, actual, Outcome.bind]
                      using tail
            | empty => exact stopped unconstrained reaches height (remaining + 1) bound _ _ _ _ fits (by simp [nodeMeets, dispatch, Value.depth, Value.free])
            | reference => exact stopped unconstrained reaches height (remaining + 1) bound _ _ _ _ fits (by simp [nodeMeets, dispatch])
            | union => exact stopped unconstrained reaches height (remaining + 1) bound _ _ _ _ fits (by simp [nodeMeets, dispatch])
            | finite fast => exact stopped unconstrained reaches height (remaining + 1) bound _ _ _ _ fits (by simp [nodeMeets, dispatch, Value.depth, Value.free, fast])
            | endpoint slow => exact stopped unconstrained reaches height (remaining + 1) bound _ _ _ _ fits (by simp [nodeMeets, dispatch, Value.depth, Value.free, slow])
            | constrained blocked => exact stopped unconstrained reaches height (remaining + 1) bound _ _ _ _ fits (by simp [nodeMeets, dispatch, Value.depth, blocked])
            | closed plain closed => exact stopped unconstrained reaches height (remaining + 1) bound _ _ _ _ fits (by simp [nodeMeets, dispatch, Value.depth, plain, closed])
            | branches slow rows =>
                cases height with
                | zero => simp only [List.length_cons] at length; omega
                | succ smaller =>
                    have checked := edges_resources unconstrained reaches smaller (outer smaller (by omega)) rows
                      (by simp only [List.length_cons] at length; omega) semantic costs
                      (fun child member => available.children child member) bound fits
                    have rowWidth := InternedStoredEncodingWidth.edges_length _
                    have mass := InternedValueMassHeap.available before fits.stored _ available
                    simp only [InternedValueMass.value] at mass
                    have below := iterate_count_mono _ (nodeBound_ge smaller) (by omega) bound
                    have wider := ordinaryBound_mono (smaller + 1) (muPrefix_ge (remaining + 1) bound)
                    refine ⟨checked.1.mono (Nat.le_trans below wider), ?_⟩
                    intro fuel enough
                    have positive := ordinaryFuel_pos (smaller + 1) (muPrefix (remaining + 1) bound)
                    cases fuel with
                    | zero => omega
                    | succ fuel =>
                        have worker : nodeFuel smaller (iterate (nodeBound smaller) _ bound) ≤ fuel := by
                          have enough := enough
                          simp only [ordinaryFuel] at enough
                          exact Nat.le_trans (nodeFuel_mono smaller (Nat.le_trans below wider)) (by omega)
                        simpa only [nodeMeets, dispatch, Value.depth, Value.free, slow, Bool.false_eq_true, ite_false]
                          using checked.2 fuel worker
      intro path value before after answer actual length semantic costs available bound fits
      have checked := phase bound actual length (rank_le fits available) semantic costs available bound fits
      have wider := ordinaryBound_mono height (muPrefix_mono (Nat.le_succ bound) (Nat.le_refl bound))
      refine ⟨checked.1.mono wider, ?_⟩
      intro fuel enough
      apply checked.2 fuel
      rw [nodeFuel_eq] at enough
      have enoughPhase := ordinaryFuel_mono height (muPrefix_mono (Nat.le_succ bound) (Nat.le_refl bound))
      exact Nat.le_trans (Nat.add_le_add_left enoughPhase bound) (by simpa only [unfoldPrefix] using (show bound + ordinaryFuel height (unfoldPrefix bound) ≤ fuel by omega))

/-- Actual primary node graphs have initial resource bounds and independent larger-fuel replay. -/
theorem node (unconstrained reaches : Value Symbol Guard → Bool) (height : Nat)
    {path : Path} {value : Value Symbol Guard} {before after : State Symbol Guard} {answer : Bool}
    (actual : NodeTrace unconstrained reaches path value before answer after) (length : path.length ≤ height)
    (semantic : SemanticReady before) (costs : CostHeap before) (available : Available before value)
    (bound : Nat) (fits : Fits bound before) : Fits (nodeBound height bound) after ∧
      ∀ fuel, nodeFuel height bound ≤ fuel → nodeMeets unconstrained reaches fuel path value before = .done (some answer) after :=
  node_spec unconstrained reaches height actual length semantic costs available bound fits

end MicroCFTA.SourceCurrentPrimaryGateNumericReplay
