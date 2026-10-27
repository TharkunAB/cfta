import MicroCFTA.SourcePruningEnumerationProbeExposureArity
import MicroCFTA.SourceCurrentAllocatedMergePhysical

/-!
# Arity through actual comparison and child selection

Each successful stage retains its exact reached cache.
Its actual reads preserve arity from the initial edge-record heap.
The source keeps its actual comparison order and short circuits.
-/
namespace MicroCFTA.SourcePruningEnumerationSelectionArity
open InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values Edges)
open MergedColdReaderClosedInputs (ClosedValues ClosedEdges)
open SourceEqualityRequiredCache SourceEqualityRequiredSemanticCache
open MergedSourceComparison (Result identity children anyCover)
open MergedFreshOrdinaryComparison (check allRows)
open SourceMergedComparisonEffects (bind_done)
open SourcePruningEnumerationArityOrigins (Heap)
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
variable {Symbol : Type}
local notation "CostHeap" => InternedFreshOrdinaryCostHeap.Heap

/-- A successful stage retains actual cache effects and preserves physical edge arity. -/
structure Effect (before after : State Symbol Guard) : Prop where
  keeps : Keeps before after
  semantic : SemanticReady after
  costs : CostHeap after
  arity : Heap before → Heap after

/-- Annotation effects retain the previously proved source cache effects. -/
theorem Effect.original {before after : State Symbol Guard} (effect : Effect before after) :
    SourceMergedComparisonEffects.Effect before after := ⟨effect.keeps, effect.semantic⟩

/-- A direct Boolean return has no cache effects. -/
theorem pure_effect (before : State Symbol Guard) (semantic : SemanticReady before) (costs : CostHeap before) (answer result : Bool)
    (after : State Symbol Guard) (done : Result.done answer before = Result.done result after) : Effect before after := by
  have parts := Result.done.inj done
  cases parts.2
  exact ⟨pure_keeps _ semantic.ready, semantic, costs, fun heap => heap⟩

/-- Ordered successful effects compose semantic caches, histories, and arity preservation. -/
theorem Effect.trans {before middle after : State Symbol Guard} (first : Effect before middle) (second : Effect middle after) : Effect before after :=
  ⟨first.keeps.trans second.keeps, second.semantic, second.costs, fun heap => second.arity (first.arity heap)⟩

/-- A completed actual row read retains both heaps and returns resident rows. -/
theorem read_effect [DecidableEq (EdgeKey Symbol Guard)]
    (fuel : Nat) (value : Value Symbol Guard) (before : State Symbol Guard)
    (semantic : SemanticReady before) (costs : CostHeap before) (available : Available before value)
    (rows : List (EdgeValue Symbol Guard)) (after : State Symbol Guard)
    (done : MergedFreshOrdinaryExposure.read fuel value before = .done rows after) :
    Effect before after ∧ Edges after rows := by
  cases actual : MergedFreshOrdinaryExposure.nodeEdges fuel value before with
  | done edges final =>
      simp only [MergedFreshOrdinaryExposure.read, actual] at done
      have parts := Result.done.inj done
      cases parts.1; cases parts.2
      have checked := SourceEqualityExposureCosts.nodeEdges_verified fuel value before semantic costs available
      have kept : Keeps before after := by simpa only [actual, MergedSourceExposure.Result.state] using checked.keeps
      have ready : SemanticReady after := by simpa only [actual, MergedSourceExposure.Result.state] using checked.semantic
      have retained : CostHeap after := by simpa only [actual, MergedSourceExposure.Result.state] using checked.costs
      refine ⟨⟨kept, ready, retained, ?_⟩, checked.rows rows after actual⟩
      intro heap
      simpa only [actual, MergedSourceExposure.Result.state] using
        SourcePruningEnumerationProbeExposureArity.nodeEdges_heap fuel value before
          semantic.ready.semantic.1.normal.facts heap available
  | pending | unresolved | exhausted =>
      simp only [MergedFreshOrdinaryExposure.read, actual] at done
      cases done

/-- Callback effects use only actual available operands and their current heaps. -/
def Callback (compare : Value Symbol Guard → Value Symbol Guard → State Symbol Guard → Result Symbol Guard Bool) : Prop :=
  ∀ wide narrow before, SemanticReady before → CostHeap before → Available before wide → Available before narrow →
    ∀ answer after, compare wide narrow before = .done answer after → Effect before after

/-- The source zip conjunction preserves arity even when a list ends early. -/
theorem children_effect (compare : Value Symbol Guard → Value Symbol Guard → State Symbol Guard → Result Symbol Guard Bool)
    (callback : Callback compare) (wides narrows : List (Value Symbol Guard)) (before : State Symbol Guard) (semantic : SemanticReady before) (costs : CostHeap before)
    (wideInputs : Values before wides) (narrowInputs : Values before narrows)
    (answer : Bool) (after : State Symbol Guard) (done : children compare wides narrows before = .done answer after) : Effect before after := by
  induction wides generalizing narrows before with
  | nil => exact pure_effect before semantic costs true answer after done
  | cons wide wides ih =>
      cases narrows with
      | nil => exact pure_effect before semantic costs true answer after done
      | cons narrow narrows =>
          obtain ⟨accepted, middle, first, later⟩ := (bind_done _ _ answer after).mp done
          have effect := callback wide narrow before semantic costs (wideInputs _ List.mem_cons_self) (narrowInputs _ List.mem_cons_self) accepted middle first
          cases accepted with
          | false => exact effect.trans (pure_effect middle effect.semantic effect.costs false answer after later)
          | true => exact effect.trans (ih narrows middle effect.semantic effect.costs
              (fun value member => effect.keeps.available value (wideInputs value (List.mem_cons_of_mem _ member)))
              (fun value member => effect.keeps.available value (narrowInputs value (List.mem_cons_of_mem _ member))) later)

/-- Actual ordered edge-cover search retains semantic cache fields and physical arity. -/
theorem anyCover_effect [DecidableEq Symbol] (clear : Guard → Bool)
    (compare : Value Symbol Guard → Value Symbol Guard → State Symbol Guard → Result Symbol Guard Bool) (callback : Callback compare)
    (narrow : EdgeValue Symbol Guard) (wides : List (EdgeValue Symbol Guard)) (before : State Symbol Guard) (semantic : SemanticReady before) (costs : CostHeap before)
    (narrowInputs : Values before narrow.children) (wideInputs : Edges before wides)
    (answer : Bool) (after : State Symbol Guard) (done : anyCover clear compare narrow wides before = .done answer after) : Effect before after := by
  induction wides generalizing before with
  | nil => exact pure_effect before semantic costs false answer after done
  | cons wide wides ih =>
      rw [anyCover] at done
      split at done
      · obtain ⟨accepted, middle, first, later⟩ := (bind_done _ _ answer after).mp done
        have effect := children_effect compare callback wide.children narrow.children before semantic costs
          (semantic.ready.semantic.1.normal.facts.cached.edges wide.entry.key wide (wideInputs _ List.mem_cons_self)) narrowInputs accepted middle first
        cases accepted with
        | true => exact effect.trans (pure_effect middle effect.semantic effect.costs true answer after later)
        | false => exact effect.trans (ih middle effect.semantic effect.costs (fun value member => effect.keeps.available value (narrowInputs value member))
            (fun edge member => InternedEdgeResidency.edge_grows before middle effect.keeps.growth edge (wideInputs edge (List.mem_cons_of_mem _ member))) later)
      · exact ih before semantic costs narrowInputs (fun edge member => wideInputs edge (List.mem_cons_of_mem _ member)) done

/-- Each actual row read and cover search retains arity and the next input scope. -/
theorem allRows_effect [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] (fuel : Nat) (clear : Guard → Bool)
    (compare : Value Symbol Guard → Value Symbol Guard → State Symbol Guard → Result Symbol Guard Bool) (callback : Callback compare)
    (wide : Value Symbol Guard) (narrows : List (EdgeValue Symbol Guard)) (before : State Symbol Guard) (semantic : SemanticReady before) (costs : CostHeap before)
    (wideInput : Available before wide) (narrowInputs : Edges before narrows)
    (answer : Bool) (after : State Symbol Guard) (done : allRows fuel clear compare wide narrows before = .done answer after) : Effect before after := by
  induction narrows generalizing before with
  | nil => exact pure_effect before semantic costs true answer after done
  | cons narrow narrows ih =>
      obtain ⟨wides, readAfter, read, later⟩ := (bind_done _ _ answer after).mp done
      have readFacts := read_effect fuel wide before semantic costs wideInput wides readAfter read
      have childInputs := semantic.ready.semantic.1.normal.facts.cached.edges narrow.entry.key narrow (narrowInputs _ List.mem_cons_self)
      obtain ⟨accepted, middle, covered, rest⟩ := (bind_done _ _ answer after).mp later
      have coverFacts := anyCover_effect clear compare callback narrow wides readAfter readFacts.1.semantic readFacts.1.costs
        (fun value member => readFacts.1.keeps.available value (childInputs value member)) readFacts.2 accepted middle covered
      have first : Effect before middle := readFacts.1.trans coverFacts
      cases accepted with
      | false => exact first.trans (pure_effect middle first.semantic first.costs false answer after rest)
      | true => exact first.trans (ih middle first.semantic first.costs (first.keeps.available wide wideInput)
          (fun edge member => InternedEdgeResidency.edge_grows before middle first.keeps.growth edge (narrowInputs edge (List.mem_cons_of_mem _ member))) rest)

/-- Every completed structural comparison retains costs and arity on available open or closed operands. -/
theorem check_effect [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] (clear : Guard → Bool)
    (fuel : Nat) (above : List (Nat × Nat)) (wide narrow : Value Symbol Guard) (before : State Symbol Guard) (semantic : SemanticReady before) (costs : CostHeap before)
    (wideInput : Available before wide) (narrowInput : Available before narrow)
    (answer : Bool) (after : State Symbol Guard) (done : check clear fuel above wide narrow before = .done answer after) : Effect before after := by
  rw [check] at done
  split at done
  · exact pure_effect before semantic costs true answer after done
  · split at done
    · exact pure_effect before semantic costs false answer after done
    · split at done
      · exact pure_effect before semantic costs true answer after done
      · cases wideFound : identity wide with
        | none => simp only [wideFound] at done; cases done
        | some wideId =>
            cases narrowFound : identity narrow with
            | none => simp only [wideFound, narrowFound] at done; cases done
            | some narrowId =>
                simp only [wideFound, narrowFound] at done
                split at done
                · exact pure_effect before semantic costs true answer after done
                · cases fuel with
                  | zero => cases done
                  | succ fuel =>
                      obtain ⟨narrows, middle, read, later⟩ := (bind_done _ _ answer after).mp done
                      have readFacts := read_effect (fuel + 1) narrow before semantic costs narrowInput narrows middle read
                      have rest := allRows_effect (fuel + 1) clear (check clear fuel ((wideId, narrowId) :: above))
                        (check_effect clear fuel ((wideId, narrowId) :: above)) wide narrows middle readFacts.1.semantic readFacts.1.costs
                        (readFacts.1.keeps.available wide wideInput) readFacts.2 answer after later
                      exact readFacts.1.trans rest
termination_by fuel


open MergedPhysicalGroupColumns (closedMu)

/-- Every completed recursive-cover scan retains arity and actual cache histories. -/
theorem anyAccepts_effect [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] (clear : Guard → Bool) (fuel : Nat)
    (narrow : Value Symbol Guard) (wides : List (Value Symbol Guard)) (before : State Symbol Guard) (semantic : SemanticReady before) (costs : CostHeap before)
    (narrowInput : Available before narrow) (wideInputs : Values before wides)
    (answer : Bool) (after : State Symbol Guard) (done : SourceMergedSelection.anyAccepts clear fuel narrow wides before = .done answer after) : Effect before after := by
  induction wides generalizing before with
  | nil => exact pure_effect before semantic costs false answer after done
  | cons wide wides ih =>
      by_cases narrowClosed : narrow.free = []
      · simp only [SourceMergedSelection.anyAccepts, narrowClosed, ite_true] at done
        obtain ⟨accepted, middle, first, later⟩ := (bind_done _ _ answer after).mp done
        have effects := check_effect clear fuel [] wide narrow before semantic costs (wideInputs _ List.mem_cons_self) narrowInput accepted middle first
        cases accepted with
        | true => exact effects.trans (pure_effect middle effects.semantic effects.costs true answer after later)
        | false => exact effects.trans (ih middle effects.semantic effects.costs (effects.keeps.available narrow narrowInput)
            (fun value member => effects.keeps.available value (wideInputs value (List.mem_cons_of_mem _ member))) later)
      · simp only [SourceMergedSelection.anyAccepts, narrowClosed, ite_false] at done
        exact pure_effect before semantic costs false answer after done

/-- Successful actual filtering retains arity heaps, semantic heaps, and both histories. -/
theorem retain_effect [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] (clear : Guard → Bool) (fuel : Nat)
    (recursive inputs : List (Value Symbol Guard)) (before : State Symbol Guard) (semantic : SemanticReady before) (costs : CostHeap before)
    (recInputs : Values before recursive) (available : Values before inputs)
    (retained : List (Value Symbol Guard)) (after : State Symbol Guard)
    (done : SourceMergedSelection.retain clear fuel recursive inputs before = .done retained after) : Effect before after := by
  induction inputs generalizing before retained after with
  | nil =>
      have parts := Result.done.inj done
      cases parts.2
      exact ⟨pure_keeps _ semantic.ready, semantic, costs, fun heap => heap⟩
  | cons child inputs ih =>
      rw [SourceMergedSelection.retain] at done
      split at done
      · obtain ⟨rest, middle, tail, returned⟩ := (bind_done _ _ retained after).mp done
        have parts := Result.done.inj returned
        cases parts.2
        exact ih before semantic costs recInputs (fun value member => available value (List.mem_cons_of_mem _ member)) rest after tail
      · obtain ⟨covered, middle, first, later⟩ := (bind_done _ _ retained after).mp done
        have effects := anyAccepts_effect clear fuel child recursive before semantic costs (available _ List.mem_cons_self) recInputs covered middle first
        obtain ⟨rest, final, tail, returned⟩ := (bind_done _ _ retained after).mp later
        have parts := Result.done.inj returned
        cases parts.2
        exact effects.trans (ih middle effects.semantic effects.costs (fun value member => effects.keeps.available value (recInputs value member))
          (fun value member => effects.keeps.available value (available value (List.mem_cons_of_mem _ member))) rest after tail)

/-- The actual retention and identity filter preserve arity at the returned cache. -/
theorem select_effect [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (clear : Guard → Bool) (fuel : Nat) (inputs : List (Value Symbol Guard)) (before : State Symbol Guard)
    (semantic : SemanticReady before) (costs : CostHeap before) (available : Values before inputs)
    (retained : List (Value Symbol Guard)) (after : State Symbol Guard)
    (done : SourceMergedSelection.select clear fuel inputs before = .done retained after) : Effect before after := by
  obtain ⟨values, middle, filtered, returned⟩ := (bind_done _ _ retained after).mp done
  have checked := retain_effect clear fuel (inputs.filter closedMu) inputs before semantic costs
    (fun value member => available value (List.mem_filter.mp member).1) available values middle filtered
  have parts := Result.done.inj returned
  cases parts.2
  exact checked



end MicroCFTA.SourcePruningEnumerationSelectionArity
