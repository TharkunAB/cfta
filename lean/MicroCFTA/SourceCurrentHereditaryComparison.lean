import MicroCFTA.SourceCurrentHereditaryExposure
import MicroCFTA.SourceCurrentMergedHeapEffects

/-!
# Local hereditary certificates through actual comparison reads

Each completed comparison uses annotations on its actual operands. The proof
retains the conditional Mu store at every successful bind. Other resident
edge guards remain unrestricted. This module does not assert completion.
-/
namespace MicroCFTA.SourceCurrentHereditaryComparison
open InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values Edges)
open MergedColdReaderClosedInputs (ClosedValues ClosedEdges)
open SourceEqualityRequiredCache SourceEqualityRequiredSemanticCache
open SourceEqualityAnnotationLanguage
open SourceCurrentHereditaryConstruction (MuStored)
open SourceCurrentHereditaryConstructors (Edge)
open MergedSourceComparison (Result identity)
open SourceMergedComparisonEffects (bind_done read_graph)
local notation "CostHeap" => InternedFreshOrdinaryCostHeap.Heap

/-- A completed comparison retains its exact physical state and causal Mu certificates. -/
structure Effect (valid : Guard → Prop) (before after : State Symbol Guard) : Prop where
  /-- Both constructor histories and closed-read readiness are retained. -/
  keeps : Keeps before after
  /-- The actual returned cache retains semantic probe invariants. -/
  semantic : SemanticReady after
  /-- Stored unfolding costs remain valid. -/
  costs : CostHeap after
  /-- Every completed Mu retains its conditional probe-to-body certificate. -/
  stored : MuStored valid after

/-- Successful ordered stages compose at the literal intermediate state. -/
theorem Effect.trans {valid : Guard → Prop} {before middle after : State Symbol Guard}
    (first : Effect valid before middle) (last : Effect valid middle after) : Effect valid before after :=
  ⟨first.keeps.trans last.keeps, last.semantic, last.costs, last.stored⟩

private theorem pure_effect (valid : Guard → Prop) (before : State Symbol Guard)
    (semantic : SemanticReady before) (costs : CostHeap before) (stored : MuStored valid before)
    (answer result : Bool) (after : State Symbol Guard) (done : Result.done answer before = Result.done result after) :
    Effect valid before after := by
  obtain ⟨_, rfl⟩ := Result.done.inj done
  exact ⟨pure_keeps _ semantic.ready, semantic, costs, stored⟩

/-- An actual row read retains the local certificate and returns annotated resident rows. -/
theorem read [DecidableEq (EdgeKey Symbol Guard)] (valid : Guard → Prop)
    {value : Value Symbol Guard} {before after : State Symbol Guard} {edges : List (EdgeValue Symbol Guard)}
    (actual : SourceEqualityProjectionRead.Read value before edges after)
    (semantic : SemanticReady before) (costs : CostHeap before) (available : Available before value)
    (closed : value.free = []) (annotated : Annotated valid value) (stored : MuStored valid before) :
    Effect valid before after ∧ Edges after edges ∧ ClosedEdges edges ∧ ∀ edge ∈ edges, Edge valid edge := by
  have physical := actual.verified semantic available closed
  cases actual with
  | done fuel completed =>
      have localRows := SourceCurrentHereditaryExposure.nodeEdges valid fuel value before semantic.ready.semantic
        semantic.ready.covered available closed annotated stored edges after completed
      have weighted := SourceEqualityExposureCosts.nodeEdges_verified fuel value before semantic costs available
      exact ⟨⟨physical.1, physical.2.1, by simpa only [completed, MergedSourceExposure.Result.state] using weighted.costs,
        localRows.1⟩, physical.2.2.1, physical.2.2.2, localRows.2⟩

private def Callback (valid : Guard → Prop)
    (compare : Value Symbol Guard → Value Symbol Guard → State Symbol Guard → Result Symbol Guard Bool) : Prop :=
  ∀ wide narrow before, SemanticReady before → CostHeap before → Available before wide → Available before narrow →
    wide.free = [] → narrow.free = [] → Annotated valid wide → Annotated valid narrow → MuStored valid before →
    ∀ answer after, compare wide narrow before = .done answer after → Effect valid before after

private theorem children_effect (valid : Guard → Prop)
    (compare : Value Symbol Guard → Value Symbol Guard → State Symbol Guard → Result Symbol Guard Bool)
    (callback : Callback valid compare) (wides narrows : List (Value Symbol Guard))
    (before : State Symbol Guard) (semantic : SemanticReady before) (costs : CostHeap before)
    (wideInputs : Values before wides) (narrowInputs : Values before narrows)
    (wideClosed : ClosedValues wides) (narrowClosed : ClosedValues narrows)
    (wideAnnotations : ∀ value ∈ wides, Annotated valid value) (narrowAnnotations : ∀ value ∈ narrows, Annotated valid value)
    (stored : MuStored valid before) (answer : Bool) (after : State Symbol Guard)
    (done : MergedSourceComparison.children compare wides narrows before = .done answer after) : Effect valid before after := by
  induction wides generalizing narrows before with
  | nil => exact pure_effect valid before semantic costs stored true answer after done
  | cons wide wides ih =>
      cases narrows with
      | nil => exact pure_effect valid before semantic costs stored true answer after done
      | cons narrow narrows =>
          obtain ⟨accepted, middle, first, later⟩ := (bind_done _ _ answer after).mp done
          have effect := callback wide narrow before semantic costs (wideInputs _ List.mem_cons_self)
            (narrowInputs _ List.mem_cons_self) (wideClosed _ List.mem_cons_self) (narrowClosed _ List.mem_cons_self)
            (wideAnnotations _ List.mem_cons_self) (narrowAnnotations _ List.mem_cons_self) stored accepted middle first
          cases accepted with
          | false => exact effect.trans (pure_effect valid middle effect.semantic effect.costs effect.stored false answer after later)
          | true => exact effect.trans (ih narrows middle effect.semantic effect.costs
              (fun value member => effect.keeps.available value (wideInputs value (List.mem_cons_of_mem _ member)))
              (fun value member => effect.keeps.available value (narrowInputs value (List.mem_cons_of_mem _ member)))
              (fun value member => wideClosed value (List.mem_cons_of_mem _ member))
              (fun value member => narrowClosed value (List.mem_cons_of_mem _ member))
              (fun value member => wideAnnotations value (List.mem_cons_of_mem _ member))
              (fun value member => narrowAnnotations value (List.mem_cons_of_mem _ member)) effect.stored later)

private theorem anyCover_effect (valid : Guard → Prop) [DecidableEq Symbol] (clear : Guard → Bool)
    (compare : Value Symbol Guard → Value Symbol Guard → State Symbol Guard → Result Symbol Guard Bool)
    (callback : Callback valid compare) (narrow : EdgeValue Symbol Guard) (wides : List (EdgeValue Symbol Guard))
    (before : State Symbol Guard) (semantic : SemanticReady before) (costs : CostHeap before)
    (narrowInputs : Values before narrow.children) (wideInputs : Edges before wides)
    (narrowClosed : ClosedValues narrow.children) (wideClosed : ClosedEdges wides)
    (narrowAnnotations : Edge valid narrow) (wideAnnotations : ∀ edge ∈ wides, Edge valid edge)
    (stored : MuStored valid before) (answer : Bool) (after : State Symbol Guard)
    (done : MergedSourceComparison.anyCover clear compare narrow wides before = .done answer after) : Effect valid before after := by
  induction wides generalizing before with
  | nil => exact pure_effect valid before semantic costs stored false answer after done
  | cons wide wides ih =>
      rw [MergedSourceComparison.anyCover] at done
      split at done
      · obtain ⟨accepted, middle, first, later⟩ := (bind_done _ _ answer after).mp done
        have effect := children_effect valid compare callback wide.children narrow.children before semantic costs
          (semantic.ready.semantic.1.normal.facts.cached.edges wide.entry.key wide (wideInputs _ List.mem_cons_self)) narrowInputs
          (wideClosed _ List.mem_cons_self) narrowClosed (wideAnnotations _ List.mem_cons_self).2 narrowAnnotations.2
          stored accepted middle first
        cases accepted with
        | true => exact effect.trans (pure_effect valid middle effect.semantic effect.costs effect.stored true answer after later)
        | false => exact effect.trans (ih middle effect.semantic effect.costs
            (fun value member => effect.keeps.available value (narrowInputs value member))
            (fun edge member => InternedEdgeResidency.edge_grows before middle effect.keeps.growth edge
              (wideInputs edge (List.mem_cons_of_mem _ member)))
            (fun edge member => wideClosed edge (List.mem_cons_of_mem _ member))
            (fun edge member => wideAnnotations edge (List.mem_cons_of_mem _ member)) effect.stored later)
      · exact ih before semantic costs narrowInputs (fun edge member => wideInputs edge (List.mem_cons_of_mem _ member))
          (fun edge member => wideClosed edge (List.mem_cons_of_mem _ member))
          (fun edge member => wideAnnotations edge (List.mem_cons_of_mem _ member)) stored done

private theorem allRows_effect (valid : Guard → Prop) [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (readFuel : Nat) (clear : Guard → Bool)
    (compare : Value Symbol Guard → Value Symbol Guard → State Symbol Guard → Result Symbol Guard Bool)
    (callback : Callback valid compare) (wide : Value Symbol Guard) (narrows : List (EdgeValue Symbol Guard))
    (before : State Symbol Guard) (semantic : SemanticReady before) (costs : CostHeap before)
    (wideInput : Available before wide) (narrowInputs : Edges before narrows)
    (wideClosed : wide.free = []) (narrowClosed : ClosedEdges narrows)
    (wideAnnotation : Annotated valid wide) (narrowAnnotations : ∀ edge ∈ narrows, Edge valid edge)
    (stored : MuStored valid before) (answer : Bool) (after : State Symbol Guard)
    (done : MergedFreshOrdinaryComparison.allRows readFuel clear compare wide narrows before = .done answer after) :
    Effect valid before after := by
  induction narrows generalizing before with
  | nil => exact pure_effect valid before semantic costs stored true answer after done
  | cons narrow narrows ih =>
      obtain ⟨wides, readAfter, readDone, later⟩ := (bind_done _ _ answer after).mp done
      have readFacts := read valid (read_graph readFuel wide before wides readAfter readDone)
        semantic costs wideInput wideClosed wideAnnotation stored
      have childInputs := semantic.ready.semantic.1.normal.facts.cached.edges narrow.entry.key narrow (narrowInputs _ List.mem_cons_self)
      obtain ⟨accepted, middle, covered, rest⟩ := (bind_done _ _ answer after).mp later
      have coverFacts := anyCover_effect valid clear compare callback narrow wides readAfter readFacts.1.semantic readFacts.1.costs
        (fun value member => readFacts.1.keeps.available value (childInputs value member)) readFacts.2.1
        (narrowClosed _ List.mem_cons_self) readFacts.2.2.1 (narrowAnnotations _ List.mem_cons_self) readFacts.2.2.2
        readFacts.1.stored accepted middle covered
      have first := readFacts.1.trans coverFacts
      cases accepted with
      | false => exact first.trans (pure_effect valid middle first.semantic first.costs first.stored false answer after rest)
      | true => exact first.trans (ih middle first.semantic first.costs (first.keeps.available wide wideInput)
          (fun edge member => InternedEdgeResidency.edge_grows before middle first.keeps.growth edge
            (narrowInputs edge (List.mem_cons_of_mem _ member)))
          (fun edge member => narrowClosed edge (List.mem_cons_of_mem _ member))
          (fun edge member => narrowAnnotations edge (List.mem_cons_of_mem _ member)) first.stored rest)

/-- Actual bounded comparison preserves the causal store from local input annotations. -/
theorem check (valid : Guard → Prop) [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] (clear : Guard → Bool)
    (fuel : Nat) (above : List (Nat × Nat)) (wide narrow : Value Symbol Guard) (before : State Symbol Guard)
    (semantic : SemanticReady before) (costs : CostHeap before) (wideInput : Available before wide) (narrowInput : Available before narrow)
    (wideClosed : wide.free = []) (narrowClosed : narrow.free = [])
    (wideAnnotation : Annotated valid wide) (narrowAnnotation : Annotated valid narrow) (stored : MuStored valid before)
    (answer : Bool) (after : State Symbol Guard)
    (done : MergedFreshOrdinaryComparison.check clear fuel above wide narrow before = .done answer after) :
    Effect valid before after := by
  rw [MergedFreshOrdinaryComparison.check] at done
  split at done
  · exact pure_effect valid before semantic costs stored true answer after done
  · split at done
    · exact pure_effect valid before semantic costs stored false answer after done
    · split at done
      · exact pure_effect valid before semantic costs stored true answer after done
      · cases wideFound : identity wide with
        | none => simp only [wideFound] at done; cases done
        | some wideId =>
            cases narrowFound : identity narrow with
            | none => simp only [wideFound, narrowFound] at done; cases done
            | some narrowId =>
                simp only [wideFound, narrowFound] at done
                split at done
                · exact pure_effect valid before semantic costs stored true answer after done
                · cases fuel with
                  | zero => cases done
                  | succ fuel =>
                      obtain ⟨narrows, middle, readDone, later⟩ := (bind_done _ _ answer after).mp done
                      have readFacts := read valid (read_graph (fuel + 1) narrow before narrows middle readDone)
                        semantic costs narrowInput narrowClosed narrowAnnotation stored
                      have rest := allRows_effect valid (fuel + 1) clear (MergedFreshOrdinaryComparison.check clear fuel ((wideId, narrowId) :: above))
                        (check valid clear fuel ((wideId, narrowId) :: above)) wide narrows middle readFacts.1.semantic readFacts.1.costs
                        (readFacts.1.keeps.available wide wideInput) readFacts.2.1 wideClosed readFacts.2.2.1
                        wideAnnotation readFacts.2.2.2 readFacts.1.stored answer after later
                      exact readFacts.1.trans rest
termination_by fuel

/-- Actual ordered child comparison uses the same local store contract at each reached pair. -/
theorem children (valid : Guard → Prop) [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (clear : Guard → Bool) (fuel : Nat) (above : List (Nat × Nat)) (wides narrows : List (Value Symbol Guard))
    (before : State Symbol Guard) (semantic : SemanticReady before) (costs : CostHeap before)
    (wideInputs : Values before wides) (narrowInputs : Values before narrows)
    (wideClosed : ClosedValues wides) (narrowClosed : ClosedValues narrows)
    (wideAnnotations : ∀ value ∈ wides, Annotated valid value) (narrowAnnotations : ∀ value ∈ narrows, Annotated valid value)
    (stored : MuStored valid before) (answer : Bool) (after : State Symbol Guard)
    (done : MergedSourceComparison.children (MergedFreshOrdinaryComparison.check clear fuel above) wides narrows before = .done answer after) :
    Effect valid before after :=
  children_effect valid _ (check valid clear fuel above) wides narrows before semantic costs wideInputs narrowInputs
    wideClosed narrowClosed wideAnnotations narrowAnnotations stored answer after done

/-- Actual cover search preserves the store across rejected candidates in source order. -/
theorem anyCover (valid : Guard → Prop) [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (clear : Guard → Bool) (fuel : Nat) (above : List (Nat × Nat)) (narrow : EdgeValue Symbol Guard) (wides : List (EdgeValue Symbol Guard))
    (before : State Symbol Guard) (semantic : SemanticReady before) (costs : CostHeap before)
    (narrowInputs : Values before narrow.children) (wideInputs : Edges before wides)
    (narrowClosed : ClosedValues narrow.children) (wideClosed : ClosedEdges wides)
    (narrowAnnotations : Edge valid narrow) (wideAnnotations : ∀ edge ∈ wides, Edge valid edge)
    (stored : MuStored valid before) (answer : Bool) (after : State Symbol Guard)
    (done : MergedSourceComparison.anyCover clear (MergedFreshOrdinaryComparison.check clear fuel above) narrow wides before = .done answer after) :
    Effect valid before after :=
  anyCover_effect valid clear _ (check valid clear fuel above) narrow wides before semantic costs narrowInputs wideInputs
    narrowClosed wideClosed narrowAnnotations wideAnnotations stored answer after done

/-- Every reached wide read supplies the local row annotations for the actual next cover search. -/
theorem allRows (valid : Guard → Prop) [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (readFuel : Nat) (clear : Guard → Bool) (fuel : Nat) (above : List (Nat × Nat))
    (wide : Value Symbol Guard) (narrows : List (EdgeValue Symbol Guard))
    (before : State Symbol Guard) (semantic : SemanticReady before) (costs : CostHeap before)
    (wideInput : Available before wide) (narrowInputs : Edges before narrows)
    (wideClosed : wide.free = []) (narrowClosed : ClosedEdges narrows)
    (wideAnnotation : Annotated valid wide) (narrowAnnotations : ∀ edge ∈ narrows, Edge valid edge)
    (stored : MuStored valid before) (answer : Bool) (after : State Symbol Guard)
    (done : MergedFreshOrdinaryComparison.allRows readFuel clear (MergedFreshOrdinaryComparison.check clear fuel above) wide narrows before = .done answer after) :
    Effect valid before after :=
  allRows_effect valid readFuel clear _ (check valid clear fuel above) wide narrows before semantic costs wideInput narrowInputs
    wideClosed narrowClosed wideAnnotation narrowAnnotations stored answer after done

end MicroCFTA.SourceCurrentHereditaryComparison
