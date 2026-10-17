import MicroCFTA.SourceMergedComparisonHistory

/-!
# Exact ordered replay of repaired comparison stages

Old successful callbacks supply their actual histories. A replay uses
those histories at the same full heaps. Failed covers keep their effects
before the next candidate. The complete comparison discharges the local
callback and reader replay premises in its own induction.
-/
namespace MicroCFTA.SourceMergedComparisonReplayStages
open InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values Edges)
open MergedColdReaderClosedInputs (ClosedValues ClosedEdges)
open SourceEqualityRequiredCache SourceEqualityRequiredSemanticCache
open SourceMergedComparisonEffects (bind_done read_graph)
open MergedSourceComparison (Result children anyCover)
open MergedFreshOrdinaryComparison (allRows)
open InternedMuDepthInventory (Bounded)
open SourceCurrentAllocatedUnfoldHistory (History)
open SourceMergedComparisonHistory (Callback)
variable {Symbol Guard : Type} [DecidableEq (EdgeKey Symbol Guard)]

/-- Local callbacks replay at each exact heap reached from the captured origin. -/
def CallbackReplay (limit : Nat) (origin : State Symbol Guard)
    (first second : Value Symbol Guard → Value Symbol Guard → State Symbol Guard → Result Symbol Guard Bool) : Prop :=
  ∀ wide narrow before, SemanticReady before → Bounded before limit → Available before wide → Available before narrow →
    wide.free = [] → narrow.free = [] → History origin before →
    ∀ answer after, first wide narrow before = .done answer after → second wide narrow before = .done answer after

/-- An ordered zip replays every demanded child at its actual returned heap. -/
theorem children_replay (limit : Nat) (origin : State Symbol Guard)
    (first second : Value Symbol Guard → Value Symbol Guard → State Symbol Guard → Result Symbol Guard Bool)
    (recorded : Callback limit first) (replay : CallbackReplay limit origin first second)
    (wides narrows : List (Value Symbol Guard)) (before : State Symbol Guard)
    (semantic : SemanticReady before) (bounded : Bounded before limit)
    (wideInputs : Values before wides) (narrowInputs : Values before narrows)
    (wideClosed : ClosedValues wides) (narrowClosed : ClosedValues narrows) (reached : History origin before)
    (answer : Bool) (after : State Symbol Guard) (done : children first wides narrows before = .done answer after) :
    children second wides narrows before = .done answer after := by
  induction wides generalizing narrows before with
  | nil => exact done
  | cons wide wides ih =>
      cases narrows with
      | nil => exact done
      | cons narrow narrows =>
          obtain ⟨accepted, middle, head, tail⟩ := (bind_done _ _ answer after).mp done
          have checked := recorded wide narrow before semantic bounded (wideInputs _ List.mem_cons_self)
            (narrowInputs _ List.mem_cons_self) (wideClosed _ List.mem_cons_self) (narrowClosed _ List.mem_cons_self)
            accepted middle head
          have headReplay := replay wide narrow before semantic bounded (wideInputs _ List.mem_cons_self)
            (narrowInputs _ List.mem_cons_self) (wideClosed _ List.mem_cons_self) (narrowClosed _ List.mem_cons_self)
            reached accepted middle head
          simp only [children, headReplay, Result.bind]
          cases accepted with
          | false => exact tail
          | true =>
              exact ih narrows middle checked.effect.2 checked.bounded
                (fun value member => checked.effect.1.available value (wideInputs value (List.mem_cons_of_mem _ member)))
                (fun value member => checked.effect.1.available value (narrowInputs value (List.mem_cons_of_mem _ member)))
                (fun value member => wideClosed value (List.mem_cons_of_mem _ member))
                (fun value member => narrowClosed value (List.mem_cons_of_mem _ member))
                (reached.trans checked.history) tail

/-- A cover replay retains each failed candidate before the original suffix. -/
theorem anyCover_replay [DecidableEq Symbol] (limit : Nat) (origin : State Symbol Guard) (clear : Guard → Bool)
    (first second : Value Symbol Guard → Value Symbol Guard → State Symbol Guard → Result Symbol Guard Bool)
    (recorded : Callback limit first) (replay : CallbackReplay limit origin first second)
    (narrow : EdgeValue Symbol Guard) (wides : List (EdgeValue Symbol Guard)) (before : State Symbol Guard)
    (semantic : SemanticReady before) (bounded : Bounded before limit)
    (narrowInputs : Values before narrow.children) (wideInputs : Edges before wides)
    (narrowClosed : ClosedValues narrow.children) (wideClosed : ClosedEdges wides) (reached : History origin before)
    (answer : Bool) (after : State Symbol Guard) (done : anyCover clear first narrow wides before = .done answer after) :
    anyCover clear second narrow wides before = .done answer after := by
  induction wides generalizing before with
  | nil => exact done
  | cons wide wides ih =>
      by_cases header : wide.entry.key.symbol = narrow.entry.key.symbol ∧
          wide.children.length = narrow.children.length ∧ clear wide.entry.key.constraint = true
      · simp only [anyCover, ite_eq_left header] at done ⊢
        obtain ⟨accepted, middle, head, tail⟩ := (bind_done _ _ answer after).mp done
        have checked := SourceMergedComparisonHistory.children_recorded limit first recorded wide.children narrow.children before
          semantic bounded (semantic.ready.semantic.1.normal.facts.cached.edges wide.entry.key wide (wideInputs _ List.mem_cons_self))
          narrowInputs (wideClosed _ List.mem_cons_self) narrowClosed accepted middle head
        have headReplay := children_replay limit origin first second recorded replay wide.children narrow.children before
          semantic bounded (semantic.ready.semantic.1.normal.facts.cached.edges wide.entry.key wide (wideInputs _ List.mem_cons_self))
          narrowInputs (wideClosed _ List.mem_cons_self) narrowClosed reached accepted middle head
        rw [headReplay]
        simp only [Result.bind]
        cases accepted with
        | true => exact tail
        | false =>
            exact ih middle checked.effect.2 checked.bounded
              (fun value member => checked.effect.1.available value (narrowInputs value member))
              (fun edge member => InternedEdgeResidency.edge_grows before middle checked.effect.1.growth edge
                (wideInputs edge (List.mem_cons_of_mem _ member)))
              narrowClosed (fun edge member => wideClosed edge (List.mem_cons_of_mem _ member))
              (reached.trans checked.history) tail
      · simp only [anyCover, ite_eq_right header] at done ⊢
        exact ih before semantic bounded narrowInputs
          (fun edge member => wideInputs edge (List.mem_cons_of_mem _ member)) narrowClosed
          (fun edge member => wideClosed edge (List.mem_cons_of_mem _ member)) reached done

/-- Each row replays its wide read and covers before the next original narrow row. -/
theorem allRows_replay [DecidableEq Symbol] (limit : Nat) (origin : State Symbol Guard)
    (firstFuel secondFuel : Nat) (clear : Guard → Bool)
    (first second : Value Symbol Guard → Value Symbol Guard → State Symbol Guard → Result Symbol Guard Bool)
    (recorded : Callback limit first) (replay : CallbackReplay limit origin first second)
    (readReplay : ∀ value before, SemanticReady before → Bounded before limit → Available before value → value.free = [] →
      History origin before → ∀ rows after,
      MergedFreshOrdinaryExposure.read firstFuel value before = .done rows after →
      MergedFreshOrdinaryExposure.read secondFuel value before = .done rows after)
    (wide : Value Symbol Guard) (narrows : List (EdgeValue Symbol Guard)) (before : State Symbol Guard)
    (semantic : SemanticReady before) (bounded : Bounded before limit)
    (wideInput : Available before wide) (narrowInputs : Edges before narrows)
    (wideClosed : wide.free = []) (narrowClosed : ClosedEdges narrows) (reached : History origin before)
    (answer : Bool) (after : State Symbol Guard)
    (done : allRows firstFuel clear first wide narrows before = .done answer after) :
    allRows secondFuel clear second wide narrows before = .done answer after := by
  induction narrows generalizing before with
  | nil => exact done
  | cons narrow narrows ih =>
      obtain ⟨wides, readAfter, readDone, later⟩ := (bind_done _ _ answer after).mp done
      have readFacts := (read_graph firstFuel wide before wides readAfter readDone).verified semantic wideInput wideClosed
      have readBudget := SourceMergedComparisonHistory.read_recorded limit firstFuel wide before
        semantic bounded wideInput wideClosed wides readAfter readDone
      have childInputs := semantic.ready.semantic.1.normal.facts.cached.edges narrow.entry.key narrow (narrowInputs _ List.mem_cons_self)
      obtain ⟨accepted, middle, covered, tail⟩ := (bind_done _ _ answer after).mp later
      have coverBudget := SourceMergedComparisonHistory.anyCover_recorded limit clear first recorded narrow wides readAfter
        readFacts.2.1 readBudget.bounded (fun value member => readFacts.1.available value (childInputs value member))
        readFacts.2.2.1 (narrowClosed _ List.mem_cons_self) readFacts.2.2.2 accepted middle covered
      have readNew := readReplay wide before semantic bounded wideInput wideClosed reached wides readAfter readDone
      have coverNew := anyCover_replay limit origin clear first second recorded replay narrow wides readAfter
        readFacts.2.1 readBudget.bounded (fun value member => readFacts.1.available value (childInputs value member))
        readFacts.2.2.1 (narrowClosed _ List.mem_cons_self) readFacts.2.2.2 (reached.trans readBudget.history) accepted middle covered
      simp only [allRows, readNew, Result.bind, coverNew]
      have firstPrefix := readBudget.trans coverBudget
      cases accepted with
      | false => exact tail
      | true =>
          exact ih middle firstPrefix.effect.2 firstPrefix.bounded (firstPrefix.effect.1.available wide wideInput)
            (fun edge member => InternedEdgeResidency.edge_grows before middle firstPrefix.effect.1.growth edge
              (narrowInputs edge (List.mem_cons_of_mem _ member))) wideClosed
            (fun edge member => narrowClosed edge (List.mem_cons_of_mem _ member))
            (reached.trans firstPrefix.history) tail

end MicroCFTA.SourceMergedComparisonReplayStages
