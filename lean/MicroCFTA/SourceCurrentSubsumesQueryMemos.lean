import MicroCFTA.SourceEqualityQueryGlobalMemos
import MicroCFTA.SourceMergedSelection
import MicroCFTA.SourceMergedWorker
import MicroCFTA.SourceConstructorGlobalUnfold

/-!
# Global memo receipts through actual structural subsumption

Receipts contain literal row exposure, constructor work, direct returns,
and ordered sequencing. Constructor work has a checked silent primitive
trace. The comparison proof follows the actual empty, identity,
ancestor, row, cover, and child branches. It derives the final global tables
and stored cost invariant. The separate merge-result memo is not modeled.
-/
namespace MicroCFTA.SourceCurrentSubsumesQueryMemos
open Cache InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values Edges)
open MergedColdReaderClosedInputs (ClosedValues ClosedEdges)
open SourceEqualityRequiredCache SourceEqualityRequiredSemanticCache
open MergedSourceComparison (Result identity children anyCover)
open MergedFreshOrdinaryComparison (check allRows)
open SourceMergedComparisonEffects (bind_done read_graph)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Valid" => EndpointMemoGateTrace.Valid
local notation "CostHeap" => InternedFreshOrdinaryCostHeap.Heap

/-- Each receipt follows exact source returns, constructor work, exposure calls, and sequencing. -/
inductive Reads [DecidableEq (EdgeKey Symbol Guard)] :
    {Output : Type} → (State Symbol Guard → Result Symbol Guard Output) →
    State Symbol Guard → Output → State Symbol Guard → Memos → Memos → Prop where
  | pure (value : Output) (state : State Symbol Guard) (memos : Memos) :
      Reads (fun current => .done value current) state value state memos memos
  | work (job : Work Symbol Guard Output) (state : State Symbol Guard) (memos : Memos) :
      Reads (MergedColdMerge.work job) state (run job state).1 (run job state).2 memos memos
  | exposure (fuel : Nat) (value : Value Symbol Guard)
      (done : MergedFreshOrdinaryExposure.read fuel value before = .done rows after)
      (receipt : SourceEqualityQueryGlobalMemos.ExposureReads fuel value before memos saved) :
      Reads (MergedFreshOrdinaryExposure.read fuel value) before rows after memos saved
  | bind {first : State Symbol Guard → Result Symbol Guard First}
      {next : First → State Symbol Guard → Result Symbol Guard Output}
      (own : Reads first before value middle memos saved)
      (later : Reads (next value) middle result after saved final) :
      Reads (fun state => (first state).bind next) before result after memos final

/-- A receipt determines the actual result and constructor heap. -/
theorem Reads.done [DecidableEq (EdgeKey Symbol Guard)]
    {action : State Symbol Guard → Result Symbol Guard Output}
    {before after : State Symbol Guard} {result : Output} {memos saved : Memos}
    (trace : Reads action before result after memos saved) : action before = .done result after := by
  induction trace with
  | pure => rfl
  | work => rfl
  | exposure _ _ done _ => exact done
  | bind _ _ own later => simp only [own, Result.bind]; exact later

/-- Every derived receipt retains the two query tables. -/
theorem Reads.query [DecidableEq (EdgeKey Symbol Guard)]
    {action : State Symbol Guard → Result Symbol Guard Output}
    {before after : State Symbol Guard} {result : Output} {memos saved : Memos}
    (trace : Reads action before result after memos saved) : saved.query = memos.query := by
  induction trace with
  | pure => rfl
  | work => rfl
  | exposure _ _ _ receipt => exact receipt.2
  | bind _ _ own later => exact later.trans own

/-- Literal constructor work derives its actual primitive trace and has no global unfolding call. -/
theorem work_receipt [DecidableEq (EdgeKey Symbol Guard)] (job : Work Symbol Guard Output)
    (state : State Symbol Guard) (memos : Memos) :
    ∃ events, SourceGlobalUnfold.Runs ⟨state, memos.unfolding⟩
      ⟨(run job state).2, memos.unfolding⟩ events ∧ SourceGlobalUnfold.NoGlobal events := by
  exact ⟨_, by simpa only [SourceConstructorGlobalUnfold.work_erase] using
    SourceConstructorGlobalUnfold.work_runs job state memos.unfolding,
    SourceConstructorGlobalUnfold.work_silent job state⟩

/-- Actual comparison effects retain the state needed by the next read. -/
structure Effect [DecidableEq (EdgeKey Symbol Guard)] (before after : State Symbol Guard) (memos saved : Memos) : Prop where
  keeps : Keeps before after
  semantic : SemanticReady after
  costs : CostHeap after
  valid : Valid after saved
  retained : Extends memos.unfolding saved.unfolding
  query : saved.query = memos.query

private theorem Effect.trans [DecidableEq (EdgeKey Symbol Guard)] {before middle after : State Symbol Guard} {memos saved final : Memos}
    (first : Effect before middle memos saved) (second : Effect middle after saved final) :
    Effect before after memos final :=
  ⟨first.keeps.trans second.keeps, second.semantic, second.costs, second.valid,
    extends_trans first.retained second.retained, second.query.trans first.query⟩

private def Post [DecidableEq (EdgeKey Symbol Guard)]
    (action : State Symbol Guard → Result Symbol Guard Output)
    (before : State Symbol Guard) (result : Output) (after : State Symbol Guard) (memos : Memos) : Prop :=
  ∃ saved, Reads action before result after memos saved ∧ Effect before after memos saved

private theorem pure_memos [DecidableEq (EdgeKey Symbol Guard)]
    (value result : Output) (before after : State Symbol Guard)
    (done : Result.done value before = Result.done result after)
    (semantic : SemanticReady before) (costs : CostHeap before) (memos : Memos) (valid : Valid before memos) :
    Post (fun state => .done value state) before result after memos := by
  cases done
  exact ⟨memos, .pure value before memos,
    ⟨pure_keeps _ semantic.ready, semantic, costs, valid, extends_refl _, rfl⟩⟩

private theorem read_memos [DecidableEq (EdgeKey Symbol Guard)]
    (fuel : Nat) (value : Value Symbol Guard) (before after : State Symbol Guard)
    (rows : List (EdgeValue Symbol Guard))
    (done : MergedFreshOrdinaryExposure.read fuel value before = .done rows after)
    (semantic : SemanticReady before) (costs : CostHeap before) (available : Available before value)
    (memos : Memos) (valid : Valid before memos) :
    Post (MergedFreshOrdinaryExposure.read fuel value) before rows after memos := by
  cases completed : MergedFreshOrdinaryExposure.nodeEdges fuel value before with
  | done actualRows actualAfter =>
      have same := Result.done.inj (by simpa only [MergedFreshOrdinaryExposure.read, completed] using done)
      cases same.1
      cases same.2
      obtain ⟨saved, receipt, coherent, retained⟩ :=
        SourceEqualityQueryGlobalMemos.exposure_memos fuel value before semantic costs available memos valid
      have checked := SourceEqualityExposureCosts.nodeEdges_verified fuel value before semantic costs available
      refine ⟨saved, .exposure fuel value done receipt, ?_⟩
      exact ⟨by simpa only [completed, MergedSourceExposure.Result.state] using checked.keeps,
        by simpa only [completed, MergedSourceExposure.Result.state] using checked.semantic,
        by simpa only [completed, MergedSourceExposure.Result.state] using checked.costs,
        by simpa only [completed, MergedSourceExposure.Result.state] using coherent,
        retained, receipt.2⟩
  | unresolved | pending | exhausted =>
      simp only [MergedFreshOrdinaryExposure.read, completed] at done
      cases done

private def Callback [DecidableEq (EdgeKey Symbol Guard)]
    (compare : Value Symbol Guard → Value Symbol Guard → State Symbol Guard → Result Symbol Guard Bool) : Prop :=
  ∀ wide narrow before, SemanticReady before → CostHeap before → Available before wide → Available before narrow →
    wide.free = [] → narrow.free = [] → ∀ answer after, compare wide narrow before = .done answer after →
    ∀ memos, Valid before memos → Post (compare wide narrow) before answer after memos

private theorem children_memos [DecidableEq (EdgeKey Symbol Guard)]
    (compare : Value Symbol Guard → Value Symbol Guard → State Symbol Guard → Result Symbol Guard Bool)
    (callback : Callback compare) (wides narrows : List (Value Symbol Guard))
    (before : State Symbol Guard) (semantic : SemanticReady before) (costs : CostHeap before)
    (wideInputs : Values before wides) (narrowInputs : Values before narrows)
    (wideClosed : ClosedValues wides) (narrowClosed : ClosedValues narrows)
    (answer : Bool) (after : State Symbol Guard)
    (done : children compare wides narrows before = .done answer after) (memos : Memos) (valid : Valid before memos) :
    Post (children compare wides narrows) before answer after memos := by
  induction wides generalizing narrows before memos with
  | nil => exact pure_memos true answer before after done semantic costs memos valid
  | cons wide wides ih =>
      cases narrows with
      | nil => exact pure_memos true answer before after done semantic costs memos valid
      | cons narrow narrows =>
          obtain ⟨accepted, middle, called, later⟩ := (bind_done _ _ answer after).mp done
          obtain ⟨saved, own, checked⟩ := callback wide narrow before semantic costs
            (wideInputs _ List.mem_cons_self) (narrowInputs _ List.mem_cons_self)
            (wideClosed _ List.mem_cons_self) (narrowClosed _ List.mem_cons_self) accepted middle called memos valid
          cases accepted with
          | false =>
              obtain ⟨final, rest, effects⟩ := pure_memos false answer middle after later checked.semantic checked.costs saved checked.valid
              exact ⟨final, .bind own rest, checked.trans effects⟩
          | true =>
              obtain ⟨final, rest, effects⟩ := ih narrows middle checked.semantic checked.costs
                (fun value member => checked.keeps.available value (wideInputs value (List.mem_cons_of_mem _ member)))
                (fun value member => checked.keeps.available value (narrowInputs value (List.mem_cons_of_mem _ member)))
                (fun value member => wideClosed value (List.mem_cons_of_mem _ member))
                (fun value member => narrowClosed value (List.mem_cons_of_mem _ member)) later saved checked.valid
              exact ⟨final, .bind own rest, checked.trans effects⟩

private theorem anyCover_memos [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (clear : Guard → Bool)
    (compare : Value Symbol Guard → Value Symbol Guard → State Symbol Guard → Result Symbol Guard Bool)
    (callback : Callback compare) (narrow : EdgeValue Symbol Guard) (wides : List (EdgeValue Symbol Guard))
    (before : State Symbol Guard) (semantic : SemanticReady before) (costs : CostHeap before)
    (narrowInputs : Values before narrow.children) (wideInputs : Edges before wides)
    (narrowClosed : ClosedValues narrow.children) (wideClosed : ClosedEdges wides)
    (answer : Bool) (after : State Symbol Guard)
    (done : anyCover clear compare narrow wides before = .done answer after)
    (memos : Memos) (valid : Valid before memos) :
    Post (anyCover clear compare narrow wides) before answer after memos := by
  induction wides generalizing before memos with
  | nil => exact pure_memos false answer before after done semantic costs memos valid
  | cons wide wides ih =>
      rw [anyCover] at done
      split at done
      · rename_i header
        obtain ⟨accepted, middle, called, later⟩ := (bind_done _ _ answer after).mp done
        obtain ⟨saved, own, checked⟩ := children_memos compare callback wide.children narrow.children before semantic costs
          (semantic.ready.semantic.1.normal.facts.cached.edges wide.entry.key wide (wideInputs _ List.mem_cons_self))
          narrowInputs (wideClosed _ List.mem_cons_self) narrowClosed accepted middle called memos valid
        cases accepted with
        | true =>
            obtain ⟨final, rest, effects⟩ := pure_memos true answer middle after later checked.semantic checked.costs saved checked.valid
            refine ⟨final, ?_, checked.trans effects⟩
            simpa only [anyCover, ite_eq_left header] using
              (Reads.bind (next := fun accepted state => if accepted then .done true state else anyCover clear compare narrow wides state) own rest)
        | false =>
            obtain ⟨final, rest, effects⟩ := ih middle checked.semantic checked.costs
              (fun value member => checked.keeps.available value (narrowInputs value member))
              (fun edge member => InternedEdgeResidency.edge_grows before middle checked.keeps.growth edge
                (wideInputs edge (List.mem_cons_of_mem _ member)))
              (fun edge member => wideClosed edge (List.mem_cons_of_mem _ member)) later saved checked.valid
            refine ⟨final, ?_, checked.trans effects⟩
            simpa only [anyCover, ite_eq_left header] using
              (Reads.bind (next := fun accepted state => if accepted then .done true state else anyCover clear compare narrow wides state) own rest)
      · rename_i header
        obtain ⟨saved, trace, checked⟩ := ih before semantic costs narrowInputs
          (fun edge member => wideInputs edge (List.mem_cons_of_mem _ member))
          (fun edge member => wideClosed edge (List.mem_cons_of_mem _ member)) done memos valid
        exact ⟨saved, by simpa only [anyCover, ite_eq_right header] using trace, checked⟩

private theorem allRows_memos [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (fuel : Nat) (clear : Guard → Bool)
    (compare : Value Symbol Guard → Value Symbol Guard → State Symbol Guard → Result Symbol Guard Bool)
    (callback : Callback compare) (wide : Value Symbol Guard) (narrows : List (EdgeValue Symbol Guard))
    (before : State Symbol Guard) (semantic : SemanticReady before) (costs : CostHeap before)
    (wideInput : Available before wide) (narrowInputs : Edges before narrows)
    (wideClosed : wide.free = []) (narrowClosed : ClosedEdges narrows)
    (answer : Bool) (after : State Symbol Guard)
    (done : allRows fuel clear compare wide narrows before = .done answer after)
    (memos : Memos) (valid : Valid before memos) :
    Post (allRows fuel clear compare wide narrows) before answer after memos := by
  induction narrows generalizing before memos with
  | nil => exact pure_memos true answer before after done semantic costs memos valid
  | cons narrow narrows ih =>
      obtain ⟨wides, readAfter, read, later⟩ := (bind_done _ _ answer after).mp done
      have readFacts := (read_graph fuel wide before wides readAfter read).verified semantic wideInput wideClosed
      obtain ⟨readMemos, readTrace, readEffects⟩ := read_memos fuel wide before readAfter wides read semantic costs wideInput memos valid
      have children := semantic.ready.semantic.1.normal.facts.cached.edges narrow.entry.key narrow (narrowInputs _ List.mem_cons_self)
      obtain ⟨accepted, middle, called, rest⟩ := (bind_done _ _ answer after).mp later
      obtain ⟨saved, own, checked⟩ := anyCover_memos clear compare callback narrow wides readAfter
        readEffects.semantic readEffects.costs (fun value member => readEffects.keeps.available value (children value member))
        readFacts.2.2.1 (narrowClosed _ List.mem_cons_self) readFacts.2.2.2 accepted middle called readMemos readEffects.valid
      have first := readEffects.trans checked
      cases accepted with
      | false =>
          obtain ⟨final, tail, effects⟩ := pure_memos false answer middle after rest checked.semantic checked.costs saved checked.valid
          exact ⟨final, .bind readTrace (.bind own tail), first.trans effects⟩
      | true =>
          obtain ⟨final, tail, effects⟩ := ih middle checked.semantic checked.costs
            (first.keeps.available wide wideInput)
            (fun edge member => InternedEdgeResidency.edge_grows before middle first.keeps.growth edge
              (narrowInputs edge (List.mem_cons_of_mem _ member)))
            (fun edge member => narrowClosed edge (List.mem_cons_of_mem _ member)) rest saved checked.valid
          exact ⟨final, .bind readTrace (.bind own tail), first.trans effects⟩

private theorem check_function [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (clear : Guard → Bool) (fuel : Nat) (above : List (Nat × Nat)) (wide narrow : Value Symbol Guard) :
    check clear fuel above wide narrow = fun state =>
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
                  (MergedFreshOrdinaryExposure.read (fuel + 1) narrow state).bind fun rows after =>
                    allRows (fuel + 1) clear (check clear fuel ((wideId, narrowId) :: above)) wide rows after := by
  funext state
  rw [check]
  rfl

/-- Every completed source subsumption call derives its exact global reads and final coherent tables. -/
theorem check_memos [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (clear : Guard → Bool) (fuel : Nat) (above : List (Nat × Nat))
    (wide narrow : Value Symbol Guard) (before : State Symbol Guard)
    (semantic : SemanticReady before) (costs : CostHeap before)
    (wideInput : Available before wide) (narrowInput : Available before narrow)
    (wideClosed : wide.free = []) (narrowClosed : narrow.free = [])
    (answer : Bool) (after : State Symbol Guard)
    (done : check clear fuel above wide narrow before = .done answer after)
    (memos : Memos) (valid : Valid before memos) :
    ∃ saved, Reads (check clear fuel above wide narrow) before answer after memos saved ∧
      Effect before after memos saved := by
  rw [check_function] at done ⊢
  split at done
  · rename_i emptyNarrow
    simp only [ite_eq_left emptyNarrow]
    exact pure_memos true answer before after done semantic costs memos valid
  · rename_i nonemptyNarrow
    simp only [ite_eq_right nonemptyNarrow]
    split at done
    · rename_i emptyWide
      simp only [ite_eq_left emptyWide]
      exact pure_memos false answer before after done semantic costs memos valid
    · rename_i nonemptyWide
      simp only [ite_eq_right nonemptyWide]
      split at done
      · rename_i same
        simp only [ite_eq_left same]
        exact pure_memos true answer before after done semantic costs memos valid
      · rename_i different
        simp only [ite_eq_right different]
        cases wideFound : identity wide with
        | none => simp only [wideFound] at done; cases done
        | some wideId =>
            cases narrowFound : identity narrow with
            | none => simp only [wideFound, narrowFound] at done; cases done
            | some narrowId =>
                simp only [wideFound, narrowFound] at done ⊢
                split at done
                · rename_i visited
                  simp only [ite_eq_left visited]
                  exact pure_memos true answer before after done semantic costs memos valid
                · rename_i fresh
                  simp only [ite_eq_right fresh]
                  cases fuel with
                  | zero => cases done
                  | succ fuel =>
                      obtain ⟨narrows, middle, read, later⟩ := (bind_done _ _ answer after).mp done
                      have readFacts := (read_graph (fuel + 1) narrow before narrows middle read).verified semantic narrowInput narrowClosed
                      obtain ⟨saved, own, checked⟩ := read_memos (fuel + 1) narrow before middle narrows read
                        semantic costs narrowInput memos valid
                      obtain ⟨final, rest, effects⟩ := allRows_memos (fuel + 1) clear
                        (check clear fuel ((wideId, narrowId) :: above))
                        (check_memos clear fuel ((wideId, narrowId) :: above)) wide narrows middle
                        checked.semantic checked.costs (checked.keeps.available wide wideInput)
                        readFacts.2.2.1 wideClosed readFacts.2.2.2 answer after later saved checked.valid
                      exact ⟨final, .bind own rest, checked.trans effects⟩
termination_by fuel

/-- Recursive-cover search retains each comparison call and its short-circuit state. -/
theorem anyAccepts_memos [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (clear : Guard → Bool) (fuel : Nat) (narrow : Value Symbol Guard) (wides : List (Value Symbol Guard))
    (before : State Symbol Guard) (semantic : SemanticReady before) (costs : CostHeap before)
    (narrowInput : Available before narrow) (wideInputs : Values before wides)
    (narrowClosed : narrow.free = []) (wideClosed : ClosedValues wides)
    (answer : Bool) (after : State Symbol Guard)
    (done : SourceMergedSelection.anyAccepts clear fuel narrow wides before = .done answer after)
    (memos : Memos) (valid : Valid before memos) :
    ∃ saved, Reads (SourceMergedSelection.anyAccepts clear fuel narrow wides) before answer after memos saved ∧
      Effect before after memos saved := by
  induction wides generalizing before memos with
  | nil => exact pure_memos false answer before after done semantic costs memos valid
  | cons wide wides ih =>
      simp only [SourceMergedSelection.anyAccepts, narrowClosed, ite_true] at done ⊢
      obtain ⟨accepted, middle, called, later⟩ := (bind_done _ _ answer after).mp done
      obtain ⟨saved, own, checked⟩ := check_memos clear fuel [] wide narrow before semantic costs
        (wideInputs _ List.mem_cons_self) narrowInput (wideClosed _ List.mem_cons_self) narrowClosed
        accepted middle called memos valid
      cases accepted with
      | true =>
          obtain ⟨final, rest, effects⟩ := pure_memos true answer middle after later checked.semantic checked.costs saved checked.valid
          exact ⟨final, .bind own rest, checked.trans effects⟩
      | false =>
          obtain ⟨final, rest, effects⟩ := ih middle checked.semantic checked.costs
            (checked.keeps.available narrow narrowInput)
            (fun value member => checked.keeps.available value (wideInputs value (List.mem_cons_of_mem _ member)))
            (fun value member => wideClosed value (List.mem_cons_of_mem _ member)) later saved checked.valid
          exact ⟨final, .bind own rest, checked.trans effects⟩

/-- Actual retention derives the ordered comparison receipts before identity deduplication. -/
theorem retain_memos [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (clear : Guard → Bool) (fuel : Nat) (recursive inputs : List (Value Symbol Guard))
    (before : State Symbol Guard) (semantic : SemanticReady before) (costs : CostHeap before)
    (recInputs : Values before recursive) (recClosed : ClosedValues recursive)
    (available : Values before inputs) (closed : ClosedValues inputs)
    (retained : List (Value Symbol Guard)) (after : State Symbol Guard)
    (done : SourceMergedSelection.retain clear fuel recursive inputs before = .done retained after)
    (memos : Memos) (valid : Valid before memos) :
    ∃ saved, Reads (SourceMergedSelection.retain clear fuel recursive inputs) before retained after memos saved ∧
      Effect before after memos saved := by
  induction inputs generalizing before retained after memos with
  | nil => exact pure_memos [] retained before after done semantic costs memos valid
  | cons child inputs ih =>
      rw [SourceMergedSelection.retain] at done
      split at done
      · rename_i marked
        obtain ⟨rest, middle, called, returned⟩ := (bind_done _ _ retained after).mp done
        obtain ⟨saved, own, checked⟩ := ih before semantic costs recInputs
          (fun value member => available value (List.mem_cons_of_mem _ member))
          (fun value member => closed value (List.mem_cons_of_mem _ member)) rest middle called memos valid
        obtain ⟨final, later, effects⟩ := pure_memos (child :: rest) retained middle after returned checked.semantic checked.costs saved checked.valid
        refine ⟨final, ?_, checked.trans effects⟩
        simpa only [SourceMergedSelection.retain, ite_eq_left marked] using
          (Reads.bind (next := fun rest state => .done (child :: rest) state) own later)
      · rename_i unmarked
        obtain ⟨covered, middle, called, later⟩ := (bind_done _ _ retained after).mp done
        obtain ⟨saved, own, checked⟩ := anyAccepts_memos clear fuel child recursive before semantic costs
          (available _ List.mem_cons_self) recInputs (closed _ List.mem_cons_self) recClosed covered middle called memos valid
        obtain ⟨rest, finalHeap, tail, returned⟩ := (bind_done _ _ retained after).mp later
        obtain ⟨next, tailReads, tailEffects⟩ := ih middle checked.semantic checked.costs
          (fun value member => checked.keeps.available value (recInputs value member))
          (fun value member => checked.keeps.available value (available value (List.mem_cons_of_mem _ member)))
          (fun value member => closed value (List.mem_cons_of_mem _ member)) rest finalHeap tail saved checked.valid
        obtain ⟨final, returnedReads, returnedEffects⟩ := pure_memos (if covered then rest else child :: rest)
          retained finalHeap after returned tailEffects.semantic tailEffects.costs next tailEffects.valid
        refine ⟨final, ?_, checked.trans (tailEffects.trans returnedEffects)⟩
        simpa only [SourceMergedSelection.retain, ite_eq_right unmarked] using
          (Reads.bind (next := fun covered state =>
            (SourceMergedSelection.retain clear fuel recursive inputs state).bind fun rest finalHeap =>
              .done (if covered then rest else child :: rest) finalHeap) own
            (Reads.bind (next := fun rest state => .done (if covered then rest else child :: rest) state) tailReads returnedReads))

/-- Source child selection retains exact global calls and all three coherent final tables. -/
theorem select_memos [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    (clear : Guard → Bool) (fuel : Nat) (inputs : List (Value Symbol Guard))
    (before : State Symbol Guard) (semantic : SemanticReady before) (costs : CostHeap before)
    (available : Values before inputs) (closed : ClosedValues inputs)
    (retained : List (Value Symbol Guard)) (after : State Symbol Guard)
    (done : SourceMergedSelection.select clear fuel inputs before = .done retained after)
    (memos : Memos) (valid : Valid before memos) :
    ∃ saved, Reads (SourceMergedSelection.select clear fuel inputs) before retained after memos saved ∧
      Effect before after memos saved := by
  obtain ⟨values, middle, filtered, returned⟩ := (bind_done _ _ retained after).mp done
  obtain ⟨saved, own, checked⟩ := retain_memos clear fuel (inputs.filter MergedPhysicalGroupColumns.closedMu) inputs
    before semantic costs (fun value member => available value (List.mem_filter.mp member).1)
    (fun value member => closed value (List.mem_filter.mp member).1) available closed values middle filtered memos valid
  obtain ⟨final, later, effects⟩ := pure_memos (distinctNodes values) retained middle after returned checked.semantic checked.costs saved checked.valid
  exact ⟨final, .bind own later, checked.trans effects⟩

end MicroCFTA.SourceCurrentSubsumesQueryMemos
