import MicroCFTA.SourceCurrentAllocatedScanWorker
import MicroCFTA.SourceCurrentAllocatedSeededWorkerCompletion
import MicroCFTA.SourceCurrentConjunctionWorkerCompletion

/-!
# Stable literal execution of completed current Scan graphs

Each actual reached gate, seeded query, and conjunction call supplies bounds.
The Scan induction combines those bounds in source order. It retains the
exact selected prefix, checked state, and fourth memo. A stopped branch
needs no suffix completion. Physical readiness, language receipts, and
host forcing correspondence remain separate from this graph direction.
-/
namespace MicroCFTA.SourceCurrentAllocatedScanWorkerCompletion
open Language EqualityNormalize InternedConstructorTemplates InternedProbeProvenance
open SourceCurrentAllocatedNativeEffects (physical)
open SourceCurrentAllocatedQueryMemo (advancePhysical)
open SourceCurrentConjunctionClassScan (Scan advanceHeap)
open SourceCurrentAllocatedScanWorker
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "source" => SourceMemoGate.unconstrained
local notation "reaches" => SourceEndpointReachability.reaches source
variable {width : Nat} {A B : Type}

/-- Larger bounds preserve the complete successful result, checked state, and fourth memo. -/
def StableRun (evaluation : Nat → Nat → Nat → Nat → Nat → Outcome A width)
    (result : A) (after : Checked width) (saved : Memo) : Prop :=
  ∃ g s p h n, ∀ G S P H N, g ≤ G → s ≤ S → p ≤ P → h ≤ H → n ≤ N →
    evaluation G S P H N = .done result after saved

/-- Successful sequencing exposes its exact intermediate checked state and fourth memo. -/
theorem bind_done_iff (first : Outcome A width) (next : A → Checked width → Memo → Outcome B width)
    (result : B) (after : Checked width) (saved : Memo) :
    first.bind next = .done result after saved ↔
      ∃ value middle current, first = .done value middle current ∧
        next value middle current = .done result after saved := by
  cases first with
  | done value state memo =>
      constructor
      · intro actual; exact ⟨value, state, memo, rfl, actual⟩
      · rintro ⟨_, _, _, same, actual⟩; cases same; exact actual
  | failed =>
      constructor
      · intro impossible; cases impossible
      · rintro ⟨_, _, _, impossible, _⟩; cases impossible

/-- Stable actual prefixes compose at their literal checked and memo return. -/
theorem bind_stable (first : Nat → Nat → Nat → Nat → Nat → Outcome A width)
    (next : Nat → Nat → Nat → Nat → Nat → A → Checked width → Memo → Outcome B width)
    (value : A) (middle : Checked width) (current : Memo) (result : B) (after : Checked width) (saved : Memo)
    (one : StableRun first value middle current)
    (two : StableRun (fun g s p h n => next g s p h n value middle current) result after saved) :
    StableRun (fun g s p h n => (first g s p h n).bind (next g s p h n)) result after saved := by
  obtain ⟨g, s, p, h, n, done⟩ := one
  obtain ⟨laterG, laterS, laterP, laterH, laterN, nextDone⟩ := two
  refine ⟨max g laterG, max s laterS, max p laterP, max h laterH, max n laterN, ?_⟩
  intro G S P H N enoughG enoughS enoughP enoughH enoughN
  dsimp only
  rw [done G S P H N (by omega) (by omega) (by omega) (by omega) (by omega)]
  exact nextDone G S P H N (by omega) (by omega) (by omega) (by omega) (by omega)

/-- Selection retains an actual successful prefix before the same returned selected classes. -/
theorem select_stable (paths : Class)
    (evaluation : Nat → Nat → Nat → Nat → Nat → Outcome Result width)
    (stopped : Option Class) (selected : Constraints) (after : Checked width) (saved : Memo)
    (actual : StableRun evaluation (stopped, selected) after saved) :
    StableRun (fun g s p h n => (evaluation g s p h n).select paths)
      (stopped, paths :: selected) after saved := by
  obtain ⟨g, s, p, h, n, done⟩ := actual
  exact ⟨g, s, p, h, n, by
    intro G S P H N enoughG enoughS enoughP enoughH enoughN
    dsimp only
    rw [done G S P H N enoughG enoughS enoughP enoughH enoughN]
    rfl⟩

/-- An actual primary class graph supplies the first gate bound and exact heap advancement. -/
theorem primary_complete [DecidableEq (EdgeKey Symbol Guard)]
    {values : List (Value Symbol Guard)} {paths : Class} {before : Checked width}
    {answer : Bool} {heap : State Symbol Guard} {memo : Memo}
    (actual : EndpointStatefulGateTrace.ClassTrace source reaches values paths before.native.machine.heap answer heap) :
    StableRun (fun g _ _ _ _ => gate true g values paths before memo)
      answer (advanceHeap before heap) memo := by
  obtain ⟨bound, returned⟩ := SourceCurrentAllocatedGateWorker.primary_complete actual
  exact ⟨bound, 0, 0, 0, 0, by
    intro G S P H N enoughG _ _ _ _
    simp only [gate, ite_true, returned G enoughG]⟩

/-- An actual secondary class graph supplies its independent gate bound. -/
theorem secondary_complete [DecidableEq (EdgeKey Symbol Guard)]
    {values : List (Value Symbol Guard)} {paths : Class} {before : Checked width}
    {answer : Bool} {heap : State Symbol Guard} {memo : Memo}
    (actual : SourceCurrentSecondaryTrace.ClassTrace source values paths before.native.machine.heap answer heap) :
    StableRun (fun _ s _ _ _ => gate false s values paths before memo)
      answer (advanceHeap before heap) memo := by
  obtain ⟨bound, returned⟩ := SourceCurrentAllocatedGateWorker.secondary_complete actual
  exact ⟨0, bound, 0, 0, 0, by
    intro G S P H N _ enoughS _ _ _
    simp only [gate, Bool.false_eq_true, ite_false, returned S enoughS]⟩

/-- The actual checked seeded graph supplies all query bounds and retains the fourth memo. -/
theorem query_complete [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    {values : List (Value Symbol Guard)} {paths : Class} {before after : Checked width}
    {result : Value Symbol Guard} {memo : Memo}
    (actual : SourceCurrentAllocatedSeededQuery.Seeded values (paths.map (List.map Int.ofNat)) before result after) :
    StableRun (fun _ _ p h n => query p h n values paths before memo) result after memo := by
  obtain ⟨p, h, n, returned⟩ := SourceCurrentAllocatedSeededWorkerCompletion.seeded_complete actual
  exact ⟨0, 0, p, h, n, by
    intro G S P H N _ _ enoughP enoughH enoughN
    simp only [query, returned P H N enoughP enoughH enoughN]⟩

/-- An actual current conjunction Call supplies shared projection/read bounds and its literal saved memo. -/
theorem decision_complete [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    [DecidableEq (Value Symbol Guard)] {budget : Nat} {paths : Class} {queryValue : Value Symbol Guard}
    {before : Checked width} {memo saved : Memo} {answer : Bool}
    {after : SourceCurrentConjunctionRowsAllocation.State Symbol FullSyntax.Formula}
    (actual : SourceCurrentConjunctionMemo.Call budget memo queryValue (physical before) answer after saved) :
    StableRun (fun _ _ p h _ => decision p h budget paths queryValue before memo)
      answer (advancePhysical before after) saved := by
  obtain ⟨p, h, returned⟩ := SourceCurrentConjunctionWorkerCompletion.call_complete actual
  refine ⟨0, 0, p, h, 0, ?_⟩
  intro G S P H N _ _ enoughP enoughH _
  have done := SourceCurrentAllocatedConjunctionWorker.call_lift (before := before)
    (returned P H enoughP enoughH)
  simp only [decision, done]

/-- Every completed current Scan supplies stable literal bounds for the same full return. -/
theorem scan_complete [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    [DecidableEq (Value Symbol Guard)] {budget : Nat} {values : List (Value Symbol Guard)}
    {classes selected : Constraints} {before after : Checked width} {memo saved : Memo} {stopped : Option Class}
    (actual : Scan budget source reaches values classes before memo stopped selected after saved) :
    StableRun (fun g s p h n => scan g s p h n budget values classes before memo)
      (stopped, selected) after saved := by
  induction actual with
  | nil => exact ⟨0, 0, 0, 0, 0, by intros; rfl⟩
  | @selected paths heap classes before memo outcome selected after saved primary rest ih =>
      obtain ⟨g, primaryDone⟩ := SourceCurrentAllocatedGateWorker.primary_complete (before := before) primary
      obtain ⟨laterG, s, p, h, n, tailDone⟩ := ih
      refine ⟨max g laterG, s, p, h, n, ?_⟩
      intro G S P H N enoughG enoughS enoughP enoughH enoughN
      have first := primaryDone G (by omega)
      have tail := tailDone G S P H N (by omega) enoughS enoughP enoughH enoughN
      simp only [scan, gate, ite_true, first, Outcome.bind, Bool.false_eq_true, ite_false, tail, Outcome.select]
  | @skipped paths heap anchor classes before memo outcome selected after saved primary secondary rest ih =>
      obtain ⟨g, primaryDone⟩ := SourceCurrentAllocatedGateWorker.primary_complete (before := before) primary
      obtain ⟨s, secondaryDone⟩ := SourceCurrentAllocatedGateWorker.secondary_complete
        (before := advanceHeap before heap) secondary
      obtain ⟨laterG, laterS, p, h, n, tailDone⟩ := ih
      refine ⟨max g laterG, max s laterS, p, h, n, ?_⟩
      intro G S P H N enoughG enoughS enoughP enoughH enoughN
      have first := primaryDone G (by omega)
      have second := secondaryDone S (by omega)
      have tail := tailDone G S P H N (by omega) (by omega) enoughP enoughH enoughN
      simp only [scan, gate, Bool.false_eq_true, ite_true, ite_false, first, second, Outcome.bind, tail]
  | @continued paths heap anchor before queryValue middle memo later savedMemo classes outcome selected after saved
      primary secondary seeded decision rest ih =>
      obtain ⟨g, primaryDone⟩ := SourceCurrentAllocatedGateWorker.primary_complete (before := before) primary
      obtain ⟨s, secondaryDone⟩ := SourceCurrentAllocatedGateWorker.secondary_complete
        (before := advanceHeap before heap) secondary
      obtain ⟨p, h, n, queryDone⟩ := SourceCurrentAllocatedSeededWorkerCompletion.seeded_complete seeded
      obtain ⟨decisionP, decisionH, checkedDone⟩ := SourceCurrentConjunctionWorkerCompletion.call_complete decision
      obtain ⟨laterG, laterS, laterP, laterH, laterN, tailDone⟩ := ih
      refine ⟨max g laterG, max s laterS, max p (max decisionP laterP),
        max h (max decisionH laterH), max n laterN, ?_⟩
      intro G S P H N enoughG enoughS enoughP enoughH enoughN
      have first := primaryDone G (by omega)
      have second := secondaryDone S (by omega)
      have projected := queryDone P H N (by omega) (by omega) (by omega)
      have checked := SourceCurrentAllocatedConjunctionWorker.call_lift (before := middle)
        (checkedDone P H (by omega) (by omega))
      have tail := tailDone G S P H N (by omega) (by omega) (by omega) (by omega) (by omega)
      simp only [scan, gate, ite_true, ite_false, first, second, Outcome.bind,
        Bool.false_eq_true, query, projected, SourceCurrentAllocatedScanWorker.decision, checked, tail]
  | @stopped paths heap anchor before queryValue middle memo later saved classes primary secondary seeded decision =>
      obtain ⟨g, primaryDone⟩ := SourceCurrentAllocatedGateWorker.primary_complete (before := before) primary
      obtain ⟨s, secondaryDone⟩ := SourceCurrentAllocatedGateWorker.secondary_complete
        (before := advanceHeap before heap) secondary
      obtain ⟨p, h, n, queryDone⟩ := SourceCurrentAllocatedSeededWorkerCompletion.seeded_complete seeded
      obtain ⟨decisionP, decisionH, checkedDone⟩ := SourceCurrentConjunctionWorkerCompletion.call_complete decision
      refine ⟨g, s, max p decisionP, max h decisionH, n, ?_⟩
      intro G S P H N enoughG enoughS enoughP enoughH enoughN
      have first := primaryDone G enoughG
      have second := secondaryDone S enoughS
      have projected := queryDone P H N (by omega) (by omega) enoughN
      have checked := SourceCurrentAllocatedConjunctionWorker.call_lift (before := middle)
        (checkedDone P H (by omega) (by omega))
      simp only [scan, gate, ite_true, ite_false, first, second, Outcome.bind,
        Bool.false_eq_true, query, projected, SourceCurrentAllocatedScanWorker.decision, checked]

/-- The five independently derived bounds also give one sufficient uniform bound. -/
theorem scan_uniform [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    [DecidableEq (Value Symbol Guard)] {budget : Nat} {values : List (Value Symbol Guard)}
    {classes selected : Constraints} {before after : Checked width} {memo saved : Memo} {stopped : Option Class}
    (actual : Scan budget source reaches values classes before memo stopped selected after saved) :
    ∃ bound, ∀ fuel, bound ≤ fuel →
      scan fuel fuel fuel fuel fuel budget values classes before memo = .done (stopped, selected) after saved := by
  obtain ⟨g, s, p, h, n, returned⟩ := scan_complete actual
  refine ⟨max (max (max (max g s) p) h) n, ?_⟩
  intro fuel enough
  exact returned fuel fuel fuel fuel fuel (by omega) (by omega) (by omega) (by omega) (by omega)

end MicroCFTA.SourceCurrentAllocatedScanWorkerCompletion
