import MicroCFTA.SourceCurrentAllocatedLocalWorker
import MicroCFTA.SourceCurrentAllocatedRecordScanWorkerActual
import MicroCFTA.SourceCurrentAllocatedClassWorkerCompletion

/-!
# Stable execution of actual local reduction graphs

Each finite local graph supplies sufficient bounds for its reached phases.
Record retention comes from that same Scan. Required children and class
editing retain their exact return states. The conjunction budget stays
fixed. This direction needs no physical invariant or host execution law.
-/
namespace MicroCFTA.SourceCurrentAllocatedLocalWorkerCompletion
open Language EqualityNormalize InternedConstructorTemplates
open SourceCurrentAllocatedLocalWorker
open SourceCurrentConjunctionSelectedRecords (Retained)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Allocated" => SourceEqualityConjoinAllocation.Constraint FullSyntax.Formula
local notation "EqValue" => SourceEqualityConstraintAllocation.Value
local notation "Fourth" => SourceCurrentEmptinessMemo.Memo
local notation "Memo" => SourceCurrentMemoMergeGraph.Memo Symbol Guard
local notation "Record" => SourceEqualityClassOrder.Record
local notation "Heap" => InternedConstructorTemplates.State Symbol Guard
variable {width : Nat} {A : Type}

/-- Nine reached phase bounds retain the same complete local return under all larger bounds. -/
def StableRun (evaluation : Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Outcome A width)
    (result : A) (after : Checked width) (fourth : Fourth) (memo : Memo) : Prop :=
  ∃ g s r e p h m c n, ∀ G S R E P H M C N,
    g ≤ G → s ≤ S → r ≤ R → e ≤ E → p ≤ P → h ≤ H → m ≤ M → c ≤ C → n ≤ N →
      evaluation G S R E P H M C N = .done result after fourth memo

variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq (Value Symbol Guard)]

omit [DecidableEq Symbol] [DecidableEq (Value Symbol Guard)] in
/-- Every literal required success supplies stable bounds at its same complete heap return. -/
theorem required_complete {r h : Nat} {paths : List SourceEqualityNeeded.Path}
    {values results : List (Value Symbol Guard)} {before after : Heap}
    (actual : SourceEqualityRequiredExecution.requireAll r h paths values before = .done results after) :
    SourceEqualityRequiredWorkerComplete.StableRun
      (fun R H => SourceEqualityRequiredExecution.requireAll R H paths values before) results after := by
  have graph := (SourceEqualityRequiredExecution.requireAll_execution_iff paths values before results after).mpr ⟨r, h, actual⟩
  cases compiled : SourceEqualityNeeded.build paths with
  | node entries =>
      simp only [compiled] at graph
      simpa only [SourceEqualityRequiredExecution.requireAll, compiled] using
        SourceEqualityRequiredWorkerComplete.children_stable graph

/-- An actual Scan continuation supplies stable literal execution with its original retained records. -/
theorem classes_complete {budget : Nat} {records : List Record} {values results : List (Value Symbol Guard)}
    {before after : Checked width} {fourth savedFourth : Fourth} {memo saved : Memo} {outcome : Option Class}
    (actual : SourceCurrentConjunctionScanClassPass.Reduction budget records values before fourth memo
      outcome results after savedFourth saved) :
    StableRun (fun g s r e p h m c n => classes g s r e p h m c n budget records values before fourth memo)
      results after savedFourth saved := by
  cases actual with
  | stopped actualScan =>
      obtain ⟨kept, retained⟩ := SourceCurrentConjunctionSelectedRecords.retained_records records actualScan
      obtain ⟨g, s, p, h, n, done⟩ := SourceCurrentAllocatedRecordScanWorkerActual.scan_complete retained
      refine ⟨g, s, 0, 0, p, h, 0, 0, n, ?_⟩
      intro G S R E P H M C N enoughG enoughS _ _ enoughP enoughH _ _ enoughN
      have first := done G S P H N enoughG enoughS enoughP enoughH enoughN
      simp only [classes, scan, first, Outcome.bind]
  | completed actualScan retained actualRequired actualPass =>
      obtain ⟨g, s, p, h, n, scanDone⟩ := SourceCurrentAllocatedRecordScanWorkerActual.scan_complete retained
      obtain ⟨r, read, requiredDone⟩ := required_complete actualRequired
      obtain ⟨e, projection, head, m, c, native, passDone⟩ :=
        SourceCurrentAllocatedClassWorkerCompletion.pass_complete actualPass
      refine ⟨g, s, r, e, max p projection, max h (max read head), m, c, max n native, ?_⟩
      intro G S R E P H M C N enoughG enoughS enoughR enoughE enoughP enoughH enoughM enoughC enoughN
      have first := scanDone G S P H N enoughG enoughS (by omega) (by omega) (by omega)
      have second := requiredDone R H enoughR (by omega)
      have last := passDone E P H M C N enoughE (by omega) (by omega) enoughM enoughC (by omega)
      simp only [classes, scan, first, Outcome.bind, required, retained.fields.2, second, pass, last]

/-- Each actual precheck branch and continuation construct stable literal local execution. -/
theorem reduce_complete {budget : Nat} {loaded : Allocated} {inherited : EqValue}
    {values results : List (Value Symbol Guard)} {before after : Checked width}
    {fourth savedFourth : Fourth} {memo saved : Memo}
    (actual : SourceCurrentAllocatedLocalReduction.Reduction budget loaded inherited values before fourth memo
      results after savedFourth saved) :
    StableRun (fun g s r e p h m c n => reduce g s r e p h m c n budget loaded inherited values before fourth memo)
      results after savedFourth saved := by
  cases actual with
  | unchanged done =>
      exact ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, by
        intro G S R E P H M C N _ _ _ _ _ _ _ _ _
        exact reduce_unchanged G S R E P H M C N budget loaded inherited values before fourth memo done⟩
  | emptyChildren done =>
      exact ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, by
        intro G S R E P H M C N _ _ _ _ _ _ _ _ _
        exact reduce_emptyChildren G S R E P H M C N budget loaded inherited values before fourth memo done⟩
  | classes done continuation =>
      obtain ⟨g, s, r, e, p, h, m, c, n, stable⟩ := classes_complete continuation
      refine ⟨g, s, r, e, p, h, m, c, n, ?_⟩
      intro G S R E P H M C N enoughG enoughS enoughR enoughE enoughP enoughH enoughM enoughC enoughN
      simpa only [reduce, done, SourceCurrentAllocatedPrecheck.state] using
        stable G S R E P H M C N enoughG enoughS enoughR enoughE enoughP enoughH enoughM enoughC enoughN

end MicroCFTA.SourceCurrentAllocatedLocalWorkerCompletion
