import MicroCFTA.SourceCurrentAllocatedScanWorkerActual

namespace MicroCFTA.CurrentScanCallerChecks
open Language EqualityNormalize InternedConstructorTemplates InternedProbeProvenance
open InternedNestedProvenance (Values)
open SourceCurrentAllocatedNativeInventoryState (Inventory At)
open SourceCurrentAllocatedPartialInvariant (Context Post)
open SourceCurrentAllocatedScanWorker
open SourceCurrentAllocatedScanWorkerCompletion (StableRun)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "unconstrained" => SourceMemoGate.unconstrained
local notation "reaches" => SourceEndpointReachability.reaches unconstrained
local notation "Ranges" => SourceCurrentConjunctionClassScanCompletion.Ranges
local notation "advance" => SourceCurrentAllocatedPartialState.advance
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq (Value Symbol Guard)] {width : Nat}
variable (formulas : SourceGuards.Formulas FullSyntax.Formula) (solver : SourceGuards.Entailment FullSyntax.Formula)

-- The second scan receives Context and At from the first computed inventory. Only its reached ranges are new.
example {inventory : Inventory} {before : Caller width} {memos : Memos}
    {g s p h n budget nextBudget : Nat} {values : List (Value Symbol Guard)}
    {classes nextClasses selected : Constraints} {outcome : Option Class} {after : Checked width} {saved : Memo}
    (initial : Context formulas solver inventory before memos)
    (available : Values before.checked.native.machine.heap values)
    (proper : ∀ paths ∈ classes, ∀ path ∈ paths, path ≠ [])
    (active : ∀ paths ∈ classes, Nontrivial paths)
    (ranges : Ranges budget unconstrained reaches values classes before.checked before.fourth)
    (first : scan g s p h n budget values classes before.checked before.fourth = .done (outcome, selected) after saved)
    (nextProper : ∀ paths ∈ nextClasses, ∀ path ∈ paths, path ≠ [])
    (nextActive : ∀ paths ∈ nextClasses, Nontrivial paths)
    (nextRanges : Ranges nextBudget unconstrained reaches values nextClasses after saved) :
    let middle := advance before after saved before.merge
    ∃ next global, Context formulas solver next middle global ∧ At formulas solver next after ∧
      ∃ G S P H N stopped kept later fourth finalInventory finalGlobal,
        scan G S P H N nextBudget values nextClasses middle.checked middle.fourth = .done (stopped, kept) later fourth ∧
        Post formulas solver finalInventory before (advance middle later fourth middle.merge) finalGlobal := by
  let middle := advance before after saved before.merge
  obtain ⟨next, global, actual, reads, post, resident, order, sound⟩ :=
    SourceCurrentAllocatedScanWorkerActual.verified formulas solver initial available proper active ranges first
  obtain ⟨stopped, kept, later, fourth, finalInventory, finalGlobal, stable, laterActual, laterReads,
      laterPost, laterResident, laterOrder, laterSound⟩ :=
    SourceCurrentAllocatedScanWorkerActual.finite formulas solver nextBudget values nextClasses post.context
      resident nextProper nextActive nextRanges
  obtain ⟨G, S, P, H, N, completed⟩ := stable
  exact ⟨next, global, post.context, post.context.admitted,
    G, S, P, H, N, stopped, kept, later, fourth, finalInventory, finalGlobal,
    completed G S P H N (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _),
    post.trans laterPost⟩

-- A supplied success derives its own strict reads and exact returned inventory, validity, and class law.
example {inventory : Inventory} {before : Caller width} {memos : Memos}
    {g s p h n budget : Nat} {values : List (Value Symbol Guard)} {classes selected : Constraints}
    {outcome : Option Class} {after : Checked width} {saved : Memo}
    (initial : Context formulas solver inventory before memos)
    (available : Values before.checked.native.machine.heap values)
    (proper : ∀ paths ∈ classes, ∀ path ∈ paths, path ≠ [])
    (active : ∀ paths ∈ classes, Nontrivial paths)
    (ranges : Ranges budget unconstrained reaches values classes before.checked before.fourth)
    (done : scan g s p h n budget values classes before.checked before.fourth = .done (outcome, selected) after saved) :
    ∃ next final,
      ∃ actual : SourceCurrentConjunctionClassScan.Scan budget unconstrained reaches values classes
          before.checked before.fourth outcome selected after saved,
        SourceCurrentAllocatedScanSourceReads.ScanReads actual memos final ∧
        Context formulas solver next (advance before after saved before.merge) final ∧
        At formulas solver next after ∧ EndpointMemoGateTrace.Valid after.native.machine.heap final ∧
        SourceCurrentEmptinessMemo.Correct formulas solver after.native.machine.heap saved ∧
        selected.Sublist classes ∧ SourceCurrentAllocatedScanCaller.StoppedSound formulas solver values classes outcome := by
  obtain ⟨next, final, actual, reads, post, resident, order, sound⟩ :=
    SourceCurrentAllocatedScanWorkerActual.verified formulas solver initial available proper active ranges done
  exact ⟨next, final, actual, reads, post.context, post.context.admitted, post.context.globals,
    post.context.correct, order, sound⟩

-- A true literal decision stops without any suffix execution. Selection retains a failed suffix's state and memo.
example (g s p h n budget : Nat) (values : List (Value Symbol Guard)) (paths : Class)
    (before middle anchor queried after : Checked width) (memo current fourth entered saved : Memo)
    (value : Value Symbol Guard)
    (primary : gate true g values paths before memo = .done true middle current)
    (secondary : gate false s values paths middle current = .done false anchor fourth)
    (query : SourceCurrentAllocatedScanWorker.query p h n values paths anchor fourth = .done value queried entered)
    (decision : SourceCurrentAllocatedScanWorker.decision p h budget paths value queried entered = .done true after saved) :
    (∀ suffix, scan g s p h n budget values (paths :: suffix) before memo = .done (some paths, []) after saved) ∧
      ∀ fault : Fault width,
        (Outcome.failed fault after saved : Outcome Result width).select paths =
          .failed (.selected paths fault) after saved := by
  constructor
  · intro suffix
    simp only [scan, primary, Outcome.bind, ite_true, secondary, Bool.false_eq_true, ite_false, query, decision]
  · intro fault
    rfl

end MicroCFTA.CurrentScanCallerChecks
