import MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryDepth
import MicroCFTA.SourceCurrentAllocatedScanSourceReads
import MicroCFTA.SourceCurrentAllocatedGateWorker

/-!
# Current primary Scan on finite ordinary forests

Available coherent records take the literal metadata shortcut. Every
primary class is false at the same heap. The Scan selects all classes
in order and retains the complete checked state and all memo families.
-/
namespace MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryScan
open Cache InternedConstructorTemplates InternedProbeProvenance InternedRecordCoherence EqualityNormalize
open InternedNestedProvenance (Values)
open EndpointStatefulGateTrace
local notation "DNode" => SourceCurrentAllocatedFiniteOrdinaryDomain.Node
local notation "DChildren" => SourceCurrentAllocatedFiniteOrdinaryDomain.Children

section Generic
variable {Symbol Guard : Type} [DecidableEq (EdgeKey Symbol Guard)]
variable (unconstrained reaches : Value Symbol Guard → Bool)

/-- Every actual domain node query takes the false same-heap source branch. -/
theorem primary_node (state : State Symbol Guard) (coherent : Coherent state)
    (value : Value Symbol Guard) (available : Available state value) (domain : DNode value) (path : Path) :
    NodeTrace unconstrained reaches path value state false state := by
  cases domain with
  | empty => exact .empty
  | ordinary rows => exact .finite (SourceCurrentAllocatedFiniteOrdinaryDepth.fast state coherent _ available (.ordinary rows))

/-- A literal child lookup is missing or takes the same false node branch. -/
theorem primary_child (state : State Symbol Guard) (coherent : Coherent state)
    (values : List (Value Symbol Guard)) (available : Values state values) (domain : DChildren values)
    (index : Nat) (path : Path) : ChildTrace unconstrained reaches values index path state false state := by
  cases found : values[index]? with
  | none => exact .missing found
  | some value =>
      have member := List.mem_of_getElem? found
      exact .present found (primary_node unconstrained reaches state coherent value (available value member)
        (domain.member value member) path)

/-- Empty and nonempty forest paths both return false without changing the heap. -/
theorem primary_path (state : State Symbol Guard) (coherent : Coherent state)
    (values : List (Value Symbol Guard)) (available : Values state values) (domain : DChildren values) (path : Path) :
    PathTrace unconstrained reaches values path state false state := by
  cases path with
  | nil => exact .empty
  | cons index rest => exact .child (primary_child unconstrained reaches state coherent values available domain index rest)

/-- The actual ordered primary class visits every path and retains its heap. -/
theorem primary_class (state : State Symbol Guard) (coherent : Coherent state)
    (values : List (Value Symbol Guard)) (available : Values state values) (domain : DChildren values) (paths : Class) :
    ClassTrace unconstrained reaches values paths state false state := by
  induction paths with
  | nil => exact .nil
  | cons path paths ih => exact .next (primary_path unconstrained reaches state coherent values available domain path) ih

/-- Any supplied primary class trace has that same false answer and heap. -/
theorem primary_class_verified {state final : State Symbol Guard} {values : List (Value Symbol Guard)}
    {paths : Class} {answer : Bool} (actual : ClassTrace unconstrained reaches values paths state answer final)
    (coherent : Coherent state) (available : Values state values) (domain : DChildren values) :
    answer = false ∧ final = state :=
  class_trace_unique unconstrained reaches values paths state answer false final state actual
    (primary_class unconstrained reaches state coherent values available domain paths)

/-- One or more gate steps execute the literal fast node branch at the same heap. -/
theorem primary_node_done (fuel : Nat) (state : State Symbol Guard) (coherent : Coherent state)
    (value : Value Symbol Guard) (available : Available state value) (domain : DNode value) (path : Path) :
    EndpointStatefulGate.nodeMeets unconstrained reaches (fuel + 1) path value state = .done (some false) state := by
  have fast := SourceCurrentAllocatedFiniteOrdinaryDepth.fast state coherent value available domain
  cases domain with
  | empty => rfl
  | ordinary rows =>
      simp only [Value.depth, Value.free] at fast
      simp only [EndpointStatefulGate.nodeMeets, EndpointStatefulGate.dispatch,
        Value.depth, Value.free, fast, ite_true]

/-- Literal path lookup completes with one or more gate steps, including absent positions. -/
theorem primary_path_done (fuel : Nat) (state : State Symbol Guard) (coherent : Coherent state)
    (values : List (Value Symbol Guard)) (available : Values state values) (domain : DChildren values) (path : Path) :
    EndpointStatefulGate.meets unconstrained reaches (fuel + 1) values path state = .done (some false) state := by
  cases path with
  | nil => rfl
  | cons index rest =>
      cases found : values[index]? with
      | none => simp only [EndpointStatefulGate.meets, InternedFreshOrdinaryStatefulGate.child, found]
      | some value =>
          simpa only [EndpointStatefulGate.meets, InternedFreshOrdinaryStatefulGate.child, found] using
            primary_node_done unconstrained reaches fuel state coherent value (available value (List.mem_of_getElem? found))
              (domain.member value (List.mem_of_getElem? found)) rest

/-- The literal class worker uses the same fixed positive gate budget for every ordered path. -/
theorem primary_class_done (fuel : Nat) (state : State Symbol Guard) (coherent : Coherent state)
    (values : List (Value Symbol Guard)) (available : Values state values) (domain : DChildren values) (paths : Class) :
    EndpointStatefulGate.classMeets unconstrained reaches (fuel + 1) values paths state = .done (some false) state := by
  unfold EndpointStatefulGate.classMeets
  induction paths with
  | nil => rfl
  | cons path paths ih =>
      rw [InternedFreshOrdinaryStatefulGate.anyKnown, primary_path_done unconstrained reaches fuel state coherent values available domain path]
      exact ih

end Generic

local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Memos" => EndpointMemoGateTrace.Memos
local notation "Memo" => SourceCurrentEmptinessMemo.Memo
local notation "sourceGate" => SourceMemoGate.unconstrained
local notation "sourceReaches" => SourceEndpointReachability.reaches sourceGate
open SourceCurrentAllocatedPrimaryReads
open SourceCurrentConjunctionClassScan (Scan Ready advanceHeap)
variable [DecidableEq (EdgeKey Symbol Guard)] {width : Nat}

/-- The strict source receipt for a domain node performs no memo operation. -/
theorem primary_node_reads (state : State Symbol Guard) (coherent : Coherent state)
    (value : Value Symbol Guard) (available : Available state value) (domain : DNode value) (path : Path) (memos : Memos) :
    NodeReads (primary_node sourceGate sourceReaches state coherent value available domain path) memos memos := by
  cases domain with
  | empty => exact .empty
  | ordinary rows => exact .finite (SourceCurrentAllocatedFiniteOrdinaryDepth.fast state coherent _ available (.ordinary rows))

/-- Strict child reads retain all three global memo tables. -/
theorem primary_child_reads (state : State Symbol Guard) (coherent : Coherent state)
    (values : List (Value Symbol Guard)) (available : Values state values) (domain : DChildren values)
    (index : Nat) (path : Path) (memos : Memos) :
    ChildReads (primary_child sourceGate sourceReaches state coherent values available domain index path) memos memos := by
  cases found : values[index]? with
  | none => exact .missing found
  | some value => exact .present found (primary_node_reads state coherent value (available value (List.mem_of_getElem? found))
      (domain.member value (List.mem_of_getElem? found)) path memos)

/-- Strict path reads retain the same complete global bundle. -/
theorem primary_path_reads (state : State Symbol Guard) (coherent : Coherent state)
    (values : List (Value Symbol Guard)) (available : Values state values) (domain : DChildren values) (path : Path) (memos : Memos) :
    PathReads (primary_path sourceGate sourceReaches state coherent values available domain path) memos memos := by
  cases path with
  | nil => exact .empty
  | cons index rest => exact .child (primary_child_reads state coherent values available domain index rest memos)

/-- Strict ordered class reads retain all three memo families without a predicate call. -/
theorem primary_class_reads (state : State Symbol Guard) (coherent : Coherent state)
    (values : List (Value Symbol Guard)) (available : Values state values) (domain : DChildren values) (paths : Class) (memos : Memos) :
    ClassReads (primary_class sourceGate sourceReaches state coherent values available domain paths) memos memos := by
  induction paths with
  | nil => exact .nil
  | cons path paths ih => exact .next (primary_path_reads state coherent values available domain path memos) ih

omit [DecidableEq (EdgeKey Symbol Guard)] in
/-- Reusing the current constructor heap is the identity on the full checked state. -/
theorem advanceHeap_self (state : Checked width) : advanceHeap state state.native.machine.heap = state := by
  cases state with
  | mk native operations => cases native <;> rfl

/-- The current checked primary worker completes at every positive fuel without changing any state field. -/
theorem primary_done (fuel : Nat) (values : List (Value Symbol Guard)) (paths : Class) (before : Checked width)
    (ready : Ready before) (available : Values before.native.machine.heap values) (domain : DChildren values) :
    SourceCurrentAllocatedGateWorker.primary (fuel + 1) values paths before = .done false before := by
  simp only [SourceCurrentAllocatedGateWorker.primary, SourceCurrentMuEndpoint.primary_class,
    primary_class_done sourceGate sourceReaches fuel before.native.machine.heap ready.good.native.machine.1.coherent values available domain paths,
    SourceCurrentAllocatedGateWorker.lift, advanceHeap_self]

variable [DecidableEq Symbol] [DecidableEq (Value Symbol Guard)]

/-- Any actual Scan selects the complete class list and retains its full state and fourth memo. -/
theorem scan {budget : Nat} {values : List (Value Symbol Guard)} {classes selected : Constraints}
    {before after : Checked width} {memo saved : Memo} {outcome : Option Class}
    (actual : Scan budget sourceGate sourceReaches values classes before memo outcome selected after saved)
    (ready : Ready before) (available : Values before.native.machine.heap values) (domain : DChildren values) :
    outcome = none ∧ selected = classes ∧ after = before ∧ saved = memo := by
  induction actual with
  | nil => exact ⟨rfl, rfl, rfl, rfl⟩
  | selected primary rest ih =>
      have same := primary_class_verified sourceGate sourceReaches primary
        ready.good.native.machine.1.coherent available domain
      rcases same with ⟨_, rfl⟩
      rw [advanceHeap_self] at ih
      obtain ⟨outcome, selected, after, memo⟩ := ih ready available
      exact ⟨outcome, congrArg (List.cons _) selected, after, memo⟩
  | skipped primary secondary rest ih =>
      have impossible := (primary_class_verified sourceGate sourceReaches primary
        ready.good.native.machine.1.coherent available domain).1
      cases impossible
  | continued primary secondary seeded decision rest ih =>
      have impossible := (primary_class_verified sourceGate sourceReaches primary
        ready.good.native.machine.1.coherent available domain).1
      cases impossible
  | stopped primary secondary seeded decision =>
      have impossible := (primary_class_verified sourceGate sourceReaches primary
        ready.good.native.machine.1.coherent available domain).1
      cases impossible

/-- Initial available domain inputs construct an actual selected-only Scan and strict unchanged-bundle reads. -/
theorem construct (budget : Nat) (values : List (Value Symbol Guard)) (classes : Constraints)
    (before : Checked width) (memo : Memo) (ready : Ready before)
    (available : Values before.native.machine.heap values) (domain : DChildren values) (memos : Memos) :
    ∃ actual : Scan budget sourceGate sourceReaches values classes before memo none classes before memo,
      SourceCurrentAllocatedScanSourceReads.ScanReads actual memos memos := by
  induction classes with
  | nil => exact ⟨.nil, .nil⟩
  | cons paths classes ih =>
      obtain ⟨tail, reads⟩ := ih
      let first := primary_class sourceGate sourceReaches before.native.machine.heap
        ready.good.native.machine.1.coherent values available domain paths
      have rest : Scan budget sourceGate sourceReaches values classes
          (advanceHeap before before.native.machine.heap) memo none classes before memo := by
        simpa only [advanceHeap_self] using tail
      refine ⟨.selected first rest, .selected (primary := first) (rest := rest) (middle := memos) ?_ ?_⟩
      · exact primary_class_reads _ ready.good.native.machine.1.coherent values available domain paths memos
      · simpa only [advanceHeap_self] using reads

/-- A supplied actual Scan admits strict receipts at the unchanged global bundle. -/
theorem verified {budget : Nat} {values : List (Value Symbol Guard)} {classes selected : Constraints}
    {before after : Checked width} {memo saved : Memo} {outcome : Option Class}
    (actual : Scan budget sourceGate sourceReaches values classes before memo outcome selected after saved)
    (ready : Ready before) (available : Values before.native.machine.heap values) (domain : DChildren values) (memos : Memos) :
    outcome = none ∧ selected = classes ∧ after = before ∧ saved = memo ∧
      SourceCurrentAllocatedScanSourceReads.ScanReads actual memos memos := by
  obtain ⟨outcomeSame, selectedSame, afterSame, memoSame⟩ := scan actual ready available domain
  subst outcome selected after saved
  obtain ⟨constructed, reads⟩ := construct budget values classes before memo ready available domain memos
  exact ⟨rfl, rfl, rfl, rfl, reads⟩

end MicroCFTA.SourceCurrentAllocatedFiniteOrdinaryScan
