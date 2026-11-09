import MicroCFTA.SourceCurrentConjunctionSharedWorkerOutcomeMemos
import MicroCFTA.SourceCurrentAllocatedQueryMemo

/-!
# Checked shared calls retain their actual private snapshot

The checked adapter retains the shared fault and entire worklist snapshot.
Both outcomes advance the checked state with that same physical endpoint.
A failed call retains the incoming fourth memo. The raw observation can be
reconstructed exactly. Existing caller selection remains separate.
-/
namespace MicroCFTA.SourceCurrentAllocatedSharedConjunctionWorker
open InternedConstructorTemplates (Value EdgeKey)
open SourceCurrentAllocatedNativeEffects (physical)
open SourceCurrentAllocatedQueryMemo (advancePhysical)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Snapshot" => SourceCurrentConjunctionSharedWorklistStep.State Symbol FullSyntax.Formula
local notation "Memo" => SourceCurrentEmptinessMemo.Memo
local notation "Fault" => SourceCurrentConjunctionSharedWorker.Fault Symbol FullSyntax.Formula
local notation "Raw" => SourceCurrentConjunctionSharedWorker.Outcome Symbol FullSyntax.Formula (Bool × Memo)

/-- Both checked outcomes retain the entire actual shared observation. -/
inductive Outcome (width : Nat) : Type 1 where
  | done (answer : Bool) (checked : Checked width) (memo : Memo) (snapshot : Snapshot)
  | failed (fault : Fault) (checked : Checked width) (memo : Memo) (snapshot : Snapshot)

/-- Read the complete checked endpoint on success or failure. -/
def Outcome.state : Outcome width → Checked width
  | .done _ checked _ _ | .failed _ checked _ _ => checked

/-- Read the actual returned fourth memo on either outcome. -/
def Outcome.memo : Outcome width → Memo
  | .done _ _ memo _ | .failed _ _ memo _ => memo

/-- Read the exact private cells, row streams, task queue and physical endpoint. -/
def Outcome.snapshot : Outcome width → Snapshot
  | .done _ _ _ snapshot | .failed _ _ _ snapshot => snapshot

/-- Reconstruct the unchanged shared observation, including its full diagnostic. -/
def Outcome.raw : Outcome width → Raw
  | .done answer _ memo snapshot => .done (answer, memo) snapshot
  | .failed fault _ _ snapshot => .failed fault snapshot

/-- Advance checked fields from the literal shared call without discarding its private state. -/
noncomputable def call [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Node]
    (p h budget : Nat) (query : Node) (before : Checked width) (memo : Memo) : Outcome width :=
  match SourceCurrentConjunctionSharedWorker.call p h budget memo query (physical before) with
  | .done (answer, saved) after =>
      .done answer (advancePhysical before after.storage.requirements.physical) saved after
  | .failed fault after =>
      .failed fault (advancePhysical before after.storage.requirements.physical) memo after

variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Node] {width : Nat}

/-- The adapter reconstructs the identical complete shared observation on every outcome. -/
theorem call_observation (p h budget : Nat) (query : Node) (before : Checked width) (memo : Memo) :
    (call p h budget query before memo).raw =
      SourceCurrentConjunctionSharedWorker.call p h budget memo query (physical before) := by
  unfold call
  cases observed : SourceCurrentConjunctionSharedWorker.call p h budget memo query (physical before) with
  | done result after => cases result; rfl
  | failed fault after => rfl

/-- The retained private snapshot is exactly the original worker endpoint. -/
theorem call_snapshot (p h budget : Nat) (query : Node) (before : Checked width) (memo : Memo) :
    (call p h budget query before memo).snapshot =
      (SourceCurrentConjunctionSharedWorker.call p h budget memo query (physical before)).state := by
  unfold call
  cases observed : SourceCurrentConjunctionSharedWorker.call p h budget memo query (physical before) with
  | done result after => cases result; rfl
  | failed fault after => rfl

/-- Both checked endpoints advance the same retained physical component. -/
theorem call_state (p h budget : Nat) (query : Node) (before : Checked width) (memo : Memo) :
    (call p h budget query before memo).state = advancePhysical before
      (call p h budget query before memo).snapshot.storage.requirements.physical := by
  unfold call
  cases observed : SourceCurrentConjunctionSharedWorker.call p h budget memo query (physical before) with
  | done result after => cases result; rfl
  | failed fault after => rfl

/-- Failed calls retain the incoming fourth memo; successful calls retain the actual saved memo. -/
theorem call_memo (p h budget : Nat) (query : Node) (before : Checked width) (memo : Memo) :
    (call p h budget query before memo).memo =
      SourceCurrentConjunctionSharedWorkerOutcomeMemos.returnedMemo memo
        (SourceCurrentConjunctionSharedWorker.call p h budget memo query (physical before)) := by
  unfold call
  cases observed : SourceCurrentConjunctionSharedWorker.call p h budget memo query (physical before) with
  | done result after => cases result; rfl
  | failed fault after => rfl

/-- A fourth-memo hit retains the checked state and its empty initial private snapshot. -/
theorem call_hit (p h budget : Nat) (query original : Node) (before : Checked width)
    (memo : Memo) (answer : Bool) (found : memo query.referenceOf = some (original, answer)) :
    call p h budget query before memo = .done answer before memo
      (SourceCurrentConjunctionSharedWorklistStep.initial budget query (physical before)) := by
  have unchanged : advancePhysical before (physical before) = before := by cases before; rfl
  unfold call
  rw [SourceCurrentConjunctionSharedWorker.call_hit p h budget memo query original (physical before) answer found]
  change Outcome.done answer (advancePhysical before (physical before)) memo
    (SourceCurrentConjunctionSharedWorklistStep.initial budget query (physical before)) = _
  rw [unchanged]

/-- The same successful raw observation supplies its exact checked and private endpoints. -/
theorem call_lift {p h budget : Nat} {query : Node} {before : Checked width}
    {memo saved : Memo} {answer : Bool} {snapshot : Snapshot}
    (actual : SourceCurrentConjunctionSharedWorker.call p h budget memo query (physical before) =
      .done (answer, saved) snapshot) :
    call p h budget query before memo =
      .done answer (advancePhysical before snapshot.storage.requirements.physical) saved snapshot := by
  simp only [call, actual]

/-- The same failed raw observation retains its original fault, incoming memo and complete snapshot. -/
theorem call_failed_lift {p h budget : Nat} {query : Node} {before : Checked width}
    {memo : Memo} {fault : Fault} {snapshot : Snapshot}
    (actual : SourceCurrentConjunctionSharedWorker.call p h budget memo query (physical before) = .failed fault snapshot) :
    call p h budget query before memo =
      .failed fault (advancePhysical before snapshot.storage.requirements.physical) memo snapshot := by
  simp only [call, actual]

/-- Every checked success exposes that same complete raw call and exact checked update. -/
theorem call_done {p h budget : Nat} {query : Node} {before after : Checked width}
    {memo saved : Memo} {answer : Bool} {snapshot : Snapshot}
    (actual : call p h budget query before memo = .done answer after saved snapshot) :
    SourceCurrentConjunctionSharedWorker.call p h budget memo query (physical before) =
        .done (answer, saved) snapshot ∧
      after = advancePhysical before snapshot.storage.requirements.physical := by
  have observed := call_observation p h budget query before memo
  have advanced := call_state p h budget query before memo
  rw [actual] at observed advanced
  exact ⟨observed.symm, advanced⟩

/-- Every checked failure retains its exact raw fault, private snapshot and unchanged fourth memo. -/
theorem call_failed {p h budget : Nat} {query : Node} {before after : Checked width}
    {memo saved : Memo} {fault : Fault} {snapshot : Snapshot}
    (actual : call p h budget query before memo = .failed fault after saved snapshot) :
    saved = memo ∧
      SourceCurrentConjunctionSharedWorker.call p h budget memo query (physical before) = .failed fault snapshot ∧
      after = advancePhysical before snapshot.storage.requirements.physical := by
  have observed := call_observation p h budget query before memo
  have advanced := call_state p h budget query before memo
  have retained := call_memo p h budget query before memo
  rw [actual] at observed advanced retained
  have raw : SourceCurrentConjunctionSharedWorker.call p h budget memo query (physical before) =
      .failed fault snapshot := observed.symm
  rw [raw] at retained
  exact ⟨retained, raw, advanced⟩

/-- Every outcome retains the same native tables and domain cache. -/
theorem call_tables (p h budget : Nat) (query : Node) (before : Checked width) (memo : Memo) :
    let after := (call p h budget query before memo).state
    after.native.nodes = before.native.nodes ∧ after.native.edges = before.native.edges ∧
      after.native.machine.domains = before.native.machine.domains := by
  rw [call_state]
  exact SourceCurrentAllocatedQueryMemo.advance_tables before _

end MicroCFTA.SourceCurrentAllocatedSharedConjunctionWorker
