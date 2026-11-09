import MicroCFTA.SourceCurrentConjunctionTuplePullTotalOutcomeMemos
import MicroCFTA.SourceCurrentAllocatedReadDeterminism

/-!
# Exact memo tables through finite tuple observations

Fixed cursor inputs determine each returned global table. A completed
observation adds no reads when its transition allowance increases.
Two observations of the same total sample therefore retain the same
memo bundle. Heap endpoint equality alone is not used for this result.
-/
namespace MicroCFTA.SourceCurrentOutcomeCursorReadDeterminism
open Cache InternedConstructorTemplates
open SourceCurrentConjunctionRowsWorker (Outcome)
open SourceCurrentConjunctionTuplePull (Cursor)
open SourceCurrentConjunctionTuplePullAdmission (advance drive)
open SourceCurrentConjunctionTuplePullTotal (observe)
open SourceCurrentConjunctionTuplePullTotalOutcomeMemos (DriveReads SampleReads)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Guard
local notation "Edge" => EdgeValue Symbol Guard
local notation "Physical" => SourceCurrentConjunctionRowsWorker.Physical Symbol FullSyntax.Formula
local notation "Memos" => EndpointMemoGateTrace.Memos
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]

omit [DecidableEq Symbol] in
private theorem exposure_unique {h : Nat} {node : Node}
    {heap : State Symbol Guard} {memos first second : Memos}
    (left : SourceEqualityQueryGlobalMemos.ExposureReads h node heap memos first)
    (right : SourceEqualityQueryGlobalMemos.ExposureReads h node heap memos second) :
    first = second := by
  have unfolding := SourceCurrentAllocatedReadDeterminism.exposure_unique left.1 right.1
  have query := left.2.trans right.2.symm
  cases first
  cases second
  cases unfolding
  cases query
  rfl

omit [DecidableEq Symbol] in
private theorem step_unique {h : Nat} {cursor : Cursor Symbol FullSyntax.Formula}
    {before : Physical} {memos first second : Memos}
    (left : SourceCurrentConjunctionTuplePullOutcomeMemos.StepReads h cursor before memos first)
    (right : SourceCurrentConjunctionTuplePullOutcomeMemos.StepReads h cursor before memos second) :
    first = second := by
  induction cursor generalizing before memos first second with
  | extend edges inner ih => exact ih left right
  | readOperand node rest edges =>
      cases edges with
      | nil => exact left.trans right.symm
      | cons => exact exposure_unique left right
  | seed => exact exposure_unique left right
  | empty | seedRows | scanOperand => exact left.trans right.symm

private theorem drive_unique {h budget steps : Nat} {cursor : Cursor Symbol FullSyntax.Formula}
    {collected : List (List Edge)} {before : Physical} {memos first second : Memos}
    (left : DriveReads h budget steps cursor collected before memos first)
    (right : DriveReads h budget steps cursor collected before memos second) : first = second := by
  induction steps generalizing cursor collected before memos first second with
  | zero => cases left; cases right; rfl
  | succ steps ih =>
      cases left <;> cases right <;> try simp_all
      all_goals first
        | exact step_unique (by assumption) (by assumption)
        | rename_i middleA nextA sampledA memoA middleB nextB sampledB memoB
            actualA callsA tailA actualB callsB tailB
          have same : memoA = memoB := step_unique callsA callsB
          cases same
          exact ih tailA tailB

private theorem drive_extend {h budget steps : Nat} {cursor : Cursor Symbol FullSyntax.Formula}
    {collected : List (List Edge)} {before : Physical} {memos saved : Memos}
    {terminal : Outcome Symbol FullSyntax.Formula (SourceCurrentConjunctionTuplePullTotal.Result Symbol FullSyntax.Formula)}
    (reads : DriveReads h budget steps cursor collected before memos saved)
    (completed : drive steps h budget cursor collected before = observe terminal) (extra : Nat) :
    DriveReads h budget (steps + extra) cursor collected before memos saved := by
  revert completed
  induction reads with
  | zero =>
      intro completed
      cases terminal with
      | failed => cases completed
      | done result after => cases result <;> cases completed
  | failed actual calls =>
      intro _
      simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        (DriveReads.failed (steps := _ + extra) actual calls)
  | fit actual calls =>
      intro _
      simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        (DriveReads.fit (steps := _ + extra) actual calls)
  | overflow actual calls =>
      intro _
      simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        (DriveReads.overflow (steps := _ + extra) actual calls)
  | running actual calls tail ih =>
      intro completed
      simp only [drive, actual, Outcome.bind] at completed
      have later := ih completed
      simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        (DriveReads.running actual calls later)

/-- Two actual observations of one total sample retain the same global bundle. -/
theorem sample_unique {h budget : Nat} {nodes : List Node} {before : Physical}
    {memos first second : Memos}
    (left : SampleReads h budget nodes before memos first)
    (right : SampleReads h budget nodes before memos second) : first = second := by
  obtain ⟨a,completedA,readsA⟩ := left
  obtain ⟨b,completedB,readsB⟩ := right
  have extendedA := drive_extend readsA completedA b
  have extendedB := drive_extend readsB completedB a
  rw [Nat.add_comm b a] at extendedB
  exact drive_unique extendedA extendedB

end MicroCFTA.SourceCurrentOutcomeCursorReadDeterminism
