import MicroCFTA.SourceCurrentConjunctionDemandWorker
import MicroCFTA.SourceCurrentAllocatedConjunctionWorker

/-!
# Tuple-budget calls in the full checked state

The adapter lifts the actual tuple call into the existing checked outcome.
Failures retain the reached checked state and the initial fourth memo.
The native tables and domain cache remain unchanged. The selected caller uses actual demand admission. Native lazy execution
remains a separate correspondence boundary.
-/
namespace MicroCFTA.SourceCurrentAllocatedTupleConjunctionWorker
open InternedConstructorTemplates
open SourceCurrentAllocatedNativeEffects (physical)
open SourceCurrentAllocatedQueryMemo (advancePhysical)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Checked" => SourceEqualityNativeDemand.State
local notation "Physical" => SourceCurrentConjunctionRowsAllocation.State Symbol FullSyntax.Formula
local notation "Memo" => SourceCurrentEmptinessMemo.Memo
local notation "Fault" => SourceCurrentConjunctionWorker.Fault Symbol FullSyntax.Formula

/-- The tuple adapter uses the existing checked success and failure type. -/
abbrev Outcome (width : Nat) : Type 1 := SourceCurrentAllocatedConjunctionWorker.Outcome width

/-- Lift the literal physical call at its exact returned heap and operation cache. -/
noncomputable def call [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
    [DecidableEq (Value Symbol Guard)] (p h budget : Nat) (query : Value Symbol Guard)
    (before : Checked width) (memo : Memo) : Outcome width :=
  match SourceCurrentConjunctionDemandWorker.call p h budget memo query (physical before) with
  | .done (answer, saved) after => .done answer (advancePhysical before after) saved
  | .failed fault after => .failed fault (advancePhysical before after) memo

variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq (Value Symbol Guard)] {width : Nat}

/-- A warm hit ignores both execution bounds and retains the identical complete checked state. -/
theorem call_hit (p h budget : Nat) (query original : Value Symbol Guard) (before : Checked width)
    (memo : Memo) (answer : Bool) (found : memo query.referenceOf = some (original, answer)) :
    call p h budget query before memo = .done answer before memo := by
  have unchanged : advancePhysical before (physical before) = before := by cases before; rfl
  simp only [call, SourceCurrentConjunctionDemandWorker.call, found, unchanged]

/-- A completed physical call yields the same answer and full checked return. -/
theorem call_lift {p h budget : Nat} {query : Value Symbol Guard} {before : Checked width}
    {memo saved : Memo} {answer : Bool} {after : Physical}
    (done : SourceCurrentConjunctionDemandWorker.call p h budget memo query (physical before) = .done (answer, saved) after) :
    call p h budget query before memo = .done answer (advancePhysical before after) saved := by
  simp only [call, done]

/-- A physical failure retains its exact reached state and installs no fourth-memo entry. -/
theorem call_failed_lift {p h budget : Nat} {query : Value Symbol Guard} {before : Checked width}
    {memo : Memo} {fault : Fault} {after : Physical}
    (failed : SourceCurrentConjunctionDemandWorker.call p h budget memo query (physical before) = .failed fault after) :
    call p h budget query before memo = .failed fault (advancePhysical before after) memo := by
  simp only [call, failed]

/-- Each supplied checked success exposes its exact completed physical observation. -/
theorem call_done {p h budget : Nat} {query : Value Symbol Guard} {before after : Checked width}
    {memo saved : Memo} {answer : Bool}
    (done : call p h budget query before memo = .done answer after saved) :
    ∃ reached, SourceCurrentConjunctionDemandWorker.call p h budget memo query (physical before) = .done (answer, saved) reached ∧
      after = advancePhysical before reached := by
  cases observed : SourceCurrentConjunctionDemandWorker.call p h budget memo query (physical before) with
  | done output reached =>
      obtain ⟨result, current⟩ := output
      simp only [call, observed] at done
      obtain ⟨rfl, rfl, rfl⟩ := SourceCurrentAllocatedConjunctionWorker.Outcome.done.inj done
      exact ⟨reached, rfl, rfl⟩
  | failed fault reached => simp only [call, observed] at done; cases done

/-- Each checked failure exposes the same physical failure and the unchanged fourth memo. -/
theorem call_failed {p h budget : Nat} {query : Value Symbol Guard} {before after : Checked width}
    {memo saved : Memo} {fault : Fault}
    (failed : call p h budget query before memo = .failed fault after saved) :
    saved = memo ∧ ∃ reached,
      SourceCurrentConjunctionDemandWorker.call p h budget memo query (physical before) = .failed fault reached ∧
        after = advancePhysical before reached := by
  cases observed : SourceCurrentConjunctionDemandWorker.call p h budget memo query (physical before) with
  | done output reached =>
      obtain ⟨result, current⟩ := output
      simp only [call, observed] at failed
      cases failed
  | failed observedFault reached =>
      simp only [call, observed] at failed
      obtain ⟨rfl, rfl, rfl⟩ := SourceCurrentAllocatedConjunctionWorker.Outcome.failed.inj failed
      exact ⟨rfl, reached, rfl, rfl⟩

/-- A supplied successful call retains both complete native tables and the domain cache. -/
theorem call_tables {p h budget : Nat} {query : Value Symbol Guard} {before after : Checked width}
    {memo saved : Memo} {answer : Bool}
    (done : call p h budget query before memo = .done answer after saved) :
    after.native.nodes = before.native.nodes ∧ after.native.edges = before.native.edges ∧
      after.native.machine.domains = before.native.machine.domains := by
  obtain ⟨reached, _, rfl⟩ := call_done done
  exact SourceCurrentAllocatedQueryMemo.advance_tables before reached

end MicroCFTA.SourceCurrentAllocatedTupleConjunctionWorker
