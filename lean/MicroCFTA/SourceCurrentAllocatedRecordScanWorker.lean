import MicroCFTA.SourceCurrentAllocatedScanWorker
import MicroCFTA.SourceEqualityClassOrder

/-!
# Literal current scanning with original class records

Each selected branch retains its literal input record. The gate, query,
and decision calls use the same paths and checked states as the path worker.
Path projection preserves every outcome, including failed selected prefixes.
Repeated path lists need no record uniqueness law.
-/
namespace MicroCFTA.SourceCurrentAllocatedRecordScanWorker
open Language EqualityNormalize InternedConstructorTemplates
open SourceEqualityClassOrder
open SourceCurrentAllocatedScanWorker (gate query decision)
local notation "Symbol" => SourceObservations.Label FullSyntax.Formula
local notation "Guard" => SourceSymbolicIndex.Constraint FullSyntax.Formula

abbrev Checked := SourceCurrentAllocatedScanWorker.Checked
abbrev Memo := SourceCurrentAllocatedScanWorker.Memo
abbrev Outcome := SourceCurrentAllocatedScanWorker.Outcome
abbrev Result := Option Class × List Record

/-- Project selected records without changing a stopped class or failed observation. -/
def mapPaths : Outcome Result width → Outcome SourceCurrentAllocatedScanWorker.Result width
  | .done (stopped, selected) state memo => .done (stopped, selected.map Record.paths) state memo
  | .failed fault state memo => .failed fault state memo

/-- Selection retains the literal head record or the same failed path prefix. -/
def select (record : Record) : Outcome Result width → Outcome Result width
  | .done (stopped, selected) state memo => .done (stopped, record :: selected) state memo
  | .failed fault state memo => .failed (.selected record.paths fault) state memo

/-- Path projection commutes with an exact successful prefix and retains failed prefixes. -/
theorem mapPaths_bind (first : Outcome A width)
    (next : A → Checked width → Memo → Outcome Result width) :
    mapPaths (first.bind next) = first.bind (fun value state memo => mapPaths (next value state memo)) := by
  cases first <;> rfl

/-- The selected record contributes exactly its paths to either returned prefix. -/
theorem mapPaths_select (record : Record) (first : Outcome Result width) :
    mapPaths (select record first) = (mapPaths first).select record.paths := by
  cases first with
  | done result => cases result; rfl
  | failed => rfl

variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Guard)]
  [DecidableEq (Value Symbol Guard)]

/-- Run each reached stage once and retain the selected input record occurrences. -/
noncomputable def scan (g s p h n budget : Nat) (values : List (Value Symbol Guard)) :
    List Record → Checked width → Memo → Outcome Result width
  | [], before, memo => .done (none, []) before memo
  | record :: records, before, memo =>
      (gate true g values record.paths before memo).bind fun primary middle current =>
        if primary then
          (gate false s values record.paths middle current).bind fun secondary later saved =>
            if secondary then scan g s p h n budget values records later saved
            else (query p h n values record.paths later saved).bind fun value checked fourth =>
              (decision p h budget record.paths value checked fourth).bind fun answer after final =>
                if answer then .done (some record.paths, []) after final
                else scan g s p h n budget values records after final
        else select record (scan g s p h n budget values records middle current)

/-- Empty input retains the complete checked state and fourth memo at every bound. -/
theorem scan_nil (g s p h n budget : Nat) (values : List (Value Symbol Guard))
    (before : Checked width) (memo : Memo) :
    scan g s p h n budget values [] before memo = .done (none, []) before memo := rfl

/-- Every full outcome projects to the path worker at the same five bounds. -/
theorem scan_mapPaths (g s p h n budget : Nat) (values : List (Value Symbol Guard))
    (records : List Record) (before : Checked width) (memo : Memo) :
    mapPaths (scan g s p h n budget values records before memo) =
      SourceCurrentAllocatedScanWorker.scan g s p h n budget values (records.map Record.paths) before memo := by
  induction records generalizing before memo with
  | nil => rfl
  | cons record records ih =>
      simp only [scan, List.map_cons, SourceCurrentAllocatedScanWorker.scan, mapPaths_bind]
      congr 1
      funext primary middle current
      cases primary with
      | false => exact (mapPaths_select record _).trans (congrArg (fun result => result.select record.paths) (ih middle current))
      | true =>
          simp only [ite_true, mapPaths_bind]
          congr 1
          funext secondary later saved
          cases secondary with
          | true => exact ih later saved
          | false =>
              simp only [Bool.false_eq_true, ite_false, mapPaths_bind]
              congr 1
              funext value checked fourth
              congr 1
              funext answer after final
              cases answer with
              | true => rfl
              | false => exact ih after final

end MicroCFTA.SourceCurrentAllocatedRecordScanWorker
