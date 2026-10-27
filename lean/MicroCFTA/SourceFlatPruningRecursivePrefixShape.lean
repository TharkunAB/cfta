import MicroCFTA.SourceFlatPruningRecursiveBase
import MicroCFTA.SourceFlatPruningSelectedPrefixReplay

/-!
# Shapes retained by actual flat selected-prefix replay

Each statement reads an existing ordered observation relation.
It does not execute a second prefix or supply a future completion premise.
-/
namespace MicroCFTA.SourceFlatPruningRecursivePrefixShape
open EnumerationState InternedConstructorTemplates
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Core" => EnumerationState.State Symbol Constraint
local notation "FlatCore" => EnumerationFlatState.State Symbol Constraint
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "FlatCached" => EnumerationFlatCached.Cached Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Queries" => SourceEndpointMemo.Memos
local notation "Metadata" => SourcePruningRecordTypes.Metadata
local notation "Observed" => SourceFlatPruningSelectedPrefix.Result
local notation "Prepared" => MergedSourceComparison.Result Symbol Constraint
  (Node × Option (EnumerateM Symbol Constraint Unit))
variable {Typing : Type} {width : Nat}

/-- An ordered relation to empty rows forces empty actual rows. -/
theorem rows_nil {α : Type} {raw : List (Except Error (α × FlatCore))}
    (related : EnumerationResultRelation.Results EnumerationFlatState.Related raw []) : raw = [] := by
  cases related
  rfl

/-- An ordered successful singleton retains its value and related actual core. -/
theorem rows_singleton {α : Type} {value : α} {after : Core}
    {raw : List (Except Error (α × FlatCore))}
    (related : EnumerationResultRelation.Results EnumerationFlatState.Related raw [.ok (value, after)]) :
    ∃ flatAfter, raw = [.ok (value, flatAfter)] ∧ EnumerationFlatState.Related flatAfter after := by
  cases related with
  | cons first rest =>
      cases rest
      cases first with
      | ok _value states => exact ⟨_, rfl, states⟩

/-- Related parked prefixes retain a present cache and every actual restart row. -/
theorem parked (observed : Observed width Typing) (checked : Core) (after : Cached)
    (raw : List (Except Error ((Metadata Typing × Option Next) × Core)))
    (related : SourceFlatPruningSelectedPrefix.ResultRelated observed
      (.parked checked (some after) (some raw))) :
    ∃ flatChecked flatAfter flatRaw,
      observed = .parked flatChecked (some flatAfter) (some flatRaw) ∧
      EnumerationFlatCached.Related flatAfter after ∧
      EnumerationResultRelation.Results EnumerationFlatState.Related flatRaw raw := by
  cases observed with
  | stopped _ _ | narrowed _ _ _ _ _ _ _ => cases related
  | parked flatChecked candidate restart =>
      obtain ⟨_checked, caches, rows⟩ := related
      cases candidate with
      | none => cases caches
      | some flatAfter =>
          cases restart with
          | none => cases rows
          | some flatRaw => exact ⟨flatChecked, flatAfter, flatRaw, rfl, caches, rows⟩

/-- An actual Empty prefix keeps its native endpoint and empty action rows. -/
theorem rejected (observed : Observed width Typing) (checked : Core) (prepared : Prepared)
    (caller : Caller width) (queries : Queries)
    (related : SourceFlatPruningSelectedPrefix.ResultRelated observed
      (.narrowed checked prepared caller queries (some []) none none none)) :
    ∃ flatChecked flatPrepared,
      observed = .narrowed flatChecked flatPrepared caller queries (some []) none none := by
  cases observed with
  | stopped _ _ | parked _ _ _ => cases related
  | narrowed flatChecked flatPrepared flatCaller flatQueries action candidate right =>
      obtain ⟨_checked, _prepared, callerSame, queriesSame, rows, caches, rightRows, _ordinary⟩ := related
      subst flatCaller flatQueries
      cases candidate with
      | some _ => cases caches
      | none =>
          cases right with
          | some _ => cases rightRows
          | none =>
              cases action with
              | none => cases rows
              | some flatRaw =>
                  obtain rfl := rows_nil rows
                  exact ⟨flatChecked, flatPrepared, rfl⟩

/-- A related accepted prefix keeps its candidate and both successful singleton observations. -/
theorem accepted (observed : Observed width Typing) (checked : Core) (prepared : Prepared)
    (caller : Caller width) (queries : Queries) (after : Cached) (metadata : Metadata Typing)
    (related : SourceFlatPruningSelectedPrefix.ResultRelated observed
      (.narrowed checked prepared caller queries (some [.ok ((), after.core)]) (some after)
        (some [.ok ((false, metadata), after.core)]) none)) :
    ∃ flatChecked flatPrepared actionCore flatAfter rightCore,
      observed = .narrowed flatChecked flatPrepared caller queries
        (some [.ok ((), actionCore)]) (some flatAfter) (some [.ok ((false, metadata), rightCore)]) ∧
      EnumerationFlatCached.Related flatAfter after := by
  cases observed with
  | stopped _ _ | parked _ _ _ => cases related
  | narrowed flatChecked flatPrepared flatCaller flatQueries action candidate right =>
      obtain ⟨_checked, _prepared, callerSame, queriesSame, rows, caches, rightRows, _ordinary⟩ := related
      subst flatCaller flatQueries
      cases candidate with
      | none => cases caches
      | some flatAfter =>
          cases action with
          | none => cases rows
          | some flatRaw =>
              obtain ⟨actionCore, rfl, _actionStates⟩ := rows_singleton rows
              cases right with
              | none => cases rightRows
              | some flatRight =>
                  obtain ⟨rightCore, rfl, _rightStates⟩ := rows_singleton rightRows
                  exact ⟨flatChecked, flatPrepared, actionCore, flatAfter, rightCore, rfl, caches⟩

end MicroCFTA.SourceFlatPruningRecursivePrefixShape
