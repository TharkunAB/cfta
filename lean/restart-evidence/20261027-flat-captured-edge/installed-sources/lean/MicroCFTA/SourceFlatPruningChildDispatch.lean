import MicroCFTA.SourceFlatPruningCachedPrepare
import MicroCFTA.EnumerationFlatNativeTerminal
import MicroCFTA.SourcePruningEnumerationChildDispatch

/-!
# Actual native child dispatch with direct-parent forests

The dispatcher preserves shallow preparation and terminal equality merging.
It retains the raw observation separately from optional cache recovery.
-/

namespace MicroCFTA.SourceFlatPruningChildDispatch

open EnumerationState InternedConstructorTemplates
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Queries" => SourceEndpointMemo.Memos
local notation "Cached" => EnumerationFlatCached.Cached Symbol Constraint
local notation "Core" => EnumerationFlatState.State Symbol Constraint
local notation "PrefixRaw" => List (Except Error ((List Nat × Nat × EnumerationWaitingIndex.Waiting) × Core))
local notation "FoldRaw" => List (Except Error (Unit × Core))
local notation "TerminalRaw" => List (Except Error (Fragments.Fragment Symbol × Core))
variable {width : Nat}

/-- Retain the complete actual child observation and its reached native endpoint. -/
abbrev Observation (width : Nat) :=
  (Except (PrefixRaw ⊕ ((SourceEqualityNativeDemand.Outcome width Node ⊕
    SourceCurrentAllocatedConjunctionWorker.Outcome width) ⊕ FoldRaw)) (Option TerminalRaw)) ×
    Caller width × Queries × Core × EnumerationWaitingIndex.Waiting

variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]

/-- Dispatch each actual partition and keep raw rows separate from cache recovery. -/
noncomputable def run (checkEmpty : Bool) (nativeFuel p h : Nat)
    (scs : List Suspended) (incoming : Node) (caller : Caller width) (before : Cached)
    (queries : Queries) : Observation width × Option Cached :=
  if incoming = .empty then
    ((.ok (some []), caller, queries, before.core, before.waiting), some before)
  else
    match scs.partition (fun sc => EqualityTrie.isTerminal sc.trie) with
    | ([], _) =>
        let observed : Observation width :=
          match SourceFlatPruningShallowChild.prepareChild scs incoming with
          | none => (.ok none, caller, queries, before.core, before.waiting)
          | some action => (.ok (some (action before.core)), caller, queries, before.core, before.waiting)
        (observed,
          match SourceFlatPruningCachedPrepare.prepareChild caller.checked.native.machine.heap scs incoming before with
          | some [] => some before
          | some [(_, after)] => some after
          | _ => none)
    | (first :: rest, descendants) =>
        EnumerationFlatNativeTerminal.run checkEmpty nativeFuel p h first rest caller before incoming descendants queries

/-- Keep every native effect, raw diagnostic and optional cache observation. -/
abbrev ResultRelated := @EnumerationFlatNativeTerminal.ResultRelated

/-- An Empty child rejects without changing its caller, raw core or cache. -/
theorem empty (checkEmpty : Bool) (nativeFuel p h : Nat) (scs : List Suspended)
    (caller : Caller width) (before : Cached) (queries : Queries) :
    run checkEmpty nativeFuel p h scs .empty caller before queries =
      ((.ok (some []), caller, queries, before.core, before.waiting), some before) := by
  simp only [run, ↓reduceIte]

end MicroCFTA.SourceFlatPruningChildDispatch
