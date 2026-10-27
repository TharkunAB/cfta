import MicroCFTA.SourceFlatPruningEntry
import MicroCFTA.SourceFlatPruningNativeBranches
import MicroCFTA.SourcePruningEnumerationNativeOrdinary

/-!
# Actual ordinary entry and sibling execution with a flat forest

The wrapper keeps every entry row.
Only a nonterminal ordinary parent starts the ordered sibling scan.
-/

namespace MicroCFTA.SourceFlatPruningNativeOrdinary
open EnumerationState InternedConstructorTemplates
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Queries" => SourceEndpointMemo.Memos
local notation "Cached" => EnumerationFlatCached.Cached Symbol Constraint
local notation "Raw" => List (Except Error ((Nat × Nat × List Suspended × Node) ×
  EnumerationFlatState.State Symbol Constraint))
variable {width : Nat}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]

/-- Enter once and scan the actual selected edges at the returned captured core. -/
noncomputable def run (checkEmpty : Bool) (nativeFuel p h uv : Nat)
    (edgesOf : Node → List (EdgeValue Symbol Constraint)) (caller : Caller width)
    (before : Cached) (queries : Queries) : Raw × Option (SourceFlatPruningNativeBranches.Result width) :=
  let raw := ExceptT.run (SourceFlatPruningEntry.enter caller.checked.native.machine.heap uv before.core)
  (raw, match raw with
    | [.ok ((target, _handle, scs, parent@(.node _ _ _ _)), entered)] =>
        if scs.any (fun sc => EqualityTrie.isTerminal sc.trie) then none
        else some (SourceFlatPruningNativeBranches.run checkEmpty nativeFuel p h target scs
          (EnumerationFlatCached.frame entered before) (edgesOf parent) caller queries)
    | _ => none)

/-- Retain all entry rows and distinguish absent scans from every actual branch result. -/
def ResultRelated (flat : Raw × Option (SourceFlatPruningNativeBranches.Result width))
    (earlier : List (Except Error ((Nat × Nat × List Suspended × Node) ×
      EnumerationState.State Symbol Constraint)) × Option (SourcePruningEnumerationNativeBranches.Result width)) : Prop :=
  EnumerationResultRelation.Results EnumerationFlatState.Related flat.1 earlier.1 ∧
    match flat.2, earlier.2 with
    | none, none => True
    | some first, some second => SourceFlatPruningNativeBranches.ResultRelated first second
    | _, _ => False

/-- The wrapper exposes the complete actual ordinary-entry observation. -/
theorem entry_readback (checkEmpty : Bool) (nativeFuel p h uv : Nat)
    (edgesOf : Node → List (EdgeValue Symbol Constraint)) (caller : Caller width)
    (before : Cached) (queries : Queries) :
    (run checkEmpty nativeFuel p h uv edgesOf caller before queries).1 =
      ExceptT.run (SourceFlatPruningEntry.enter caller.checked.native.machine.heap uv before.core) := rfl

end MicroCFTA.SourceFlatPruningNativeOrdinary
