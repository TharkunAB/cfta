import MicroCFTA.SourceFlatPruningNativeOrdinary
import MicroCFTA.SourceFlatPruningNativeContinuations

namespace MicroCFTA.SourceFlatPruningNativeOrdinaryContinuations
open EnumerationState InternedConstructorTemplates
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Fragment" => Fragments.Fragment Symbol
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Queries" => SourceEndpointMemo.Memos
local notation "Cached" => EnumerationFlatCached.Cached Symbol Constraint
local notation "Raw" => List (Except EnumerationState.Error ((Nat × Nat × List Suspended × Node) ×
  EnumerationFlatState.State Symbol Constraint))
universe u v
variable {width : Nat} {Output : Type u} {Reason : Type v}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]

/-- Enter once and run each completed edge's continuation before its next sibling. -/
noncomputable def run
    (hook : Fragment → Caller width → Queries → Cached →
      SourceFlatPruningNativeContinuations.HookResult Output Reason width)
    (checkEmpty : Bool) (nativeFuel p h uv : Nat)
    (edgesOf : Node → List (EdgeValue Symbol Constraint)) (caller : Caller width)
    (before : Cached) (queries : Queries) :
    Raw × Option (SourceFlatPruningNativeContinuations.Result Output Reason width) :=
  let raw := ExceptT.run (SourceFlatPruningEntry.enter caller.checked.native.machine.heap uv before.core)
  (raw, match raw with
    | [.ok ((target, _handle, scs, parent@(.node _ _ _ _)), entered)] =>
        if scs.any (fun sc => EqualityTrie.isTerminal sc.trie) then none
        else some (SourceFlatPruningNativeContinuations.run hook checkEmpty nativeFuel p h target scs
          (EnumerationFlatCached.frame entered before) (edgesOf parent) caller queries)
    | _ => none)

/-- The wrapper retains every actual entry error, rejection and unsupported observation. -/
theorem entry_readback
    (hook : Fragment → Caller width → Queries → Cached →
      SourceFlatPruningNativeContinuations.HookResult Output Reason width)
    (checkEmpty : Bool) (nativeFuel p h uv : Nat)
    (edgesOf : Node → List (EdgeValue Symbol Constraint)) (caller : Caller width)
    (before : Cached) (queries : Queries) :
    (run hook checkEmpty nativeFuel p h uv edgesOf caller before queries).1 =
      ExceptT.run (SourceFlatPruningEntry.enter caller.checked.native.machine.heap uv before.core) := rfl

/-- An actual nonterminal ordinary entry supplies the captured input to the hook-aware fold. -/
theorem entered
    (hook : Fragment → Caller width → Queries → Cached →
      SourceFlatPruningNativeContinuations.HookResult Output Reason width)
    (checkEmpty : Bool) (nativeFuel p h uv target handle : Nat) (scs : List Suspended)
    (entry : Cache.Interned InternedBinderProtocol.NodeKey) (edges : List (EdgeValue Symbol Constraint))
    (depth : Nat) (free : List InternedBinderProtocol.Reference)
    (edgesOf : Node → List (EdgeValue Symbol Constraint)) (caller : Caller width)
    (before : Cached) (queries : Queries) (after : EnumerationFlatState.State Symbol Constraint)
    (observed : ExceptT.run (SourceFlatPruningEntry.enter caller.checked.native.machine.heap uv before.core) =
      [.ok ((target, handle, scs, .node entry edges depth free), after)])
    (nonterminal : scs.any (fun sc => EqualityTrie.isTerminal sc.trie) = false) :
    run hook checkEmpty nativeFuel p h uv edgesOf caller before queries =
      ([.ok ((target, handle, scs, .node entry edges depth free), after)],
        some (SourceFlatPruningNativeContinuations.run hook checkEmpty nativeFuel p h target scs
          (EnumerationFlatCached.frame after before) (edgesOf (.node entry edges depth free)) caller queries)) := by
  simp only [run, observed, nonterminal, Bool.false_eq_true, ↓reduceIte]

/-- An identity continuation preserves every actual flat ordinary result at each native bound. -/
theorem identity_run
    (checkEmpty : Bool) (nativeFuel p h uv : Nat)
    (edgesOf : Node → List (EdgeValue Symbol Constraint)) (caller : Caller width)
    (before : Cached) (queries : Queries) :
    run (SourceFlatPruningNativeContinuations.identityHook (Output := Output) (Reason := Reason))
      checkEmpty nativeFuel p h uv edgesOf caller before queries =
      ((SourceFlatPruningNativeOrdinary.run checkEmpty nativeFuel p h uv edgesOf caller before queries).1,
        (SourceFlatPruningNativeOrdinary.run checkEmpty nativeFuel p h uv edgesOf caller before queries).2.map
          SourceFlatPruningNativeContinuations.ofBranches) := by
  unfold run SourceFlatPruningNativeOrdinary.run
  dsimp only
  congr 1
  generalize ExceptT.run (SourceFlatPruningEntry.enter caller.checked.native.machine.heap uv before.core) = rows
  cases rows with
  | nil => rfl
  | cons first rest =>
      cases rest with
      | cons _ _ =>
          cases first with
          | error _ => rfl
          | ok pair =>
              obtain ⟨⟨_target, _handle, _scs, parent⟩, _entered⟩ := pair
              cases parent <;> rfl
      | nil =>
          cases first with
          | error _ => rfl
          | ok pair =>
              obtain ⟨⟨target, handle, scs, parent⟩, entered⟩ := pair
              cases parent with
              | node entry edges depth free =>
                  by_cases terminal : scs.any (fun sc => EqualityTrie.isTerminal sc.trie) = true
                  · simp only [terminal, ↓reduceIte, Option.map_none]
                  · simp only [terminal, Bool.false_eq_true, ↓reduceIte,
                      SourceFlatPruningNativeContinuations.identity_run, Option.map_some]
              | empty | reference _ | union _ _ _ _ | mu _ _ _ _ => rfl

end MicroCFTA.SourceFlatPruningNativeOrdinaryContinuations
