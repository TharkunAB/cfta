import MicroCFTA.SourcePruningEnumerationSelectedOpaqueDispatch
import MicroCFTA.SourcePruningEnumerationChildKeyAncestry
import MicroCFTA.SourcePruningEnumerationKeyAncestryOwnFinalize

/-!
# Historical key shapes at actual opaque completion

The actual child cache retains the original carrier.
The same captured finalizer clears expansion keys and retains slot histories.
-/
namespace MicroCFTA.SourcePruningEnumerationSelectedOpaqueDispatch
open EnumerationState SourcePruningEnumerationKeyAncestry InternedConstructorTemplates
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
variable {width : Nat}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]

/-- Actual opaque completion retains the original historical key-shape carrier. -/
theorem complete_key_ancestry
    {checkEmpty : Bool} {r n p h k target : Nat} {scs : List Suspended} {value : Node}
    {caller reached : Caller width} {before after : Cached}
    {queries saved : SourceEndpointMemo.Memos} {fragment : Fragments.Fragment Symbol}
    {carrier : List (List (List (List Nat)))}
    (bounded : KeyAncestry carrier before.core)
    (observed : run checkEmpty r n p h k target scs value caller before queries =
      some (.complete fragment reached saved after)) : KeyAncestry carrier after.core := by
  let originalValue := value
  cases value
  case empty =>
    simp only [run, ↓reduceIte] at observed
    cases observed
  case' reference =>
    simp only [run, reduceCtorEq, Bool.false_eq_true, ↓reduceIte] at observed
  case' mu =>
    simp only [run, reduceCtorEq, Bool.false_eq_true, ↓reduceIte] at observed
  case' union =>
    simp only [run, reduceCtorEq, Bool.false_eq_true, ↓reduceIte] at observed
  case' node entry edges depth free =>
    cases terminal : scs.any (fun sc => EqualityTrie.isTerminal sc.trie)
    case false =>
      simp only [run, reduceCtorEq, terminal, Bool.not_false, ↓reduceIte] at observed
    case' true =>
      simp only [run, reduceCtorEq, terminal, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at observed
  all_goals
    rcases childRun : SourcePruningEnumerationChildDispatch.run checkEmpty r n p h k
        scs originalValue caller before queries with
      ⟨⟨outcome, actual, actualQueries, outer, waiting⟩, candidate⟩
    dsimp only [originalValue] at childRun
    rw [childRun] at observed
    cases outcome with
    | error _fault => cases observed
    | ok raw =>
        cases raw with
        | none => cases observed
        | some rows =>
            cases rows with
            | nil => cases observed
            | cons first rest =>
                cases first with
                | error _fault => cases observed
                | ok pair =>
                    rcases pair with ⟨produced, returned⟩
                    cases rest with
                    | cons _next _tail => cases observed
                    | nil =>
                        cases candidate with
                        | none => cases observed
                        | some middle =>
                            obtain ⟨finished, finalized, same⟩ := Option.map_eq_some_iff.mp observed
                            have sameCache : finished = after :=
                              (SourcePruningEnumerationSelectedEdge.Result.complete.inj same).2.2.2
                            rw [← sameCache]
                            exact SourcePruningEnumerationFinalize.run_key_ancestry
                              actual.checked.native.machine.heap k target produced middle finished
                              (SourcePruningEnumerationChildDispatch.observed_cache_key_ancestry
                                checkEmpty r n p h k scs originalValue caller before queries
                                bounded middle (congrArg Prod.snd childRun)) finalized

end MicroCFTA.SourcePruningEnumerationSelectedOpaqueDispatch
