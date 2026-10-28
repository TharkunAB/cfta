import MicroCFTA.SourcePruningEnumerationSelectedOpaqueDispatch
import MicroCFTA.SourcePruningEnumerationChildProper
import MicroCFTA.SourcePruningEnumerationOwnFinalizeProper

/-!
# Proper storage at the actual prepared opaque completion

The actual child candidate retains proper stored paths.
Finalization writes the captured slot with that same child fragment.
The stored source and prepared value remain separate.
-/
namespace MicroCFTA.SourcePruningEnumerationSelectedOpaqueDispatch
open EnumerationState EnumerationProgress InternedConstructorTemplates
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
variable {width : Nat}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]

/-- Actual opaque completion retains proper storage from its original child inputs. -/
theorem complete_proper
    {checkEmpty : Bool} {r n p h k target : Nat} {scs : List Suspended} {value : Node}
    {caller reached : Caller width} {before after : Cached}
    {queries saved : SourceEndpointMemo.Memos} {fragment : Fragments.Fragment Symbol}
    (proper : ProperState before.core) (inputs : ProperInputs scs)
    (observed : run checkEmpty r n p h k target scs value caller before queries =
      some (.complete fragment reached saved after)) : ProperState after.core := by
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
                            exact SourcePruningEnumerationFinalize.run_proper
                              actual.checked.native.machine.heap k target produced middle finished
                              (SourcePruningEnumerationChildDispatch.observed_cache_proper
                                checkEmpty r n p h k scs originalValue caller before queries
                                proper inputs middle (congrArg Prod.snd childRun)) finalized

end MicroCFTA.SourcePruningEnumerationSelectedOpaqueDispatch
