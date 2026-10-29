import MicroCFTA.SourcePruningEnumerationSelectedOpaqueDispatch
import MicroCFTA.SourcePruningEnumerationChildAncestryExtension
import MicroCFTA.SourcePruningEnumerationAncestryExtensionOwn

/-!
# Retained ancestry at actual opaque and terminal receipts

Each actual attached child cache retains every original slot key.
Successful captured finalization clears the active expansion history.
Stopped receipts keep their actual child cache and expansion history.
-/
namespace MicroCFTA.SourcePruningEnumerationSelectedOpaqueDispatch
open EnumerationState SourcePruningEnumerationAncestryExtension InternedConstructorTemplates
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Queries" => SourceEndpointMemo.Memos
local notation "Cached" => EnumerationExpandableIndex.Cached Symbol Constraint
local notation "Result" => SourcePruningEnumerationSelectedEdge.Result
variable {width : Nat}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]

/-- Every actual opaque receipt extends its own input histories at each attached cache. -/
theorem observed_cache_ancestry_extension
    {checkEmpty : Bool} {r n p h k target : Nat} {scs : List Suspended} {value : Node}
    {caller : Caller width} {before : Cached} {queries : Queries} {result : Result width}
    (observed : run checkEmpty r n p h k target scs value caller before queries = some result) :
    match (generalizing := false) result with
    | .complete _ _ _ after => Extends before.core after.core ∧ after.core.expansionAncestry = []
    | .rejected _ _ after | .stopped _ _ (some after) =>
        Extends before.core after.core ∧ after.core.expansionAncestry = before.core.expansionAncestry
    | _ => True := by
  let originalValue := value
  cases value
  case empty =>
    simp only [run, ↓reduceIte] at observed
    cases observed
    exact ⟨Extends.refl before.core, rfl⟩
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
    have childFields (middle : Cached) (attached : candidate = some middle) :
        Extends before.core middle.core ∧
          middle.core.expansionAncestry = before.core.expansionAncestry :=
      SourcePruningEnumerationChildDispatch.observed_cache_ancestry_extension
        checkEmpty r n p h k scs originalValue caller before queries middle
        ((congrArg Prod.snd childRun).trans attached)
    cases outcome with
    | error fault =>
        cases observed
        cases candidate with
        | none => trivial
        | some middle => exact childFields middle rfl
    | ok raw =>
        cases raw with
        | none =>
            cases observed
            cases candidate with
            | none => trivial
            | some middle => exact childFields middle rfl
        | some rows =>
            cases rows with
            | nil =>
                cases observed
                cases candidate with
                | none => trivial
                | some middle => exact childFields middle rfl
            | cons first rest =>
                cases first with
                | error fault =>
                    cases observed
                    cases candidate with
                    | none => trivial
                    | some middle => exact childFields middle rfl
                | ok pair =>
                    rcases pair with ⟨produced, returned⟩
                    cases rest with
                    | cons next later =>
                        cases observed
                        cases candidate with
                        | none => trivial
                        | some middle => exact childFields middle rfl
                    | nil =>
                        cases candidate with
                        | none =>
                            cases observed
                            trivial
                        | some middle =>
                            obtain ⟨finished, finalized, same⟩ := Option.map_eq_some_iff.mp observed
                            have inherited := childFields middle rfl
                            have finishedFields := SourcePruningEnumerationFinalize.run_ancestry_extension
                              actual.checked.native.machine.heap k target produced middle finished finalized
                            cases same
                            exact ⟨inherited.1.trans finishedFields.1, finishedFields.2⟩

end MicroCFTA.SourcePruningEnumerationSelectedOpaqueDispatch
