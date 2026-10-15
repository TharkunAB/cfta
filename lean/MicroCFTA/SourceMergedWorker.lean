import MicroCFTA.SourceMergedCache
import MicroCFTA.MergedSourceGrouping

/-!
# General repaired merged-alternative execution

Each comparison uses the actual fresh ordinary reader. The worker keeps
the source grouping, four-row threshold, guards, and recursive boundaries.
The ordinary recursion bound and comparison bound remain separate.
-/
namespace MicroCFTA.SourceMergedWorker
open InternedConstructorTemplates
open MergedSourceComparison (Result)
open MergedColdMerge (Action pure bind work map retainedColumn small)

/-- Complete the actual repaired child filter before the retained-column source branches. -/
def column [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Symbol]
    (recurse : Value Symbol Guard → Action Symbol Guard (Value Symbol Guard))
    (clear : Guard → Bool) (comparisonFuel : Nat) (inputs : List (Value Symbol Guard)) : Action Symbol Guard (Value Symbol Guard) :=
  bind (SourceMergedSelection.select clear comparisonFuel inputs) (retainedColumn recurse)

/-- A large group merges each ordered column and creates the source Top-guard edge. -/
def large [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Symbol]
    (recurse : Value Symbol Guard → Action Symbol Guard (Value Symbol Guard))
    (clear : Guard → Bool) (comparisonFuel : Nat) (top : Guard)
    (first : EdgeValue Symbol Guard) (rest : List (EdgeValue Symbol Guard)) : Action Symbol Guard (EdgeValue Symbol Guard) :=
  bind (map (column recurse clear comparisonFuel)
    (MergedAlternativesGroups.columns ((first :: rest).map EdgeValue.children) first.children.length))
    fun children => work (makeEdge first.entry.key.symbol top children)

/-- At most four rows keep their original guards; larger groups use the column branch. -/
def group [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Symbol]
    (recurse : Value Symbol Guard → Action Symbol Guard (Value Symbol Guard))
    (clear : Guard → Bool) (comparisonFuel : Nat) (top : Guard) (edges : List (EdgeValue Symbol Guard)) :
    Action Symbol Guard (List (EdgeValue Symbol Guard)) :=
  if edges.length ≤ 4 then map (small recurse) edges
  else match edges with
  | [] => pure []
  | first :: rest => bind (large recurse clear comparisonFuel top first rest) (fun edge => pure [edge])

/-- Finish every group in source order before actual ordinary-node construction. -/
def root [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Symbol]
    (recurse : Value Symbol Guard → Action Symbol Guard (Value Symbol Guard))
    (clear : Guard → Bool) (comparisonFuel : Nat) (top : Guard) (groups : List (List (EdgeValue Symbol Guard))) :
    Action Symbol Guard (Value Symbol Guard) :=
  bind (map (group recurse clear comparisonFuel top) groups) fun rows => work (makeNode rows.flatten)

/-- Recurse into closed ordinary roots and return source recursive boundaries unchanged. -/
def worker [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Symbol]
    (grouping : List (EdgeValue Symbol Guard) → List (List (EdgeValue Symbol Guard)))
    (clear : Guard → Bool) (top : Guard) : Nat → Nat → Value Symbol Guard → Action Symbol Guard (Value Symbol Guard)
  | ordinaryFuel, comparisonFuel, value => match value with
    | .node _ edges _ free =>
        if free = [] then match ordinaryFuel with
          | 0 => fun state => .failed .exhausted state
          | remaining + 1 => root (worker grouping clear top remaining comparisonFuel) clear comparisonFuel top (grouping edges)
        else pure value
    | _ => pure value

/-- The source ordinary height supplies the recursion bound for executable grouping. -/
def execute [DecidableEq (EdgeKey Symbol Guard)] [DecidableEq Symbol]
    (clear : Guard → Bool) (top : Guard) (comparisonFuel : Nat) (value : Value Symbol Guard) : Action Symbol Guard (Value Symbol Guard) :=
  worker MergedSourceGrouping.groups clear top (MergedOrdinaryHeight.height value) comparisonFuel value

end MicroCFTA.SourceMergedWorker
