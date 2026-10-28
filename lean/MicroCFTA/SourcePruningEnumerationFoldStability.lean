import MicroCFTA.SourcePruningEnumerationFold
import MicroCFTA.SourcePruningEnumerationDispatchStability

/-!
# Successful fold observations at larger bounds

Each dispatcher retains its exact optional action and endpoints.
The same action produces the same raw list.
Singleton successful lists continue from the same core and caller.
-/
namespace MicroCFTA.SourcePruningEnumerationFold
open EnumerationState InternedConstructorTemplates
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Queries" => SourceEndpointMemo.Memos
variable {EnumGuard : Type} {width : Nat}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]

/-- Every outer successful fold result retains its raw option and all exact endpoints. -/
theorem run_ok_stable
    {checkEmpty : Bool} {n p h N P H : Nat} {sources : List Nat}
    {beforeCaller afterCaller : Caller width} {before after : EnumerationState.State Symbol EnumGuard}
    {target : Nat} {queries savedQueries : Queries}
    {result : Option (List (Except EnumerationState.Error
      (Unit × EnumerationState.State Symbol EnumGuard)))}
    (observed : run checkEmpty n p h sources beforeCaller before target queries =
      (.ok result, afterCaller, savedQueries, after))
    (enoughNative : n ≤ N) (enoughP : p ≤ P) (enoughH : h ≤ H) :
    run checkEmpty N P H sources beforeCaller before target queries =
      (.ok result, afterCaller, savedQueries, after) := by
  induction sources generalizing beforeCaller before queries with
  | nil => simpa only [run] using observed
  | cons source rest ih =>
      rcases selected : SourcePruningEnumerationDispatch.dispatch checkEmpty n p h
          beforeCaller before source target queries with ⟨selection, headCaller, headQueries⟩
      cases selection with
      | error _fault =>
          simp only [run, selected] at observed
          cases observed
      | ok possible =>
          have later := SourcePruningEnumerationDispatch.dispatch_ok_stable
            selected enoughNative enoughP enoughH
          cases possible with
          | none => simpa only [run, selected, later] using observed
          | some action =>
              cases raw : ExceptT.run (action before) with
              | nil => simpa only [run, selected, later, raw] using observed
              | cons first tail =>
                  cases first with
                  | error _fault => simpa only [run, selected, later, raw] using observed
                  | ok pair =>
                      rcases pair with ⟨token, middle⟩
                      cases token
                      cases tail with
                      | nil =>
                          simp only [run, selected, raw] at observed
                          have tailLater := ih (beforeCaller := headCaller) (before := middle)
                            (queries := headQueries) observed
                          simpa only [run, later, raw] using tailLater
                      | cons _second _remaining =>
                          simpa only [run, selected, later, raw] using observed

end MicroCFTA.SourcePruningEnumerationFold
