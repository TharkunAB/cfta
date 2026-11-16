import MicroCFTA.SourcePruningEnumerationSharedCachedTerminal
import MicroCFTA.SourcePruningEnumerationSharedDispatchUnionNormal
import MicroCFTA.SourcePruningEnumerationSharedIncomingUnionNormal

set_option autoImplicit false

namespace MicroCFTA.SourcePruningEnumerationSharedCachedTerminalUnionNormal
open EnumerationState InternedConstructorTemplates
open SourceCurrentRequiredUnionNormal (UnionNormal)
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Queries" => SourceEndpointMemo.Memos
variable {width : Nat}
variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]

/-- Every actual ordered shared fold retains normality at its returned caller. -/
theorem rawFold_unionNormal
    (checkEmpty : Bool) (nativeFuel p h : Nat) (sources : List Nat)
    (beforeCaller : Caller width) (before : EnumerationState.State Symbol Constraint)
    (target : Nat) (queries : Queries)
    (normal : UnionNormal beforeCaller.checked.native.machine.heap) :
    UnionNormal
      (SourcePruningEnumerationSharedCachedTerminal.rawFold checkEmpty nativeFuel p h sources
        beforeCaller before target queries).2.1.checked.native.machine.heap := by
  induction sources generalizing beforeCaller before queries with
  | nil => exact normal
  | cons source rest ih =>
      have retained := SourcePruningEnumerationSharedDispatchUnionNormal.dispatch_unionNormal
        checkEmpty nativeFuel p h beforeCaller before source target queries normal
      cases dispatched : SourcePruningEnumerationSharedDispatch.dispatch
          checkEmpty nativeFuel p h beforeCaller before source target queries with
      | mk result saved =>
          obtain ⟨reachedCaller, savedQueries⟩ := saved
          rw [dispatched] at retained
          dsimp only at retained
          cases result with
          | error fault =>
              simpa only [SourcePruningEnumerationSharedCachedTerminal.rawFold, dispatched] using retained
          | ok returned =>
              cases returned with
              | none =>
                  simpa only [SourcePruningEnumerationSharedCachedTerminal.rawFold, dispatched] using retained
              | some action =>
                  cases observed : ExceptT.run (action before) with
                  | nil =>
                      simpa only [SourcePruningEnumerationSharedCachedTerminal.rawFold, dispatched, observed] using retained
                  | cons row tail =>
                      cases row with
                      | error rowError =>
                          simpa only [SourcePruningEnumerationSharedCachedTerminal.rawFold, dispatched, observed] using retained
                      | ok value =>
                          obtain ⟨returnedUnit, after⟩ := value
                          cases returnedUnit
                          cases tail with
                          | nil =>
                              simpa only [SourcePruningEnumerationSharedCachedTerminal.rawFold, dispatched, observed] using
                                ih reachedCaller after savedQueries retained
                          | cons second remaining =>
                              simpa only [SourcePruningEnumerationSharedCachedTerminal.rawFold, dispatched, observed] using retained

/-- The actual cached fold has the same returned caller as the shared raw fold. -/
theorem fold_unionNormal
    (checkEmpty : Bool) (nativeFuel p h : Nat) (sources : List Nat)
    (beforeCaller : Caller width) (before : EnumerationExpandableIndex.Cached Symbol Constraint)
    (target : Nat) (queries : Queries)
    (normal : UnionNormal beforeCaller.checked.native.machine.heap) :
    UnionNormal
      (SourcePruningEnumerationSharedCachedTerminal.fold checkEmpty nativeFuel p h sources
        beforeCaller before target queries).1.2.1.checked.native.machine.heap := by
  rw [SourcePruningEnumerationSharedCachedTerminal.fold_erase]
  exact rawFold_unionNormal checkEmpty nativeFuel p h sources beforeCaller before.core target queries normal

/-- Every raw shared terminal outcome retains its actual returned caller normality. -/
theorem raw_unionNormal
    (checkEmpty : Bool) (representativeFuel nativeFuel p h : Nat)
    (first : EnumerationState.Suspended) (rest : List EnumerationState.Suspended)
    (waiting : EnumerationWaitingIndex.Waiting)
    (beforeCaller : Caller width) (before : EnumerationState.State Symbol Constraint)
    (incoming : Node) (incomingScs : List EnumerationState.Suspended) (queries : Queries)
    (normal : UnionNormal beforeCaller.checked.native.machine.heap) :
    UnionNormal
      (SourcePruningEnumerationSharedCachedTerminal.raw checkEmpty representativeFuel nativeFuel p h
        first rest waiting beforeCaller before incoming incomingScs queries).2.1.checked.native.machine.heap := by
  unfold SourcePruningEnumerationSharedCachedTerminal.raw
  by_cases empty : incoming = .empty
  · simpa only [ite_eq_left empty] using normal
  · simp only [ite_eq_right empty]
    generalize prefixObserved : ExceptT.run (SourcePruningEnumerationTerminalPrefix.run
      representativeFuel first rest waiting before) = actualPrefix
    cases actualPrefix with
    | nil => exact normal
    | cons prefixRow prefixTail =>
        cases prefixRow with
        | error prefixError => exact normal
        | ok prefixValue =>
            obtain ⟨⟨recorded, winner, moved⟩, joined⟩ := prefixValue
            cases prefixTail with
            | cons second remaining => exact normal
            | nil =>
                dsimp only
                have foldedNormal := rawFold_unionNormal checkEmpty nativeFuel p h recorded
                  beforeCaller joined winner queries normal
                generalize foldObserved : SourcePruningEnumerationSharedCachedTerminal.rawFold
                  checkEmpty nativeFuel p h recorded beforeCaller joined winner queries = folded at foldedNormal ⊢
                obtain ⟨foldResult, foldCaller, foldQueries, foldOuter⟩ := folded
                dsimp only at foldedNormal ⊢
                cases foldResult with
                | error foldFault => exact foldedNormal
                | ok foldReturned =>
                    cases foldReturned with
                    | none => exact foldedNormal
                    | some foldRaw =>
                        cases foldRaw with
                        | nil => exact foldedNormal
                        | cons foldRow foldTail =>
                            cases foldRow with
                            | error foldError => exact foldedNormal
                            | ok foldValue =>
                                obtain ⟨returnedUnit, foldCore⟩ := foldValue
                                cases returnedUnit
                                cases foldTail with
                                | cons second remaining => exact foldedNormal
                                | nil =>
                                    dsimp only
                                    have incomingNormal := SourcePruningEnumerationSharedIncomingUnionNormal.run_unionNormal
                                      checkEmpty representativeFuel nativeFuel p h foldCaller foldCore winner
                                      incoming incomingScs foldQueries foldedNormal
                                    generalize incomingObserved : SourcePruningEnumerationSharedIncomingNode.run
                                      checkEmpty representativeFuel nativeFuel p h foldCaller foldCore winner
                                      incoming incomingScs foldQueries = actualIncoming at incomingNormal ⊢
                                    obtain ⟨incomingResult, afterCaller, savedQueries, read⟩ := actualIncoming
                                    dsimp only at incomingNormal ⊢
                                    cases incomingResult with
                                    | error incomingFault => exact incomingNormal
                                    | ok incomingReturned =>
                                        cases incomingReturned <;> exact incomingNormal

/-- The actual cached shared terminal retains normality for every original fuel. -/
theorem run_unionNormal
    (checkEmpty : Bool) (representativeFuel nativeFuel p h indexFuel : Nat)
    (first : EnumerationState.Suspended) (rest : List EnumerationState.Suspended)
    (beforeCaller : Caller width) (before : EnumerationExpandableIndex.Cached Symbol Constraint)
    (incoming : Node) (incomingScs : List EnumerationState.Suspended) (queries : Queries)
    (normal : UnionNormal beforeCaller.checked.native.machine.heap) :
    UnionNormal
      (SourcePruningEnumerationSharedCachedTerminal.run checkEmpty representativeFuel nativeFuel p h indexFuel
        first rest beforeCaller before incoming incomingScs queries).1.2.1.checked.native.machine.heap := by
  rw [SourcePruningEnumerationSharedCachedTerminal.erase]
  exact raw_unionNormal checkEmpty representativeFuel nativeFuel p h first rest before.waiting
    beforeCaller before.core incoming incomingScs queries normal

end MicroCFTA.SourcePruningEnumerationSharedCachedTerminalUnionNormal
