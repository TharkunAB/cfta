import MicroCFTA.SourcePruningEnumerationTerminalPrefixStability
import MicroCFTA.SourcePruningEnumerationFoldStability
import MicroCFTA.SourcePruningEnumerationIncomingNodeStability
import MicroCFTA.SourcePruningEnumerationTerminal

/-!
# Stable successful terminal observations

Empty rejection and successful singleton rows retain every returned endpoint.
The representative, native, probing and worker bounds may increase separately.
-/
namespace MicroCFTA.SourcePruningEnumerationTerminal
open EnumerationState EnumerationCorrectness EnumerationSchedule
open InternedConstructorTemplates SourcePruningEnumerationNodes
local notation "Symbol" => SourcePruningTemplates.Symbol
local notation "Constraint" => SourceSymbolicIndex.Constraint FullSyntax.Formula
local notation "Node" => Value Symbol Constraint
local notation "Caller" => SourceCurrentAllocatedPartialState.State
local notation "Queries" => SourceEndpointMemo.Memos
variable {EnumGuard : Type} {width : Nat}
local notation "Core" => EnumerationState.State Symbol EnumGuard
local notation "Raw" => List (Except EnumerationState.Error (Fragments.Fragment Symbol × Core))
local notation "IncomingRaw" => List (Except EnumerationState.Error (Unit × Core))
private theorem incoming_rows_clean (winner : Nat) {incomingRaw : IncomingRaw} {raw : Raw}
    (mapped : incomingRaw.map (fun row => match row with
      | .error error => .error error
      | .ok result => .ok (.hole winner, result.2)) = raw)
    (clean : raw = [] ∨ ∃ fragment returned, raw = [.ok (fragment, returned)]) :
    incomingRaw = [] ∨ ∃ returned, incomingRaw = [.ok ((), returned)] := by
  rcases clean with empty | ⟨fragment, returned, single⟩
  · exact .inl (List.map_eq_nil_iff.mp (mapped.trans empty))
  · have singleMap := mapped.trans single
    cases incomingRaw with
    | nil => cases singleMap
    | cons row rest =>
      cases row with
      | error fault => cases singleMap
      | ok result =>
        rcases result with ⟨⟨⟩, actual⟩
        have restEmpty : rest = [] := List.map_eq_nil_iff.mp (List.cons.inj singleMap).2
        exact .inr ⟨actual, by simp only [restEmpty]⟩

variable [DecidableEq Symbol] [DecidableEq (EdgeKey Symbol Constraint)] [DecidableEq Node]
attribute [local instance] terminalMonadList

/-- A completed empty or singleton terminal point retains all fields at larger bounds. -/
theorem run_ok_stable
    {checkEmpty : Bool} {r R n N p P h H : Nat}
    {first : Suspended} {rest : List Suspended} {waiting : EnumerationWaitingIndex.Waiting}
    {beforeCaller afterCaller : Caller width} {before outer : Core}
    {incoming : Node} {incomingScs : List Suspended} {queries savedQueries : Queries}
    {raw : Raw} {moved : EnumerationWaitingIndex.Waiting}
    (observed : run checkEmpty r n p h first rest waiting beforeCaller before incoming incomingScs queries =
      (.ok (some raw), afterCaller, savedQueries, outer, moved))
    (successful : raw = [] ∨ ∃ fragment returned, raw = [.ok (fragment, returned)])
    (enoughRepresentative : r ≤ R) (enoughNative : n ≤ N) (enoughP : p ≤ P) (enoughH : h ≤ H) :
    run checkEmpty R N P H first rest waiting beforeCaller before incoming incomingScs queries =
      (.ok (some raw), afterCaller, savedQueries, outer, moved) := by
  unfold run at observed ⊢
  by_cases empty : incoming = .empty
  · simp only [ite_eq_left empty] at observed ⊢
    exact observed
  · simp only [ite_eq_right empty] at observed ⊢
    cases prefixObserved : ExceptT.run (SourcePruningEnumerationTerminalPrefix.run r first rest waiting before) with
    | nil =>
      simp only [prefixObserved] at observed
      cases observed
    | cons prefixEntry prefixTail =>
      cases prefixEntry with
      | error fault =>
        simp only [prefixObserved] at observed
        cases observed
      | ok prefixResult =>
        rcases prefixResult with ⟨⟨recorded, winner, transfer⟩, joined⟩
        cases prefixTail with
        | cons second remaining =>
          simp only [prefixObserved] at observed
          cases observed
        | nil =>
          have prefixLater := SourcePruningEnumerationTerminalPrefix.run_singleton_stable
            prefixObserved enoughRepresentative
          simp only [prefixObserved] at observed
          rw [prefixLater]
          dsimp only
          rcases foldObserved : SourcePruningEnumerationFold.run checkEmpty n p h recorded
              beforeCaller joined winner queries with
            ⟨foldResult, foldCaller, foldQueries, foldOuter⟩
          rw [foldObserved] at observed
          cases foldResult with
          | error fault => cases observed
          | ok possible =>
            have foldLater := SourcePruningEnumerationFold.run_ok_stable
              foldObserved enoughNative enoughP enoughH
            rw [foldLater]
            cases possible with
            | none => cases observed
            | some foldRaw =>
              cases foldRaw with
              | nil => exact observed
              | cons row tail =>
                cases row with
                | error fault => cases observed
                | ok result =>
                  rcases result with ⟨⟨⟩, folded⟩
                  cases tail with
                  | cons second remaining => cases observed
                  | nil =>
                    dsimp only at observed ⊢
                    rcases incomingObserved : SourcePruningEnumerationIncomingNode.run checkEmpty r n p h
                        foldCaller folded winner incoming incomingScs foldQueries with
                      ⟨incomingResult, reached, saved, read⟩
                    rw [incomingObserved] at observed
                    cases incomingResult with
                    | error fault => cases observed
                    | ok possible =>
                      cases possible with
                      | none => cases observed
                      | some incomingRaw =>
                        have mapped := Option.some.inj (Except.ok.inj (congrArg Prod.fst observed))
                        have incomingSuccessful := incoming_rows_clean winner mapped successful
                        have incomingLater := SourcePruningEnumerationIncomingNode.run_ok_stable
                          incomingObserved incomingSuccessful enoughRepresentative enoughNative enoughP enoughH
                        rw [incomingLater]
                        exact observed

/-- A successful literal terminal singleton is stable at independently larger bounds. -/
theorem run_singleton_stable
    {checkEmpty : Bool} {r R n N p P h H : Nat}
    {first : Suspended} {rest : List Suspended} {waiting : EnumerationWaitingIndex.Waiting}
    {beforeCaller afterCaller : Caller width} {before outer returned : Core}
    {incoming : Node} {incomingScs : List Suspended} {queries savedQueries : Queries}
    {fragment : Fragments.Fragment Symbol} {moved : EnumerationWaitingIndex.Waiting}
    (observed : run checkEmpty r n p h first rest waiting beforeCaller before incoming incomingScs queries =
      (.ok (some [.ok (fragment, returned)]), afterCaller, savedQueries, outer, moved))
    (enoughRepresentative : r ≤ R) (enoughNative : n ≤ N) (enoughP : p ≤ P) (enoughH : h ≤ H) :
    run checkEmpty R N P H first rest waiting beforeCaller before incoming incomingScs queries =
      (.ok (some [.ok (fragment, returned)]), afterCaller, savedQueries, outer, moved) :=
  run_ok_stable observed (.inr ⟨fragment, returned, rfl⟩)
    enoughRepresentative enoughNative enoughP enoughH

end MicroCFTA.SourcePruningEnumerationTerminal
